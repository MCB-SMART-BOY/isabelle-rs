use std::collections::{BTreeMap, HashSet};
use std::path::Path;

use serde_json::{Map, Value, json};
use sha1::{Digest as _, Sha1};

use super::super::common::{digest_bytes, require};
use super::super::decode_execution;
use super::super::decode_inventory::ROOTS;
use crate::runner::StepError;

const SOURCE_PREFIX: &str = "/work/fixed-source/";
const INITIAL_THEORIES: [&str; 3] = ["Pure", "ML_Bootstrap", "Pure.Sessions"];
const OBSERVED: [&str; 2] = ["executed_theory_commands", "resolved_ML_file_inputs"];
const UNAVAILABLE: [&str; 6] = [
    "Pure_bootstrap_command_spans",
    "anonymous_ephemeral_facts",
    "unregistered_proof_steps",
    "dynamic_fact_evaluations",
    "ML_runtime_call_graph",
    "implicit_ML_load_events",
];
const OBSERVER: &str = "Reference_Execution.Reference_Observer";
const ORDERING: &str = "per_theory_source_segments_not_global_thread_order";
const RESOURCE_COMMANDS: [&str; 6] = [
    "ML_file",
    "ML_file_debug",
    "ML_file_no_debug",
    "SML_file",
    "SML_file_debug",
    "SML_file_no_debug",
];

pub(super) struct SourceInventory<'a> {
    pub sources: BTreeMap<String, String>,
    pub manifest: &'a Map<String, Value>,
}

fn arr<'a>(value: &'a Value, context: &str) -> Result<&'a [Value], StepError> {
    value
        .as_array()
        .map(Vec::as_slice)
        .ok_or_else(|| StepError::Input(format!("{context}: expected list")))
}

fn text<'a>(value: &'a Value, context: &str) -> Result<&'a str, StepError> {
    value
        .as_str()
        .filter(|text| !text.is_empty())
        .ok_or_else(|| StepError::Input(format!("{context}: missing string")))
}

pub(super) fn inspect_inventory<'a>(
    inventory: &'a Value,
    root: &Path,
) -> Result<SourceInventory<'a>, StepError> {
    let (sources, manifest) = decode_execution::inspect_inventory(inventory, root)?;
    isabelle_evidence::validate_graph(arr(&inventory["theories"], "inventory theories")?)
        .map_err(|error| StepError::Input(error.to_string()))?;
    Ok(SourceInventory { sources, manifest })
}
fn inspect_commands(theory: &Value) -> Result<(), StepError> {
    let name = text(&theory["name"], "executed theory")?;
    let commands = arr(&theory["commands"], "executed commands")?;
    require(!commands.is_empty(), format!("{name}: missing commands"))?;
    let (mut previous_line, mut previous_offset) = (0, 0);
    let mut theory_count = 0;
    for (index, command) in commands.iter().enumerate() {
        let identity = text(&command["name"], "command name")?;
        let line = command["line"]
            .as_u64()
            .ok_or_else(|| StepError::Input(format!("{name}: invalid command line")))?;
        let offset = command["offset"]
            .as_u64()
            .ok_or_else(|| StepError::Input(format!("{name}: invalid command offset")))?;
        require(
            command["source"] == theory["source"]
                && command["skipped"] == false
                && command["sequence"] == index + 1
                && line >= previous_line
                && offset > previous_offset,
            format!("{name}: command identity, order or location mismatch"),
        )?;
        previous_line = line;
        previous_offset = offset;
        let files = arr(&command["files"], "resolved command files")?;
        require(
            files.len() == usize::from(RESOURCE_COMMANDS.contains(&identity)),
            format!("{name}: resolved file binding count mismatch"),
        )?;
        if identity == "theory" {
            theory_count += 1;
        }
    }
    require(
        theory_count == 1 && commands.last().is_some_and(|last| last["name"] == "end"),
        format!("{name}: incomplete command sequence"),
    )
}

pub(super) fn inspect_execution<'a>(
    execution: &'a Value,
    inventory: &SourceInventory<'_>,
) -> Result<&'a [Value], StepError> {
    require(
        execution["schema"] == 1
            && execution["reference"] == "Isabelle2025"
            && execution["session"] == "Reference_Execution"
            && execution["roots"] == json!(ROOTS)
            && execution["initial_theories"] == json!(INITIAL_THEORIES),
        "Execution identity or fixed roots mismatch",
    )?;
    let coverage = &execution["coverage"];
    require(
        coverage["observed"] == json!(OBSERVED)
            && coverage["unavailable"] == json!(UNAVAILABLE)
            && coverage["ordering"] == ORDERING
            && coverage["excluded_observer_theory"] == OBSERVER,
        "Execution coverage contract mismatch",
    )?;
    let theories = arr(&execution["theories"], "executed theories")?;
    let mut names = HashSet::new();
    for theory in theories {
        let name = text(&theory["name"], "executed theory name")?;
        require(names.insert(name), format!("Duplicate executed theory {name}"))?;
        let relative = inventory
            .sources
            .get(name)
            .ok_or_else(|| StepError::Input(format!("Unexpected executed theory {name}")))?;
        require(
            theory["source"] == relative.as_str()
                && theory["sha256"] == inventory.manifest[relative.as_str()],
            format!("{name}: executed source differs from inventory"),
        )?;
        inspect_commands(theory)?;
    }
    require(
        names.len() + 1 == inventory.sources.len()
            && inventory
                .sources
                .keys()
                .filter(|name| name.as_str() != "Pure")
                .all(|name| names.contains(name.as_str())),
        "Executed theory set differs from inventory (excluding Pure)",
    )?;
    Ok(theories)
}

pub(super) fn catalog_commands(
    theories: &[Value],
    root: &Path,
) -> Result<(Vec<Value>, Vec<Value>), StepError> {
    let mut requirements: std::collections::BTreeMap<&str, Vec<Value>> =
        std::collections::BTreeMap::new();
    let mut bindings = Vec::new();
    for theory in theories {
        for command in arr(&theory["commands"], "executed commands")? {
            let name = text(&command["name"], "command name")?;
            let occurrence = json!({"theory": theory["name"], "source": command["source"], "line": command["line"], "offset": command["offset"], "sequence": command["sequence"]});
            requirements.entry(name).or_default().push(occurrence.clone());
            for file in arr(&command["files"], "command file bindings")? {
                let relative = text(&file["path"], "ML file path")?;
                let (canonical, bytes) = decode_execution::read_fixed_file(
                    &format!("{SOURCE_PREFIX}{relative}"),
                    root,
                    "ML file binding",
                )?;
                require(
                    canonical == relative,
                    format!(
                        "ML file binding identity mismatch: {relative} resolves to {canonical}"
                    ),
                )?;
                let sha1 = base16ct::lower::encode_string(&Sha1::digest(&bytes));
                require(
                    file["sha256"] == digest_bytes(&bytes) && file["sha1"] == sha1,
                    format!("ML file binding hash mismatch: {relative}"),
                )?;
                let mut binding =
                    occurrence.as_object().cloned().ok_or_else(|| StepError::Protocol {
                        operation: "catalog command".into(),
                        detail: "malformed internal occurrence".into(),
                    })?;
                binding.insert("command".into(), json!(name));
                binding.insert("file".into(), file.clone());
                bindings.push(Value::Object(binding));
            }
        }
    }
    let requirements = requirements.into_iter().map(|(name, occurrences)| json!({"name": name, "occurrences": occurrences, "native_rust_status": "Unsupported", "scope": "general_official_source_execution", "rationale": "src/theory/trusted_loader.rs::compile_trusted_source accepts only the separate TrueI (HOL) and Pure identity fixture forms; it does not execute general official theory commands"})).collect();
    Ok((requirements, bindings))
}
