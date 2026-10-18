use super::{
    common::{digest_file, require, resolve_source_path},
    yxml::{self, Node},
};
use crate::runner::{StepError, io_error};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, HashSet},
    path::Path,
};
mod encoded;
mod entities;

pub const ROOTS: [&str; 9] = [
    "HOL.HOL",
    "HOL.Orderings",
    "HOL.Set",
    "HOL.Nat",
    "HOL.List",
    "HOL.Fun",
    "HOL.Product_Type",
    "HOL.Sum_Type",
    "HOL.Option",
];
pub const EXPECTED_THEORY_COUNT: usize = 67;
const SECTIONS: [(&str, &str); 15] = [
    ("parents", "parent"),
    ("import_specifications", "import_specification"),
    ("default_sort", "sort"),
    ("types", "type_declaration"),
    ("classes", "class"),
    ("class_relations", "class_relation"),
    ("arities", "arity"),
    ("constants", "constant"),
    ("axioms", "axiom"),
    ("specifications", "specification"),
    ("constant_definitions", "constant_definition"),
    ("fact_indexes", "fact_index"),
    ("fact_groups", "fact_group"),
    ("named_derivations", "named_derivation"),
    ("oracle_registrations", "oracle_registration"),
];
const OBSERVED: [&str; 5] = [
    "static_theory_snapshot",
    "raw_named_static_facts",
    "registered_oracles",
    "transitive_oracle_footprints",
    "named_theorem_dependencies",
];
const UNAVAILABLE: [&str; 7] = [
    "executed_commands",
    "ML_load_events",
    "resource_load_events",
    "anonymous_ephemeral_facts",
    "unregistered_proof_steps",
    "external_process_events",
    "dynamic_fact_evaluations",
];

fn decode_theory(node: &Node) -> Result<Value, StepError> {
    let (attrs, body) = yxml::inspect(node, "theory", &["name", "master_directory", "source"])?;
    require(
        !attrs["name"].is_empty() && body.len() == SECTIONS.len(),
        "Missing theory identity or section",
    )?;
    let nodes = yxml::elements(body)?;
    require(
        nodes.iter().zip(SECTIONS).all(|(node, (section, _))| node.tag == section),
        format!("{}: invalid section order/shape", attrs["name"]),
    )?;
    let mut decoded = json!({"name":attrs["name"],"master_directory":attrs["master_directory"],"source":attrs["source"]});
    for (index, (section, tag)) in SECTIONS.iter().enumerate() {
        decoded[*section] = if *section == "default_sort" {
            encoded::typed_child(nodes[index], section, encoded::sort)?
        } else {
            entities::decode_section(body, index, section, tag)?
        };
    }
    Ok(decoded)
}
fn decode_coverage(node: &Node) -> Result<Value, StepError> {
    let (_, body) = yxml::inspect(node, "coverage", &[])?;
    let mut observed = vec![];
    let mut unavailable = vec![];
    for item in yxml::elements(body)? {
        let value = yxml::text(item, &item.tag)?;
        match item.tag.as_str() {
            "observed" => observed.push(value),
            "unavailable" => unavailable.push(value),
            _ => return Err(StepError::Input("Invalid coverage record".into())),
        }
    }
    yxml::unique(observed.clone(), "observed coverage entries")?;
    yxml::unique(unavailable.clone(), "unavailable coverage entries")?;
    require(
        observed.iter().map(String::as_str).collect::<HashSet<_>>() == HashSet::from(OBSERVED)
            && unavailable.iter().map(String::as_str).collect::<HashSet<_>>()
                == HashSet::from(UNAVAILABLE),
        "Snapshot coverage differs from the v1 observed/unavailable contract",
    )?;
    Ok(json!({"observed":observed,"unavailable":unavailable}))
}
fn attach_sources(
    theories: &mut [Value],
    source_root: &Path,
    source_map: &Value,
) -> Result<Value, StepError> {
    let mut manifest = BTreeMap::new();
    for theory in theories {
        let name = yxml::string(theory, "name")?.to_owned();
        let expected = source_map
            .get(&name)
            .and_then(|mapping| mapping.get("source"))
            .and_then(Value::as_str)
            .ok_or_else(|| StepError::Input(format!("Missing built source mapping for {name}")))?;
        let source = resolve_source_path(yxml::string(theory, "source")?, source_root)?;
        let master = resolve_source_path(
            &format!("{}/", yxml::string(theory, "master_directory")?),
            source_root,
        )?;
        require(
            source.is_file() && master.is_dir() && source.parent() == Some(master.as_path()),
            format!("Theory {name}: missing source or inconsistent master directory"),
        )?;
        require(
            source == resolve_source_path(expected, source_root)?,
            format!("Theory {name}: source differs from built session mapping"),
        )?;
        let relative = source
            .strip_prefix(source_root)
            .map_err(|_| StepError::Input(format!("{name}: source outside fixed root")))?
            .to_str()
            .ok_or_else(|| StepError::Input(format!("{name}: non-UTF8 source path")))?
            .replace(std::path::MAIN_SEPARATOR, "/");
        require(
            !manifest.contains_key(&relative),
            format!("Source file reused for different theory identities: {relative}"),
        )?;
        manifest.insert(relative.clone(), digest_file(&source)?);
        theory["source"] = json!(relative);
        theory["master_directory"] = json!(
            master
                .strip_prefix(source_root)
                .map_err(|_| StepError::Input(format!("{name}: master outside fixed root")))?
                .to_str()
                .ok_or_else(|| StepError::Input(format!("{name}: non-UTF8 master path")))?
                .replace(std::path::MAIN_SEPARATOR, "/")
        );
    }
    Ok(json!(manifest))
}
pub fn decode_inventory(
    raw: &str,
    source_root: &Path,
    source_map: &Value,
) -> Result<Value, StepError> {
    let source_root = source_root.canonicalize().map_err(|source| {
        io_error(format!("resolve fixed source root {}", source_root.display()), source)
    })?;
    require(source_root.is_dir(), format!("Missing fixed source root {}", source_root.display()))?;
    let parsed = yxml::parse(raw)?;
    let (attrs, body) = yxml::inspect(&parsed, "reference_snapshot", &["version", "reference"])?;
    require(
        attrs["version"] == "1" && attrs["reference"] == "Isabelle2025",
        "Unsupported reference snapshot version",
    )?;
    require(body.len() == 3, "Missing snapshot roots/coverage/theories")?;
    let roots: Vec<String> = yxml::group(yxml::child(body, 0)?, "roots", "root")?
        .into_iter()
        .map(|root| {
            Ok(yxml::empty_attrs(root, "root", &["name"])?
                .get("name")
                .and_then(Value::as_str)
                .ok_or_else(|| StepError::Input("Invalid inventory root".into()))?
                .to_owned())
        })
        .collect::<Result<_, StepError>>()?;
    require(roots.iter().map(String::as_str).eq(ROOTS), "Fixed root identities or order mismatch")?;
    let coverage = decode_coverage(yxml::child(body, 1)?)?;
    let mut theories: Vec<Value> = yxml::group(yxml::child(body, 2)?, "theories", "theory")?
        .into_iter()
        .map(decode_theory)
        .collect::<Result<_, _>>()?;
    isabelle_evidence::validate_graph(&theories)
        .map_err(|error| StepError::Input(error.to_string()))?;
    isabelle_evidence::validate_entities(&theories)
        .map_err(|error| StepError::Input(error.to_string()))?;
    let source_sha256 = attach_sources(&mut theories, &source_root, source_map)?;
    let mut output = json!({"schema_version":1,"reference":"Isabelle2025","roots":roots});
    output["coverage"] = coverage;
    output["theories"] = Value::Array(theories);
    output["source_sha256"] = source_sha256;
    Ok(output)
}

/// Decode the inventory against executed overlay R bytes, not the frozen B snapshot.
pub fn decode_inventory_v2(
    raw: &str,
    executed_root: &Path,
    source_map: &Value,
    run_id: &str,
    pure_heap_sha256: &str,
) -> Result<Value, StepError> {
    require(
        !run_id.is_empty() && crate::reference::decode_execution::valid_hash(pure_heap_sha256, 64),
        "instrumented inventory lacks run or loaded Pure heap identity",
    )?;
    let mut inventory = decode_inventory(raw, executed_root, source_map)?;
    inventory["schema_version"] = json!(2);
    inventory["run_id"] = json!(run_id);
    inventory["loaded_pure_heap_tree_sha256"] = json!(pure_heap_sha256);
    Ok(inventory)
}
