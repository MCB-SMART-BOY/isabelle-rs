use super::{
    common::{digest_bytes, open_regular, require, resolve_source_path},
    decode_inventory::ROOTS,
    yxml::{self, Node, Part},
};
use crate::runner::{StepError, io_error};
use serde_json::{Value, json};
use sha1::{Digest, Sha1};
use std::{
    collections::{BTreeMap, HashSet},
    io::Read,
    path::Path,
};

const MAX_SOURCE_BYTES: u64 = 512 * 1024 * 1024;
pub const RESOURCE_COMMANDS: [&str; 6] = [
    "ML_file",
    "ML_file_debug",
    "ML_file_no_debug",
    "SML_file",
    "SML_file_debug",
    "SML_file_no_debug",
];
const OBSERVER: &str = "Reference_Execution.Reference_Observer";
const OBSERVER_SOURCE: &str = "/work/session/Reference_Observer.thy";
const INITIAL: [&str; 3] = ["Pure", "ML_Bootstrap", "Pure.Sessions"];
const OBSERVED: [&str; 2] = ["executed_theory_commands", "resolved_ML_file_inputs"];
const UNAVAILABLE: [&str; 6] = [
    "Pure_bootstrap_command_spans",
    "anonymous_ephemeral_facts",
    "unregistered_proof_steps",
    "dynamic_fact_evaluations",
    "ML_runtime_call_graph",
    "implicit_ML_load_events",
];

pub fn read_empty_attributes(
    node: &Node,
    tag: &str,
    fields: &[&str],
) -> Result<serde_json::Map<String, Value>, StepError> {
    yxml::empty_attrs(node, tag, fields)
}
fn relative_path(value: &str, context: &str) -> Result<(), StepError> {
    require(
        value.starts_with("src/")
            && value.split('/').all(|part| !matches!(part, "" | "." | ".."))
            && !value.contains('\\'),
        format!("{context}: invalid fixed-source relative path {value:?}"),
    )
}
pub fn read_fixed_file(
    symbolic: &str,
    source_root: &Path,
    context: &str,
) -> Result<(String, Vec<u8>), StepError> {
    let path = resolve_source_path(symbolic, source_root)?;
    require(path.is_file(), format!("{context}: not a regular file {symbolic:?}"))?;
    let relative = path
        .strip_prefix(source_root)
        .map_err(|_| StepError::Input(format!("{context}: file outside fixed root {symbolic}")))?
        .to_str()
        .ok_or_else(|| StepError::Input(format!("{context}: non-UTF8 source {symbolic}")))?
        .replace(std::path::MAIN_SEPARATOR, "/");
    relative_path(&relative, context)?;
    let file = open_regular(&path)?;
    let limit = MAX_SOURCE_BYTES;
    require(
        file.metadata()
            .map_err(|source| {
                io_error(format!("{context}: stat fixed source {}", path.display()), source)
            })?
            .len()
            <= limit,
        format!("{context}: fixed source exceeds byte budget {}", path.display()),
    )?;
    let mut bytes = Vec::new();
    file.take(limit + 1).read_to_end(&mut bytes).map_err(|source| {
        io_error(format!("{context}: read fixed source {}", path.display()), source)
    })?;
    require(
        bytes.len() as u64 <= limit,
        format!("{context}: fixed source grew beyond byte budget {}", path.display()),
    )?;
    Ok((relative, bytes))
}
pub type InventoryInputs<'a> = (BTreeMap<String, String>, &'a serde_json::Map<String, Value>);

pub fn inspect_inventory<'a>(
    inventory: &'a Value,
    source_root: &Path,
) -> Result<InventoryInputs<'a>, StepError> {
    let source_root = source_root.canonicalize().map_err(|source| {
        io_error(format!("resolve fixed source root {}", source_root.display()), source)
    })?;
    require(source_root.is_dir(), format!("Missing fixed source root {}", source_root.display()))?;
    require(
        (inventory["schema_version"] == 1 || inventory["schema_version"] == 2)
            && inventory["reference"] == "Isabelle2025"
            && inventory["roots"] == json!(ROOTS),
        "Inventory reference or fixed roots mismatch",
    )?;
    let theories = yxml::array(inventory, "theories")?;
    let manifest = inventory
        .get("source_sha256")
        .and_then(Value::as_object)
        .ok_or_else(|| StepError::Input("Missing inventory source hashes".into()))?;
    let mut sources = BTreeMap::new();
    let mut seen = HashSet::new();
    for theory in theories {
        let name = yxml::string(theory, "name")?;
        require(
            !name.is_empty()
                && sources
                    .insert(name.to_owned(), yxml::string(theory, "source")?.to_owned())
                    .is_none(),
            "Malformed or duplicate inventory theory identity",
        )?;
        let relative = yxml::string(theory, "source")?;
        relative_path(relative, name)?;
        require(seen.insert(relative), format!("{name}: duplicate inventory source"))?;
    }
    require(
        sources.contains_key("Pure")
            && ROOTS.iter().all(|root| sources.contains_key(*root))
            && !sources.contains_key(OBSERVER),
        "Missing Pure or fixed roots, or observer present in inventory",
    )?;
    require(
        manifest.len() == seen.len()
            && manifest.keys().all(|source| seen.contains(source.as_str())),
        "Inventory source hash set differs from theory sources",
    )?;
    for (name, relative) in &sources {
        let expected = manifest
            .get(relative)
            .and_then(Value::as_str)
            .ok_or_else(|| StepError::Input(format!("{name}: invalid inventory SHA256")))?;
        require(valid_hash(expected, 64), format!("{name}: invalid inventory SHA256"))?;
        let (actual, bytes) =
            read_fixed_file(&format!("/work/fixed-source/{relative}"), &source_root, name)?;
        require(
            actual == *relative && digest_bytes(&bytes) == expected,
            format!("{name}: fixed source SHA256 differs from inventory"),
        )?;
    }
    Ok((sources, manifest))
}
pub fn valid_hash(value: &str, length: usize) -> bool {
    value.len() == length
        && value.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}
fn decode_file(node: &Node, source_root: &Path, name: &str) -> Result<Value, StepError> {
    let attrs = read_empty_attributes(node, "file", &["path", "sha1"])?;
    let path = attrs["path"]
        .as_str()
        .ok_or_else(|| StepError::Input("Missing resolved ML path".into()))?;
    let expected = attrs["sha1"]
        .as_str()
        .ok_or_else(|| StepError::Input("Missing resolved ML SHA1".into()))?;
    let (relative, bytes) =
        read_fixed_file(path, source_root, &format!("{name}: resolved ML file input"))?;
    require(valid_hash(expected, 40), format!("{name}: invalid resource SHA1"))?;
    require(
        base16ct::lower::encode_string(&Sha1::digest(&bytes)) == expected,
        format!("{name}: resource SHA1 drift at {relative}"),
    )?;
    Ok(json!({"path":relative,"sha1":expected,"sha256":digest_bytes(&bytes)}))
}
fn position(
    attrs: &std::collections::BTreeMap<String, String>,
    name: &str,
    previous: (u64, u64),
) -> Result<(u64, u64), StepError> {
    let decode_field = |field: &str| -> Result<u64, StepError> {
        let value = &attrs[field];
        require(
            !value.is_empty() && value.bytes().all(|byte| byte.is_ascii_digit()),
            format!("{name}: invalid command {field} {value:?}"),
        )?;
        let number = value.parse::<u64>().map_err(|_| {
            StepError::Input(format!("{name}: command {field} exceeds integer range: {value}"))
        })?;
        require(number > 0, format!("{name}: invalid command {field} {value:?}"))?;
        Ok(number)
    };
    let line = decode_field("line")?;
    let offset = decode_field("offset")?;
    require(
        line >= previous.0 && offset > previous.1,
        format!("{name}: command positions not in source order"),
    )?;
    require(!yxml::bool_value(&attrs["skipped"])?, format!("{name}: skipped command"))?;
    Ok((line, offset))
}
fn command(
    node: &Node,
    source_root: &Path,
    name: &str,
    source: &str,
    normalized: &str,
    sequence: usize,
    previous: (u64, u64),
) -> Result<Value, StepError> {
    let (attrs, body) =
        yxml::inspect(node, "command", &["name", "source", "line", "offset", "skipped"])?;
    require(
        !attrs["name"].is_empty() && attrs["source"] == source,
        format!("{name}: empty command name or foreign source"),
    )?;
    let (line, offset) = position(attrs, name, previous)?;
    let children = yxml::elements(body)?;
    let expected = usize::from(RESOURCE_COMMANDS.contains(&attrs["name"].as_str()));
    require(
        children.len() == expected,
        format!("{name}: {} has invalid resolved file count", attrs["name"]),
    )?;
    let files = children
        .into_iter()
        .map(|node| decode_file(node, source_root, name))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(
        json!({"sequence":sequence,"name":attrs["name"],"source":normalized,"line":line,"offset":offset,"skipped":false,"files":files}),
    )
}
fn observer_commands(body: &[Part], source: &str) -> Result<(), StepError> {
    let children = yxml::elements(body)?;
    require(!children.is_empty(), format!("{OBSERVER}: missing observed command"))?;
    let mut previous = (0, 0);
    for node in children {
        let (attrs, files) =
            yxml::inspect(node, "command", &["name", "source", "line", "offset", "skipped"])?;
        require(
            !attrs["name"].is_empty() && attrs["source"] == source,
            format!("{OBSERVER}: malformed excluded command identity"),
        )?;
        previous = position(attrs, OBSERVER, previous)?;
        let files = yxml::elements(files)?;
        require(
            files.len() == usize::from(RESOURCE_COMMANDS.contains(&attrs["name"].as_str())),
            format!("{OBSERVER}: invalid excluded command file count"),
        )?;
        for file in files {
            let attrs = read_empty_attributes(file, "file", &["path", "sha1"])?;
            require(
                valid_hash(attrs["sha1"].as_str().unwrap_or(""), 40),
                format!("{OBSERVER}: malformed excluded command file"),
            )?;
        }
    }
    Ok(())
}
fn decode_theory(
    node: &Node,
    root: &Path,
    sources: &BTreeMap<String, String>,
    manifest: &serde_json::Map<String, Value>,
) -> Result<Option<Value>, StepError> {
    let (attrs, body) = yxml::inspect(node, "theory", &["name", "source"])?;
    let name = &attrs["name"];
    let source = &attrs["source"];
    if name == OBSERVER {
        require(source == OBSERVER_SOURCE, "Observer source mismatch")?;
        observer_commands(body, source)?;
        return Ok(None);
    }
    let relative = sources
        .get(name)
        .ok_or_else(|| StepError::Input(format!("Unexpected executed theory {name:?}")))?;
    require(source != OBSERVER_SOURCE, format!("{name}: observer source is not a target source"))?;
    let (normalized, _) = read_fixed_file(source, root, name)?;
    require(
        normalized == *relative,
        format!("{name}: source differs from inventory theory identity"),
    )?;
    let mut previous = (0, 0);
    let commands = yxml::elements(body)?
        .into_iter()
        .enumerate()
        .map(|(index, node)| {
            let value = command(node, root, name, source, &normalized, index + 1, previous)?;
            previous = (value["line"].as_u64().unwrap_or(0), value["offset"].as_u64().unwrap_or(0));
            Ok(value)
        })
        .collect::<Result<Vec<_>, StepError>>()?;
    require(!commands.is_empty(), format!("{name}: missing observed command"))?;
    require(
        commands.iter().filter(|item| item["name"] == "theory").count() == 1,
        format!("{name}: expected exactly one theory command"),
    )?;
    require(
        commands.last().is_some_and(|item| item["name"] == "end"),
        format!("{name}: missing successful final end command"),
    )?;
    Ok(Some(
        json!({"name":name,"source":relative,"sha256":manifest.get(relative).ok_or_else(||StepError::Input(format!("{name}: missing source SHA256")))?, "commands":commands}),
    ))
}
pub fn decode_execution(
    raw: &str,
    source_root: &Path,
    inventory: &Value,
) -> Result<Value, StepError> {
    let source_root = source_root.canonicalize().map_err(|source| {
        io_error(format!("resolve fixed source root {}", source_root.display()), source)
    })?;
    require(source_root.is_dir(), format!("Missing fixed source root {}", source_root.display()))?;
    let (sources, manifest) = inspect_inventory(inventory, &source_root)?;
    let root = yxml::parse(raw)?;
    let (attrs, body) =
        yxml::inspect(&root, "execution_snapshot", &["version", "reference", "session"])?;
    require(
        attrs["version"] == "1"
            && attrs["reference"] == "Isabelle2025"
            && attrs["session"] == "Reference_Execution",
        "Unsupported execution snapshot identity",
    )?;
    require(body.len() == 3, "Missing execution roots/initial_theories/theories")?;
    let roots = yxml::read_names(yxml::child(body, 0)?, "roots", "root")?;
    require(
        roots == json!(ROOTS).as_array().cloned().unwrap_or_default(),
        "Execution fixed root identities or order mismatch",
    )?;
    let initial = yxml::read_names(yxml::child(body, 1)?, "initial_theories", "theory")?;
    require(
        initial == json!(INITIAL).as_array().cloned().unwrap_or_default(),
        "Execution reused or missing preloaded theory (expected audited Pure heap bootstrap only)",
    )?;
    let entries = yxml::group(yxml::child(body, 2)?, "theories", "theory")?;
    let mut names = HashSet::new();
    for entry in &entries {
        let attrs = yxml::inspect(entry, "theory", &["name", "source"])?.0;
        require(names.insert(attrs["name"].as_str()), "Duplicate executed theory identities")?;
    }
    require(
        names.len() == sources.len()
            && names.contains(OBSERVER)
            && !names.contains("Pure")
            && sources
                .keys()
                .filter(|name| name.as_str() != "Pure")
                .all(|name| names.contains(name.as_str())),
        "Missing or foreign executed theories",
    )?;
    let mut theories: Vec<Value> = entries
        .into_iter()
        .map(|node| decode_theory(node, &source_root, &sources, manifest))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .flatten()
        .collect();
    theories.sort_by(|left, right| left["name"].as_str().cmp(&right["name"].as_str()));
    let mut output = json!({"schema":1,"reference":"Isabelle2025","session":"Reference_Execution","roots":roots,"initial_theories":initial,"coverage":{"observed":OBSERVED,"unavailable":UNAVAILABLE,"excluded_observer_theory":OBSERVER,"ordering":"per_theory_source_segments_not_global_thread_order"}});
    output["theories"] = Value::Array(theories);
    Ok(output)
}

/// Preserve the v1 snapshot decoder while recording this inventory run's real R identity.
pub fn decode_execution_v2(
    raw: &str,
    executed_root: &Path,
    inventory: &Value,
    run_id: &str,
) -> Result<Value, StepError> {
    require(
        inventory["schema_version"] == 2 && inventory["run_id"] == run_id && !run_id.is_empty(),
        "executed commands must belong to instrumented inventory run",
    )?;
    let mut execution = decode_execution(raw, executed_root, inventory)?;
    execution["schema"] = json!(2);
    execution["run_id"] = json!(run_id);
    execution["loaded_pure_heap_tree_sha256"] = inventory["loaded_pure_heap_tree_sha256"].clone();
    let theories = execution["theories"]
        .as_array_mut()
        .ok_or_else(|| StepError::Input("decoded execution has no theories".into()))?;
    for theory in theories {
        let theory_name = theory["name"].clone();
        let commands = theory["commands"]
            .as_array_mut()
            .ok_or_else(|| StepError::Input("decoded theory has no commands".into()))?;
        for command in commands {
            command["command_id"] = json!({"run_id":run_id,"theory":theory_name,
                "sequence":command["sequence"],"source":command["source"]});
        }
    }
    Ok(execution)
}
