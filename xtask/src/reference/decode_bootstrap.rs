use super::{
    common::{digest_bytes, require},
    decode_execution::{RESOURCE_COMMANDS, read_empty_attributes, read_fixed_file},
    yxml::{self, Node},
};
use crate::runner::{StepError, io_error};
use serde_json::{Value, json};
use sha1::{Digest, Sha1};
use std::{collections::HashMap, path::Path};
const BOOTSTRAP_SOURCES: [&str; 2] = ["src/Pure/ROOT0.ML", "src/Pure/ROOT.ML"];
const HEADINGS: [&str; 6] =
    ["chapter", "section", "subsection", "subsubsection", "paragraph", "subparagraph"];
const PRELUDE_SOURCES: [(&str, u64, Option<u64>, &str); 4] = [
    ("src/Pure/ML/ml_process.scala", 45, Some(117), "platform_startup_prelude_and_heap_selection"),
    ("src/Pure/Build/build_job.scala", 127, Some(146), "session_parent_and_Pure_prelude_selection"),
    ("src/Pure/ML/ml_name_space.ML", 61, Some(93), "hidden_and_bootstrap_namespace_boundaries"),
    (
        "src/Pure/Concurrent/thread_attributes.ML",
        1,
        None,
        "runtime_specific_thread_attribute_replacement",
    ),
];
fn build_reads(profile: &Value) -> Result<HashMap<String, Vec<Value>>, StepError> {
    let mut reads: HashMap<String, Vec<Value>> = HashMap::new();
    for observation in yxml::array(profile, "fixed_source_reads")? {
        if observation["phase"] == "build" {
            let source = yxml::string(observation, "source")?;
            let mut record = serde_json::Map::new();
            for key in ["phase", "tid", "sequence", "timestamp"] {
                record.insert(
                    key.into(),
                    observation
                        .get(key)
                        .ok_or_else(|| {
                            StepError::Input(format!("Build read {source}: missing {key}"))
                        })?
                        .clone(),
                );
            }
            reads.entry(source.into()).or_default().push(Value::Object(record));
        }
    }
    Ok(reads)
}
fn bind_source(
    path: &str,
    sha1: &str,
    root: &Path,
    reads: &HashMap<String, Vec<Value>>,
) -> Result<Value, StepError> {
    let (relative, bytes) = read_fixed_file(path, root, "bootstrap source")?;
    require(
        format!("{:x}", Sha1::digest(&bytes)) == sha1,
        format!("{relative}: bootstrap source SHA1 differs"),
    )?;
    let observations = reads.get(&relative).ok_or_else(|| {
        StepError::Input(format!("{relative}: missing successful build-time source observation"))
    })?;
    Ok(json!({"source":relative,"sha256":digest_bytes(&bytes),"build_reads":observations}))
}
fn statement(
    node: &Node,
    root: &Path,
    reads: &HashMap<String, Vec<Value>>,
    previous_line: u64,
    sequence: usize,
) -> Result<Value, StepError> {
    let (attrs, files) =
        yxml::inspect(node, "statement", &["command", "kind", "argument", "line"])?;
    let line = yxml::positive(&attrs["line"], "bootstrap source line")?;
    require(line > previous_line, "Bootstrap source statements are not strictly ordered")?;
    let command = &attrs["command"];
    let argument = &attrs["argument"];
    require(!argument.is_empty(), "Missing bootstrap literal argument")?;
    let mut result = json!({"command":command,"argument":argument,"kind":attrs["kind"],"line":line,"sequence":sequence});
    if HEADINGS.contains(&command.as_str()) {
        require(attrs["kind"] == "heading" && files.is_empty(), "Invalid bootstrap heading")?;
        return Ok(result);
    }
    require(
        RESOURCE_COMMANDS.contains(&command.as_str())
            && attrs["kind"] == "load"
            && files.len() == 1,
        "Unsupported bootstrap source statement",
    )?;
    require(
        !argument.starts_with('/')
            && !argument.contains('\\')
            && argument.split('/').all(|segment| !matches!(segment, "" | "." | "..")),
        "Bootstrap argument escapes source directory",
    )?;
    let file = read_empty_attributes(yxml::child(files, 0)?, "file", &["path", "sha1"])?;
    let bound = bind_source(
        file["path"].as_str().unwrap_or(""),
        file["sha1"].as_str().unwrap_or(""),
        root,
        reads,
    )?;
    require(
        bound["source"] == format!("src/Pure/{argument}"),
        "Bootstrap literal and resolved input differ",
    )?;
    result["file"] = bound;
    Ok(result)
}
fn source(
    node: &Node,
    root: &Path,
    reads: &HashMap<String, Vec<Value>>,
) -> Result<Value, StepError> {
    let (attrs, body) = yxml::inspect(node, "source", &["path", "sha1"])?;
    let mut result = bind_source(&attrs["path"], &attrs["sha1"], root, reads)?;
    let mut previous_line = 0;
    let statements = yxml::elements(body)?
        .into_iter()
        .enumerate()
        .map(|(index, node)| {
            let decoded = statement(node, root, reads, previous_line, index + 1)?;
            previous_line = decoded["line"]
                .as_u64()
                .ok_or_else(|| StepError::Input("Missing bootstrap line".into()))?;
            Ok(decoded)
        })
        .collect::<Result<Vec<_>, StepError>>()?;
    require(
        !statements.is_empty(),
        format!("{}: empty bootstrap source observation", result["source"]),
    )?;
    result["statements"] = json!(statements);
    Ok(result)
}
fn prelude(root: &Path) -> Result<Vec<Value>, StepError> {
    PRELUDE_SOURCES.into_iter().map(|(source,first,last,role)|{
        let (relative,bytes)=read_fixed_file(&format!("/work/fixed-source/{source}"),root,"bootstrap prelude")?;
        let line_end=last.unwrap_or_else(||if bytes.is_empty() {0} else {bytes.split(|byte|*byte==b'\n').count() as u64-u64::from(bytes.last()==Some(&b'\n'))});
        Ok(json!({"source":relative,"sha256":digest_bytes(&bytes),"line_start":first,"line_end":line_end,"role":role,"evidence":"audited_source_not_observed_ML_execution"}))
    }).collect()
}
pub fn decode_bootstrap(
    raw: &str,
    source_root: &Path,
    profile: &Value,
) -> Result<Value, StepError> {
    let source_root = source_root.canonicalize().map_err(|source| {
        io_error(format!("resolve fixed source root {}", source_root.display()), source)
    })?;
    require(source_root.is_dir(), format!("Missing fixed source root {}", source_root.display()))?;
    let parsed = yxml::parse(raw)?;
    let (attrs, body) =
        yxml::inspect(&parsed, "bootstrap_snapshot", &["version", "reference", "semantics"])?;
    require(
        attrs["version"] == "1"
            && attrs["reference"] == "Isabelle2025"
            && attrs["semantics"] == "source_declared_order_not_call_trace",
        "Unsupported bootstrap snapshot",
    )?;
    let reads = build_reads(profile)?;
    let sources = yxml::elements(body)?
        .into_iter()
        .map(|node| source(node, &source_root, &reads))
        .collect::<Result<Vec<_>, _>>()?;
    require(
        sources.iter().map(|source| source["source"].as_str().unwrap_or("")).eq(BOOTSTRAP_SOURCES),
        "Missing, reordered or foreign bootstrap source",
    )?;
    Ok(
        json!({"schema":1,"reference":"Isabelle2025","authorization":"none_reference_requirements_only","ordering":"source_declared_order_not_call_trace","sources":sources,"prelude_sources":prelude(&source_root)?,"limits":["build-time open observations do not independently prove a compiler invocation","source-declared ML_file order does not enumerate implicit nested runtime calls","bootstrap and hidden runtime bindings require independently reviewed Rust replacements"]}),
    )
}
