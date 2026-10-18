//! Fixed-source identity diagnostics; digests never authorize theorem acceptance.
use std::collections::BTreeMap;

use serde_json::Value;

use super::common::{as_array, as_object, as_str, field, require, require_fields};
use super::compare::ComparisonDiagnostics;
use crate::EvidenceError as StepError;

const SHA256_HEX_LENGTH: usize = 64;

fn insert_source<'a>(
    sources: &mut BTreeMap<&'a str, &'a str>,
    path: &'a Value,
    digest: &'a Value,
) -> Result<(), StepError> {
    insert_named_source(sources, as_str(path, "source path")?, as_str(digest, "source digest")?)
}

fn insert_named_source<'a>(
    sources: &mut BTreeMap<&'a str, &'a str>,
    path: &'a str,
    digest: &'a str,
) -> Result<(), StepError> {
    require(
        !path.starts_with('/')
            && !path.contains('\0')
            && path.split('/').all(|part| !matches!(part, "" | "." | "..")),
        format!("source path: invalid fixed-source identity {path:?}"),
    )?;
    require(
        digest.len() == SHA256_HEX_LENGTH
            && digest.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        format!("{path}: invalid SHA256"),
    )?;
    if let Some(previous) = sources.insert(path, digest) {
        require(previous == digest, format!("{path}: contradictory source bindings"))?;
    }
    Ok(())
}

pub fn collect_required_sources<'a>(
    reference: &'a Value,
    execution: &'a Value,
    manifest: &'a Value,
) -> Result<BTreeMap<&'a str, &'a str>, StepError> {
    let mut sources = BTreeMap::new();
    for (path, digest) in as_object(field(reference, "source_sha256")?, "source SHA256")? {
        insert_named_source(&mut sources, path, as_str(digest, "source digest")?)?;
    }
    for theory in as_array(field(execution, "theories")?, "executed theories")? {
        for command in as_array(field(theory, "commands")?, "executed commands")? {
            for file in as_array(field(command, "files")?, "command files")? {
                insert_source(&mut sources, field(file, "path")?, field(file, "sha256")?)?;
            }
        }
    }
    let bootstrap = field(field(manifest, "session_graph")?, "bootstrap")?;
    collect_bootstrap_sources(&mut sources, bootstrap)?;
    Ok(sources)
}

fn collect_bootstrap_sources<'a>(
    sources: &mut BTreeMap<&'a str, &'a str>,
    bootstrap: &'a Value,
) -> Result<(), StepError> {
    for unit in as_array(field(bootstrap, "sources")?, "bootstrap sources")? {
        insert_source(sources, field(unit, "source")?, field(unit, "sha256")?)?;
        for statement in as_array(field(unit, "statements")?, "bootstrap statements")? {
            if field(statement, "kind")? == "load" {
                let file = field(statement, "file")?;
                insert_source(sources, field(file, "source")?, field(file, "sha256")?)?;
            }
        }
    }
    for prelude in as_array(field(bootstrap, "prelude_sources")?, "bootstrap preludes")? {
        insert_source(sources, field(prelude, "source")?, field(prelude, "sha256")?)?;
    }
    Ok(())
}

pub fn compare_sources(
    result: &mut ComparisonDiagnostics,
    reference: &Value,
    execution: &Value,
    native: &Value,
    manifest: &Value,
) -> Result<(), StepError> {
    let required = collect_required_sources(reference, execution, manifest)?;
    let mut observed = BTreeMap::new();
    for file in as_array(field(manifest, "observed_fixed_source_files")?, "observed sources")? {
        insert_source(&mut observed, field(file, "source")?, field(file, "sha256")?)?;
    }
    for (path, digest) in &required {
        if let Some(observation) = observed.get(path) {
            require(observation == digest, format!("{path}: contradictory source bindings"))?;
        }
    }
    let mut actual = BTreeMap::new();
    for file in as_array(field(native, "source_files")?, "native source files")? {
        require_fields(file, &["path", "sha256"], "native source file")?;
        let path = as_str(&file["path"], "source path")?;
        require(!actual.contains_key(path), format!("duplicate source file: {path:?}"))?;
        insert_source(&mut actual, &file["path"], &file["sha256"])?;
    }
    for (path, digest) in &required {
        result.compare_value(format!("source:{path}"), &Some(*digest), &actual.get(path).copied());
    }
    for (path, digest) in &actual {
        if !required.contains_key(path) {
            result.compare_value(
                format!("additional source:{path}"),
                &observed.get(path).copied(),
                &Some(*digest),
            );
        }
    }
    Ok(())
}
