use std::fs;
use std::path::Path;

use serde_json::{Value, json};

use super::super::common::{digest_bytes, require, require_regular, resolve_source_path};
use super::super::trace::SYSCALLS;
use crate::runner::{StepError, io_error};

const SOURCE_PREFIX: &str = "/work/fixed-source/";
const GENERATED_DIRECTORIES: [&str; 2] = ["lib/classes", "src/Tools/Demo/lib"];
const GENERATED_PREFIXES: [&str; 2] = ["lib/classes/", "src/Tools/Demo/lib/"];

pub(super) struct TraceCatalog {
    pub reads: Vec<Value>,
    pub generated: Vec<Value>,
    pub executables: Vec<Value>,
    pub unresolved: Vec<Value>,
}

fn valid_result(value: &str) -> bool {
    value == "?"
        || value.strip_prefix('-').unwrap_or(value).bytes().all(|byte| byte.is_ascii_digit())
            && !value.is_empty()
            && value != "-"
}

fn is_valid_timestamp(timestamp: &str) -> bool {
    timestamp.split_once('.').is_some_and(|(seconds, fractional)| {
        !seconds.is_empty()
            && !fractional.is_empty()
            && seconds.bytes().chain(fractional.bytes()).all(|byte| byte.is_ascii_digit())
    })
}

fn inspect_trace<'a>(phase: &str, trace: &'a Value) -> Result<&'a [Value], StepError> {
    let summary = &trace["summary"];
    let events = trace["events"]
        .as_array()
        .ok_or_else(|| StepError::Input(format!("{phase}: missing trace data")))?;
    let scope = summary["scope"]
        .as_array()
        .ok_or_else(|| StepError::Input(format!("{phase}: incomplete syscall observation")))?;
    require(
        summary["complete"] == true
            && summary["error_count"] == 0
            && summary["event_count"] == events.len()
            && scope.len() == SYSCALLS.len()
            && SYSCALLS.iter().all(|name| scope.contains(&json!(name))),
        format!("{phase}: incomplete syscall observation"),
    )?;
    let mut unresolved_count = 0;
    for (index, event) in events.iter().enumerate() {
        let path = event["path"]
            .as_str()
            .filter(|path| !path.is_empty() && !path.contains('\0'))
            .ok_or_else(|| StepError::Input(format!("{phase}: invalid event pathname")))?;
        let result = event["result"]
            .as_str()
            .ok_or_else(|| StepError::Input(format!("{phase}: invalid event result")))?;
        let timestamp = event["timestamp"]
            .as_str()
            .ok_or_else(|| StepError::Input(format!("{phase}: missing event timestamp")))?;
        require(
            event["sequence"] == index + 1
                && event["tid"].as_u64().is_some_and(|id| id > 0)
                && is_valid_timestamp(timestamp)
                && SYSCALLS.iter().any(|name| event["syscall"] == *name)
                && valid_result(result),
            format!("{phase}: invalid event identity or outcome"),
        )?;
        if let Some(resolved) = event.get("resolved_path") {
            require(
                matches!(event["syscall"].as_str(), Some("open" | "openat"))
                    && result.bytes().all(|byte| byte.is_ascii_digit())
                    && resolved
                        .as_str()
                        .is_some_and(|path| path.starts_with('/') && !path.contains('\0')),
                format!("{phase}: invalid returned FD path"),
            )?;
        } else if !path.starts_with('/') {
            unresolved_count += 1;
        }
    }
    require(
        summary["unresolved_relative_paths"] == unresolved_count
            && summary["relative_paths_resolved"] == (unresolved_count == 0),
        format!("{phase}: unresolved relative path count mismatch"),
    )?;
    Ok(events)
}

fn event_reference(phase: &str, event: &Value) -> Value {
    let mut reference = json!({"phase": phase, "tid": event["tid"], "sequence": event["sequence"], "timestamp": event["timestamp"], "syscall": event["syscall"], "path": event["path"], "result": event["result"]});
    if let Some(path) = event.get("resolved_path") {
        reference["resolved_path"] = path.clone();
    }
    reference
}

fn append(reference: &Value, additions: &[(&str, Value)]) -> Value {
    let mut entry = reference.clone();
    for &(key, ref value) in additions {
        entry[key] = value.clone();
    }
    entry
}

fn catalog_resource_event(
    phase: &str,
    event: &Value,
    reference: &Value,
    source_root: &Path,
    catalog: &mut TraceCatalog,
) -> Result<(), StepError> {
    let path = event["path"]
        .as_str()
        .ok_or_else(|| StepError::Input(format!("{phase}: missing trace path")))?;
    let effective = event["resolved_path"].as_str().unwrap_or(path);
    if path.starts_with(SOURCE_PREFIX) && !effective.starts_with(SOURCE_PREFIX) {
        return Err(StepError::Input(format!(
            "{phase}: source open resolved outside fixed root: {reference}"
        )));
    }
    let Some(relative) = effective.strip_prefix(SOURCE_PREFIX) else {
        return Ok(());
    };
    require(
        !relative.is_empty()
            && relative.split('/').all(|part| !part.is_empty() && part != "." && part != ".."),
        format!("{phase}: unsafe fixed-source trace path {effective}"),
    )?;
    if GENERATED_DIRECTORIES.contains(&relative)
        || GENERATED_PREFIXES.iter().any(|prefix| relative.starts_with(prefix))
    {
        catalog
            .generated
            .push(append(reference, &[("mount_path", json!(effective)), ("hash", Value::Null)]));
        return Ok(());
    }
    let source = resolve_source_path(effective, source_root)?;
    if source.is_dir() {
        catalog
            .unresolved
            .push(append(reference, &[("reason", json!("source_directory_not_file"))]));
        return Ok(());
    }
    require_regular(&source)?;
    let bytes = fs::read(&source).map_err(|cause| {
        io_error(format!("read observed fixed-source input {}", source.display()), cause)
    })?;
    let relative = source.strip_prefix(source_root).map_err(|_| {
        StepError::Input(format!("{phase}: observed source escapes fixed root: {effective}"))
    })?;
    let relative = relative.to_str().ok_or_else(|| {
        StepError::Input(format!("{phase}: non-UTF8 observed fixed-source path: {effective}"))
    })?;
    catalog.reads.push(append(
        reference,
        &[("source", json!(relative.replace('\\', "/"))), ("sha256", json!(digest_bytes(&bytes)))],
    ));
    Ok(())
}

pub(super) fn catalog_traces(
    traces: &[Value],
    source_root: &Path,
) -> Result<TraceCatalog, StepError> {
    require(
        traces.len() == 2 && traces[0]["phase"] == "build" && traces[1]["phase"] == "inventory",
        "Expected ordered build and inventory traces",
    )?;
    let mut catalog = TraceCatalog {
        reads: Vec::new(),
        generated: Vec::new(),
        executables: Vec::new(),
        unresolved: Vec::new(),
    };
    for trace in traces {
        let phase = trace["phase"]
            .as_str()
            .ok_or_else(|| StepError::Input("Missing reference trace phase".into()))?;
        for event in inspect_trace(phase, trace)? {
            let reference = event_reference(phase, event);
            let path = event["path"]
                .as_str()
                .ok_or_else(|| StepError::Input(format!("{phase}: missing event path")))?;
            let result = event["result"]
                .as_str()
                .ok_or_else(|| StepError::Input(format!("{phase}: missing event outcome")))?;
            let is_success = result.bytes().all(|byte| byte.is_ascii_digit());
            if !path.starts_with('/') && event.get("resolved_path").is_none() {
                catalog.unresolved.push(append(
                    &reference,
                    &[
                        ("reason", json!("relative_path_without_returned_fd_binding")),
                        ("credited_as_input", json!(false)),
                    ],
                ));
                if is_success && matches!(event["syscall"].as_str(), Some("execve" | "execveat")) {
                    require(result == "0", format!("{phase}: invalid successful exec result"))?;
                    catalog.executables.push(reference);
                }
                continue;
            }
            if !is_success {
                continue;
            }
            if matches!(event["syscall"].as_str(), Some("execve" | "execveat")) {
                require(result == "0", format!("{phase}: invalid successful exec result"))?;
                catalog.executables.push(reference);
            } else {
                catalog_resource_event(phase, event, &reference, source_root, &mut catalog)?;
            }
        }
    }
    Ok(catalog)
}
