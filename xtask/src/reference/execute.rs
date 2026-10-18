mod cgroup;
mod finalize;
mod sandbox;
#[cfg(test)]
mod tests;
mod v2;
mod validate;
pub use v2::execute_reference_v2;

use std::path::Path;

use serde_json::{Map, Value, json};

use super::{common, prepare};
use crate::runner::StepError;

pub(super) const OBSERVER_FILES: [&str; 7] = [
    "ROOT",
    "Reference_Observer.thy",
    "observe_execution.ML",
    "observe_origins.ML",
    "export_reference.ML",
    "export_interfaces.ML",
    "export_bootstrap.ML",
];
const TOOL_FILES: [&str; 27] = [
    "common.rs",
    "common/json.rs",
    "prepare.rs",
    "prepare/archive.rs",
    "execute.rs",
    "execute/validate.rs",
    "execute/sandbox.rs",
    "execute/finalize.rs",
    "artifacts.rs",
    "trace.rs",
    "trace/unix.rs",
    "profile.rs",
    "profile/coverage.rs",
    "profile/execution.rs",
    "profile/trace_events.rs",
    "classify_axioms.rs",
    "classify_axioms/data.rs",
    "decode_observations.rs",
    "observe.rs",
    "decode_inventory.rs",
    "decode_inventory/validate.rs",
    "decode_inventory/entities.rs",
    "decode_inventory/encoded.rs",
    "decode_execution.rs",
    "decode_interfaces.rs",
    "decode_bootstrap.rs",
    "yxml.rs",
];
const REFERENCE_OPTIONS: [&str; 18] = [
    "-o",
    "threads=2",
    "-o",
    "parallel_proofs=0",
    "-o",
    "timeout=3600",
    "-o",
    "record_proofs=2",
    "-o",
    "export_theory=true",
    "-o",
    "export_proofs=false",
    "-o",
    "export_standard_proofs=false",
    "-o",
    "prune_proofs=true",
    "-o",
    "quick_and_dirty=false",
];

pub(super) fn build_options() -> Vec<String> {
    ["build", "-f", "-b", "-v", "-j", "1"]
        .into_iter()
        .chain(REFERENCE_OPTIONS)
        .chain(["HOL"])
        .map(str::to_owned)
        .collect()
}

pub(super) fn inventory_options() -> Vec<String> {
    ["build", "-d", "/work/session", "-v", "-j", "1"]
        .into_iter()
        .chain(REFERENCE_OPTIONS)
        .chain(["Reference_Execution"])
        .map(str::to_owned)
        .collect()
}

pub(super) fn describe_sources(directory: &Path, names: &[&str]) -> Result<Value, StepError> {
    let mut sources = Map::new();
    for name in names {
        sources.insert((*name).to_owned(), json!(common::digest_file(&directory.join(name))?));
    }
    Ok(Value::Object(sources))
}

pub fn execute_reference(
    repository: &Path,
    workspace: &Path,
    operation: &str,
    build_run: Option<&Path>,
) -> Result<(), StepError> {
    if operation != "build" && operation != "inventory" {
        return Err(StepError::Input(format!("unsupported reference operation: {operation}")));
    }
    let workspace = prepare::require_external_workspace(workspace, repository)?;
    if operation == "build" && build_run.is_some() {
        return Err(prepare::failure(
            "select build inputs",
            build_run.unwrap_or(&workspace),
            "--build-run is inventory-only",
        ));
    }
    let build_run = if operation == "inventory" {
        Some(build_run.ok_or_else(|| {
            prepare::failure("select inventory build", &workspace, "--build-run is required")
        })?)
    } else {
        None
    };
    let (report, prepared_sha256, component_text) =
        validate::require_prepared(repository, &workspace)?;
    let (bwrap, strace) = validate::require_tools()?;
    if let Some(build) = build_run {
        validate::require_build_run(build, &workspace, &prepared_sha256, &component_text)?;
    }
    let observer_sources = if operation == "inventory" {
        describe_sources(&repository.join("scripts/reference"), &OBSERVER_FILES)?
    } else {
        json!({})
    };
    let tool_sources = describe_sources(&repository.join("xtask/src/reference"), &TOOL_FILES)?;
    let run = validate::make_run_directory(&workspace, operation)?;
    validate::make_build_home(&run, &component_text)?;
    if operation == "inventory" {
        prepare::ensure_directory(&run.join("inventory"))?;
    }
    let (argv, arguments) =
        sandbox::construct_command(repository, &workspace, &run, build_run, operation, &bwrap)?;
    let report_command = json!({"command":argv.iter().map(|a| a.to_string_lossy().into_owned()).collect::<Vec<_>>(),"arguments":arguments,"bwrap":bwrap,"strace":strace,"isabelle":workspace.join("fixed-source/bin/isabelle"),"source_root":report["source_root"],"archive_sha256":prepare::ARCHIVE_SHA256,"prepared_sha256":prepared_sha256,"build_run":build_run,"observer_sources":observer_sources,"tool_sources":tool_sources});
    common::write_json_exclusive(&run.join("command.json"), &report_command)?;
    println!("{}", json!({"run":run,"operation":operation}));
    let execution = sandbox::run_traced_reference(&run, &argv)?;
    finalize::publish_result(
        repository,
        &workspace,
        &run,
        build_run,
        operation,
        &prepared_sha256,
        execution,
    )
}
