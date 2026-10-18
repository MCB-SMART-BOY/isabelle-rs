//! The v2 path never reuses P0 launch, inputs, or publication semantics.
use std::path::Path;

use serde_json::{Value, json};

use super::super::{approved_identity, artifacts, common, compare, instrumentation, prepare};
use super::{finalize, sandbox, validate};
use crate::runner::{StepError, io_error};

const SOURCE_LIMIT: u64 = 512 * 1024 * 1024;
const RECEIPT_LIMIT: u64 = 128 * 1024;

fn prepare_home(run: &Path, components: &str) -> Result<(), StepError> {
    let config = run.join("home/.isabelle/p0-reference/etc");
    prepare::ensure_directory(&config)?;
    prepare::exclusive_text(&config.join("settings"), prepare::SETTINGS)?;
    prepare::exclusive_text(&config.join("components"), components)?;
    prepare::ensure_directory(&run.join("tmp"))?;
    prepare::ensure_directory(&run.join("inventory"))
}

fn require_preapproved_build(
    build: &Path,
    workspace: &Path,
    preapproval_sha256: &str,
    overlay_id: &str,
    prepared_sha256: &str,
) -> Result<(), StepError> {
    common::require(
        build.is_absolute() && build.parent() == Some(workspace.join("runs").as_path()),
        "v2 build must be an explicit managed run",
    )?;
    artifacts::require_managed_directory(build, workspace)?;
    let command = common::decode_json(
        &compare::read_checked_bytes(&build.join("command.json"), RECEIPT_LIMIT)?,
        "read approved build command",
    )?;
    let result = common::decode_json(
        &compare::read_checked_bytes(&build.join("result.json"), RECEIPT_LIMIT)?,
        "read approved build completion",
    )?;
    let receipt = common::decode_json(
        &compare::read_checked_bytes(&build.join("completion-receipt.json"), RECEIPT_LIMIT)?,
        "read supervised build receipt",
    )?;
    common::require(
        command["schema_version"] == 2
            && command["operation"] == "build"
            && command["preapproval_sha256"] == preapproval_sha256
            && command["overlay"]["id"] == overlay_id
            && command["prepared_sha256"] == prepared_sha256
            && command["arguments"] == json!(super::build_options())
            && result["exit_code"] == 0
            && result["interruption"].is_null()
            && result["heap_tree_sha256"] == artifacts::pure_heap_sha256(build)?
            && receipt["command_sha256"]
                == compare::digest_checked_file(&build.join("command.json"), RECEIPT_LIMIT)?
            && receipt["result_sha256"]
                == compare::digest_checked_file(&build.join("result.json"), RECEIPT_LIMIT)?
            && receipt["writer_drain"] == true
            && receipt["descendants_drained"] == true,
        "build is not a complete, preapproved, drained v2 Pure heap",
    )
}

fn save_attestation(
    run: &Path,
    overlay: &instrumentation::Overlay,
    command: &Value,
) -> Result<(), StepError> {
    instrumentation::attest_overlay(
        run,
        &overlay.source_snapshot_sha256,
        &overlay.source_map_sha256,
    )?;
    common::write_json_exclusive(
        &run.join("source-attestation.json"),
        &json!({
            "schema_version": 1,
            "run_id": command["run_id"],
            "source_snapshot_sha256_before": overlay.source_snapshot_sha256,
            "source_snapshot_sha256_after": instrumentation::snapshot_sha256(run)?,
            "source_map_sha256": overlay.source_map_sha256,
            "ml_roots": command["ml_roots"],
            "mount_identity": command["mount_identity"],
        }),
    )
}

fn describe_mounts(run: &Path, operation: &str) -> Value {
    json!({"source_snapshot":{"path":run.join("fixed-source"),"guest":"/work/fixed-source","readonly":true},
        "session":{"path":run.join("session"),"guest":"/work/session","readonly":true,"phase":operation},
        "scratch":{"path":run.join("tmp"),"guest":"/work/tmp","readonly":false},
        "output":{"path":run.join("inventory"),"guest":"/work/inventory","readonly":false},
        "heaps":{"guest":"/work/empty-system-heaps","readonly":true}})
}

pub fn execute_reference_v2(
    repository: &Path,
    workspace: &Path,
    operation: &str,
    build_run: Option<&Path>,
    preapproval_path: &Path,
) -> Result<(), StepError> {
    common::require(
        matches!(operation, "build" | "inventory")
            && (operation == "inventory") == build_run.is_some(),
        "v2 reference requires build or inventory and exactly one build-run for inventory",
    )?;
    let workspace = prepare::require_external_workspace(workspace, repository)?;
    common::require(
        !preapproval_path.starts_with(workspace.join("runs")),
        "preapproval must be outside sandbox-writable run roots",
    )?;
    let (approved, preapproval_sha256) = approved_identity::load_preapproval(
        preapproval_path,
        &repository.join("tests/fixtures/isabelle2025/closure.json"),
    )?;
    let (report, prepared_sha256, components) = validate::require_prepared(repository, &workspace)?;
    let (bwrap, strace) = validate::require_tools()?;
    let strace =
        strace.canonicalize().map_err(|source| io_error("resolve strace executable", source))?;
    if let Some(build) = build_run {
        require_preapproved_build(
            build,
            &workspace,
            &preapproval_sha256,
            &approved.overlay_id,
            &prepared_sha256,
        )?;
    }
    let run = validate::make_run_directory(&workspace, operation)?;
    prepare_home(&run, &components)?;
    let overlay = instrumentation::prepare_overlay(
        repository, &workspace, &run, &report, &approved, &bwrap, &strace,
    )?;
    common::require(
        compare::digest_checked_file(&overlay.root.join("bin/isabelle"), SOURCE_LIMIT)?
            == approved.isabelle_binary_sha256,
        "Isabelle launcher differs from preapproved bytes",
    )?;
    let heap_tree_sha256 =
        build_run.map(|build| artifacts::stage_pure_heap(build, &run)).transpose()?;
    if let Some(build) = build_run {
        common::require(
            heap_tree_sha256.as_deref() == Some(artifacts::pure_heap_sha256(build)?.as_str()),
            "inventory would load a different Pure heap",
        )?;
    }
    let (argv, arguments) =
        sandbox::v2::construct_command(&workspace, &run, build_run, operation, &bwrap)?;
    let run_id = run
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| StepError::Input("invalid v2 run name".into()))?;
    let mount_identity = describe_mounts(&run, operation);
    let command = json!({"schema_version":2,"operation":operation,"run_id":run_id,
        "command":argv.iter().map(|value| value.to_string_lossy().into_owned()).collect::<Vec<_>>(),
        "command_argv":argv.iter().map(|value| value.to_string_lossy().into_owned()).collect::<Vec<_>>(),
        "arguments":arguments,"bwrap":bwrap,"strace":strace,"isabelle":overlay.root.join("bin/isabelle"),
        "source_root":report["source_root"],"archive_sha256":prepare::ARCHIVE_SHA256,
        "prepared_sha256":prepared_sha256,"preapproval_sha256":preapproval_sha256,
        "source_files":report["source_files"],"overlay":{"id":approved.overlay_id,
            "patches":overlay.patches,"observer_sha256":approved.observer_sha256,
            "generator_sha256":approved.generator_sha256},
        "resource_budget":approved.resource_budget,
        "source_snapshot_sha256":overlay.source_snapshot_sha256,
        "source_snapshot_sha256_before":overlay.source_snapshot_sha256,
        "source_map_sha256":overlay.source_map_sha256,
        "ml_roots":["src/Pure/ROOT0.ML","src/Pure/ROOT.ML"],
        "mount_identity":mount_identity,"executed_root":overlay.root,
        "loaded_pure_heap_tree_sha256":heap_tree_sha256,"build_run":build_run});
    common::write_json_exclusive(&run.join("command.json"), &command)?;
    instrumentation::attest_overlay(
        &run,
        &overlay.source_snapshot_sha256,
        &overlay.source_map_sha256,
    )?;
    let execution = sandbox::v2::run_reference(&run, &argv, &approved.resource_budget)?;
    save_attestation(&run, &overlay, &command)?;
    finalize::publish_v2_result(
        repository,
        &workspace,
        &run,
        build_run,
        operation,
        &prepared_sha256,
        execution,
    )
}
