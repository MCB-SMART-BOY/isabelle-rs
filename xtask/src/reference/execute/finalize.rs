use std::io::Read;
use std::path::Path;

use super::super::{
    artifacts, classify_axioms, common, decode_bootstrap, decode_execution, decode_interfaces,
    decode_inventory, observe, prepare, profile,
};
use super::{OBSERVER_FILES, TOOL_FILES, describe_sources};
use crate::runner::StepError;
use serde_json::{Map, Value, json};

fn read_trace_artifact(run: &Path, phase: &str, summary: Value) -> Result<Value, StepError> {
    let path = run.join("events.jsonl");
    let content = prepare::read_text(&path)?;
    let events = content
        .lines()
        .map(|line| {
            serde_json::from_str::<Value>(line).map_err(|source| StepError::Json {
                operation: format!("decode trace event at {}", path.display()),
                source,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(json!({"phase":phase,"summary":summary,"events":events}))
}

pub(super) fn publish(
    directory: &Path,
    name: &str,
    payload: &Value,
) -> Result<Map<String, Value>, StepError> {
    let output = directory.join(format!("{name}.json"));
    common::write_json_exclusive(&output, payload)?;
    let mut result = Map::new();
    let key = name.replace('-', "_");
    result.insert(key.clone(), json!(output));
    result.insert(format!("{key}_sha256"), json!(common::digest_file(&output)?));
    Ok(result)
}

fn read_observation(path: &Path) -> Result<String, StepError> {
    prepare::read_text(path)
}

fn finalize_catalogs(
    workspace: &Path,
    run: &Path,
    build_run: &Path,
    inventory: &Value,
    execution: &Value,
    trace: Value,
) -> Result<Map<String, Value>, StepError> {
    let directory = run.join("inventory");
    let source_root = workspace.join("fixed-source");
    let build_result = common::read_json(&build_run.join("result.json"))?;
    let traces = [
        read_trace_artifact(build_run, "build", build_result["trace"].clone())?,
        read_trace_artifact(run, "inventory", trace)?,
    ];
    let profile = profile::build_reference_profile(inventory, execution, &source_root, &traces)?;
    let interface_path = directory.join("interfaces.yxml");
    let bootstrap_path = directory.join("bootstrap.yxml");
    let mut interfaces = decode_interfaces::decode_interfaces(
        &read_observation(&interface_path)?,
        inventory,
        execution,
    )?;
    let mut bootstrap = decode_bootstrap::decode_bootstrap(
        &read_observation(&bootstrap_path)?,
        &source_root,
        &profile,
    )?;
    interfaces["raw_yxml_sha256"] = json!(common::digest_file(&interface_path)?);
    bootstrap["raw_yxml_sha256"] = json!(common::digest_file(&bootstrap_path)?);
    let mut result = Map::new();
    for (name, payload) in
        [("profile", profile), ("interfaces", interfaces), ("bootstrap", bootstrap)]
    {
        result.extend(publish(&directory, name, &payload)?);
    }
    Ok(result)
}

fn finalize_inventory(
    repository: &Path,
    workspace: &Path,
    run: &Path,
    build_run: &Path,
    trace: Value,
) -> Result<Map<String, Value>, StepError> {
    let command = common::read_json(&run.join("command.json"))?;
    if command["observer_sources"]
        != describe_sources(&repository.join("scripts/reference"), &OBSERVER_FILES)?
    {
        return Err(prepare::failure("verify observer inputs", run, "observer sources changed"));
    }
    let directory = run.join("inventory");
    for name in ["inventory", "execution", "interfaces", "bootstrap", "fact-origins"] {
        common::require_regular(&directory.join(format!("{name}.yxml")))?;
    }
    let source_root = workspace.join("fixed-source");
    let inventory_path = directory.join("inventory.yxml");
    let execution_path = directory.join("execution.yxml");
    let mut inventory = decode_inventory::decode_inventory(
        &read_observation(&inventory_path)?,
        &source_root,
        &artifacts::read_build_source_map(build_run)?,
    )?;
    inventory["raw_yxml_sha256"] = json!(common::digest_file(&inventory_path)?);
    inventory["owner_semantics"] = json!("transferred_certificate_context_not_derivation_origin");
    let mut execution = decode_execution::decode_execution(
        &read_observation(&execution_path)?,
        &source_root,
        &inventory,
    )?;
    execution["raw_yxml_sha256"] = json!(common::digest_file(&execution_path)?);
    let axioms = classify_axioms::classify_axioms(&inventory)?;
    let mut result = Map::new();
    for (name, value) in
        [("inventory", &inventory), ("execution", &execution), ("axiom-provenance", &axioms)]
    {
        result.extend(publish(&directory, name, value)?);
    }
    result.insert("raw_yxml_sha256".into(), inventory["raw_yxml_sha256"].clone());
    result.extend(finalize_catalogs(workspace, run, build_run, &inventory, &execution, trace)?);
    observe::publish_run(repository, run, &inventory, &execution)?;
    let manifest = run.join("reference-manifest.json");
    result.insert("reference_manifest".into(), json!(manifest));
    result.insert("reference_manifest_sha256".into(), json!(common::digest_file(&manifest)?));
    Ok(result)
}

pub(super) fn finalize_reference_outputs(
    repository: &Path,
    workspace: &Path,
    run: &Path,
    build_run: Option<&Path>,
    operation: &str,
    trace: Value,
) -> Result<Map<String, Value>, StepError> {
    let command = common::read_json(&run.join("command.json"))?;
    if command["tool_sources"]
        != describe_sources(&repository.join("xtask/src/reference"), &TOOL_FILES)?
    {
        return Err(prepare::failure("verify reference tools", run, "reference tools changed"));
    }
    if operation == "inventory" {
        return finalize_inventory(
            repository,
            workspace,
            run,
            build_run.ok_or_else(|| StepError::Input("inventory requires --build-run".into()))?,
            trace,
        );
    }
    super::validate::require_rebuilt_sessions(run)?;
    let input = run.join(artifacts::INPUT_MANIFEST);
    common::write_json_exclusive(&input, &artifacts::collect_build_inputs(run)?)?;
    let source_map = run.join("source-map.json");
    common::write_json_exclusive(&source_map, &artifacts::read_build_source_map(run)?)?;
    Ok(Map::from_iter([
        ("build_inputs_sha256".into(), json!(common::digest_file(&input)?)),
        ("source_map_sha256".into(), json!(common::digest_file(&source_map)?)),
    ]))
}

pub(super) fn publish_result(
    repository: &Path,
    workspace: &Path,
    run: &Path,
    build_run: Option<&Path>,
    operation: &str,
    prepared_sha256: &str,
    execution: (Option<i32>, Option<String>, Value, f64),
) -> Result<(), StepError> {
    let (exit_code, mut interruption, trace, elapsed) = execution;
    let artifacts = if exit_code == Some(0) && interruption.is_none() {
        match finalize_reference_outputs(
            repository,
            workspace,
            run,
            build_run,
            operation,
            trace.clone(),
        ) {
            Ok(artifacts) => artifacts,
            Err(error) => {
                interruption = Some(format!(
                    "user-fixable: finalize reference output on {}: {error}",
                    run.display()
                ));
                Map::new()
            },
        }
    } else {
        Map::new()
    };
    let mut result = json!({"operation":operation,"exit_code":exit_code,"interruption":interruption,"elapsed_seconds":elapsed,"prepared_sha256":prepared_sha256,"stdout_sha256":common::digest_file(&run.join("stdout.log"))?,"command_sha256":common::digest_file(&run.join("command.json"))?,"events_sha256":common::digest_file(&run.join("events.jsonl"))?,"run":run,"trace":trace,"events":run.join("events.jsonl")});
    for (key, value) in artifacts {
        result[key] = value;
    }
    common::write_json_exclusive(&run.join("result.json"), &result)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&result).map_err(|source| StepError::Json {
            operation: "print reference result".into(),
            source
        })?
    );
    if exit_code == Some(0) && interruption.is_none() {
        Ok(())
    } else {
        Err(StepError::Protocol {
            operation: format!("official reference {operation} on {}", run.display()),
            detail: format!(
                "exit_code={exit_code:?}; interruption={interruption:?}; see result.json"
            ),
        })
    }
}

const MAX_V2_OBSERVATION_BYTES: u64 = 512 * 1024 * 1024;

fn read_v2_observation(path: &Path) -> Result<String, StepError> {
    let file = common::open_regular(path)?;
    common::require(
        file.metadata()
            .map_err(|source| {
                crate::runner::io_error(
                    format!("stat instrumented observation {}", path.display()),
                    source,
                )
            })?
            .len()
            <= MAX_V2_OBSERVATION_BYTES,
        format!("instrumented observation exceeds byte budget: {}", path.display()),
    )?;
    let mut bytes = Vec::new();
    file.take(MAX_V2_OBSERVATION_BYTES + 1).read_to_end(&mut bytes).map_err(|source| {
        crate::runner::io_error(format!("read instrumented observation {}", path.display()), source)
    })?;
    common::require(
        bytes.len() as u64 <= MAX_V2_OBSERVATION_BYTES,
        format!("instrumented observation grew past byte budget: {}", path.display()),
    )?;
    String::from_utf8(bytes).map_err(|source| StepError::Utf8 {
        operation: format!("decode instrumented observation {}", path.display()),
        source,
    })
}

fn finalize_v2_inventory(run: &Path, build_run: &Path) -> Result<Map<String, Value>, StepError> {
    let directory = run.join("inventory");
    let command = common::read_json(&run.join("command.json"))?;
    let run_id = common::as_str(common::field(&command, "run_id")?, "inventory run ID")?;
    let heap = artifacts::heap_tree_sha256(&run.join("pure-heap"))?;
    common::require(
        command["loaded_pure_heap_tree_sha256"] == heap
            && artifacts::pure_heap_sha256(build_run)? == heap,
        "inventory did not load exact supervised build Pure heap",
    )?;
    let inventory_path = directory.join("inventory.yxml");
    let execution_path = directory.join("execution.yxml");
    let mut inventory = decode_inventory::decode_inventory_v2(
        &read_v2_observation(&inventory_path)?,
        &run.join("fixed-source"),
        &artifacts::read_build_source_map(build_run)?,
        run_id,
        &heap,
    )?;
    let mut execution = decode_execution::decode_execution_v2(
        &read_v2_observation(&execution_path)?,
        &run.join("fixed-source"),
        &inventory,
        run_id,
    )?;
    inventory["initial_theories"] = execution["initial_theories"].clone();
    inventory["raw_yxml_sha256"] = json!(common::digest_file(&inventory_path)?);
    execution["raw_yxml_sha256"] = json!(common::digest_file(&execution_path)?);
    let mut published = Map::new();
    published.extend(publish(&directory, "inventory", &inventory)?);
    published.extend(publish(&directory, "execution", &execution)?);
    published.insert("heap_tree_sha256".into(), json!(heap));
    Ok(published)
}

fn finalize_v2_build(run: &Path) -> Result<Map<String, Value>, StepError> {
    let heap = artifacts::pure_heap_sha256(run)?;
    let source_map = artifacts::read_build_source_map(run)?;
    common::write_json_exclusive(&run.join("source-map.json"), &source_map)?;
    Ok(Map::from_iter([
        ("heap_tree_sha256".into(), json!(heap)),
        ("source_map_sha256".into(), json!(common::digest_file(&run.join("source-map.json"))?)),
    ]))
}

fn publish_v2_receipt(run: &Path, build_run: &Path, manifest: &Value) -> Result<(), StepError> {
    let command = common::read_json(&run.join("command.json"))?;
    let result = common::read_json(&run.join("result.json"))?;
    let build_result = common::read_json(&build_run.join("result.json"))?;
    let build_command = common::read_json(&build_run.join("command.json"))?;
    let attestation = common::read_json(&run.join("source-attestation.json"))?;
    let build_attestation = common::read_json(&build_run.join("source-attestation.json"))?;
    for (current, source) in [(&attestation, &command), (&build_attestation, &build_command)] {
        common::require(
            current["source_snapshot_sha256_before"] == source["source_snapshot_sha256"]
                && current["source_snapshot_sha256_after"] == source["source_snapshot_sha256"]
                && current["ml_roots"] == source["ml_roots"]
                && current["mount_identity"] == source["mount_identity"],
            "supervisor source bytes or immutable mount changed during --use run",
        )?;
    }
    let receipt = json!({"schema_version":1,"run_root":run,"run_id":command["run_id"],
        "phase":"inventory","preapproval_sha256":command["preapproval_sha256"],
        "overlay_id":command["overlay"]["id"],"source_snapshot_sha256":command["source_snapshot_sha256"],
        "heap_tree_sha256":result["heap_tree_sha256"],
        "manifest_sha256":common::digest_file(&run.join("reference-manifest.json"))?,
        "result_sha256":common::digest_file(&run.join("result.json"))?,
        "command_sha256":result["command_sha256"],
        "build_result_sha256":common::digest_file(&build_run.join("result.json"))?,
        "build_run_id":build_result["run_id"],
        "raw_hashes":{"build":common::digest_file(&build_run.join("inventory/observer-raw"))?,
            "inventory":common::digest_file(&run.join("inventory/observer-raw"))?},
        "executed_root":command["executed_root"],"ml_roots":command["ml_roots"],
        "mount_identity":command["mount_identity"],"command_argv":command["command_argv"],
        "source_attestation_sha256":common::digest_file(&run.join("source-attestation.json"))?,
        "build_source_attestation_sha256":common::digest_file(&build_run.join("source-attestation.json"))?,
        "writer_drain":true,"descendants_drained":true});
    common::require(
        manifest["runs"][0]["run_id"] == build_result["run_id"]
            && manifest["runs"][1]["run_id"] == result["run_id"],
        "completion receipt run identities differ from frozen manifest",
    )?;
    common::write_json_exclusive(&run.join("completion-receipt.json"), &receipt)
}

/// Called only after the supervisor has drained the domain and closed every raw writer.
pub(super) fn publish_v2_result(
    repository: &Path,
    workspace: &Path,
    run: &Path,
    build_run: Option<&Path>,
    operation: &str,
    prepared_sha256: &str,
    execution: (Option<i32>, Option<String>, Value, f64),
) -> Result<(), StepError> {
    let (exit_code, mut interruption, trace, elapsed) = execution;
    let artifacts = if exit_code == Some(0) && interruption.is_none() {
        let output = match operation {
            "build" => finalize_v2_build(run),
            "inventory" => build_run
                .ok_or_else(|| {
                    StepError::Input("instrumented inventory requires the exact build run".into())
                })
                .and_then(|build| finalize_v2_inventory(run, build)),
            _ => Err(StepError::Input(format!("unexpected instrumented operation {operation}"))),
        };
        match output {
            Ok(records) => records,
            Err(error) => {
                interruption = Some(format!("user-fixable: finalize instrumented run: {error}"));
                Map::new()
            },
        }
    } else {
        Map::new()
    };
    let command = common::read_json(&run.join("command.json"))?;
    let mut result = json!({"operation":operation,"run_id":command["run_id"],"schema_version":2,
        "exit_code":exit_code,"interruption":interruption,"elapsed_seconds":elapsed,
        "prepared_sha256":prepared_sha256,
        "stdout_sha256":common::digest_file(&run.join("stdout.log"))?,
        "command_sha256":common::digest_file(&run.join("command.json"))?,
        "events_sha256":common::digest_file(&run.join("events.jsonl"))?,
        "run":run,"trace":trace,"events":run.join("events.jsonl")});
    for (key, value) in artifacts {
        result[key] = value;
    }
    common::write_json_exclusive(&run.join("result.json"), &result)?;
    if exit_code != Some(0) || interruption.is_some() {
        return Err(StepError::Protocol {
            operation: format!("instrumented reference {operation} on {}", run.display()),
            detail: format!("exit_code={exit_code:?}; interruption={interruption:?}"),
        });
    }
    if operation == "inventory" {
        let build = build_run
            .ok_or_else(|| StepError::Input("inventory missing supervised build".into()))?;
        let inventory = common::read_json(&run.join("inventory/inventory.json"))?;
        let execution = common::read_json(&run.join("inventory/execution.json"))?;
        let manifest =
            observe::publish_v2_run(repository, workspace, run, build, &inventory, &execution)?;
        publish_v2_receipt(run, build, &manifest)?;
    }
    Ok(())
}
