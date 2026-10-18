//! Package actual same-version reference observations without claiming unobserved fields.
use std::collections::BTreeMap;
use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::path::Path;

use isabelle_evidence::{P0_MISSING, collect_required_sources, verify_reference};
use serde_json::{Value, json};

use super::{artifacts, common, decode_bootstrap_events, decode_observations, execute, prepare};
use crate::runner::{StepError, io_error};

const MAX_ARTIFACT_BYTES: u64 = 512 * 1024 * 1024;
const UNAVAILABLE_REASONS: [&str; 6] = [
    "Pure/thm_deps.ML:54-71 stops at named nodes; the Build hook does not expose full axiom/class/definition/typedef leaf certificates. Requires approved proof-derivation leaf instrumentation.",
    "Pure/thm.ML:1048-1073 stores private constraints; shyps/extra_shyps cannot expose unresolved obligations or occurrence paths. Requires approved observation at constraint creation/discharge.",
    "Pure/Build/build.ML:32-42 retains completed states, not each fact member's immutable registration owner and overwrite/alias history. Requires approved member registration event observation in Global_Theory.note_thmss/Facts.add_static.",
    "Pure/Build/build.ML:32-42 retains completed states only; unnamed transient proof results are not enumerable afterwards. Requires approved theorem/proof-step creation event observation.",
    "Pure/facts.ML:193-203 executes Dynamic callbacks during lookup; completed states do not retain the expression, invocation, or returned ephemeral thms. Requires approved Facts.lookup/Attrib.eval_thms invocation observation.",
    "Pure/Isar/outer_syntax.ML:78-92 keeps command parsers in private Theory_Data; final method/attribute spaces omit registration order, replacement and ML hooks. Requires approved per-registration effect observation.",
];

fn map_evidence_error(source: isabelle_evidence::EvidenceError) -> StepError {
    match source {
        isabelle_evidence::EvidenceError::Input(detail) => {
            StepError::Input(format!("verify observed reference run: {detail}"))
        },
        isabelle_evidence::EvidenceError::Json { name, source } => {
            StepError::Json { operation: format!("verify observed artifact {name}"), source }
        },
    }
}

fn read_bytes(path: &Path) -> Result<Vec<u8>, StepError> {
    let file = common::open_regular(path)?;
    let size = file
        .metadata()
        .map_err(|source| io_error(format!("stat observed artifact {}", path.display()), source))?
        .len();
    common::require(
        size <= MAX_ARTIFACT_BYTES,
        format!("observed artifact exceeds size limit: {}", path.display()),
    )?;
    let mut bytes = Vec::new();
    file.take(MAX_ARTIFACT_BYTES + 1)
        .read_to_end(&mut bytes)
        .map_err(|source| io_error(format!("read observed artifact {}", path.display()), source))?;
    common::require(
        bytes.len() as u64 <= MAX_ARTIFACT_BYTES,
        format!("observed artifact grew past size limit: {}", path.display()),
    )?;
    Ok(bytes)
}

fn artifact_record(run: &Path, name: &str) -> Result<Value, StepError> {
    let path = format!("inventory/{name}.json");
    let absolute = run.join(&path);
    let bytes = common::open_regular(&absolute)?
        .metadata()
        .map_err(|source| {
            io_error(format!("stat observed artifact {}", absolute.display()), source)
        })?
        .len();
    common::require(
        bytes <= MAX_ARTIFACT_BYTES,
        format!("observed artifact exceeds size limit: {}", absolute.display()),
    )?;
    Ok(json!({"name":name,"path":path,"sha256":common::digest_file(&absolute)?,"bytes":bytes}))
}

fn source_files(
    inventory: &Value,
    execution: &Value,
    frozen: &Value,
) -> Result<Vec<Value>, StepError> {
    let entries =
        collect_required_sources(inventory, execution, frozen).map_err(map_evidence_error)?;
    Ok(entries.into_iter().map(|(path, sha256)| json!({"path":path,"sha256":sha256})).collect())
}

fn make_observer() -> (Value, Value) {
    let records: Vec<_> = P0_MISSING
        .iter()
        .zip(UNAVAILABLE_REASONS)
        .map(|(field, reason)| {
            json!({"field":field,"reason":reason,
            "observation":{"artifact":"fact-origins","pointer":"/observations"}})
        })
        .collect();
    let fields = P0_MISSING
        .iter()
        .enumerate()
        .map(|(index, field)| {
            (
                field.to_string(),
                json!({"status":"Unavailable","reason":UNAVAILABLE_REASONS[index],
            "evidence":{"artifact":"observer","pointer":format!("/records/{index}")}}),
            )
        })
        .collect::<serde_json::Map<_, _>>();
    (
        json!({"schema_version":1,"source_commit":common::COMMIT,
        "fact_origins_artifact":"fact-origins","records":records}),
        json!({"schema_version":1,"source_commit":common::COMMIT,"fields":fields}),
    )
}

fn verify_packaged_run(repository: &Path, run: &Path, manifest: &Value) -> Result<(), StepError> {
    let mut artifacts = BTreeMap::new();
    artifacts.insert(
        "closure.json".into(),
        read_bytes(&repository.join("tests/fixtures/isabelle2025/closure.json"))?,
    );
    for record in manifest["artifacts"]
        .as_array()
        .ok_or_else(|| StepError::Input("artifact records missing".into()))?
    {
        let name = common::as_str(common::field(record, "name")?, "artifact name")?;
        let path = common::as_str(common::field(record, "path")?, "artifact path")?;
        artifacts.insert(name.into(), read_bytes(&run.join(path))?);
    }
    verify_reference(manifest, &artifacts).map_err(map_evidence_error)?;
    Ok(())
}

pub fn publish_run(
    repository: &Path,
    run: &Path,
    inventory: &Value,
    execution: &Value,
) -> Result<Value, StepError> {
    let frozen_path = repository.join("tests/fixtures/isabelle2025/closure.json");
    let frozen_bytes = read_bytes(&frozen_path)?;
    let frozen = common::decode_json(&frozen_bytes, "original frozen P0 manifest")?;
    common::require(
        frozen["source"]["git_commit"] == common::COMMIT,
        "frozen P0 source differs from observed version",
    )?;
    let path = run.join("inventory/fact-origins.yxml");
    let raw = prepare::read_text(&path)?;
    let source_root = run
        .parent()
        .and_then(Path::parent)
        .ok_or_else(|| StepError::Input("run has no fixed-source workspace".into()))?
        .join("fixed-source");
    let mut origins = decode_observations::decode_fact_origins(&raw, &source_root, execution)?;
    origins["raw_yxml_sha256"] = json!(common::digest_bytes(raw.as_bytes()));
    let (observer, closure) = make_observer();
    for (name, payload) in
        [("fact-origins", origins), ("observer", observer), ("closure-evidence", closure)]
    {
        common::write_json_exclusive(&run.join(format!("inventory/{name}.json")), &payload)?;
    }
    let artifacts = ["inventory", "execution", "fact-origins", "observer", "closure-evidence"]
        .iter()
        .map(|name| artifact_record(run, name))
        .collect::<Result<Vec<_>, _>>()?;
    let manifest = json!({"schema_version":1,"purpose":"native_reference_evidence",
        "source_commit":common::COMMIT,"p0_manifest_sha256":common::digest_bytes(&frozen_bytes),
        "source_files":source_files(inventory, execution, &frozen)?,"artifacts":artifacts});
    verify_packaged_run(repository, run, &manifest)?;
    common::write_json_exclusive(&run.join("reference-manifest.json"), &manifest)?;
    Ok(manifest)
}

/// Package an existing successful, same-observer run without launching Isabelle or a solver.
pub fn package_completed_run(repository: &Path, run: &Path) -> Result<Value, StepError> {
    common::require(
        run.is_absolute()
            && run
                .parent()
                .is_some_and(|parent| parent.file_name().is_some_and(|name| name == "runs")),
        "observed reference run must be an absolute direct child of runs",
    )?;
    let workspace = run
        .parent()
        .and_then(Path::parent)
        .ok_or_else(|| StepError::Input("run has no workspace".into()))?;
    artifacts::require_managed_directory(run, workspace)?;
    let result = common::read_json(&run.join("result.json"))?;
    common::require(
        result["operation"] == "inventory"
            && result["exit_code"] == 0
            && result["interruption"].is_null(),
        "only completed successful inventory runs can be packaged",
    )?;
    let command = common::read_json(&run.join("command.json"))?;
    common::require(
        command["observer_sources"]
            == execute::describe_sources(
                &repository.join("scripts/reference"),
                &execute::OBSERVER_FILES,
            )?,
        "completed run did not execute the current observation probe",
    )?;
    for (name, field) in [
        ("command.json", "command_sha256"),
        ("inventory/inventory.json", "inventory_sha256"),
        ("inventory/execution.json", "execution_sha256"),
    ] {
        common::require(
            result[field] == common::digest_file(&run.join(name))?,
            format!("completed run artifact changed: {name}"),
        )?;
    }
    let inventory = common::read_json(&run.join("inventory/inventory.json"))?;
    let execution = common::read_json(&run.join("inventory/execution.json"))?;
    publish_run(repository, run, &inventory, &execution)
}

fn read_executed_sources(run: &Path) -> Result<Value, StepError> {
    let path = run.join("source-hashes.tsv");
    let bytes = read_bytes(&path)?;
    let text = std::str::from_utf8(&bytes).map_err(|_| {
        StepError::Input(format!("executed R source hashes are not UTF-8: {}", path.display()))
    })?;
    let mut hashes = serde_json::Map::new();
    for line in text.lines() {
        let (source, hash) = line
            .split_once('\t')
            .ok_or_else(|| StepError::Input("malformed executed R source map line".into()))?;
        common::require(
            source.starts_with("src/")
                && source.split('/').all(|part| !matches!(part, "" | "." | ".."))
                && hash.len() == 64
                && hash.bytes().all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
                && hashes.insert(source.into(), json!(hash)).is_none()
                && common::digest_file(&run.join("fixed-source").join(source))? == hash,
            format!("executed R source map differs from snapshot at {source}"),
        )?;
    }
    common::require(!hashes.is_empty(), "supervised R source map is empty")?;
    Ok(Value::Object(hashes))
}

fn merge_observer_raw(build_run: &Path, run: &Path) -> Result<Vec<u8>, StepError> {
    let first = read_bytes(&build_run.join("inventory/observer-raw"))?;
    let second = read_bytes(&run.join("inventory/observer-raw"))?;
    common::require(
        !first.is_empty()
            && !second.is_empty()
            && first.len().saturating_add(second.len()) <= MAX_ARTIFACT_BYTES as usize,
        "merged build/inventory original observer bytes exceed approved budget",
    )?;
    let mut merged = Vec::with_capacity(first.len() + second.len());
    merged.extend_from_slice(&first);
    merged.extend_from_slice(&second);
    let path = run.join("inventory/observer-raw.merged");
    let mut file =
        OpenOptions::new().write(true).create_new(true).mode(0o600).open(&path).map_err(
            |source| io_error(format!("create merged observer bytes {}", path.display()), source),
        )?;
    file.write_all(&merged).map_err(|source| {
        io_error(format!("write original merged observer bytes {}", path.display()), source)
    })?;
    Ok(merged)
}

fn artifact_record_v2(run: &Path, name: &str, path: &str) -> Result<Value, StepError> {
    let bytes = read_bytes(&run.join(path))?;
    Ok(json!({"name":name,"path":path,"sha256":common::digest_bytes(&bytes),
        "bytes":bytes.len()}))
}

fn run_record(run: &Path, phase: &str) -> Result<Value, StepError> {
    let command = common::read_json(&run.join("command.json"))?;
    let result = common::read_json(&run.join("result.json"))?;
    common::require(
        command["schema_version"] == 2
            && command["run_id"] == result["run_id"]
            && result["operation"] == phase
            && result["exit_code"] == 0
            && result["interruption"].is_null()
            && result["command_sha256"] == common::digest_file(&run.join("command.json"))?,
        format!("{phase}: supervised reference run did not complete with fixed command bytes"),
    )?;
    Ok(json!({"phase":phase,"run_id":command["run_id"],
        "prepared_sha256":result["prepared_sha256"],
        "source_snapshot_sha256":command["source_snapshot_sha256"],
        "heap_tree_sha256":result["heap_tree_sha256"],
        "command_sha256":result["command_sha256"],
        "result_sha256":common::digest_file(&run.join("result.json"))?}))
}

fn make_v2_closure(observer: &Value, bootstrap: &Value) -> Value {
    let has_unattested_load = bootstrap["loads"].as_array().is_none_or(|loads| {
        loads.iter().any(|load| {
            load["source_provenance"] == "immutable_bootstrap_use" || load["sealed"] != true
        })
    });
    let fields = P0_MISSING.iter().map(|field| {
        let reason = if has_unattested_load {
            "Bootstrap contains opaque or unsealed source loads; immutable source/launch receipt requires independent trusted review before any field can be complete."
        } else if observer["coverage"].as_array().is_none_or(|seals|
            !seals.iter().any(|seal| seal["field"] == *field)) {
            "No fully sealed original instrumentation coverage for this field."
        } else {
            "Original event coverage has not been independently verified against the approved host identity."
        };
        (field.to_string(), json!({"status":"Unavailable","reason":reason}))
    }).collect::<serde_json::Map<_, _>>();
    json!({"schema_version":2,"source_commit":common::COMMIT,"fields":fields})
}

/// Package actual successful supervised build/inventory bytes without self-approving observations.
pub fn publish_v2_run(
    repository: &Path,
    workspace: &Path,
    run: &Path,
    build_run: &Path,
    inventory: &Value,
    execution: &Value,
) -> Result<Value, StepError> {
    let build_command = common::read_json(&build_run.join("command.json"))?;
    let command = common::read_json(&run.join("command.json"))?;
    common::require(
        build_command["overlay"] == command["overlay"]
            && build_command["source_files"] == command["source_files"]
            && build_command["source_snapshot_sha256"] == command["source_snapshot_sha256"]
            && build_command["preapproval_sha256"] == command["preapproval_sha256"],
        "inventory differs from exact preapproved build overlay/source bytes",
    )?;
    let mut source_hashes = read_executed_sources(run)?;
    common::require(
        source_hashes == read_executed_sources(build_run)?,
        "build/inventory executed R source maps differ",
    )?;
    for patch in command["overlay"]["patches"]
        .as_array()
        .ok_or_else(|| StepError::Input("approved P overlay patch list missing".into()))?
    {
        let path = common::as_str(common::field(patch, "path")?, "overlay patch source path")?;
        if path.starts_with("session/") {
            let hash = common::as_str(
                common::field(patch, "patched_sha256")?,
                "session observer source hash",
            )?;
            common::require(
                path.split('/').all(|part| !matches!(part, "" | "." | ".."))
                    && common::digest_file(&run.join(path))? == hash,
                format!("session observer source differs from approved P: {path}"),
            )?;
            source_hashes[path] = json!(hash);
        }
    }
    let build = run_record(build_run, "build")?;
    let inventory_run = run_record(run, "inventory")?;
    common::require(
        build["heap_tree_sha256"] == inventory_run["heap_tree_sha256"]
            && inventory["loaded_pure_heap_tree_sha256"] == build["heap_tree_sha256"],
        "inventory loaded a different Pure heap from supervised build",
    )?;
    let raw = merge_observer_raw(build_run, run)?;
    let identity = json!({"build_run_id":build["run_id"],
        "inventory_run_id":inventory_run["run_id"],"source_commit":common::COMMIT,
        "overlay_id":command["overlay"]["id"],"source_hashes":source_hashes});
    let bootstrap = decode_bootstrap_events::decode_bootstrap_events_v2(&raw, &identity)?;
    let observer = decode_observations::decode_observer_events_v2(
        &raw, &identity, inventory, execution, &bootstrap,
    )?;
    let closure = make_v2_closure(&observer, &bootstrap);
    let directory = run.join("inventory");
    for (name, payload) in [
        ("bootstrap-events", bootstrap),
        ("observer-events", observer),
        ("closure-evidence", closure),
    ] {
        common::write_json_exclusive(&directory.join(format!("{name}.json")), &payload)?;
    }
    let artifacts = [
        ("inventory", "inventory/inventory.json"),
        ("execution", "inventory/execution.json"),
        ("closure-evidence", "inventory/closure-evidence.json"),
        ("observer-events", "inventory/observer-events.json"),
        ("observer-raw", "inventory/observer-raw.merged"),
        ("bootstrap-events", "inventory/bootstrap-events.json"),
    ]
    .iter()
    .map(|(name, path)| artifact_record_v2(run, name, path))
    .collect::<Result<Vec<_>, _>>()?;
    let frozen = read_bytes(&repository.join("tests/fixtures/isabelle2025/closure.json"))?;
    let source_root = workspace.join("fixed-source");
    for original in command["source_files"]
        .as_array()
        .ok_or_else(|| StepError::Input("supervised original B source map missing".into()))?
    {
        let path = common::as_str(common::field(original, "path")?, "original source path")?;
        common::require(
            path.starts_with("src/")
                && path.split('/').all(|part| !matches!(part, "" | "." | ".."))
                && original["sha256"] == common::digest_file(&source_root.join(path))?,
            format!("original B source bytes differ at {path}"),
        )?;
    }
    let manifest = json!({"schema_version":2,"purpose":"native_reference_evidence",
        "source_commit":common::COMMIT,"p0_manifest_sha256":common::digest_bytes(&frozen),
        "source_files":command["source_files"],"overlay":command["overlay"],
        "runs":[build,inventory_run],"artifacts":artifacts});
    common::write_json_exclusive(&run.join("reference-manifest.json"), &manifest)?;
    Ok(manifest)
}
