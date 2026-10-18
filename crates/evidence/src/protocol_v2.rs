//! Instrumented reference observations: identity and provenance, never theorem authority.
mod match_fields;
mod raw;
#[cfg(test)]
mod tests;

use crate::common::{COMMIT, ROOTS, as_array, as_object, as_str, field, require, require_fields};
use crate::compare::{ComparisonDiagnostics, P0_MISSING};
use crate::compare_syntax::require_index;
use crate::protocol::{Comparison, VerifiedReferenceEvidence, validate_relative_path};
use crate::{EvidenceError, validate_entities, validate_graph};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

const REQUIRED_ARTIFACTS: [&str; 6] = [
    "inventory",
    "execution",
    "closure-evidence",
    "observer-events",
    "observer-raw",
    "bootstrap-events",
];
const MAX_ARTIFACT_BYTES: u64 = 512 * 1024 * 1024;

/// Validated import ceilings. These restrict processing; they do not attest execution.
#[derive(Clone, Copy, Debug)]
pub struct ObservationLimits {
    pub raw_total_bytes: u64,
    pub decoded_total_bytes: u64,
    pub max_artifacts: usize,
    pub max_events: usize,
    pub max_depth: usize,
}
/// Untrusted values supplied by a host that has independently verified the external bytes.
/// Constructing this bundle does not certify the host checks or grant theorem authority.
pub struct ObserverHostInputs<'a> {
    pub preapproval: &'a Value,
    pub approval: &'a Value,
    pub preapproval_sha256: &'a str,
    pub manifest_sha256: &'a str,
    pub receipt_sha256: &'a str,
    pub run_root: &'a str,
    pub original_sources: BTreeMap<String, String>,
    pub manifest: &'a Value,
}

/// Approval validated by the trusted host against independent preapproval and completion receipt bytes.
/// Construct only after checking the external ordinary files and all original frozen source bytes.
#[derive(Debug)]
pub struct ApprovedObserverIdentity {
    approved_manifest: Value,
    source_commit: String,
    p0_manifest_sha256: String,
    overlay_id: String,
    observer_sha256: String,
    generator_sha256: String,
    patches: Value,
    original_sources: BTreeMap<String, String>,
    limits: ObservationLimits,
}

fn digest(bytes: &[u8]) -> String {
    base16ct::lower::encode_string(&Sha256::digest(bytes))
}

fn sha<'a>(value: &'a Value, context: &str) -> Result<&'a str, EvidenceError> {
    let text = as_str(value, context)?;
    require(
        text.len() == 64 && text.bytes().all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c)),
        format!("{context}: invalid SHA256"),
    )?;
    Ok(text)
}

fn identity(value: &Value, context: &str) -> Result<String, EvidenceError> {
    let text = as_str(value, context)?;
    require(!text.is_empty(), format!("{context}: empty identity"))?;
    Ok(text.to_owned())
}

fn check_approval_budget(value: &Value) -> Result<ObservationLimits, EvidenceError> {
    let budget = field(value, "resource_budget")?;
    let maximum = [
        ("memory_bytes", 8 * 1024 * 1024 * 1024_u64),
        ("swap_bytes", 0),
        ("pids", 64),
        ("cpu_quota_us", 200_000),
        ("cpu_period_us", 100_000),
        ("wall_seconds", 7200),
        ("scratch_bytes", 4 * 1024 * 1024 * 1024),
        ("raw_total_bytes", 512 * 1024 * 1024),
        ("decoded_total_bytes", 512 * 1024 * 1024),
        ("max_artifacts", 16),
        ("max_events", 2_000_000),
        ("max_depth", 512),
    ];
    let names = maximum.map(|(name, _)| name);
    require_fields(budget, &names, "reference resource budget")?;
    require(
        as_object(budget, "reference resource budget")?.len() == names.len(),
        "resource budget has unknown fields",
    )?;
    for (key, limit) in maximum {
        let amount = require_index(field(budget, key)?, key)?;
        require(
            if key == "swap_bytes" { amount == 0 } else { amount > 0 && amount <= limit },
            format!("resource budget {key} outside approved bounds"),
        )?;
    }
    let count = |key| {
        usize::try_from(require_index(field(budget, key)?, key)?)
            .map_err(|source| EvidenceError::Input(format!("resource budget {key}: {source}")))
    };
    Ok(ObservationLimits {
        raw_total_bytes: require_index(field(budget, "raw_total_bytes")?, "raw byte budget")?,
        decoded_total_bytes: require_index(
            field(budget, "decoded_total_bytes")?,
            "decoded byte budget",
        )?,
        max_artifacts: count("max_artifacts")?,
        max_events: count("max_events")?,
        max_depth: count("max_depth")?,
    })
}

fn validate_approved_patches(preapproval: &Value) -> Result<(), EvidenceError> {
    let mut patches = BTreeSet::new();
    let mut previous_patch = None;
    for patch in as_array(field(preapproval, "approved_patch_sha256")?, "approved patches")? {
        require_fields(
            patch,
            &["path", "original_sha256", "patched_sha256", "patch_sha256"],
            "approved patch",
        )?;
        require(
            as_object(patch, "approved patch")?.len() == 4,
            "approved patch has unexpected fields",
        )?;
        let path = as_str(field(patch, "path")?, "approved path")?;
        validate_relative_path(path)?;
        require(patches.insert(path), format!("duplicate approved patch {path}"))?;
        require(
            previous_patch.is_none_or(|previous| previous < path),
            "approved patches must have unique canonical path order",
        )?;
        previous_patch = Some(path);
        if !patch["original_sha256"].is_null() {
            sha(&patch["original_sha256"], path)?;
        }
        sha(&patch["patched_sha256"], path)?;
        sha(&patch["patch_sha256"], path)?;
    }
    Ok(())
}

impl ApprovedObserverIdentity {
    /// The importer must apply these ceilings before reading or allocating artifact data.
    pub fn import_limits(&self) -> ObservationLimits {
        self.limits
    }

    /// The input bundle itself does not authenticate any of these host-side checks.
    pub fn from_verified_host(input: ObserverHostInputs<'_>) -> Result<Self, EvidenceError> {
        let ObserverHostInputs {
            preapproval,
            approval,
            preapproval_sha256,
            manifest_sha256,
            receipt_sha256,
            run_root,
            original_sources,
            manifest,
        } = input;
        let base = [
            "schema_version",
            "purpose",
            "source_commit",
            "p0_manifest_sha256",
            "overlay_id",
            "observer_sha256",
            "generator_sha256",
            "approved_patch_sha256",
            "isabelle_binary_sha256",
            "threat_model",
            "resource_budget",
        ];
        require_fields(preapproval, &base, "reference preapproval")?;
        let extra = [
            "preapproval_sha256",
            "approved_manifest_sha256",
            "approved_run_root",
            "receipt_sha256",
        ];
        let mut approval_keys = base.to_vec();
        approval_keys.extend(extra);
        require_fields(approval, &approval_keys, "reference approval")?;
        require(
            as_object(preapproval, "preapproval")?.len() == base.len()
                && as_object(approval, "approval")?.len() == approval_keys.len(),
            "approval has unknown or missing fields",
        )?;
        for key in base {
            if key != "purpose" {
                require(
                    preapproval[key] == approval[key],
                    format!("approval differs from preapproval at {key}"),
                )?;
            }
        }
        require(
            preapproval["schema_version"] == 1
                && preapproval["source_commit"] == COMMIT
                && preapproval["purpose"] == "instrumented_reference_preapproval"
                && approval["purpose"] == "instrumented_reference_approval"
                && preapproval["threat_model"] == "trusted_same_uid",
            "preapproval identity mismatch",
        )?;
        for key in [
            "p0_manifest_sha256",
            "overlay_id",
            "observer_sha256",
            "generator_sha256",
            "isabelle_binary_sha256",
        ] {
            sha(&preapproval[key], key)?;
        }
        for (key, supplied) in [
            ("preapproval_sha256", preapproval_sha256),
            ("approved_manifest_sha256", manifest_sha256),
            ("receipt_sha256", receipt_sha256),
        ] {
            require(
                approval[key] == supplied,
                format!("approved {key} differs from verified host bytes"),
            )?;
            sha(&approval[key], key)?;
        }
        require(
            run_root.starts_with('/')
                && !run_root.contains('\0')
                && approval["approved_run_root"] == run_root,
            "approved absolute run root differs from verified host root",
        )?;
        let limits = check_approval_budget(preapproval)?;
        validate_approved_patches(preapproval)?;
        require(!original_sources.is_empty(), "host supplied no frozen source byte identities")?;
        for (path, hash) in &original_sources {
            validate_relative_path(path)?;
            sha(&json!(hash), path)?;
        }
        Ok(Self {
            approved_manifest: manifest.clone(),
            source_commit: COMMIT.into(),
            p0_manifest_sha256: identity(&preapproval["p0_manifest_sha256"], "P0 hash")?,
            overlay_id: identity(&preapproval["overlay_id"], "overlay id")?,
            observer_sha256: identity(&preapproval["observer_sha256"], "observer hash")?,
            generator_sha256: identity(&preapproval["generator_sha256"], "generator hash")?,
            patches: preapproval["approved_patch_sha256"].clone(),
            original_sources,
            limits,
        })
    }

    /// Bind an offline, operator-selected approval to the exact manifest and independently
    /// opened original source bytes. The host, not the package, verifies approval/receipt IO.
    pub fn from_offline_host(
        approval: &Value,
        manifest: &Value,
        manifest_sha256: &str,
        receipt_sha256: &str,
        run_root: &str,
        original_sources: BTreeMap<String, String>,
    ) -> Result<Self, EvidenceError> {
        let keys = [
            "schema_version",
            "purpose",
            "producer",
            "source_commit",
            "p0_manifest_sha256",
            "overlay_id",
            "observer_sha256",
            "generator_sha256",
            "approved_patch_sha256",
            "isabelle_binary_sha256",
            "resource_budget",
            "manifest_sha256",
            "receipt_sha256",
            "approved_run_root",
            "runs",
            "source_files",
        ];
        require_fields(approval, &keys, "offline reference approval")?;
        require(
            as_object(approval, "offline reference approval")?.len() == keys.len()
                && approval["schema_version"] == 1
                && approval["purpose"] == "offline_reference_approval"
                && approval["source_commit"] == COMMIT
                && approval["producer"]["kind"] == "independent_official"
                && approval["producer"]["identity"].as_str().is_some_and(|name| !name.is_empty()),
            "offline approval has no independent producer or fixed source identity",
        )?;
        require(
            approval["manifest_sha256"] == manifest_sha256
                && approval["receipt_sha256"] == receipt_sha256
                && run_root.starts_with('/')
                && approval["approved_run_root"] == run_root
                && approval["runs"] == manifest["runs"]
                && approval["source_files"] == manifest["source_files"],
            "offline approval does not bind the opened manifest, receipt, run root and sources",
        )?;
        for key in [
            "p0_manifest_sha256",
            "overlay_id",
            "observer_sha256",
            "generator_sha256",
            "isabelle_binary_sha256",
            "manifest_sha256",
            "receipt_sha256",
        ] {
            sha(&approval[key], key)?;
        }
        let limits = check_approval_budget(approval)?;
        require(!original_sources.is_empty(), "no independently opened source bytes")?;
        for (path, hash) in &original_sources {
            validate_relative_path(path)?;
            sha(&json!(hash), path)?;
        }
        Ok(Self {
            approved_manifest: manifest.clone(),
            source_commit: COMMIT.into(),
            p0_manifest_sha256: identity(&approval["p0_manifest_sha256"], "P0 hash")?,
            overlay_id: identity(&approval["overlay_id"], "overlay id")?,
            observer_sha256: identity(&approval["observer_sha256"], "observer hash")?,
            generator_sha256: identity(&approval["generator_sha256"], "generator hash")?,
            patches: approval["approved_patch_sha256"].clone(),
            original_sources,
            limits,
        })
    }
}

/// The approved bytes/identity are diagnostics only: no proof token or kernel privilege is conferred.
#[derive(Debug)]
pub(crate) struct VerifiedV2 {
    source_files: BTreeMap<String, String>,
    run_build: String,
    run_inventory: String,
    incomplete: Vec<&'static str>,
}

fn validate_sources(
    manifest: &Value,
    approved: &ApprovedObserverIdentity,
) -> Result<BTreeMap<String, String>, EvidenceError> {
    let mut base = BTreeMap::new();
    for file in as_array(field(manifest, "source_files")?, "frozen source files")? {
        require_fields(file, &["path", "sha256"], "frozen source")?;
        let path = as_str(field(file, "path")?, "frozen source path")?;
        validate_relative_path(path)?;
        let hash = sha(field(file, "sha256")?, path)?;
        require(
            base.insert(path.to_owned(), hash.to_owned()).is_none(),
            format!("duplicate frozen source {path}"),
        )?;
    }
    require(
        base == approved.original_sources,
        "manifest frozen B differs from actual host-read original source bytes",
    )?;
    let overlay = field(manifest, "overlay")?;
    require_fields(overlay, &["id", "patches", "observer_sha256", "generator_sha256"], "overlay")?;
    require(as_object(overlay, "overlay")?.len() == 4, "overlay has unknown fields")?;
    require(
        overlay["id"] == approved.overlay_id
            && overlay["observer_sha256"] == approved.observer_sha256
            && overlay["generator_sha256"] == approved.generator_sha256,
        "overlay differs from external approval",
    )?;
    let mut executed = base;
    let mut patches = BTreeMap::new();
    for patch in as_array(field(overlay, "patches")?, "overlay patches")? {
        require_fields(
            patch,
            &["path", "original_sha256", "patched_sha256", "patch_sha256"],
            "overlay patch",
        )?;
        require(
            as_object(patch, "overlay patch")?.len() == 4,
            "overlay patch has unexpected fields",
        )?;
        let path = as_str(field(patch, "path")?, "patch path")?;
        validate_relative_path(path)?;
        sha(field(patch, "patch_sha256")?, path)?;
        let target = sha(field(patch, "patched_sha256")?, path)?;
        let original = field(patch, "original_sha256")?;
        let expected = approved.original_sources.get(path);
        let matches_original = if original.is_null() {
            expected.is_none()
        } else {
            expected.map(String::as_str) == Some(sha(original, path)?)
        };
        require(matches_original, format!("{path}: overlay P original differs from frozen B"))?;
        if path.ends_with("/reference_observation.ML") {
            require(
                original.is_null() && target == approved.observer_sha256,
                "observer implementation differs from approved original ML bytes",
            )?;
        }
        require(
            patches.insert(path.to_owned(), patch.clone()).is_none(),
            format!("duplicate overlay patch {path}"),
        )?;
        executed.insert(path.to_owned(), target.to_owned());
    }
    require(
        patches.keys().any(|path| path.ends_with("/reference_observation.ML")),
        "overlay lacks actual approved observer implementation",
    )?;
    let approved_patches = as_array(&approved.patches, "approved patch list")?;
    require(patches.len() == approved_patches.len(), "overlay patch set differs from approval")?;
    for approved_patch in approved_patches {
        let path = as_str(field(approved_patch, "path")?, "approved patch path")?;
        require(
            patches.get(path) == Some(approved_patch),
            format!("{path}: overlay patch not approved"),
        )?;
    }
    Ok(executed)
}

fn decode_artifacts(
    manifest: &Value,
    opened: &BTreeMap<String, Vec<u8>>,
    limits: ObservationLimits,
) -> Result<BTreeMap<String, Value>, EvidenceError> {
    let mut decoded = BTreeMap::new();
    let mut paths = BTreeSet::new();
    let records = as_array(field(manifest, "artifacts")?, "v2 artifacts")?;
    require(records.len() <= limits.max_artifacts, "artifact count exceeds approved budget")?;
    let mut decoded_bytes = 0_u64;
    let mut raw_bytes = 0_u64;
    for record in records {
        require_fields(record, &["name", "path", "sha256", "bytes"], "v2 artifact")?;
        let name = as_str(field(record, "name")?, "artifact name")?;
        require(
            !name.is_empty() && name.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'-'),
            format!("invalid artifact name {name}"),
        )?;
        let path = as_str(field(record, "path")?, "artifact path")?;
        validate_relative_path(path)?;
        require(paths.insert(path), format!("duplicate artifact path {path}"))?;
        let bytes = opened
            .get(name)
            .ok_or_else(|| EvidenceError::Input(format!("missing opened artifact {name}")))?;
        require(
            bytes.len() as u64 == require_index(field(record, "bytes")?, "artifact byte length")?
                && bytes.len() as u64 <= MAX_ARTIFACT_BYTES
                && digest(bytes) == sha(field(record, "sha256")?, name)?,
            format!("{name}: opened artifact byte identity differs"),
        )?;
        if name == "observer-raw" {
            raw_bytes = raw_bytes
                .checked_add(bytes.len() as u64)
                .ok_or_else(|| EvidenceError::Input("raw byte count overflow".into()))?;
        } else {
            decoded_bytes = decoded_bytes
                .checked_add(bytes.len() as u64)
                .ok_or_else(|| EvidenceError::Input("decoded byte count overflow".into()))?;
        }
        require(
            raw_bytes <= limits.raw_total_bytes && decoded_bytes <= limits.decoded_total_bytes,
            "opened artifact bytes exceed approved resource budget",
        )?;
        let parsed = if name == "observer-raw" {
            Value::Null
        } else {
            crate::json::decode_reader_with_limit(bytes.as_slice(), limits.max_depth)
                .map_err(|source| EvidenceError::Json { name: name.into(), source })?
        };
        require(
            decoded.insert(name.to_owned(), parsed).is_none(),
            format!("duplicate artifact {name}"),
        )?;
    }
    require(
        REQUIRED_ARTIFACTS.iter().all(|key| decoded.contains_key(*key))
            && opened.len() == decoded.len() + 1
            && opened.keys().all(|name| name == "closure.json" || decoded.contains_key(name)),
        "v2 artifact set differs from required opened bytes",
    )?;
    Ok(decoded)
}

fn validate_runs(
    manifest: &Value,
    inventory: &Value,
    execution: &Value,
) -> Result<(String, String), EvidenceError> {
    let runs = as_array(field(manifest, "runs")?, "approved runs")?;
    require(runs.len() == 2, "exactly one build and one inventory run required")?;
    let mut ids = BTreeSet::new();
    let mut by_phase = BTreeMap::new();
    for run in runs {
        require_fields(
            run,
            &[
                "phase",
                "run_id",
                "prepared_sha256",
                "source_snapshot_sha256",
                "heap_tree_sha256",
                "command_sha256",
                "result_sha256",
            ],
            "run record",
        )?;
        let phase = as_str(field(run, "phase")?, "run phase")?;
        require(
            matches!(phase, "build" | "inventory") && by_phase.insert(phase, run).is_none(),
            "duplicate or unknown run phase",
        )?;
        let id = identity(field(run, "run_id")?, "run id")?;
        require(ids.insert(id), "duplicate run id")?;
        for key in [
            "prepared_sha256",
            "source_snapshot_sha256",
            "heap_tree_sha256",
            "command_sha256",
            "result_sha256",
        ] {
            sha(field(run, key)?, key)?;
        }
    }
    let build =
        by_phase.get("build").ok_or_else(|| EvidenceError::Input("missing build run".into()))?;
    let inventory_run = by_phase
        .get("inventory")
        .ok_or_else(|| EvidenceError::Input("missing inventory run".into()))?;
    require(
        build["heap_tree_sha256"] == inventory_run["heap_tree_sha256"]
            && inventory["loaded_pure_heap_tree_sha256"] == build["heap_tree_sha256"],
        "inventory did not inherit exact built Pure heap",
    )?;
    let id = &inventory_run["run_id"];
    require(
        inventory["run_id"] == *id && execution["run_id"] == *id,
        "inventory/execution run identity differs from inventory phase",
    )?;
    require(
        inventory["initial_theories"] == execution["initial_theories"]
            && inventory["initial_theories"].is_array(),
        "initial theories differ across inventory/execution",
    )?;
    Ok((
        build["run_id"].as_str().unwrap_or_default().into(),
        id.as_str().unwrap_or_default().into(),
    ))
}

fn check_executed_source(
    path: &Value,
    hash: &Value,
    executed: &BTreeMap<String, String>,
) -> Result<(), EvidenceError> {
    let source = as_str(path, "executed source path")?;
    validate_relative_path(source)?;
    let actual = sha(hash, source)?;
    require(
        executed.get(source).is_some_and(|expected| expected == actual),
        format!("{source}: actual executed R hash differs from B/P/R"),
    )
}

fn validate_executed_sources(
    inventory: &Value,
    execution: &Value,
    bootstrap: &Value,
    executed: &BTreeMap<String, String>,
) -> Result<(), EvidenceError> {
    for (path, hash) in as_object(field(inventory, "source_sha256")?, "inventory executed sources")?
    {
        check_executed_source(&json!(path), hash, executed)?;
    }
    for theory in as_array(field(execution, "theories")?, "executed theories")? {
        for command in as_array(field(theory, "commands")?, "executed commands")? {
            for file in as_array(field(command, "files")?, "executed command files")? {
                check_executed_source(field(file, "path")?, field(file, "sha256")?, executed)?;
            }
        }
    }
    for load in as_array(field(bootstrap, "loads")?, "bootstrap source loads")? {
        check_executed_source(field(load, "source")?, field(load, "source_sha256")?, executed)?;
    }
    Ok(())
}

fn validate_bootstrap_load_frames(
    load: &Value,
    frames: &[raw::Frame<'_>],
    source: &str,
    mode: &str,
) -> Result<(), EvidenceError> {
    let run = as_str(field(load, "run_id")?, "load run")?;
    let id = as_str(field(load, "load_id")?, "load identity")?;
    let begin = raw::referenced_frame_at(
        load,
        frames,
        "raw_begin_index",
        "raw_begin_sha256",
        "bootstrap begin",
    )?;
    require(
        begin.channel == "bootstrap"
            && begin.tag == "load_begin"
            && begin.run_id == run
            && begin.root_id == id,
        "load begin differs from original frame",
    )?;
    let end = if load["finished"] == true {
        let end = raw::referenced_frame(load, frames, "bootstrap end")?;
        require(
            end.channel == "bootstrap"
                && end.tag == "load_end"
                && end.run_id == run
                && end.root_id == id,
            "load end differs from original frame",
        )?;
        Some(end)
    } else {
        None
    };
    let seal = if load["sealed"] == true {
        let seal = raw::referenced_frame_at(
            load,
            frames,
            "raw_seal_index",
            "raw_seal_sha256",
            "bootstrap seal",
        )?;
        require(
            seal.channel == "bootstrap"
                && seal.tag == "load_seal"
                && seal.run_id == run
                && seal.root_id == id,
            "load seal differs from original frame",
        )?;
        Some(seal)
    } else {
        None
    };
    for (frame, is_end) in std::iter::once((begin, false))
        .chain(end.map(|frame| (frame, true)))
        .chain(seal.map(|frame| (frame, false)))
    {
        let payload = raw::parse_fields(frame.payload, 7)?;
        require(
            payload[0] == source.as_bytes()
                && payload[5] == mode.as_bytes()
                && payload[2] == as_str(field(load, "session")?, "load session")?.as_bytes()
                && payload[3] == as_str(field(load, "theory")?, "load theory")?.as_bytes(),
            format!("{source}: nested load identity differs"),
        )?;
        let parent = load["parent_load_id"].as_str().unwrap_or_default();
        require(
            payload[1] == parent.as_bytes()
                && payload[4] == load["source_order"].to_string().as_bytes(),
            format!("{source}: nested load parent or order differs"),
        )?;
        if mode == "actual_read_bytes" && is_end {
            require(
                digest(payload[6]) == as_str(field(load, "source_sha256")?, "consumed bytes")?,
                format!("{source}: consumed source bytes differ from executed R"),
            )?;
        } else {
            require(payload[6].is_empty(), format!("{source}: false consumed bytes claim"))?;
        }
    }
    Ok(())
}

fn validate_bootstrap_event(
    event: &Value,
    load: &Value,
    frames: &[raw::Frame<'_>],
    build: &str,
    max_depth: usize,
) -> Result<(), EvidenceError> {
    let frame = raw::referenced_frame(event, frames, "bootstrap event")?;
    require(
        frame.channel == "observer"
            && frame.tag == "event"
            && frame.run_id == build
            && event["run_id"] == frame.run_id
            && event["load_id"] == frame.root_id
            && event["local_id"] == frame.local_id,
        "bootstrap event differs from original raw frame",
    )?;
    let (attrs, original) = raw::decode_observer_payload(frame, max_depth)?;
    require(
        attrs[0] == "original_bootstrap"
            && load["source"] == attrs[2]
            && load["source_sha256"] == attrs[3]
            && P0_MISSING.contains(&attrs[4])
            && field(event, "field")? == attrs[4]
            && field(event, "value")? == &original,
        "bootstrap observation payload differs from source load or decoded event",
    )
}

fn validate_bootstrap(
    bootstrap: &Value,
    frames: &[raw::Frame<'_>],
    build: &str,
    inventory: &str,
    executed: &BTreeMap<String, String>,
    max_depth: usize,
) -> Result<bool, EvidenceError> {
    require_fields(
        bootstrap,
        &["schema_version", "source_commit", "overlay_id", "loads", "events"],
        "bootstrap event artifact",
    )?;
    require(
        bootstrap["schema_version"] == 2 && bootstrap["source_commit"] == COMMIT,
        "bootstrap identity differs",
    )?;
    let mut sealed = BTreeSet::new();
    let mut has_incomplete_load = false;
    let mut loads = BTreeMap::new();
    for load in as_array(field(bootstrap, "loads")?, "bootstrap loads")? {
        let run = as_str(field(load, "run_id")?, "bootstrap run")?;
        require(run == build || run == inventory, "bootstrap load has foreign run identity")?;
        let id = identity(field(load, "load_id")?, "bootstrap load id")?;
        let source = as_str(field(load, "source")?, "bootstrap source")?;
        check_executed_source(&json!(source), field(load, "source_sha256")?, executed)?;
        let mode = as_str(field(load, "source_provenance")?, "bootstrap provenance mode")?;
        require(
            matches!(mode, "actual_read_bytes" | "immutable_bootstrap_use"),
            format!("{source}: unknown bootstrap source provenance"),
        )?;
        require(
            load["started"] == true
                && load["finished"].is_boolean()
                && load["sealed"].is_boolean()
                && (load["sealed"] != true || load["finished"] == true),
            format!("{source}: inconsistent bootstrap completion flags"),
        )?;
        validate_bootstrap_load_frames(load, frames, source, mode)?;
        let is_finished = load["finished"] == true && load["sealed"] == true;
        if !is_finished {
            has_incomplete_load = true;
        }
        if is_finished {
            if mode == "immutable_bootstrap_use" {
                has_incomplete_load = true;
            }
            sealed.insert((run.to_owned(), id.clone(), source.to_owned()));
        }
        require(
            loads.insert((run.to_owned(), id.clone()), load).is_none(),
            format!("duplicate bootstrap load {run}/{id}"),
        )?;
    }
    for event in as_array(field(bootstrap, "events")?, "bootstrap events")? {
        let run = as_str(field(event, "run_id")?, "bootstrap event run")?;
        let id = as_str(field(event, "load_id")?, "bootstrap event load")?;
        let load = loads.get(&(run.to_owned(), id.to_owned())).ok_or_else(|| {
            EvidenceError::Input(format!("bootstrap event references missing load {run}/{id}"))
        })?;
        validate_bootstrap_event(event, load, frames, build, max_depth)?;
    }
    Ok(!has_incomplete_load
        && sealed.iter().any(|(run, _, source)| run == build && source.ends_with("ROOT0.ML")))
}

fn has_complete_command_controls(
    frames: &[raw::Frame<'_>],
    run: &str,
    execution: &Value,
) -> Result<bool, EvidenceError> {
    let mut controls = BTreeMap::<(String, u64, String), (usize, usize)>::new();
    let mut has_exception = false;
    for frame in frames.iter().filter(|frame| frame.channel == "observer" && frame.run_id == run) {
        if frame.tag == "callback_exception" {
            has_exception = true;
        }
        if !matches!(frame.tag, "command_begin" | "command_end") {
            continue;
        }
        let command: Value = serde_json::from_str(frame.root_id).map_err(|source| {
            EvidenceError::Input(format!("invalid original command root: {source}"))
        })?;
        require(command["run_id"] == run, "command control root has foreign run")?;
        let key = (
            identity(field(&command, "theory")?, "command theory")?,
            require_index(field(&command, "sequence")?, "command sequence")?,
            identity(field(&command, "source")?, "command source")?,
        );
        let state = controls.entry(key).or_default();
        if frame.tag == "command_begin" {
            state.0 += 1;
        } else {
            state.1 += 1;
        }
    }
    let mut expected = BTreeSet::new();
    for theory in as_array(field(execution, "theories")?, "execution theories")? {
        let name = identity(field(theory, "name")?, "executed theory")?;
        for command in as_array(field(theory, "commands")?, "executed commands")? {
            let source = identity(field(command, "source")?, "executed source")?;
            expected.insert((
                name.clone(),
                require_index(field(command, "sequence")?, "sequence")?,
                source,
            ));
        }
    }
    Ok(!has_exception
        && expected.len() == controls.len()
        && expected.iter().all(|key| controls.get(key) == Some(&(1, 1))))
}

fn validate_observer_load_root(
    metadata: &Value,
    load: &Value,
    loads: &[Value],
    run: &str,
) -> Result<(), EvidenceError> {
    let root = field(metadata, "load_root")?;
    require(
        as_object(root, "decoded source load root")?.len() == 7,
        "decoded source load root has unexpected fields",
    )?;
    let parent_source = load["parent_load_id"].as_str().and_then(|parent| {
        loads
            .iter()
            .find(|candidate| candidate["run_id"] == run && candidate["load_id"] == parent)
            .map(|candidate| &candidate["source"])
    });
    require(
        field(root, "source")? == field(load, "source")?
            && field(root, "parent_source")? == parent_source.unwrap_or(&Value::Null)
            && field(root, "source_order")? == field(load, "source_order")?
            && field(root, "session")? == field(load, "session")?
            && field(root, "theory")? == field(load, "theory")?
            && field(root, "source_provenance")? == field(load, "source_provenance")?
            && field(root, "missing_parent")? == (load["missing_parent"] == true),
        "decoded source load root differs from actual bootstrap load",
    )
}

fn validate_observer_metadata(
    metadata: &Value,
    frame: &raw::Frame<'_>,
    attrs: [&str; 5],
    bootstrap: &Value,
) -> Result<(), EvidenceError> {
    let loads = as_array(field(bootstrap, "loads")?, "bootstrap loads")?;
    let load = loads
        .iter()
        .find(|load| load["run_id"] == frame.run_id && load["load_id"] == frame.root_id);
    require(
        as_object(metadata, "decoded observer metadata")?.len()
            == if load.is_some() { 8 } else { 7 }
            && metadata["run_id"] == frame.run_id
            && metadata["phase"] == attrs[0]
            && metadata["theory"] == attrs[1]
            && metadata["source"] == attrs[2]
            && metadata["source_sha256"] == attrs[3]
            && metadata["root_id"] == frame.root_id
            && metadata["local_id"] == frame.local_id,
        "decoded observer metadata differs from original event",
    )?;
    if let Some(load) = load {
        validate_observer_load_root(metadata, load, loads, frame.run_id)?;
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct ObserverRecordInputs<'a, 'f> {
    build: &'a str,
    inventory: &'a str,
    executed: &'a BTreeMap<String, String>,
    bootstrap: &'a Value,
    reference_inventory: &'a Value,
    execution: &'a Value,
    is_bootstrap_verified: bool,
    max_depth: usize,
    frames: &'f [raw::Frame<'f>],
}

fn validate_observer_record_items(
    records: &[Value],
    inputs: ObserverRecordInputs<'_, '_>,
) -> Result<(), EvidenceError> {
    let ObserverRecordInputs { build, inventory, executed, bootstrap, max_depth, frames, .. } =
        inputs;
    let mut seen = BTreeSet::new();
    for record in records {
        require(
            as_object(record, "observer record")?.len() == 3,
            "observer record has unexpected fields",
        )?;
        let field_name = as_str(field(record, "field")?, "observer field")?;
        let run = as_str(field(record, "run_id")?, "observer run")?;
        require(
            P0_MISSING.contains(&field_name)
                && (run == build || run == inventory)
                && seen.insert((run, field_name)),
            "duplicate, foreign, or invalid observer record",
        )?;
        for item in as_array(field(record, "value")?, "observer field records")? {
            require(
                as_object(item, "observer item")?.len() == 4,
                "decoded observer event has unexpected fields",
            )?;
            let metadata = field(item, "metadata")?;
            require(metadata["run_id"] == run, "observer item has foreign run")?;
            let phase = as_str(field(metadata, "phase")?, "observer work phase")?;
            require(
                matches!(
                    (run == build, phase),
                    (true, "original_bootstrap" | "preparation")
                        | (false, "original_target" | "reference_export")
                ),
                "observer event has invalid build/inventory phase",
            )?;
            check_executed_source(
                field(metadata, "source")?,
                field(metadata, "source_sha256")?,
                executed,
            )?;
            let frame = raw::referenced_frame(item, frames, "observer item")?;
            require(
                frame.channel == "observer" && frame.tag == "event" && frame.run_id == run,
                "observer item differs from original raw event",
            )?;
            let (attrs, original) = raw::decode_observer_payload(frame, max_depth)?;
            require(
                attrs[4] == field_name && &original == field(item, "value")?,
                "original observer payload differs from decoded event",
            )?;
            validate_observer_metadata(metadata, frame, attrs, bootstrap)?;
        }
    }
    Ok(())
}

fn validate_observer_seals(
    coverage: &[Value],
    inputs: ObserverRecordInputs<'_, '_>,
) -> Result<(), EvidenceError> {
    let ObserverRecordInputs { build, inventory, executed, max_depth, frames, .. } = inputs;
    let mut covered = BTreeSet::new();
    for seal in coverage {
        require(
            as_object(seal, "observer coverage")?.len() == 7,
            "decoded observation seal has unexpected fields",
        )?;
        let run = as_str(field(seal, "run_id")?, "coverage run")?;
        let name = as_str(field(seal, "field")?, "coverage field")?;
        require(
            (run == build || run == inventory)
                && P0_MISSING.contains(&name)
                && covered.insert((run, name)),
            "duplicate/foreign observation coverage",
        )?;
        let frame = raw::referenced_frame(seal, frames, "observation seal")?;
        require(
            frame.channel == "observer" && frame.tag == "seal" && frame.run_id == run,
            "coverage seal differs from original raw frame",
        )?;
        let (attrs, original) = raw::decode_observer_payload(frame, max_depth)?;
        require(
            attrs[4] == name
                && matches!(
                    (run == build, attrs[0]),
                    (true, "original_bootstrap" | "preparation")
                        | (false, "original_target" | "reference_export")
                )
                && executed.get(attrs[2]).is_some_and(|hash| hash == attrs[3]),
            "original observation seal has foreign field, phase or source",
        )?;
        let original = as_object(&original, "original observation seal")?;
        require(original.len() == 3, "original observation seal has unexpected fields")?;
        for key in ["named_members", "executed_commands", "bootstrap_loads"] {
            require(
                original.get(key) == Some(field(seal, key)?),
                format!("{key}: original observation seal differs from decoded coverage"),
            )?;
            as_array(field(seal, key)?, key)?;
        }
    }
    Ok(())
}

fn validate_available_observer(
    name: &str,
    wrapper: &Value,
    observer: &Value,
    coverage: &[Value],
    inputs: ObserverRecordInputs<'_, '_>,
    is_command_verified: bool,
) -> Result<bool, EvidenceError> {
    let ObserverRecordInputs {
        build,
        inventory,
        bootstrap,
        reference_inventory,
        execution,
        is_bootstrap_verified,
        ..
    } = inputs;
    require_fields(wrapper, &["status", "value", "evidence", "completeness"], name)?;
    require(wrapper["completeness"] == "complete", format!("{name}: incomplete claim"))?;
    let provenance = field(wrapper, "evidence")?;
    require_fields(provenance, &["artifact", "pointer"], "v2 observation pointer")?;
    require(
        provenance["artifact"] == "observer-events",
        "v2 Available requires original observer",
    )?;
    let pointer = as_str(field(provenance, "pointer")?, "v2 record pointer")?;
    require(
        pointer.starts_with("/records/")
            && pointer["/records/".len()..].bytes().all(|c| c.is_ascii_digit()),
        format!("{name}: invalid observer pointer"),
    )?;
    let record = observer
        .pointer(pointer)
        .ok_or_else(|| EvidenceError::Input(format!("{name}: missing original observer record")))?;
    require(
        record["field"] == name && record["value"] == wrapper["value"],
        format!("{name}: closure value differs from original observer record"),
    )?;
    let run = as_str(field(record, "run_id")?, "available record run")?;
    require(
        run == inventory || (run == build && name != "declaration_origin"),
        format!("{name}: available field has invalid run source"),
    )?;
    if !is_bootstrap_verified || !is_command_verified {
        return Ok(false);
    }
    validate_coverage(name, run, record, coverage, reference_inventory, execution, bootstrap)
}

fn validate_observer_records(
    observer: &Value,
    closure: &Value,
    inputs: ObserverRecordInputs<'_, '_>,
) -> Result<Vec<&'static str>, EvidenceError> {
    let ObserverRecordInputs { inventory, execution, frames, .. } = inputs;
    require_fields(
        observer,
        &["schema_version", "source_commit", "overlay_id", "records", "coverage"],
        "observer event artifact",
    )?;
    require(
        observer["schema_version"] == 2 && observer["source_commit"] == COMMIT,
        "observer events identity differs",
    )?;
    require_fields(closure, &["schema_version", "source_commit", "fields"], "v2 closure evidence")?;
    require(
        closure["schema_version"] == 2 && closure["source_commit"] == COMMIT,
        "closure evidence identity differs",
    )?;
    let fields = as_object(field(closure, "fields")?, "six closure fields")?;
    require(
        fields.keys().all(|name| P0_MISSING.contains(&name.as_str())),
        "v2 closure evidence contains an unknown field",
    )?;
    let records = as_array(field(observer, "records")?, "observer records")?;
    let coverage = as_array(field(observer, "coverage")?, "observer coverage")?;
    validate_observer_record_items(records, inputs)?;
    validate_observer_seals(coverage, inputs)?;
    raw::require_all_raw_events_mapped(frames, observer)?;
    let is_command_verified = has_complete_command_controls(frames, inventory, execution)?;
    let mut incomplete = Vec::new();
    for name in P0_MISSING {
        if !fields.contains_key(name) {
            incomplete.push(name);
            continue;
        }
        let wrapper = &fields[name];
        match as_str(field(wrapper, "status")?, name)? {
            "Unavailable" => {
                require_fields(wrapper, &["status", "reason"], name)?;
                require(
                    !as_str(field(wrapper, "reason")?, name)?.is_empty(),
                    format!("{name}: missing unavailability reason"),
                )?;
            },
            "Available" => {
                if !validate_available_observer(
                    name,
                    wrapper,
                    observer,
                    coverage,
                    inputs,
                    is_command_verified,
                )? {
                    incomplete.push(name);
                }
            },
            _ => return Err(EvidenceError::Input(format!("{name}: unknown observation status"))),
        }
    }
    Ok(incomplete)
}

fn validate_coverage(
    name: &str,
    run: &str,
    record: &Value,
    coverage: &[Value],
    inventory: &Value,
    execution: &Value,
    bootstrap: &Value,
) -> Result<bool, EvidenceError> {
    let Some(seal) = coverage.iter().find(|seal| seal["run_id"] == run && seal["field"] == name)
    else {
        return Ok(false);
    };
    let mut named = BTreeSet::new();
    for theory in as_array(field(inventory, "theories")?, "inventory theories")? {
        for group in as_array(field(theory, "fact_groups")?, "fact groups")? {
            for member in as_array(field(group, "theorems")?, "fact members")? {
                named.insert((
                    identity(field(theory, "name")?, "inventory theory")?,
                    identity(field(group, "name")?, "inventory fact group")?,
                    require_index(field(member, "index")?, "member index")?,
                ));
            }
        }
    }
    let mut observed = BTreeSet::new();
    for member in as_array(field(seal, "named_members")?, "covered members")? {
        require_fields(member, &["theory", "fact_group_name", "member_index"], "covered member")?;
        require(
            as_object(member, "covered member")?.len() == 3,
            "covered member has unexpected fields",
        )?;
        let key = (
            identity(field(member, "theory")?, "covered theory")?,
            identity(field(member, "fact_group_name")?, "covered fact group")?,
            require_index(field(member, "member_index")?, "covered index")?,
        );
        require(observed.insert(key), "duplicate covered named member")?;
    }
    let mut commands = BTreeSet::new();
    for theory in as_array(field(execution, "theories")?, "execution theories")? {
        for command in as_array(field(theory, "commands")?, "executed commands")? {
            commands.insert((
                theory["name"].to_string(),
                require_index(field(command, "sequence")?, "command sequence")?,
                command["source"].to_string(),
            ));
        }
    }
    let mut covered_commands = BTreeSet::new();
    for command in as_array(field(seal, "executed_commands")?, "covered commands")? {
        require(
            covered_commands.insert((
                command["theory"].to_string(),
                require_index(field(command, "sequence")?, "covered command sequence")?,
                command["source"].to_string(),
            )),
            "duplicate covered command",
        )?;
    }
    let mut loads = BTreeSet::new();
    for load in as_array(field(bootstrap, "loads")?, "bootstrap loads")? {
        if load["run_id"] == run || (load["run_id"] != run && load["session"] == "Pure") {
            loads.insert((load["run_id"].to_string(), load["load_id"].to_string()));
        }
    }
    let mut covered_loads = BTreeSet::new();
    for load in as_array(field(seal, "bootstrap_loads")?, "covered bootstrap loads")? {
        require(
            covered_loads.insert((load["run_id"].to_string(), load["load_id"].to_string())),
            "duplicate covered bootstrap load",
        )?;
    }
    let is_named = matches!(
        name,
        "full_axiom_extension_dependencies" | "unresolved_sort_obligations" | "declaration_origin"
    );
    let has_records =
        !is_named || (inventory["run_id"] == run && has_exact_named_records(record, &named)?);
    Ok(named == observed && commands == covered_commands && loads == covered_loads && has_records)
}

fn has_exact_named_records(
    record: &Value,
    named: &BTreeSet<(String, String, u64)>,
) -> Result<bool, EvidenceError> {
    let mut actual = BTreeSet::new();
    for item in as_array(field(record, "value")?, "named observer events")? {
        if field(field(item, "metadata")?, "phase")? != "original_target" {
            continue;
        }
        let value = field(item, "value")?;
        let key = (
            identity(field(value, "theory")?, "observed theory")?,
            identity(field(value, "fact_group_name")?, "observed fact group")?,
            require_index(field(value, "member_index")?, "named member index")?,
        );
        require(actual.insert(key), "duplicate named observer member event")?;
    }
    Ok(&actual == named)
}

/// Verify a v2 reference against already-opened raw bytes and a host-verified external approval.
/// It does not perform I/O or construct any theorem acceptance authority.
pub fn verify_reference_v2(
    manifest: &Value,
    artifacts: &BTreeMap<String, Vec<u8>>,
    approved_identity: &ApprovedObserverIdentity,
) -> Result<VerifiedReferenceEvidence, EvidenceError> {
    require(
        manifest == &approved_identity.approved_manifest,
        "v2 manifest differs from externally approved same-fd decoded bytes",
    )?;
    require_fields(
        manifest,
        &[
            "schema_version",
            "purpose",
            "source_commit",
            "p0_manifest_sha256",
            "source_files",
            "overlay",
            "runs",
            "artifacts",
        ],
        "v2 reference manifest",
    )?;
    require(
        as_object(manifest, "v2 manifest")?.len() == 8
            && manifest["schema_version"] == 2
            && manifest["purpose"] == "native_reference_evidence"
            && manifest["source_commit"] == approved_identity.source_commit
            && manifest["p0_manifest_sha256"] == approved_identity.p0_manifest_sha256,
        "v2 manifest schema/approved identity differs",
    )?;
    let bytes = artifacts
        .get("closure.json")
        .ok_or_else(|| EvidenceError::Input("missing original closure.json bytes".into()))?;
    require(
        digest(bytes) == approved_identity.p0_manifest_sha256,
        "original P0 manifest bytes differ from external approval",
    )?;
    let frozen = crate::decode_json_reader(bytes.as_slice(), "closure.json")?;
    require(
        frozen["source"]["git_commit"] == COMMIT
            && frozen["purpose"] == "isabelle2025_p0_reference_snapshot",
        "frozen P0 identity differs",
    )?;
    let executed_sources = validate_sources(manifest, approved_identity)?;
    let mut decoded = decode_artifacts(manifest, artifacts, approved_identity.limits)?;
    let inventory = decoded
        .remove("inventory")
        .ok_or_else(|| EvidenceError::Input("missing inventory".into()))?;
    let execution = decoded
        .remove("execution")
        .ok_or_else(|| EvidenceError::Input("missing execution".into()))?;
    let closure = decoded
        .remove("closure-evidence")
        .ok_or_else(|| EvidenceError::Input("missing closure evidence".into()))?;
    let bootstrap = field(&json!(decoded), "bootstrap-events")?.clone();
    let observer = field(&json!(decoded), "observer-events")?.clone();
    require(
        inventory["roots"] == json!(ROOTS)
            && execution["roots"] == json!(ROOTS)
            && inventory["reference"] == "Isabelle2025"
            && execution["reference"] == "Isabelle2025",
        "v2 reference roots or identity differ",
    )?;
    validate_graph(as_array(field(&inventory, "theories")?, "inventory theories")?)?;
    validate_entities(as_array(field(&inventory, "theories")?, "inventory theories")?)?;
    let (run_build, run_inventory) = validate_runs(manifest, &inventory, &execution)?;
    require(
        observer["overlay_id"] == approved_identity.overlay_id
            && bootstrap["overlay_id"] == approved_identity.overlay_id,
        "decoded overlay differs from approved identity",
    )?;
    validate_executed_sources(&inventory, &execution, &bootstrap, &executed_sources)?;
    let raw_bytes = artifacts
        .get("observer-raw")
        .ok_or_else(|| EvidenceError::Input("missing original binary observer stream".into()))?;
    let frames = raw::parse_frames(raw_bytes, approved_identity.limits.max_events)?;
    require(
        frames.iter().all(|frame| frame.run_id == run_build || frame.run_id == run_inventory),
        "raw observer stream contains unapproved run identity",
    )?;
    let is_bootstrap_verified = validate_bootstrap(
        &bootstrap,
        &frames,
        &run_build,
        &run_inventory,
        &executed_sources,
        approved_identity.limits.max_depth,
    )?;
    let incomplete = validate_observer_records(
        &observer,
        &closure,
        ObserverRecordInputs {
            build: &run_build,
            inventory: &run_inventory,
            executed: &executed_sources,
            bootstrap: &bootstrap,
            reference_inventory: &inventory,
            execution: &execution,
            is_bootstrap_verified,
            max_depth: approved_identity.limits.max_depth,
            frames: &frames,
        },
    )?;
    Ok(VerifiedReferenceEvidence {
        inventory,
        execution,
        closure,
        frozen,
        incomplete_observations: Vec::new(),
        version_two: Some(VerifiedV2 {
            source_files: approved_identity.original_sources.clone(),
            run_build,
            run_inventory,
            incomplete,
        }),
    })
}

/// v2 comparisons are diagnostics only. The in-memory native host owns proof DAG replay.
pub(crate) fn compare_candidate_v2(
    reference: &VerifiedReferenceEvidence,
    verified: &VerifiedV2,
    candidate: &Value,
) -> Result<Comparison, EvidenceError> {
    let mut differences = crate::compare::compare_candidate_observations_v2(
        &reference.inventory,
        &reference.execution,
        candidate,
        &verified.source_files,
    )?;
    let fields = as_object(field(&reference.closure, "fields")?, "v2 closure fields")?;
    for name in P0_MISSING {
        if !fields.contains_key(name) {
            differences.blocked.push(json!({"field":name,"status":"Unavailable",
                "reason":"independent observation field absent"}));
            continue;
        }
        if fields[name]["status"] == "Unavailable" {
            differences.blocked.push(json!({"field":name,"status":"Unavailable",
                "reason":fields[name]["reason"]}));
            continue;
        }
        if verified.incomplete.contains(&name) {
            differences.blocked.push(json!({"field":name,"status":"Unavailable",
                "reason":"raw observation coverage not established"}));
            continue;
        }
        compare_field(
            &mut differences,
            name,
            field(&fields[name], "value")?,
            candidate,
            &reference.inventory,
            &verified.run_build,
            &verified.run_inventory,
        )?;
    }
    if !differences.differences.is_empty() {
        return Ok(Comparison::Different(differences.report()));
    }
    if !differences.blocked.is_empty() {
        return Ok(Comparison::Incomplete(differences.report()));
    }
    Ok(Comparison::Matched)
}

fn compare_field(
    result: &mut ComparisonDiagnostics,
    name: &str,
    observed: &Value,
    candidate: &Value,
    inventory: &Value,
    build: &str,
    run: &str,
) -> Result<(), EvidenceError> {
    let mut business = Vec::new();
    for record in as_array(observed, name)? {
        let metadata = field(record, "metadata")?;
        match as_str(field(metadata, "phase")?, "event business phase")? {
            "original_bootstrap" => require(
                metadata["run_id"] == build,
                "bootstrap business record comes from wrong run",
            )?,
            "original_target" => {
                require(metadata["run_id"] == run, "target business record comes from wrong run")?
            },
            "preparation" | "reference_export" => continue,
            _ => return Err(EvidenceError::Input(format!("{name}: invalid business phase"))),
        }
        if matches!(
            name,
            "anonymous_ephemeral_facts"
                | "dynamic_fact_evaluations"
                | "runtime_registration_effects"
        ) {
            business.push(record);
        } else {
            business.push(field(record, "value")?);
        }
    }
    if matches!(
        name,
        "anonymous_ephemeral_facts" | "dynamic_fact_evaluations" | "runtime_registration_effects"
    ) {
        match_fields::compare_events(result, name, &business, candidate, inventory)
    } else {
        match_fields::compare_named(result, name, &business, candidate, inventory)
    }
}
