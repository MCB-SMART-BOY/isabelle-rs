//! Host-side approval bytes are outside the sandbox and are never proof authority.
use std::collections::BTreeMap;
use std::path::{Component, Path};

use isabelle_evidence::{ApprovedObserverIdentity, ObserverHostInputs};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use super::{common, compare};
use crate::runner::StepError;

const APPROVAL_LIMIT: u64 = 128 * 1024;
const MANIFEST_LIMIT: u64 = 16 * 1024 * 1024;
const SOURCE_LIMIT: u64 = 512 * 1024 * 1024;
const MAX_SOURCE_FILES: usize = 100_000;

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ResourceBudget {
    pub memory_bytes: u64,
    pub swap_bytes: u64,
    pub pids: u64,
    pub cpu_quota_us: u64,
    pub cpu_period_us: u64,
    pub wall_seconds: u64,
    pub scratch_bytes: u64,
    pub raw_total_bytes: u64,
    pub decoded_total_bytes: u64,
    pub max_artifacts: u64,
    pub max_events: u64,
    pub max_depth: u64,
}

impl ResourceBudget {
    pub fn require_policy(&self) -> Result<(), StepError> {
        let limits = [
            (self.memory_bytes, 8 * 1024 * 1024 * 1024),
            (self.swap_bytes, 0),
            (self.pids, 64),
            (self.cpu_quota_us, 200_000),
            (self.cpu_period_us, 100_000),
            (self.wall_seconds, 7200),
            (self.scratch_bytes, 4 * 1024 * 1024 * 1024),
            (self.raw_total_bytes, 512 * 1024 * 1024),
            (self.decoded_total_bytes, 512 * 1024 * 1024),
            (self.max_artifacts, 16),
            (self.max_events, 2_000_000),
            (self.max_depth, 512),
        ];
        common::require(
            limits.iter().all(|(value, ceiling)| *value <= *ceiling)
                && self.memory_bytes > 0
                && self.pids > 0
                && self.cpu_quota_us > 0
                && self.cpu_period_us > 0
                && self.wall_seconds > 0
                && self.scratch_bytes > 0
                && self.raw_total_bytes > 0
                && self.decoded_total_bytes > 0
                && self.max_artifacts >= 6
                && self.max_events > 0
                && self.max_depth > 0,
            "reference preapproval budget is outside the approved resource envelope",
        )
    }
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ApprovedPatch {
    pub path: String,
    pub original_sha256: Option<String>,
    pub patched_sha256: String,
    pub patch_sha256: String,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Preapproval {
    pub schema_version: u64,
    pub purpose: String,
    pub source_commit: String,
    pub p0_manifest_sha256: String,
    pub overlay_id: String,
    pub observer_sha256: String,
    pub generator_sha256: String,
    pub approved_patch_sha256: Vec<ApprovedPatch>,
    pub isabelle_binary_sha256: String,
    pub threat_model: String,
    pub resource_budget: ResourceBudget,
}

fn parse_preapproval(bytes: &[u8]) -> Result<Preapproval, StepError> {
    let approval: Preapproval = serde_json::from_slice(bytes).map_err(|source| {
        StepError::Json { operation: "decode reference preapproval".into(), source }
    })?;
    common::require(
        approval.schema_version == 1
            && approval.purpose == "instrumented_reference_preapproval"
            && approval.source_commit == common::COMMIT
            && approval.threat_model == "trusted_same_uid"
            && [
                &approval.p0_manifest_sha256,
                &approval.overlay_id,
                &approval.observer_sha256,
                &approval.generator_sha256,
                &approval.isabelle_binary_sha256,
            ]
            .iter()
            .all(|hash| is_hash(hash)),
        "reference preapproval identity differs from fixed policy",
    )?;
    approval.resource_budget.require_policy()?;
    let mut prior = "";
    for patch in &approval.approved_patch_sha256 {
        common::require(
            is_safe_relative(&patch.path)
                && patch.path.as_str() > prior
                && patch.original_sha256.as_ref().is_none_or(|hash| is_hash(hash))
                && is_hash(&patch.patched_sha256)
                && is_hash(&patch.patch_sha256),
            format!("invalid or unsorted approved source patch {}", patch.path),
        )?;
        prior = &patch.path;
    }
    Ok(approval)
}

pub fn is_hash(hash: &str) -> bool {
    hash.len() == 64
        && hash.bytes().all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
}

pub fn is_safe_relative(path: &str) -> bool {
    !path.is_empty()
        && Path::new(path).components().all(|part| matches!(part, Component::Normal(_)))
        && !path.contains('\\')
        && !path.contains('\0')
}

pub fn load_preapproval(
    path: &Path,
    p0_manifest: &Path,
) -> Result<(Preapproval, String), StepError> {
    let bytes = compare::read_checked_bytes(path, APPROVAL_LIMIT)?;
    let approval = parse_preapproval(&bytes)?;
    common::require(
        common::digest_bytes(&compare::read_checked_bytes(p0_manifest, MANIFEST_LIMIT)?)
            == approval.p0_manifest_sha256,
        "reference preapproval does not attest actual frozen P0 bytes",
    )?;
    Ok((approval, common::digest_bytes(&bytes)))
}

fn require_receipt(
    approval: &Value,
    receipt: &Value,
    root: &Path,
    manifest_sha256: &str,
    receipt_sha256: &str,
    preapproval_sha256: &str,
) -> Result<(), StepError> {
    let root_text = root.to_str().ok_or_else(|| StepError::Input("non-UTF8 run root".into()))?;
    common::require(
        root.is_absolute()
            && root
                .components()
                .all(|part| matches!(part, Component::Normal(_) | Component::RootDir)),
        "unsafe reference run root",
    )?;
    for (name, expected) in [
        ("approved_run_root", root_text),
        ("approved_manifest_sha256", manifest_sha256),
        ("receipt_sha256", receipt_sha256),
        ("preapproval_sha256", preapproval_sha256),
    ] {
        common::require(
            approval[name] == expected,
            format!("reference approval {name} differs from actual file bytes"),
        )?;
    }
    common::require(
        receipt["schema_version"] == 1
            && receipt["run_root"] == root_text
            && receipt["manifest_sha256"] == manifest_sha256
            && receipt["preapproval_sha256"] == preapproval_sha256
            && receipt["writer_drain"] == true
            && receipt["descendants_drained"] == true,
        "reference completion receipt has not attested a fully drained run",
    )
}

fn frozen_sources(root: &Path) -> Result<BTreeMap<String, String>, StepError> {
    let workspace = root
        .parent()
        .and_then(Path::parent)
        .ok_or_else(|| StepError::Input("reference run is not inside a workspace".into()))?;
    common::require(
        root.parent().and_then(Path::file_name).is_some_and(|name| name == "runs"),
        "reference run is not inside the workspace runs directory",
    )?;
    let report = common::decode_json(
        &compare::read_checked_bytes(&workspace.join("prepared.json"), MANIFEST_LIMIT)?,
        "read trusted frozen source inventory",
    )?;
    let entries = report["source_files"]
        .as_array()
        .ok_or_else(|| StepError::Input("prepared source inventory is absent".into()))?;
    let mut sources = BTreeMap::new();
    for entry in entries {
        let path =
            entry["path"].as_str().ok_or_else(|| StepError::Input("invalid source path".into()))?;
        let expected = entry["sha256"]
            .as_str()
            .ok_or_else(|| StepError::Input("invalid source hash".into()))?;
        common::require(
            is_safe_relative(path) && is_hash(expected),
            format!("unsafe frozen source {path}"),
        )?;
        let actual =
            compare::digest_checked_file(&workspace.join("fixed-source").join(path), SOURCE_LIMIT)?;
        common::require(
            actual == expected && sources.insert(path.into(), actual).is_none(),
            format!("frozen original source differs: {path}"),
        )?;
    }
    Ok(sources)
}

pub fn load_approved_identity(
    approval_path: &Path,
    manifest_path: &Path,
    run_root: &Path,
) -> Result<ApprovedObserverIdentity, StepError> {
    let approval_bytes = compare::read_checked_bytes(approval_path, APPROVAL_LIMIT)?;
    let approval: Value = common::decode_json(&approval_bytes, "decode sealed reference approval")?;
    let preapproval_path = approval_path
        .parent()
        .ok_or_else(|| StepError::Input("reference approval has no parent directory".into()))?
        .join("reference-preapproval.json");
    common::require(
        !approval_path.starts_with(run_root) && !preapproval_path.starts_with(run_root),
        "reference approvals must be outside the run",
    )?;
    let preapproval_bytes = compare::read_checked_bytes(&preapproval_path, APPROVAL_LIMIT)?;
    let preapproval = parse_preapproval(&preapproval_bytes)?;
    let mut shared = approval.clone();
    let shared_object = shared
        .as_object_mut()
        .ok_or_else(|| StepError::Input("reference approval must be an object".into()))?;
    for name in
        ["preapproval_sha256", "approved_manifest_sha256", "approved_run_root", "receipt_sha256"]
    {
        common::require(shared_object.remove(name).is_some(), format!("approval missing {name}"))?;
    }
    common::require(
        shared_object
            .insert("purpose".into(), Value::String("instrumented_reference_preapproval".into()))
            == Some(Value::String("instrumented_reference_approval".into()))
            && serde_json::from_value::<Preapproval>(shared).ok() == Some(preapproval.clone()),
        "approval shared policy differs from preapproval",
    )?;
    let manifest_bytes = compare::read_checked_bytes(manifest_path, MANIFEST_LIMIT)?;
    let manifest = common::decode_json(&manifest_bytes, "decode sealed reference manifest")?;
    let receipt_bytes =
        compare::read_checked_bytes(&run_root.join("completion-receipt.json"), APPROVAL_LIMIT)?;
    let receipt = common::decode_json(&receipt_bytes, "decode reference completion receipt")?;
    let manifest_hash = common::digest_bytes(&manifest_bytes);
    let receipt_hash = common::digest_bytes(&receipt_bytes);
    let preapproval_hash = common::digest_bytes(&preapproval_bytes);
    require_receipt(
        &approval,
        &receipt,
        run_root,
        &manifest_hash,
        &receipt_hash,
        &preapproval_hash,
    )?;
    let preapproval_value = serde_json::to_value(&preapproval).map_err(|source| {
        StepError::Json { operation: "re-encode checked preapproval".into(), source }
    })?;
    ApprovedObserverIdentity::from_verified_host(ObserverHostInputs {
        preapproval: &preapproval_value,
        approval: &approval,
        preapproval_sha256: &preapproval_hash,
        manifest_sha256: &manifest_hash,
        receipt_sha256: &receipt_hash,
        run_root: run_root.to_str().ok_or_else(|| StepError::Input("non-UTF8 run root".into()))?,
        original_sources: frozen_sources(run_root)?,
        manifest: &manifest,
    })
    .map_err(|error| StepError::Input(format!("verify reference approval identity: {error}")))
}

pub(super) const OFFLINE_PREREQUISITE: &str = "independent reference prerequisite";

pub(super) fn missing_offline_prerequisite(detail: impl Into<String>) -> StepError {
    StepError::Protocol { operation: OFFLINE_PREREQUISITE.into(), detail: detail.into() }
}

fn require_offline_receipt(
    approval: &Value,
    receipt: &Value,
    manifest: &Value,
    manifest_hash: &str,
    run_root: &str,
) -> Result<(), StepError> {
    if [
        "schema_version",
        "purpose",
        "producer",
        "source_commit",
        "manifest_sha256",
        "run_root",
        "runs",
        "executed",
        "writer_drain",
        "descendants_drained",
    ]
    .iter()
    .any(|key| receipt.get(*key).is_none())
    {
        return Err(missing_offline_prerequisite("offline execution/drain receipt is incomplete"));
    }
    common::require_fields(
        receipt,
        &[
            "schema_version",
            "purpose",
            "producer",
            "source_commit",
            "manifest_sha256",
            "run_root",
            "runs",
            "executed",
            "writer_drain",
            "descendants_drained",
        ],
        "offline run receipt",
    )?;
    if receipt["executed"] != true
        || receipt["writer_drain"] != true
        || receipt["descendants_drained"] != true
    {
        return Err(missing_offline_prerequisite(
            "offline run execution or draining is unconfirmed",
        ));
    }
    if approval["producer"]["identity"].as_str().is_none_or(str::is_empty) {
        return Err(missing_offline_prerequisite("independent producer approval is absent"));
    }
    common::require_fields(&approval["producer"], &["kind", "identity"], "approved producer")?;
    common::require(
        receipt["schema_version"] == 1
            && receipt["purpose"] == "offline_reference_run_receipt"
            && receipt["producer"] == approval["producer"]
            && receipt["source_commit"] == common::COMMIT
            && receipt["manifest_sha256"] == manifest_hash
            && receipt["run_root"] == run_root
            && approval["approved_run_root"] == run_root
            && receipt["runs"] == manifest["runs"]
            && receipt["executed"] == true
            && receipt["writer_drain"] == true
            && receipt["descendants_drained"] == true,
        "offline producer execution/drain receipt missing or inconsistent",
    )
}

/// Only the trusted caller selects this approval path; neither the package nor native report does.
pub fn load_offline_identity(
    approval_path: &Path,
    manifest_path: &Path,
    run_root: &Path,
    manifest: &Value,
    manifest_bytes: &[u8],
    remaining: &mut u64,
) -> Result<ApprovedObserverIdentity, StepError> {
    let is_clean = |path: &Path| {
        path.is_absolute()
            && path
                .components()
                .all(|part| matches!(part, Component::Normal(_) | Component::RootDir))
    };
    common::require(
        is_clean(run_root)
            && is_clean(approval_path)
            && is_clean(manifest_path)
            && manifest_path.parent() == Some(run_root),
        "offline input paths must be absolute, canonical components and manifest inside run root",
    )?;
    let package = run_root
        .parent()
        .ok_or_else(|| StepError::Input("offline package has no parent".into()))?;
    if approval_path.starts_with(package) {
        return Err(missing_offline_prerequisite(
            "offline approval must reside outside the entire imported package",
        ));
    }
    let approval_bytes = compare::read_budgeted_bytes(approval_path, APPROVAL_LIMIT, remaining)?;
    let approval = common::decode_json(&approval_bytes, "decode external offline approval")?;
    if approval["producer"]["identity"].as_str().is_none_or(str::is_empty)
        || approval.get("approved_run_root").is_none()
    {
        return Err(missing_offline_prerequisite("independent producer approval is absent"));
    }
    let receipt_bytes = compare::read_budgeted_bytes(
        &run_root.join("completion-receipt.json"),
        APPROVAL_LIMIT,
        remaining,
    )?;
    let receipt = common::decode_json(&receipt_bytes, "decode offline run receipt")?;
    let manifest_hash = common::digest_bytes(manifest_bytes);
    let run_text = run_root
        .to_str()
        .ok_or_else(|| StepError::Input("offline run root is not UTF-8".into()))?;
    require_offline_receipt(&approval, &receipt, manifest, &manifest_hash, run_text)?;
    let mut sources = BTreeMap::new();
    let entries = manifest["source_files"]
        .as_array()
        .ok_or_else(|| missing_offline_prerequisite("offline manifest lacks source files"))?;
    if entries.is_empty() {
        return Err(missing_offline_prerequisite("offline source inventory is absent"));
    }
    common::require(
        entries.len() <= MAX_SOURCE_FILES,
        "offline source inventory exceeds the file-count budget",
    )?;
    for entry in entries {
        let path = entry["path"]
            .as_str()
            .ok_or_else(|| StepError::Input("offline source path is not a string".into()))?;
        common::require(
            is_safe_relative(path)
                && !path.contains(':')
                && path.split('/').all(|part| !matches!(part, "" | "." | "..")),
            format!("unsafe offline source {path}"),
        )?;
        let actual = compare::digest_budgeted_file(
            &run_root.join("fixed-source").join(path),
            SOURCE_LIMIT,
            remaining,
        )?;
        common::require(
            entry["sha256"].as_str() == Some(actual.as_str()),
            format!("source bytes differ: {path}"),
        )?;
        common::require(
            sources.insert(path.into(), actual).is_none(),
            format!("duplicate offline source {path}"),
        )?;
    }
    ApprovedObserverIdentity::from_offline_host(
        &approval,
        manifest,
        &manifest_hash,
        &common::digest_bytes(&receipt_bytes),
        run_text,
        sources,
    )
    .map_err(|error| StepError::Input(format!("verify external offline approval: {error}")))
}
