use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::path::PathBuf;
use xtask::reference::common::COMMIT;

struct OfflineApprovalFixture {
    _directory: tempfile::TempDir,
    run: PathBuf,
    manifest_path: PathBuf,
    approval_path: PathBuf,
    manifest: Value,
    manifest_bytes: Vec<u8>,
}

impl OfflineApprovalFixture {
    fn new() -> Self {
        let directory = tempfile::tempdir().unwrap();
        let run = directory.path().join("package/run");
        std::fs::create_dir_all(run.join("fixed-source/src/Pure")).unwrap();
        let source = b"independently opened source bytes";
        std::fs::write(run.join("fixed-source/src/Pure/ROOT.ML"), source).unwrap();
        let source_hash = format!("{:x}", Sha256::digest(source));
        let run_record = |phase: &str, id: &str| {
            json!({"phase":phase,"run_id":id,
            "prepared_sha256":"a".repeat(64),"source_snapshot_sha256":"a".repeat(64),
            "heap_tree_sha256":"a".repeat(64),"command_sha256":"a".repeat(64),
            "result_sha256":"a".repeat(64)})
        };
        let manifest = json!({"runs":[run_record("build","build-id"),
            run_record("inventory","inventory-id")],"source_files":[
            {"path":"src/Pure/ROOT.ML","sha256":source_hash}]});
        let manifest_bytes = serde_json::to_vec(&manifest).unwrap();
        let manifest_path = run.join("manifest.json");
        std::fs::write(&manifest_path, &manifest_bytes).unwrap();
        let approval_path = directory.path().join("operator-approval.json");
        let manifest_hash = format!("{:x}", Sha256::digest(&manifest_bytes));
        let producer =
            json!({"kind":"independent_official","identity":"outside operator reviewed producer"});
        let receipt = json!({"schema_version":1,"purpose":"offline_reference_run_receipt",
            "producer":producer,"source_commit":COMMIT,"manifest_sha256":manifest_hash,
            "run_root":run,"runs":manifest["runs"],"executed":true,
            "writer_drain":true,"descendants_drained":true});
        let receipt_bytes = serde_json::to_vec(&receipt).unwrap();
        std::fs::write(run.join("completion-receipt.json"), &receipt_bytes).unwrap();
        let hash = "a".repeat(64);
        let approval = json!({"schema_version":1,"purpose":"offline_reference_approval",
            "producer":producer,"source_commit":COMMIT,"p0_manifest_sha256":hash,
            "overlay_id":hash,"observer_sha256":hash,"generator_sha256":hash,
            "approved_patch_sha256":[],"isabelle_binary_sha256":hash,
            "resource_budget":{"memory_bytes":1024,"swap_bytes":0,"pids":1,
                "cpu_quota_us":1,"cpu_period_us":1,"wall_seconds":1,"scratch_bytes":1024,
                "raw_total_bytes":1024,"decoded_total_bytes":1024,
                "max_artifacts":6,"max_events":1,"max_depth":1},
            "manifest_sha256":manifest_hash,
            "receipt_sha256":format!("{:x}",Sha256::digest(&receipt_bytes)),
            "approved_run_root":run,"runs":manifest["runs"],"source_files":manifest["source_files"]});
        std::fs::write(&approval_path, serde_json::to_vec(&approval).unwrap()).unwrap();
        Self { _directory: directory, run, manifest_path, approval_path, manifest, manifest_bytes }
    }

    fn import(
        &self,
        approval: &std::path::Path,
    ) -> Result<isabelle_evidence::ApprovedObserverIdentity, xtask::runner::StepError> {
        let mut remaining = 1024 * 1024;
        xtask::reference::approved_identity::load_offline_identity(
            approval,
            &self.manifest_path,
            &self.run,
            &self.manifest,
            &self.manifest_bytes,
            &mut remaining,
        )
    }

    fn run_cli(&self) -> std::process::Output {
        std::process::Command::new(env!("CARGO_BIN_EXE_xtask"))
            .args(["reference", "compare", "--reference-run"])
            .arg(&self.run)
            .arg("--rust-report")
            .arg(self.run.join("native.json"))
            .arg("--reference-manifest")
            .arg(&self.manifest_path)
            .arg("--reference-approval")
            .arg(&self.approval_path)
            .output()
            .unwrap()
    }
}

#[test]
fn offline_approval_package_self_authorization_rejected() {
    let fixture = OfflineApprovalFixture::new();
    assert!(fixture.import(&fixture.approval_path).is_ok());
    let inside = fixture.run.join("self-approval.json");
    std::fs::copy(&fixture.approval_path, &inside).unwrap();
    assert!(fixture.import(&inside).is_err());
}

#[test]
fn offline_approval_changed_source_rejected() {
    let fixture = OfflineApprovalFixture::new();
    std::fs::write(fixture.run.join("fixed-source/src/Pure/ROOT.ML"), b"swapped").unwrap();
    assert!(fixture.import(&fixture.approval_path).is_err());
}

#[test]
fn offline_approval_changed_receipt_rejected() {
    let fixture = OfflineApprovalFixture::new();
    std::fs::write(fixture.run.join("completion-receipt.json"), b"{}").unwrap();
    assert!(fixture.import(&fixture.approval_path).is_err());
}

#[test]
fn offline_approval_changed_manifest_bytes_rejected() {
    let fixture = OfflineApprovalFixture::new();
    let mut changed = fixture.manifest_bytes.clone();
    changed.push(b' ');
    std::fs::write(&fixture.manifest_path, changed).unwrap();
    let bytes = std::fs::read(&fixture.manifest_path).unwrap();
    let mut remaining = 1024 * 1024;
    assert!(
        xtask::reference::approved_identity::load_offline_identity(
            &fixture.approval_path,
            &fixture.manifest_path,
            &fixture.run,
            &fixture.manifest,
            &bytes,
            &mut remaining
        )
        .is_err()
    );
}

#[test]
fn offline_approval_missing_receipt_rejected() {
    let fixture = OfflineApprovalFixture::new();
    std::fs::remove_file(fixture.run.join("completion-receipt.json")).unwrap();
    assert!(fixture.import(&fixture.approval_path).is_err());
}

#[test]
fn offline_approval_duplicate_json_keys_rejected() {
    let fixture = OfflineApprovalFixture::new();
    std::fs::write(&fixture.approval_path, br#"{"schema_version":1,"schema_version":1}"#).unwrap();
    assert!(fixture.import(&fixture.approval_path).is_err());
}

#[test]
fn offline_comparison_without_operator_approval_blocks() {
    let fixture = OfflineApprovalFixture::new();
    let error = xtask::reference::compare::run(
        &fixture.run.join("absent-frozen.json"),
        &fixture.run,
        &fixture.run.join("absent-native.json"),
        Some(&fixture.manifest_path),
        None,
    )
    .unwrap_err();
    assert!(error.to_string().contains("BlockedPrerequisite"));
}

#[test]
fn offline_approval_exhausted_read_budget_rejected() {
    let fixture = OfflineApprovalFixture::new();
    let mut remaining = 1;
    assert!(
        xtask::reference::approved_identity::load_offline_identity(
            &fixture.approval_path,
            &fixture.manifest_path,
            &fixture.run,
            &fixture.manifest,
            &fixture.manifest_bytes,
            &mut remaining
        )
        .is_err()
    );
}

#[test]
fn offline_comparison_without_run_records_blocks() {
    let fixture = OfflineApprovalFixture::new();
    let mut manifest = fixture.manifest.clone();
    manifest.as_object_mut().unwrap().remove("runs");
    std::fs::write(&fixture.manifest_path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let error = xtask::reference::compare::run(
        &fixture.run.join("absent-frozen.json"),
        &fixture.run,
        &fixture.run.join("absent-native.json"),
        Some(&fixture.manifest_path),
        Some(&fixture.approval_path),
    )
    .unwrap_err();
    assert!(error.to_string().contains("BlockedPrerequisite"));
}

#[test]
fn offline_cli_missing_receipt_reports_blocked_prerequisite() {
    let fixture = OfflineApprovalFixture::new();
    std::fs::remove_file(fixture.run.join("completion-receipt.json")).unwrap();
    let output = fixture.run_cli();
    assert!(!output.status.success());
    let report: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(report["purpose"], "official_compatibility_result");
    assert_eq!(report["result"], "BlockedPrerequisite");
}

#[test]
fn offline_cli_wrong_approved_manifest_hash_fails_input() {
    let fixture = OfflineApprovalFixture::new();
    let mut approval: Value =
        serde_json::from_slice(&std::fs::read(&fixture.approval_path).unwrap()).unwrap();
    approval["manifest_sha256"] = json!("b".repeat(64));
    std::fs::write(&fixture.approval_path, serde_json::to_vec(&approval).unwrap()).unwrap();
    let output = fixture.run_cli();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty(), "invalid input cannot publish a compatibility report");
    assert!(String::from_utf8_lossy(&output.stderr).contains("manifest"));
}
