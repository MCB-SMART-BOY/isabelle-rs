use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use isabelle_evidence::EvidenceError;
use isabelle_rs::ml::host::lifecycle::{BuildLifecycle, WorkKind};
use isabelle_rs::ml::{DenyHost, Vm};
use isabelle_rs::theory::native::reference::{ReferenceInputError, load_reference_inputs};

static NEXT_AREA: AtomicU64 = AtomicU64::new(0);

struct TestArea(PathBuf);

impl TestArea {
    fn new() -> Self {
        let id = NEXT_AREA.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir()
            .join(format!("native-reference-input-{}-{id}", std::process::id()));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn load(&self, manifest: Option<&str>) -> ReferenceInputError {
        let path = self.0.join("manifest.json");
        if let Some(manifest) = manifest {
            fs::write(&path, manifest).unwrap();
        }
        let vm = Vm::new(DenyHost);
        let lifecycle = BuildLifecycle::new(vm.stop_handle());
        let lease = lifecycle.start_root(WorkKind::Evaluation, "reference input").unwrap();
        let error = load_reference_inputs(&lifecycle, &lease, &path, &self.0).unwrap_err();
        lease.complete().unwrap();
        error
    }
}

impl Drop for TestArea {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn reference_input_missing_manifest_reports_prerequisite() {
    assert!(TestArea::new().load(None).is_missing_prerequisite());
}

#[test]
fn reference_input_duplicate_json_field_is_malformed_not_missing() {
    let error = TestArea::new().load(Some(r#"{"artifacts":[],"artifacts":[]}"#));
    assert!(!error.is_missing_prerequisite());
    assert!(matches!(
        error,
        ReferenceInputError::Evidence { source: EvidenceError::Json { .. }, .. }
    ));
}

#[test]
fn reference_input_parent_traversal_rejects_before_artifact_open() {
    let error = TestArea::new()
        .load(Some(r#"{"artifacts":[{"name":"inventory","path":"../absent.json","bytes":1}]}"#));
    assert!(matches!(error, ReferenceInputError::Evidence { source: EvidenceError::Input(_), .. }));
}

#[test]
fn reference_input_artifact_exceeding_declared_length_rejects() {
    let area = TestArea::new();
    fs::write(area.0.join("inventory.json"), b"[]").unwrap();
    let error = area
        .load(Some(r#"{"artifacts":[{"name":"inventory","path":"inventory.json","bytes":1}]}"#));
    assert!(matches!(
        error,
        ReferenceInputError::Read { source, .. }
            if matches!(*source, isabelle_rs::ml::host::files::HostIoError::TooLarge { limit: 1, .. })
    ));
}

#[test]
fn reference_input_symlink_artifact_never_reaches_evidence_verification() {
    let area = TestArea::new();
    fs::write(area.0.join("real.json"), b"[]").unwrap();
    std::os::unix::fs::symlink(area.0.join("real.json"), area.0.join("inventory.json")).unwrap();
    let error = area
        .load(Some(r#"{"artifacts":[{"name":"inventory","path":"inventory.json","bytes":2}]}"#));
    assert!(matches!(error, ReferenceInputError::Read { .. }));
    assert!(!error.is_missing_prerequisite());
}
