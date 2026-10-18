use std::{fs, path::Path};

use tempfile::TempDir;
use xtask::{gates::check_firewall, runner::StepError};

fn create_fixture() -> TempDir {
    let fixture = tempfile::tempdir().expect("create isolated fixture");
    fs::create_dir_all(fixture.path().join("src/kernel")).expect("create kernel directory");
    fixture
}

fn write_kernel(root: &Path, text: &str) {
    fs::write(root.join("src/kernel/fixture.rs"), text).expect("write fixture source");
}

#[test]
fn firewall_clean_kernel_accepts_source() {
    let fixture = create_fixture();
    write_kernel(fixture.path(), "pub struct Safe;\n");
    assert!(check_firewall(fixture.path()).is_ok());
}

#[test]
fn firewall_legacy_import_rejects_source() {
    let fixture = create_fixture();
    write_kernel(fixture.path(), "use crate::core::unsafe_dependency;\n");
    let error = check_firewall(fixture.path()).expect_err("reject upper-layer import");
    assert!(error.to_string().contains("FIREWALL BREACH"), "{error}");
}

#[test]
fn firewall_forbidden_pattern_rejects_source() {
    let fixture = create_fixture();
    write_kernel(fixture.path(), "fn invalid() { let _ = Typ::dummy; }\n");
    let error = check_firewall(fixture.path()).expect_err("reject forbidden term");
    assert!(error.to_string().contains("Typ::dummy"), "{error}");
}

#[test]
fn firewall_missing_directory_reports_scan_error() {
    let fixture = tempfile::tempdir().expect("create fixture");
    let error = check_firewall(fixture.path()).expect_err("missing kernel must fail");
    assert!(matches!(error, StepError::Io { .. }), "{error}");
}

#[test]
fn firewall_unreadable_source_reports_read_error() {
    let fixture = create_fixture();
    fs::write(fixture.path().join("src/kernel/invalid.rs"), [0xff])
        .expect("write invalid UTF-8 fixture");
    let error = check_firewall(fixture.path()).expect_err("source read failure must propagate");
    assert!(matches!(error, StepError::Io { .. }), "{error}");
    assert!(error.to_string().contains("invalid.rs"), "{error}");
}
