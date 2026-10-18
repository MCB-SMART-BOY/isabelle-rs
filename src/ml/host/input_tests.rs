use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use super::files::HostIoError;
use super::input::read_supervisor_input;
use super::lifecycle::{BuildLifecycle, WorkKind};
use crate::ml::{DenyHost, Vm};

static NEXT_AREA: AtomicU64 = AtomicU64::new(0);

struct TestArea(PathBuf);

impl TestArea {
    fn new() -> Self {
        let index = NEXT_AREA.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir()
            .join(format!("native-supervisor-input-{}-{index}", std::process::id()));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
}

impl Drop for TestArea {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn supervisor_input_exact_limit_preserves_all_bytes() {
    let area = TestArea::new();
    let vm = Vm::new(DenyHost);
    let lifecycle = BuildLifecycle::new(vm.stop_handle());
    let lease = lifecycle.start_root(WorkKind::Evaluation, "reference read").unwrap();
    let path = area.0.join("input.json");
    let content = b"{\"field\":\"value\"}\r\n";
    fs::write(&path, content).unwrap();
    assert_eq!(read_supervisor_input(&lifecycle, &lease, &path, content.len()).unwrap(), content);
    assert!(matches!(
        read_supervisor_input(&lifecycle, &lease, &path, content.len() - 1),
        Err(HostIoError::TooLarge { .. })
    ));
    lease.complete().unwrap();
}

#[test]
fn supervisor_input_symlink_components_never_follow_target() {
    let area = TestArea::new();
    let vm = Vm::new(DenyHost);
    let lifecycle = BuildLifecycle::new(vm.stop_handle());
    let lease = lifecycle.start_root(WorkKind::Evaluation, "reference read").unwrap();
    let real = area.0.join("real");
    fs::create_dir(&real).unwrap();
    fs::write(real.join("input.json"), b"[]").unwrap();
    std::os::unix::fs::symlink(&real, area.0.join("linked")).unwrap();
    std::os::unix::fs::symlink(real.join("input.json"), area.0.join("leaf.json")).unwrap();
    for path in [area.0.join("linked/input.json"), area.0.join("leaf.json")] {
        assert!(matches!(
            read_supervisor_input(&lifecycle, &lease, &path, 2),
            Err(HostIoError::Permission { .. } | HostIoError::Io { .. })
        ));
    }
    assert_eq!(fs::read(real.join("input.json")).unwrap(), b"[]");
    lease.complete().unwrap();
}

#[test]
fn supervisor_input_cancelled_lease_rejects_before_open() {
    let area = TestArea::new();
    let vm = Vm::new(DenyHost);
    let lifecycle = BuildLifecycle::new(vm.stop_handle());
    let lease = lifecycle.start_root(WorkKind::Evaluation, "reference read").unwrap();
    lifecycle.cancel("test cancelled reference read".into()).unwrap();
    assert!(matches!(
        read_supervisor_input(&lifecycle, &lease, &area.0.join("absent"), 1),
        Err(HostIoError::Lifecycle { .. })
    ));
    assert!(lease.complete().is_err());
    lifecycle.finish_failed().unwrap();
}

#[test]
fn supervisor_input_foreign_lease_cannot_read_existing_file() {
    let area = TestArea::new();
    let vm = Vm::new(DenyHost);
    let lifecycle = BuildLifecycle::new(vm.stop_handle());
    let foreign = BuildLifecycle::new(vm.stop_handle());
    let lease = foreign.start_root(WorkKind::Evaluation, "foreign reference read").unwrap();
    let path = area.0.join("input.json");
    fs::write(&path, b"[]").unwrap();
    assert!(matches!(
        read_supervisor_input(&lifecycle, &lease, &path, 2),
        Err(HostIoError::Lifecycle { .. })
    ));
    lease.complete().unwrap();
}
