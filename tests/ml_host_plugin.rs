use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use isabelle_rs::ml::host::files::{
    EffectSet, FileHostBridge, HostIoError, HostRoots, PhaseEffects, RestrictedHost,
};
use isabelle_rs::ml::host::lifecycle::{
    BuildLifecycle, LifecycleErrorKind, RuntimePhase, WorkKind,
};
use isabelle_rs::ml::{DenyHost, Vm};

// Independent test roots need unique names when the test runner executes concurrently.
static NEXT_AREA: AtomicU64 = AtomicU64::new(0);
const CONTENT: &[u8] = &[0, 255, 65, 0];

struct Fixture {
    root: PathBuf,
    vm: Vm,
    lifecycle: BuildLifecycle,
    bridge: FileHostBridge,
}

impl Fixture {
    fn create() -> Self {
        let id = NEXT_AREA.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!("ml-plugin-host-{}-{id}", std::process::id()));
        fs::create_dir(&root).unwrap();
        fs::create_dir(root.join("source")).unwrap();
        fs::create_dir(root.join("resource")).unwrap();
        fs::create_dir(root.join("staging")).unwrap();
        fs::set_permissions(root.join("staging"), fs::Permissions::from_mode(0o700)).unwrap();
        fs::write(root.join("source/input"), CONTENT).unwrap();
        fs::write(root.join("source/empty"), []).unwrap();
        fs::write(root.join("resource/input"), CONTENT).unwrap();
        let vm = Vm::new(DenyHost);
        let lifecycle = BuildLifecycle::new(vm.stop_handle());
        let lease = lifecycle.start_root(WorkKind::Evaluation, "plugin host contract").unwrap();
        let roots = HostRoots {
            source: root.join("source"),
            resources: BTreeMap::from([("data".into(), root.join("resource"))]),
            staging_parent: root.join("staging"),
            staging_name: "private".into(),
        };
        let grants = EffectSet {
            read_source: true,
            read_resources: BTreeSet::from(["data".into()]),
            ..EffectSet::default()
        };
        let host = RestrictedHost::new(
            lifecycle.clone(),
            &lease,
            roots,
            grants.clone(),
            grants.clone(),
            PhaseEffects { active: grants.clone(), draining: grants },
            BTreeMap::new(),
        )
        .unwrap();
        Self { root, vm, lifecycle, bridge: FileHostBridge::new(host, lease) }
    }

    fn close(&self) {
        self.bridge.complete().unwrap();
        self.lifecycle.begin_draining().unwrap();
        self.lifecycle.try_close().unwrap();
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.root).unwrap();
    }
}

#[test]
fn plugin_host_exact_read_budgets_preserve_raw_bytes() {
    let fixture = Fixture::create();
    fixture
        .bridge
        .with_plugin_task(&fixture.vm, WorkKind::Callback, "bounded reads", |host, lease| {
            assert_eq!(
                host.read_source_bounded(lease, Path::new("input"), CONTENT.len())?,
                CONTENT
            );
            assert_eq!(
                host.read_resource_bounded(lease, "data", Path::new("input"), CONTENT.len())?,
                CONTENT
            );
            assert_eq!(host.read_source_bounded(lease, Path::new("empty"), 0)?, Vec::<u8>::new());
            Ok(())
        })
        .unwrap();
    fixture.close();
}

#[test]
fn plugin_host_oversized_source_revokes_build_and_releases_child() {
    let fixture = Fixture::create();
    let limit = CONTENT.len() - 1;
    let result = fixture.bridge.with_plugin_task(
        &fixture.vm,
        WorkKind::Callback,
        "oversized source",
        |host, lease| host.read_source_bounded(lease, Path::new("input"), limit),
    );
    assert!(matches!(result, Err(HostIoError::TooLarge { limit: actual, .. }) if actual == limit));
    assert_eq!(fixture.lifecycle.pending_counts().unwrap().count(WorkKind::Callback), 0);
    assert_eq!(fixture.lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    assert!(fixture.bridge.complete().is_err());
    fixture.lifecycle.finish_failed().unwrap();
}

#[test]
fn plugin_host_oversized_resource_revokes_build_and_releases_child() {
    let fixture = Fixture::create();
    let result = fixture.bridge.with_plugin_task(
        &fixture.vm,
        WorkKind::Callback,
        "oversized resource",
        |host, lease| host.read_resource_bounded(lease, "data", Path::new("input"), 0),
    );
    assert!(matches!(result, Err(HostIoError::TooLarge { limit: 0, .. })));
    assert_eq!(fixture.lifecycle.pending_counts().unwrap().count(WorkKind::Callback), 0);
    assert!(fixture.bridge.complete().is_err());
    fixture.lifecycle.finish_failed().unwrap();
}

#[test]
fn plugin_host_missing_file_preserves_live_build_for_next_call() {
    let fixture = Fixture::create();
    let result = fixture.bridge.with_plugin_task(
        &fixture.vm,
        WorkKind::Callback,
        "missing file",
        |host, lease| host.read_resource_bounded(lease, "data", Path::new("absent"), CONTENT.len()),
    );
    assert!(
        matches!(result, Err(HostIoError::Io { ref source, .. }) if source.kind() == std::io::ErrorKind::NotFound)
    );
    assert_eq!(fixture.lifecycle.phase().unwrap(), RuntimePhase::Active);
    let bytes = fixture
        .bridge
        .with_plugin_task(&fixture.vm, WorkKind::Callback, "existing file", |host, lease| {
            host.read_source_bounded(lease, Path::new("input"), CONTENT.len())
        })
        .unwrap();
    assert_eq!(bytes, CONTENT);
    fixture.close();
}

#[test]
fn plugin_host_nested_calls_retain_both_child_leases() {
    let fixture = Fixture::create();
    let bytes = fixture
        .bridge
        .with_plugin_task(&fixture.vm, WorkKind::Callback, "outer", |_, _| {
            fixture.bridge.with_plugin_task(
                &fixture.vm,
                WorkKind::Callback,
                "inner",
                |host, lease| {
                    assert_eq!(
                        fixture.lifecycle.pending_counts().unwrap().count(WorkKind::Callback),
                        2
                    );
                    host.read_source_bounded(lease, Path::new("input"), CONTENT.len())
                },
            )
        })
        .unwrap();
    assert_eq!(bytes, CONTENT);
    fixture.close();
}

#[test]
fn plugin_host_reserved_worker_after_evaluation_drains_real_read() {
    let fixture = Fixture::create();
    let reservation = fixture
        .bridge
        .reserve_plugin_task(&fixture.vm, WorkKind::Callback, "queued file read")
        .unwrap();
    fixture.bridge.complete().unwrap();
    fixture.lifecycle.begin_draining().unwrap();
    assert_eq!(fixture.lifecycle.try_close().unwrap_err().kind, LifecycleErrorKind::PendingWork);
    let bridge = &fixture.bridge;
    let lifecycle = &fixture.lifecycle;
    let bytes = std::thread::scope(|scope| {
        scope
            .spawn(|| {
                bridge.with_reserved_plugin_task(
                    &reservation,
                    WorkKind::Future,
                    "worker file read",
                    |host, lease| {
                        assert_eq!(
                            lifecycle.pending_counts().unwrap().count(WorkKind::Callback),
                            1
                        );
                        assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Future), 1);
                        host.read_source_bounded(lease, Path::new("input"), CONTENT.len())
                    },
                )
            })
            .join()
            .unwrap()
            .unwrap()
    });
    assert_eq!(bytes, CONTENT);
    assert_eq!(fixture.lifecycle.try_close().unwrap_err().kind, LifecycleErrorKind::PendingWork);
    reservation.complete().unwrap();
    fixture.lifecycle.try_close().unwrap();
}

#[test]
fn plugin_host_foreign_reservation_rejects_without_running_callback() {
    let fixture = Fixture::create();
    let foreign = Fixture::create();
    let reservation = foreign
        .bridge
        .reserve_plugin_task(&foreign.vm, WorkKind::Callback, "foreign request")
        .unwrap();
    let result = fixture.bridge.with_reserved_plugin_task(
        &reservation,
        WorkKind::Future,
        "foreign worker",
        |_, _| -> Result<(), HostIoError> { panic!("foreign callback must not run") },
    );
    assert!(matches!(result, Err(HostIoError::Lifecycle { source, .. })
        if source.kind == LifecycleErrorKind::WrongBuild));
    assert_eq!(fixture.lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    assert_eq!(foreign.lifecycle.phase().unwrap(), RuntimePhase::Active);
    assert!(fixture.bridge.complete().is_err());
    fixture.lifecycle.finish_failed().unwrap();
    reservation.complete().unwrap();
    foreign.close();
}

#[test]
fn plugin_host_cancelled_reservation_rejects_without_running_callback() {
    let fixture = Fixture::create();
    let reservation = fixture
        .bridge
        .reserve_plugin_task(&fixture.vm, WorkKind::Callback, "cancelled request")
        .unwrap();
    fixture.vm.request_stop();
    let result = fixture.bridge.with_reserved_plugin_task(
        &reservation,
        WorkKind::Future,
        "cancelled worker",
        |_, _| -> Result<(), HostIoError> { panic!("cancelled callback must not run") },
    );
    assert!(matches!(result, Err(HostIoError::Lifecycle { source, .. })
        if source.kind == LifecycleErrorKind::Cancelled));
    assert!(reservation.complete().is_err());
    assert!(fixture.bridge.complete().is_err());
    fixture.lifecycle.finish_failed().unwrap();
}
