use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, SystemTime};

use isabelle_rs::ml::host::files::{
    DiagnosticChannel, EffectSet, EnvironmentUse, FileHostBridge, HostIoError, HostRoots,
    PhaseEffects, RestrictedHost,
};
use isabelle_rs::ml::host::lifecycle::{BuildLifecycle, RuntimePhase, WorkKind};
use isabelle_rs::ml::{DenyHost, Vm};

static NEXT_AREA: AtomicU64 = AtomicU64::new(0);

struct TestArea(PathBuf);

impl TestArea {
    fn new() -> Self {
        let id = NEXT_AREA.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("native-bootstrap-host-{}-{id}", std::process::id()));
        fs::create_dir(&path).unwrap();
        fs::create_dir(path.join("source")).unwrap();
        fs::create_dir(path.join("staging")).unwrap();
        Self(path)
    }

    fn create_bridge(&self) -> (Vm, BuildLifecycle, Arc<FileHostBridge>) {
        self.create_bridge_with(
            EffectSet { read_source: true, ..EffectSet::default() },
            BTreeMap::new(),
        )
    }

    fn create_bridge_with(
        &self,
        grant: EffectSet,
        environment: BTreeMap<EnvironmentUse, Option<String>>,
    ) -> (Vm, BuildLifecycle, Arc<FileHostBridge>) {
        self.create_bridge_with_policy(
            grant.clone(),
            grant.clone(),
            PhaseEffects { active: grant.clone(), draining: grant },
            environment,
        )
    }

    fn create_bridge_with_policy(
        &self,
        caller: EffectSet,
        manifest: EffectSet,
        phases: PhaseEffects,
        environment: BTreeMap<EnvironmentUse, Option<String>>,
    ) -> (Vm, BuildLifecycle, Arc<FileHostBridge>) {
        let vm = Vm::new(DenyHost);
        let lifecycle = BuildLifecycle::new(vm.stop_handle());
        let lease = lifecycle.start_root(WorkKind::Evaluation, "native bootstrap test").unwrap();
        let host = RestrictedHost::new(
            lifecycle.clone(),
            &lease,
            HostRoots {
                source: self.0.join("source"),
                resources: BTreeMap::new(),
                staging_parent: self.0.join("staging"),
                staging_name: "private".into(),
            },
            caller,
            manifest,
            phases,
            environment,
        )
        .unwrap();
        (vm, lifecycle, Arc::new(FileHostBridge::new(host, lease)))
    }
}

impl Drop for TestArea {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn bootstrap_host_missing_file_preserves_lease_and_next_read_bytes() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = area.create_bridge();
    fs::write(area.0.join("source/source.ML"), b"val x = 1;\r\n").unwrap();
    bridge.check_vm(&vm).unwrap();
    assert!(bridge.read_source_bytes(Path::new("missing.ML")).unwrap_err().is_ordinary_ml_io());
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Active);
    assert_eq!(bridge.read_source_bytes(Path::new("source.ML")).unwrap(), b"val x = 1;\r\n");
    bridge.complete().unwrap();
}

#[test]
fn bootstrap_host_foreign_vm_revokes_both_domains_before_read() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = area.create_bridge();
    let mut foreign = Vm::new(DenyHost);
    let foreign_lifecycle = BuildLifecycle::new(foreign.stop_handle());
    let foreign_lease =
        foreign_lifecycle.start_root(WorkKind::Evaluation, "foreign caller").unwrap();
    assert!(matches!(bridge.check_vm(&foreign), Err(HostIoError::Permission { .. })));
    assert!(vm.check_stop().is_err());
    assert!(foreign.check_stop().is_err());
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    assert_eq!(foreign_lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    assert!(foreign_lifecycle.start_root(WorkKind::Evaluation, "retry").is_err());
    let error = foreign
        .evaluate("foreign-retry.sml", "val escaped = (1 handle _ => 2);")
        .expect_err("ML handlers cannot clear cross-runtime revocation");
    assert_eq!(error.kind, isabelle_rs::ml::MlErrorKind::Stopped);
    assert!(bridge.read_source_bytes(Path::new("source.ML")).is_err());
    assert!(bridge.complete().is_err());
    lifecycle.finish_failed().unwrap();
    assert!(foreign_lease.complete().is_err());
    foreign_lifecycle.finish_failed().unwrap();
}

#[test]
fn bootstrap_host_completed_lease_cannot_read_again() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = area.create_bridge();
    bridge.complete().unwrap();
    assert!(matches!(
        bridge.read_source_bytes(Path::new("source.ML")),
        Err(HostIoError::LeaseCompleted)
    ));
    assert!(vm.check_stop().is_err());
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    lifecycle.finish_failed().unwrap();
}

#[test]
fn bootstrap_host_environment_without_capability_revokes_access() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = area.create_bridge();
    assert!(matches!(
        bridge.read_environment("ML_SYSTEM", "ML bootstrap environment"),
        Err(HostIoError::Permission { .. })
    ));
    assert!(vm.check_stop().is_err());
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    assert!(bridge.complete().is_err());
    lifecycle.finish_failed().unwrap();
}

#[test]
fn bootstrap_host_stream_blocks_close_until_explicit_completion() {
    let area = TestArea::new();
    let (_vm, lifecycle, bridge) = area.create_bridge();
    fs::write(area.0.join("source/source.ML"), b"val x = 1;\n").unwrap();
    let (bytes, stream) = bridge.open_source_stream(Path::new("source.ML")).unwrap();
    assert_eq!(bytes, b"val x = 1;\n");
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Stream), 1);
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    assert!(lifecycle.try_close().is_err());
    stream.complete().unwrap();
    lifecycle.try_close().unwrap();
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Closed);
}

#[test]
fn bootstrap_host_explicit_absence_and_empty_value_remain_distinct() {
    let area = TestArea::new();
    let absent = EnvironmentUse {
        key: "ISABELLE_ML_DEBUGGER".into(),
        purpose: "ML bootstrap environment".into(),
    };
    let empty = EnvironmentUse { key: "ML_OPTIONS".into(), purpose: absent.purpose.clone() };
    let grants =
        EffectSet { environment: [absent.clone(), empty.clone()].into(), ..EffectSet::default() };
    let (_vm, lifecycle, bridge) = area.create_bridge_with(
        grants,
        [(absent.clone(), None), (empty.clone(), Some(String::new()))].into(),
    );
    assert_eq!(bridge.read_environment(&absent.key, &absent.purpose).unwrap(), None);
    assert_eq!(bridge.read_environment(&empty.key, &empty.purpose).unwrap(), Some(String::new()));
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Active);
    bridge.complete().unwrap();
}

#[test]
fn bootstrap_host_missing_snapshot_entry_revokes_instead_of_returning_absent() {
    let area = TestArea::new();
    let usage = EnvironmentUse {
        key: "ISABELLE_ML_DEBUGGER".into(),
        purpose: "ML bootstrap environment".into(),
    };
    let grants = EffectSet { environment: [usage.clone()].into(), ..EffectSet::default() };
    let (vm, lifecycle, bridge) = area.create_bridge_with(grants, BTreeMap::new());
    assert!(matches!(
        bridge.read_environment(&usage.key, &usage.purpose),
        Err(HostIoError::Permission { .. })
    ));
    assert!(vm.check_stop().is_err());
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    assert!(bridge.complete().is_err());
    lifecycle.finish_failed().unwrap();
}

#[test]
fn bootstrap_host_diagnostics_preserve_bytes_channels_and_order() {
    let area = TestArea::new();
    let grants = EffectSet { write_staging: true, ..EffectSet::default() };
    let (_vm, lifecycle, bridge) = area.create_bridge_with(grants, BTreeMap::new());
    bridge.write_output(DiagnosticChannel::Stdout, b"\0out\xff").unwrap();
    bridge.write_output(DiagnosticChannel::Stderr, b"error\n").unwrap();
    bridge.write_output(DiagnosticChannel::Stdout, b"next").unwrap();
    let output = area.0.join("staging/private/diagnostics");
    assert_eq!(fs::read(output.join("0.stdout")).unwrap(), b"\0out\xff");
    assert_eq!(fs::read(output.join("1.stderr")).unwrap(), b"error\n");
    assert_eq!(fs::read(output.join("2.stdout")).unwrap(), b"next");
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
}

#[test]
fn bootstrap_host_diagnostics_without_permission_create_no_output() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = area.create_bridge();
    assert!(matches!(
        bridge.write_output(DiagnosticChannel::Stdout, b"denied"),
        Err(HostIoError::Permission { .. })
    ));
    assert!(!area.0.join("staging/private/diagnostics").exists());
    assert!(vm.check_stop().is_err());
    assert!(bridge.complete().is_err());
    lifecycle.finish_failed().unwrap();
}

#[test]
fn bootstrap_host_diagnostics_cancelled_before_write_create_no_output() {
    let area = TestArea::new();
    let grants = EffectSet { write_staging: true, ..EffectSet::default() };
    let (vm, lifecycle, bridge) = area.create_bridge_with(grants, BTreeMap::new());
    vm.request_stop();
    assert!(bridge.write_output(DiagnosticChannel::Stderr, b"cancelled").is_err());
    assert!(!area.0.join("staging/private/diagnostics").exists());
    assert!(bridge.complete().is_err());
    lifecycle.finish_failed().unwrap();
}

#[test]
fn bootstrap_clock_missing_permission_in_any_layer_revokes_build() {
    for missing in 0..3 {
        let area = TestArea::new();
        let mut layers = [EffectSet::default(), EffectSet::default(), EffectSet::default()];
        for layer in &mut layers {
            layer.read_clock = true;
        }
        layers[missing].read_clock = false;
        let [caller, manifest, active] = layers;
        let (vm, lifecycle, bridge) = area.create_bridge_with_policy(
            caller,
            manifest,
            PhaseEffects { active, draining: EffectSet::default() },
            BTreeMap::new(),
        );
        assert!(matches!(bridge.read_clock(&vm), Err(HostIoError::Permission { .. })));
        assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
        assert!(bridge.complete().is_err());
        lifecycle.finish_failed().unwrap();
    }
}

#[test]
fn bootstrap_sleep_zero_without_each_permission_revokes_build() {
    for missing in 0..3 {
        let area = TestArea::new();
        let mut layers = [EffectSet::default(), EffectSet::default(), EffectSet::default()];
        for layer in &mut layers {
            layer.sleep = true;
        }
        layers[missing].sleep = false;
        let [caller, manifest, active] = layers;
        let (vm, lifecycle, bridge) = area.create_bridge_with_policy(
            caller,
            manifest,
            PhaseEffects { active, draining: EffectSet::default() },
            BTreeMap::new(),
        );
        assert!(matches!(bridge.sleep(&vm, Duration::ZERO), Err(HostIoError::Permission { .. })));
        assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
        assert!(bridge.complete().is_err());
        lifecycle.finish_failed().unwrap();
    }
}

#[test]
fn bootstrap_clock_authorized_returns_wall_time_and_closes_lease() {
    let area = TestArea::new();
    let grant = EffectSet { read_clock: true, sleep: true, ..EffectSet::default() };
    let (vm, lifecycle, bridge) = area.create_bridge_with(grant, BTreeMap::new());
    let before = SystemTime::now();
    let observed = bridge.read_clock(&vm).unwrap();
    let after = SystemTime::now();
    assert!(observed >= before.min(after) && observed <= before.max(after));
    bridge.sleep(&vm, Duration::ZERO).unwrap();
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
}

#[test]
fn bootstrap_sleep_nonzero_waits_at_least_requested_duration() {
    let area = TestArea::new();
    let grant = EffectSet { sleep: true, ..EffectSet::default() };
    let (vm, lifecycle, bridge) = area.create_bridge_with(grant, BTreeMap::new());
    let requested = Duration::from_millis(2);
    let started = std::time::Instant::now();
    bridge.sleep(&vm, requested).unwrap();
    assert!(started.elapsed() >= requested);
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
}

#[test]
fn bootstrap_clock_draining_without_permission_rejects() {
    let area = TestArea::new();
    let grant = EffectSet { read_clock: true, ..EffectSet::default() };
    let (vm, lifecycle, bridge) = area.create_bridge_with_policy(
        grant.clone(),
        grant.clone(),
        PhaseEffects { active: grant, draining: EffectSet::default() },
        BTreeMap::new(),
    );
    lifecycle.begin_draining().unwrap();
    assert!(matches!(bridge.read_clock(&vm), Err(HostIoError::Permission { .. })));
    assert!(bridge.complete().is_err());
    lifecycle.finish_failed().unwrap();
}

#[test]
fn bootstrap_clock_foreign_vm_revokes_both_domains() {
    let area = TestArea::new();
    let grant = EffectSet { read_clock: true, ..EffectSet::default() };
    let (vm, lifecycle, bridge) = area.create_bridge_with(grant, BTreeMap::new());
    let foreign = Vm::new(DenyHost);
    assert!(matches!(bridge.read_clock(&foreign), Err(HostIoError::Permission { .. })));
    assert!(vm.check_stop().is_err());
    assert!(foreign.check_stop().is_err());
    assert!(bridge.complete().is_err());
    lifecycle.finish_failed().unwrap();
}

#[test]
fn bootstrap_sleep_long_duration_observes_external_stop_and_releases_work() {
    let (started, ready) = std::sync::mpsc::channel();
    let (finished, result) = std::sync::mpsc::channel();
    let worker = std::thread::spawn(move || {
        let area = TestArea::new();
        let grant = EffectSet { sleep: true, ..EffectSet::default() };
        let (vm, lifecycle, bridge) = area.create_bridge_with(grant, BTreeMap::new());
        started.send(vm.stop_handle()).unwrap();
        let outcome = bridge.sleep(&vm, Duration::MAX);
        assert!(bridge.complete().is_err());
        lifecycle.finish_failed().unwrap();
        finished.send(outcome).unwrap();
    });
    let stop = ready.recv_timeout(Duration::from_secs(5)).unwrap();
    stop.request_stop();
    assert!(matches!(
        result.recv_timeout(Duration::from_secs(5)).unwrap(),
        Err(HostIoError::Lifecycle { .. })
    ));
    worker.join().unwrap();
}
