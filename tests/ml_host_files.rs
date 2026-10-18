use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs;
use std::os::unix::fs::{PermissionsExt, symlink};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Barrier};

use isabelle_kernel::{CTerm, ProofContext, RawTerm, Signature, TrustedTheory, Ty};
use isabelle_rs::ml::host::files::{
    EffectSet, EnvironmentUse, FileHostBridge, HostIoError, HostRoots, MAX_FILE_BYTES,
    PhaseEffects, RestrictedHost,
};
use isabelle_rs::ml::host::lifecycle::{
    BuildLifecycle, LifecycleErrorKind, RuntimePhase, TaskLease, WorkKind,
};
use isabelle_rs::ml::host::objects::{ObjectError, ObjectStore};
use isabelle_rs::ml::host::publisher::BuildPublisher;
use isabelle_rs::ml::{DenyHost, MlErrorKind, Type, TypeScheme, Value, Vm};

static NEXT_AREA: AtomicU64 = AtomicU64::new(0);

struct TestArea(PathBuf);

impl TestArea {
    fn new() -> Self {
        let id = NEXT_AREA.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("native-ml-host-files-{}-{id}", std::process::id()));
        fs::create_dir(&path).unwrap();
        fs::create_dir(path.join("source")).unwrap();
        fs::create_dir(path.join("resource")).unwrap();
        fs::create_dir(path.join("staging")).unwrap();
        fs::set_permissions(path.join("staging"), fs::Permissions::from_mode(0o700)).unwrap();
        Self(path)
    }

    fn path(&self, path: &str) -> PathBuf {
        self.0.join(path)
    }

    fn roots(&self, name: &str) -> HostRoots {
        HostRoots {
            source: self.path("source"),
            resources: BTreeMap::from([("components".to_owned(), self.path("resource"))]),
            staging_parent: self.path("staging"),
            staging_name: PathBuf::from(name),
        }
    }
}

impl Drop for TestArea {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn grants() -> EffectSet {
    EffectSet {
        read_source: true,
        read_resources: BTreeSet::from(["components".to_owned()]),
        write_staging: true,
        run_fixed_verit: false,
        read_clock: false,
        sleep: false,
        environment: BTreeSet::from([EnvironmentUse {
            key: "ISABELLE_VERIT".into(),
            purpose: "solver request".into(),
        }]),
    }
}

fn build_host(
    area: &TestArea,
    caller: EffectSet,
    manifest: EffectSet,
    phases: PhaseEffects,
    name: &str,
) -> (Vm, BuildLifecycle, TaskLease, RestrictedHost) {
    let vm = Vm::new(DenyHost);
    let lifecycle = BuildLifecycle::new(vm.stop_handle());
    let lease = lifecycle.start_root(WorkKind::Evaluation, "filesystem test").unwrap();
    let environment = BTreeMap::from([(
        EnvironmentUse { key: "ISABELLE_VERIT".into(), purpose: "solver request".into() },
        Some("approved-snapshot".to_owned()),
    )]);
    let host = RestrictedHost::new(
        lifecycle.clone(),
        &lease,
        area.roots(name),
        caller,
        manifest,
        phases,
        environment,
    )
    .unwrap();
    (vm, lifecycle, lease, host)
}

fn build_bridged_vm(area: &TestArea) -> (Vm, BuildLifecycle, Arc<FileHostBridge>) {
    let mut created = None;
    let vm = Vm::with_host_factory(|stop| -> Result<_, HostIoError> {
        let lifecycle = BuildLifecycle::new(stop);
        let lease = lifecycle.start_root(WorkKind::Evaluation, "bridged VM").unwrap();
        let host = RestrictedHost::new(
            lifecycle.clone(),
            &lease,
            area.roots("build-A"),
            grants(),
            grants(),
            all_phases(),
            BTreeMap::new(),
        )?;
        let bridge = Arc::new(FileHostBridge::new(host, lease));
        created = Some((lifecycle, Arc::clone(&bridge)));
        Ok(bridge)
    })
    .unwrap();
    let (lifecycle, bridge) = created.unwrap();
    (vm, lifecycle, bridge)
}

fn all_phases() -> PhaseEffects {
    PhaseEffects { active: grants(), draining: grants() }
}

fn finish(lifecycle: &BuildLifecycle, lease: TaskLease) {
    lease.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Closed);
}

#[test]
fn files_approved_source_resource_and_staging_preserve_bytes() {
    let area = TestArea::new();
    fs::write(area.path("source/a.ML"), [0, 1, 2, 255]).unwrap();
    fs::write(area.path("resource/data"), "component").unwrap();
    let (_vm, lifecycle, lease, host) =
        build_host(&area, grants(), grants(), all_phases(), "build-A");
    assert_eq!(host.read_source(&lease, Path::new("a.ML")).unwrap(), [0, 1, 2, 255]);
    assert_eq!(
        host.read_resource_text(&lease, "components", Path::new("data")).unwrap(),
        "component"
    );
    assert_eq!(
        host.read_environment(&lease, "ISABELLE_VERIT", "solver request").unwrap(),
        Some("approved-snapshot".to_owned())
    );
    host.write_staging(&lease, Path::new("artifacts/out"), &[0, 10, 255]).unwrap();
    assert_eq!(fs::read(area.path("staging/build-A/artifacts/out")).unwrap(), [0, 10, 255]);
    assert!(!area.path("source/artifacts/out").exists());
    finish(&lifecycle, lease);
}

#[test]
fn files_missing_authorized_source_is_ordinary_io_without_revoking() {
    let area = TestArea::new();
    fs::write(area.path("source/present.ML"), b"valid").unwrap();
    let (vm, lifecycle, lease, host) =
        build_host(&area, grants(), grants(), all_phases(), "ordinary-io");
    let error = host.read_source(&lease, Path::new("missing.ML")).unwrap_err();
    assert!(error.is_ordinary_ml_io());
    assert_eq!(
        error.source().unwrap().downcast_ref::<std::io::Error>().unwrap().kind(),
        std::io::ErrorKind::NotFound
    );
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Active);
    assert!(vm.check_stop().is_ok());
    assert_eq!(host.read_source(&lease, Path::new("present.ML")).unwrap(), b"valid");
    finish(&lifecycle, lease);
}

#[test]
fn files_regular_parent_is_ordinary_io_but_symlink_parent_revokes() {
    let area = TestArea::new();
    fs::write(area.path("source/regular"), b"data").unwrap();
    symlink("regular", area.path("source/alias")).unwrap();
    let (vm, lifecycle, lease, host) =
        build_host(&area, grants(), grants(), all_phases(), "classify-parent");
    let error = host.read_source(&lease, Path::new("regular/child")).unwrap_err();
    assert!(matches!(error, HostIoError::OrdinaryIo { .. }));
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Active);
    assert!(vm.check_stop().is_ok());
    assert!(matches!(
        host.read_source(&lease, Path::new("alias/child")),
        Err(HostIoError::Permission { .. })
    ));
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    lease.complete().unwrap_err();
    lifecycle.finish_failed().unwrap();
}

#[test]
fn files_manifest_and_phase_intersection_revokes_on_denial() {
    let area = TestArea::new();
    fs::write(area.path("source/a.ML"), "safe").unwrap();
    let mut manifest = grants();
    manifest.read_source = false;
    let (vm, lifecycle, lease, host) =
        build_host(&area, grants(), manifest, all_phases(), "build-A");
    assert!(matches!(
        host.read_source(&lease, Path::new("a.ML")),
        Err(HostIoError::Permission { .. })
    ));
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    assert_eq!(vm.check_stop().unwrap_err().kind, MlErrorKind::Stopped);
    assert!(host.read_resource(&lease, "components", Path::new("anything")).is_err());
    lease.complete().unwrap_err();
    lifecycle.finish_failed().unwrap();

    let mut phases = all_phases();
    phases.draining.write_staging = false;
    let (_vm, lifecycle, lease, host) = build_host(&area, grants(), grants(), phases, "build-B");
    lifecycle.begin_draining().unwrap();
    assert!(host.read_source_text(&lease, Path::new("a.ML")).is_ok());
    assert!(matches!(
        host.write_staging(&lease, Path::new("new"), b"denied"),
        Err(HostIoError::Permission { .. })
    ));
    assert!(!area.path("staging/build-B/new").exists());
    lease.complete().unwrap_err();
    lifecycle.finish_failed().unwrap();
}

#[test]
fn files_foreign_lease_and_cancelled_build_never_authorize() {
    let area = TestArea::new();
    fs::write(area.path("source/a.ML"), "safe").unwrap();
    let (_vm, lifecycle, lease, host) =
        build_host(&area, grants(), grants(), all_phases(), "build-A");
    let foreign_vm = Vm::new(DenyHost);
    let foreign_lifecycle = BuildLifecycle::new(foreign_vm.stop_handle());
    let foreign_lease = foreign_lifecycle.start_root(WorkKind::Future, "foreign").unwrap();
    let error = host.read_source(&foreign_lease, Path::new("a.ML")).unwrap_err();
    assert!(
        matches!(error, HostIoError::Lifecycle { source, .. } if source.kind == LifecycleErrorKind::WrongBuild)
    );
    assert!(foreign_lifecycle.check_task(&foreign_lease).is_ok());
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    assert!(
        matches!(host.read_source(&lease, Path::new("a.ML")), Err(HostIoError::Lifecycle { source, .. }) if source.kind == LifecycleErrorKind::Cancelled)
    );
    assert_eq!(lease.complete().unwrap_err().kind, LifecycleErrorKind::Cancelled);
    lifecycle.finish_failed().unwrap();
    finish(&foreign_lifecycle, foreign_lease);
}

#[test]
fn files_symlink_parent_leaf_fifo_and_absolute_path_are_rejected() {
    let area = TestArea::new();
    fs::write(area.path("source/real"), b"inside").unwrap();
    fs::create_dir(area.path("source/sub")).unwrap();
    symlink("real", area.path("source/linked")).unwrap();
    symlink("sub", area.path("source/alias")).unwrap();
    let fifo = area.path("source/pipe");
    assert!(Command::new("mkfifo").arg(&fifo).status().unwrap().success());
    for (index, path) in
        ["linked", "alias/real", "pipe", "../resource/x", "/etc/passwd"].iter().enumerate()
    {
        let (_vm, lifecycle, lease, host) =
            build_host(&area, grants(), grants(), all_phases(), &format!("build-{index}"));
        let error = host.read_source(&lease, Path::new(path)).unwrap_err();
        assert!(matches!(
            error,
            HostIoError::Io { .. } | HostIoError::Permission { .. } | HostIoError::InvalidPath(_)
        ));
        lease.complete().unwrap_err();
        lifecycle.finish_failed().unwrap();
    }
}

#[test]
fn files_staging_is_unique_create_only_and_private() {
    let area = TestArea::new();
    let (_vm, lifecycle, lease, host) =
        build_host(&area, grants(), grants(), all_phases(), "build-A");
    host.write_staging(&lease, Path::new("saved"), b"first").unwrap();
    let vm_b = Vm::new(DenyHost);
    let lifecycle_b = BuildLifecycle::new(vm_b.stop_handle());
    let lease_b = lifecycle_b.start_root(WorkKind::Evaluation, "build B").unwrap();
    assert!(
        RestrictedHost::new(
            lifecycle_b.clone(),
            &lease_b,
            area.roots("build-A"),
            grants(),
            grants(),
            all_phases(),
            BTreeMap::new(),
        )
        .is_err()
    );
    assert_eq!(fs::read(area.path("staging/build-A/saved")).unwrap(), b"first");
    assert!(host.write_staging(&lease, Path::new("saved"), b"second").is_err());
    assert_eq!(fs::read(area.path("staging/build-A/saved")).unwrap(), b"first");
    host.write_staging(&lease, Path::new("new"), b"third").unwrap();
    assert_eq!(fs::read(area.path("staging/build-A/new")).unwrap(), b"third");
    let (_vm_c, lifecycle_c, lease_c, host_c) =
        build_host(&area, grants(), grants(), all_phases(), "build-C");
    host_c.write_staging(&lease_c, Path::new("saved"), b"independent").unwrap();
    assert_eq!(fs::read(area.path("staging/build-A/saved")).unwrap(), b"first");
    assert_eq!(fs::read(area.path("staging/build-C/saved")).unwrap(), b"independent");
    finish(&lifecycle_c, lease_c);
    finish(&lifecycle, lease);
    lease_b.complete().unwrap_err();
    lifecycle_b.finish_failed().unwrap();
}

#[test]
fn files_bridge_vm_effect_reads_text_and_denial_revokes_lease() {
    let area = TestArea::new();
    fs::write(area.path("source/a.ML"), "val answer = 42;").unwrap();
    let (mut vm, lifecycle, bridge) = build_bridged_vm(&area);
    vm.register_host_effect(
        "File.read",
        TypeScheme::mono(Type::Function(
            Box::new(Type::Constructor("string".into(), vec![])),
            Box::new(Type::Constructor("string".into(), vec![])),
        )),
        "filesystem.read_source",
    )
    .unwrap();
    vm.evaluate("entry.sml", "val source = File.read \"a.ML\";").unwrap();
    assert_eq!(vm.lookup_value("source").unwrap().unwrap().as_text(), Some("val answer = 42;"));
    assert!(
        vm.call_host(
            "filesystem.write_staging",
            &[Value::text("result.txt"), Value::text("saved by VM"),]
        )
        .unwrap()
        .is_unit()
    );
    assert_eq!(fs::read(area.path("staging/build-A/result.txt")).unwrap(), b"saved by VM");
    let error = vm.call_host("OS.Process.system", &[Value::text("true")]).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::HostPermission);
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    assert_eq!(
        vm.evaluate("after-denial.sml", "val answer = 42;").unwrap_err().kind,
        MlErrorKind::Stopped
    );
    assert_eq!(
        vm.call_host(
            "filesystem.write_staging",
            &[Value::text("after-denial"), Value::text("forbidden"),]
        )
        .unwrap_err()
        .kind,
        MlErrorKind::Stopped
    );
    assert!(!area.path("staging/build-A/after-denial").exists());
    assert!(bridge.complete().is_err());
    lifecycle.finish_failed().unwrap();
}

#[test]
fn files_legacy_host_bridge_missing_file_still_fails_closed() {
    let area = TestArea::new();
    let (mut vm, lifecycle, bridge) = build_bridged_vm(&area);
    let error = vm.call_host("filesystem.read_source", &[Value::text("missing.ML")]).unwrap_err();
    assert_eq!(error.kind, MlErrorKind::HostFailure);
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    assert_eq!(vm.check_stop().unwrap_err().kind, MlErrorKind::Stopped);
    bridge.complete().unwrap_err();
    lifecycle.finish_failed().unwrap();
}

#[test]
fn files_bridge_external_cancellation_stops_same_vm_before_effect() {
    let area = TestArea::new();
    let (mut vm, lifecycle, bridge) = build_bridged_vm(&area);
    lifecycle.cancel("supervisor cancellation".to_owned()).unwrap();
    let error = vm.evaluate("after-cancel.sml", "val answer = 42;").unwrap_err();
    assert_eq!(error.kind, MlErrorKind::Stopped);
    assert_eq!(
        vm.call_host(
            "filesystem.write_staging",
            &[Value::text("after-cancel"), Value::text("forbidden"),]
        )
        .unwrap_err()
        .kind,
        MlErrorKind::Stopped
    );
    assert!(!area.path("staging/build-A/after-cancel").exists());
    assert!(bridge.complete().is_err());
    lifecycle.finish_failed().unwrap();
}

#[test]
fn files_bridge_success_closes_same_vm_before_publication() {
    let area = TestArea::new();
    let (mut vm, lifecycle, bridge) = build_bridged_vm(&area);
    vm.evaluate("entry.sml", "val answer = 42;").unwrap();
    assert_eq!(vm.lookup_value("answer").unwrap().and_then(Value::as_int), Some(42));
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
    assert_eq!(
        vm.evaluate("after-close.sml", "val answer = 43;").unwrap_err().kind,
        MlErrorKind::Stopped
    );
    assert_eq!(
        vm.call_host(
            "filesystem.write_staging",
            &[Value::text("after-close"), Value::text("forbidden"),]
        )
        .unwrap_err()
        .kind,
        MlErrorKind::Stopped
    );
    assert!(!area.path("staging/build-A/after-close").exists());
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Closed);
}

#[test]
fn files_utf8_failure_preserves_decoder_cause_and_revokes() {
    let area = TestArea::new();
    fs::write(area.path("source/invalid"), [0xff]).unwrap();
    let (_vm, lifecycle, lease, host) =
        build_host(&area, grants(), grants(), all_phases(), "build-A");
    let error = host.read_source_text(&lease, Path::new("invalid")).unwrap_err();
    assert!(matches!(&error, HostIoError::Utf8 { .. }));
    assert!(error.source().is_some());
    lease.complete().unwrap_err();
    lifecycle.finish_failed().unwrap();
}

#[test]
fn files_source_above_limit_is_rejected_without_unbounded_read() {
    let area = TestArea::new();
    fs::File::create(area.path("source/huge"))
        .unwrap()
        .set_len((MAX_FILE_BYTES as u64) + 1)
        .unwrap();
    let (_vm, lifecycle, lease, host) =
        build_host(&area, grants(), grants(), all_phases(), "build-A");
    assert!(matches!(
        host.read_source(&lease, Path::new("huge")),
        Err(HostIoError::TooLarge { .. })
    ));
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    lease.complete().unwrap_err();
    lifecycle.finish_failed().unwrap();
}

#[test]
fn files_oversize_relative_paths_reject_without_creating_parents() {
    let area = TestArea::new();
    let paths = [
        format!("first/{}", "x".repeat(256)),
        format!("first/{}", vec!["x"; 64].join("/")),
        format!("first/{}", vec!["x".repeat(140); 30].join("/")),
    ];
    for (index, path) in paths.iter().enumerate() {
        let (_vm, lifecycle, lease, host) =
            build_host(&area, grants(), grants(), all_phases(), &format!("write-{index}"));
        assert!(matches!(
            host.write_staging(&lease, Path::new(path), b""),
            Err(HostIoError::PathLimit { .. })
        ));
        assert!(!area.path(&format!("staging/write-{index}/first")).exists());
        assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
        lease.complete().unwrap_err();
        lifecycle.finish_failed().unwrap();

        let (_vm, lifecycle, lease, host) =
            build_host(&area, grants(), grants(), all_phases(), &format!("read-{index}"));
        assert!(matches!(
            host.read_source(&lease, Path::new(path)),
            Err(HostIoError::PathLimit { .. })
        ));
        assert!(!area.path("source/first").exists());
        lease.complete().unwrap_err();
        lifecycle.finish_failed().unwrap();
    }
}

#[test]
fn files_oversize_staging_root_rejects_before_creating_parent() {
    let area = TestArea::new();
    let vm = Vm::new(DenyHost);
    let lifecycle = BuildLifecycle::new(vm.stop_handle());
    let lease = lifecycle.start_root(WorkKind::Evaluation, "oversize staging name").unwrap();
    let roots = area.roots(&format!("nested/{}", "x".repeat(256)));
    let error = RestrictedHost::new(
        lifecycle.clone(),
        &lease,
        roots,
        grants(),
        grants(),
        all_phases(),
        BTreeMap::new(),
    )
    .err()
    .unwrap();
    assert!(matches!(error, HostIoError::PathLimit { .. }));
    assert!(!area.path("staging/nested").exists());
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    lease.complete().unwrap_err();
    lifecycle.finish_failed().unwrap();
}

#[test]
fn files_environment_home_and_unapproved_purpose_are_denied() {
    let area = TestArea::new();
    for (index, (key, purpose)) in
        [("HOME", "solver request"), ("ISABELLE_VERIT", "unapproved")].iter().enumerate()
    {
        let (_vm, lifecycle, lease, host) =
            build_host(&area, grants(), grants(), all_phases(), &format!("build-{index}"));
        assert!(matches!(
            host.read_environment(&lease, key, purpose),
            Err(HostIoError::Permission { .. })
        ));
        assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
        lease.complete().unwrap_err();
        lifecycle.finish_failed().unwrap();
    }
}

#[test]
fn files_symlink_in_approved_root_is_rejected_before_staging_creation() {
    let area = TestArea::new();
    symlink(area.path("source"), area.path("linked-source")).unwrap();
    let vm = Vm::new(DenyHost);
    let lifecycle = BuildLifecycle::new(vm.stop_handle());
    let lease = lifecycle.start_root(WorkKind::Evaluation, "linked root").unwrap();
    let mut roots = area.roots("build-A");
    roots.source = area.path("linked-source");
    let error = RestrictedHost::new(
        lifecycle.clone(),
        &lease,
        roots,
        grants(),
        grants(),
        all_phases(),
        BTreeMap::new(),
    )
    .err()
    .unwrap();
    assert!(matches!(error, HostIoError::Permission { .. }));
    assert!(!area.path("staging/build-A").exists());
    lease.complete().unwrap_err();
    lifecycle.finish_failed().unwrap();
}

#[test]
fn solver_default_and_missing_intersection_grants_revoke_without_process() {
    let area = TestArea::new();
    for denied in 0..4 {
        let mut caller = grants();
        let mut manifest = grants();
        let mut phases = all_phases();
        if denied != 0 {
            caller.run_fixed_verit = true;
            manifest.run_fixed_verit = true;
            phases.active.run_fixed_verit = true;
            match denied {
                1 => caller.run_fixed_verit = false,
                2 => manifest.run_fixed_verit = false,
                _ => phases.active.run_fixed_verit = false,
            }
        }
        let (_vm, lifecycle, lease, host) =
            build_host(&area, caller, manifest, phases, &format!("denied-{denied}"));
        assert!(matches!(host.authorize_fixed_solver(&lease), Err(HostIoError::Permission { .. })));
        assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Process), 0);
        assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
        lease.complete().unwrap_err();
        lifecycle.finish_failed().unwrap();
    }
}

#[test]
fn solver_three_grants_require_live_same_build_child() {
    let area = TestArea::new();
    let mut grants = grants();
    grants.run_fixed_verit = true;
    let phases = PhaseEffects { active: grants.clone(), draining: EffectSet::default() };
    let (_vm, lifecycle, lease, host) =
        build_host(&area, grants.clone(), grants, phases, "allowed");
    host.authorize_fixed_solver(&lease).unwrap();
    let process = lease.start_child(WorkKind::Process, "no actual process").unwrap();
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Process), 1);
    lifecycle.begin_draining().unwrap();
    assert!(matches!(host.authorize_fixed_solver(&process), Err(HostIoError::Permission { .. })));
    process.complete().unwrap_err();
    lease.complete().unwrap_err();
    lifecycle.finish_failed().unwrap();
}

#[test]
fn solver_registered_child_during_draining_obeys_same_capability_intersection() {
    let area = TestArea::new();
    let mut grants = grants();
    grants.run_fixed_verit = true;
    let phases = PhaseEffects { active: grants.clone(), draining: grants.clone() };
    let (_vm, lifecycle, lease, host) =
        build_host(&area, grants.clone(), grants, phases, "draining-grant");
    lifecycle.begin_draining().unwrap();
    host.authorize_fixed_solver(&lease).unwrap();
    let process = lease.start_child(WorkKind::Process, "pure lease accounting").unwrap();
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Process), 1);
    assert_eq!(lifecycle.try_close().unwrap_err().kind, LifecycleErrorKind::PendingWork);
    process.complete().unwrap();
    lease.complete().unwrap();
    lifecycle.try_close().unwrap();
}

#[test]
fn publisher_closed_report_renames_private_staging_without_overwriting() {
    let area = TestArea::new();
    let (_vm, lifecycle, lease, host) =
        build_host(&area, grants(), grants(), all_phases(), "private-build");
    let output_dir = area.path("staging/final-build");
    let mut publisher = BuildPublisher::new(&host, &lease, &output_dir).unwrap();
    assert!(publisher.matches_lifecycle(&lifecycle));
    assert!(publisher.validates_output_dir(&output_dir));
    assert!(!publisher.validates_output_dir(&area.path("staging/other")));
    lease.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
    publisher.write_report(b"frozen report").unwrap();
    publisher.commit().unwrap();
    assert_eq!(fs::read(output_dir.join("report.json")).unwrap(), b"frozen report");
    assert!(!area.path("staging/private-build").exists());
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Succeeded);
    assert_eq!(lifecycle.cancel("late".into()).unwrap_err().kind, LifecycleErrorKind::InvalidPhase);

    for target in ["directory", "symlink"] {
        let (_vm, lifecycle, lease, host) =
            build_host(&area, grants(), grants(), all_phases(), &format!("private-{target}"));
        let output = area.path(&format!("staging/existing-{target}"));
        let mut publisher = BuildPublisher::new(&host, &lease, &output).unwrap();
        if target == "directory" {
            fs::create_dir(&output).unwrap();
            fs::write(output.join("keep"), b"unchanged").unwrap();
        } else {
            symlink(&output_dir, &output).unwrap();
        }
        lease.complete().unwrap();
        lifecycle.begin_draining().unwrap();
        lifecycle.try_close().unwrap();
        publisher.write_report(b"rejected").unwrap();
        let error = publisher.commit().unwrap_err();
        assert_eq!(error.kind, LifecycleErrorKind::Cancelled);
        assert_eq!(
            error
                .source()
                .unwrap()
                .source()
                .unwrap()
                .downcast_ref::<std::io::Error>()
                .unwrap()
                .kind(),
            std::io::ErrorKind::AlreadyExists
        );
        assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
        lifecycle.finish_failed().unwrap();
        if target == "directory" {
            assert_eq!(fs::read(output.join("keep")).unwrap(), b"unchanged");
        } else {
            assert_eq!(fs::read_link(output).unwrap(), output_dir);
        }
    }
}

#[test]
fn publisher_rejects_foreign_build_path_and_cancellation_before_commit() {
    let area = TestArea::new();
    let (_vm, lifecycle, lease, host) =
        build_host(&area, grants(), grants(), all_phases(), "private-build");
    for path in [
        area.path("source/out"),
        area.path("staging/private-build"),
        area.path("staging/nested/out"),
    ] {
        assert!(BuildPublisher::new(&host, &lease, &path).is_err());
    }
    let other_vm = Vm::new(DenyHost);
    let other = BuildLifecycle::new(other_vm.stop_handle());
    let foreign_lease = other.start_root(WorkKind::Evaluation, "foreign").unwrap();
    assert!(BuildPublisher::new(&host, &foreign_lease, &area.path("staging/out")).is_err());
    foreign_lease.complete().unwrap();
    other.begin_draining().unwrap();
    other.try_close().unwrap();
    let output_dir = area.path("staging/final");
    let mut publisher = BuildPublisher::new(&host, &lease, &output_dir).unwrap();
    lease.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
    publisher.write_report(b"frozen").unwrap();
    lifecycle.cancel("cancel before commit".into()).unwrap();
    assert_eq!(publisher.commit().unwrap_err().kind, LifecycleErrorKind::Cancelled);
    assert!(!output_dir.exists());
    lifecycle.finish_failed().unwrap();
}

#[test]
fn publisher_existing_target_and_early_report_are_rejected() {
    let area = TestArea::new();
    let output = area.path("staging/final");
    fs::write(&output, b"existing").unwrap();
    let (_vm, lifecycle, lease, host) =
        build_host(&area, grants(), grants(), all_phases(), "private-build");
    assert!(matches!(
        BuildPublisher::new(&host, &lease, &output),
        Err(HostIoError::Permission { .. })
    ));
    assert_eq!(fs::read(&output).unwrap(), b"existing");
    fs::remove_file(&output).unwrap();
    let mut publisher = BuildPublisher::new(&host, &lease, &output).unwrap();
    assert!(matches!(publisher.write_report(b"too early"), Err(HostIoError::Permission { .. })));
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    lease.complete().unwrap_err();
    assert_eq!(publisher.commit().unwrap_err().kind, LifecycleErrorKind::Cancelled);
    assert!(!output.exists());
    lifecycle.finish_failed().unwrap();
}

#[test]
fn publisher_commit_without_report_preserves_failed_state() {
    let area = TestArea::new();
    let (_vm, lifecycle, lease, host) =
        build_host(&area, grants(), grants(), all_phases(), "unprepared-build");
    let unprepared = area.path("staging/unprepared-final");
    let publisher = BuildPublisher::new(&host, &lease, &unprepared).unwrap();
    lease.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
    let error = publisher.commit().unwrap_err();
    assert_eq!(error.kind, LifecycleErrorKind::Cancelled);
    assert_eq!(
        error
            .source()
            .unwrap()
            .downcast_ref::<isabelle_rs::ml::host::lifecycle::LifecycleError>()
            .unwrap()
            .kind,
        LifecycleErrorKind::PublicationFailed
    );
    assert!(!unprepared.exists());
    lifecycle.finish_failed().unwrap();
}

#[test]
fn publisher_nonprivate_parent_is_rejected() {
    let area = TestArea::new();
    let (_vm, lifecycle, lease, host) =
        build_host(&area, grants(), grants(), all_phases(), "private-other");
    fs::set_permissions(area.path("staging"), fs::Permissions::from_mode(0o755)).unwrap();
    assert!(matches!(
        BuildPublisher::new(&host, &lease, &area.path("staging/other")),
        Err(HostIoError::Permission { .. })
    ));
    lease.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
}

#[test]
fn publisher_cancel_commit_race_has_one_filesystem_and_state_winner() {
    for attempt in 0..16 {
        let area = TestArea::new();
        let (_vm, lifecycle, lease, host) =
            build_host(&area, grants(), grants(), all_phases(), "private-build");
        let output_dir = area.path("staging/final");
        let mut publisher = BuildPublisher::new(&host, &lease, &output_dir).unwrap();
        lease.complete().unwrap();
        lifecycle.begin_draining().unwrap();
        lifecycle.try_close().unwrap();
        publisher.write_report(b"race report").unwrap();
        let barrier = Arc::new(Barrier::new(3));
        let publishing_barrier = Arc::clone(&barrier);
        let publishing = std::thread::spawn(move || {
            publishing_barrier.wait();
            publisher.commit()
        });
        let cancelling_barrier = Arc::clone(&barrier);
        let cancelling_lifecycle = lifecycle.clone();
        let cancelling = std::thread::spawn(move || {
            cancelling_barrier.wait();
            cancelling_lifecycle.cancel(format!("cancel race {attempt}"))
        });
        barrier.wait();
        match (publishing.join().unwrap(), cancelling.join().unwrap()) {
            (Ok(()), Err(_)) => {
                assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Succeeded);
                assert_eq!(fs::read(output_dir.join("report.json")).unwrap(), b"race report");
            },
            (Err(error), Ok(())) => {
                assert_eq!(error.kind, LifecycleErrorKind::Cancelled);
                assert!(!output_dir.exists());
                lifecycle.finish_failed().unwrap();
                assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Failed);
            },
            _ => panic!("publication and cancellation must have exactly one winner"),
        }
    }
}

#[test]
fn publisher_external_vm_stop_race_has_one_publication_winner() {
    for attempt in 0..16 {
        let area = TestArea::new();
        let (vm, lifecycle, lease, host) =
            build_host(&area, grants(), grants(), all_phases(), "external-race");
        let output_dir = area.path("staging/final");
        let mut publisher = BuildPublisher::new(&host, &lease, &output_dir).unwrap();
        lease.complete().unwrap();
        lifecycle.begin_draining().unwrap();
        lifecycle.try_close().unwrap();
        publisher.write_report(b"race report").unwrap();
        let barrier = Arc::new(Barrier::new(3));
        let publishing_barrier = Arc::clone(&barrier);
        let publishing = std::thread::spawn(move || {
            publishing_barrier.wait();
            publisher.commit()
        });
        let stopping_barrier = Arc::clone(&barrier);
        let stop = vm.stop_handle();
        let stopping = std::thread::spawn(move || {
            stopping_barrier.wait();
            stop.request_stop();
        });
        barrier.wait();
        let result = publishing.join().unwrap();
        stopping.join().unwrap();
        match result {
            Ok(()) => {
                assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Succeeded);
                assert_eq!(fs::read(output_dir.join("report.json")).unwrap(), b"race report");
            },
            Err(error) => {
                assert_eq!(error.kind, LifecycleErrorKind::Cancelled, "attempt {attempt}");
                assert!(!output_dir.exists());
                lifecycle.finish_failed().unwrap();
                assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Failed);
            },
        }
    }
}

#[test]
fn host_foreign_cterm_stops_both_shared_vm_builds_and_blocks_publication() {
    let area = TestArea::new();
    fs::write(area.path("source/valid.ML"), b"val x = 1").unwrap();
    let mut vm = Vm::new(DenyHost);
    let lifecycle_a = BuildLifecycle::new(vm.stop_handle());
    let lifecycle_b = BuildLifecycle::new(vm.stop_handle());
    let store_a = ObjectStore::new(&vm, lifecycle_a.clone()).unwrap();
    let store_b = ObjectStore::new(&vm, lifecycle_b.clone()).unwrap();
    let lease_a = lifecycle_a.start_root(WorkKind::Evaluation, "build A").unwrap();
    let lease_b = lifecycle_b.start_root(WorkKind::Evaluation, "build B").unwrap();
    let host_a = RestrictedHost::new(
        lifecycle_a.clone(),
        &lease_a,
        area.roots("stage-a"),
        grants(),
        grants(),
        all_phases(),
        BTreeMap::new(),
    )
    .unwrap();
    let mut allowed = grants();
    allowed.run_fixed_verit = true;
    let host_b = RestrictedHost::new(
        lifecycle_b.clone(),
        &lease_b,
        area.roots("stage-b"),
        allowed.clone(),
        allowed.clone(),
        PhaseEffects { active: allowed.clone(), draining: allowed },
        BTreeMap::new(),
    )
    .unwrap();
    let output = area.path("staging/final-b");
    let publisher = BuildPublisher::new(&host_b, &lease_b, &output).unwrap();
    let signature = Signature::new().extend_const("P", Ty::prop()).unwrap();
    let owner = TrustedTheory::root("ObjectBoundary", signature);
    let real_term: CTerm = ProofContext::new(owner.snapshot().clone())
        .certify_term(RawTerm::const_("P", Ty::prop()))
        .unwrap();
    let reference = store_a.insert(&mut vm, &lease_a, real_term).unwrap();
    assert!(matches!(
        store_b.get::<CTerm>(&vm, &lease_b, &reference),
        Err(ObjectError::ForeignBuild)
    ));
    assert!(vm.check_stop().is_err());
    assert!(host_a.read_source(&lease_a, Path::new("valid.ML")).is_err());
    assert!(host_b.authorize_fixed_solver(&lease_b).is_err());
    assert_eq!(lifecycle_a.phase().unwrap(), RuntimePhase::Cancelling);
    assert_eq!(lifecycle_b.phase().unwrap(), RuntimePhase::Cancelling);
    assert!(publisher.commit().is_err());
    assert!(!output.exists());
    lease_a.complete().unwrap_err();
    lease_b.complete().unwrap_err();
    lifecycle_a.finish_failed().unwrap();
    lifecycle_b.finish_failed().unwrap();
}

#[test]
fn host_external_stop_handle_revokes_active_build_and_private_publisher() {
    let area = TestArea::new();
    fs::write(area.path("source/valid.ML"), b"val x = 1").unwrap();
    let (vm, lifecycle, lease, host) =
        build_host(&area, grants(), grants(), all_phases(), "external-stop");
    let output = area.path("staging/external-final");
    let publisher = BuildPublisher::new(&host, &lease, &output).unwrap();
    vm.stop_handle().request_stop();
    assert!(matches!(
        host.read_source(&lease, Path::new("valid.ML")),
        Err(HostIoError::Lifecycle { .. })
    ));
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    assert!(lifecycle.begin_draining().is_err());
    assert!(publisher.commit().is_err());
    assert!(!output.exists());
    lease.complete().unwrap_err();
    lifecycle.finish_failed().unwrap();
}
