use super::super::lifecycle::WorkKind;
use super::*;
use crate::ml::DenyHost;
use std::fs;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Barrier, mpsc};

// Test-only sequence keeps independently runnable temporary roots disjoint.
static NEXT_AREA: AtomicU64 = AtomicU64::new(0);
const RESULT_TIMEOUT: Duration = Duration::from_secs(5);

struct TestArea(PathBuf);

impl Drop for TestArea {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn prepare_wait() -> (TestArea, Vm, BuildLifecycle, TaskLease, RestrictedHost) {
    let id = NEXT_AREA.fetch_add(1, Ordering::Relaxed);
    let area =
        TestArea(std::env::temp_dir().join(format!("host-wait-{}-{id}", std::process::id())));
    fs::create_dir(&area.0).unwrap();
    fs::create_dir(area.0.join("source")).unwrap();
    fs::create_dir(area.0.join("staging")).unwrap();
    let vm = Vm::new(DenyHost);
    let lifecycle = BuildLifecycle::new(vm.stop_handle());
    let lease = lifecycle.start_root(WorkKind::Evaluation, "timing contract").unwrap();
    let grant = EffectSet { sleep: true, ..EffectSet::default() };
    let host = RestrictedHost::new(
        lifecycle.clone(),
        &lease,
        HostRoots {
            source: area.0.join("source"),
            resources: BTreeMap::new(),
            staging_parent: area.0.join("staging"),
            staging_name: "private".into(),
        },
        grant.clone(),
        grant.clone(),
        PhaseEffects { active: grant, draining: EffectSet::default() },
        BTreeMap::new(),
    )
    .unwrap();
    (area, vm, lifecycle, lease, host)
}

fn exercise_revocation_during_wait(revoke: impl FnOnce(&Vm, &BuildLifecycle)) -> HostIoError {
    let (_area, vm, lifecycle, lease, mut host) = prepare_wait();
    let entry = Arc::new((Barrier::new(2), Barrier::new(2)));
    host.sleep_entry = Some(Arc::clone(&entry));
    let (sender, receiver) = mpsc::channel();
    let worker = std::thread::spawn(move || {
        let result = host.sleep(&lease, Duration::MAX);
        let completion = lease.complete();
        sender.send((result, completion)).unwrap();
    });
    // The worker has passed authorization and computed Duration::MAX's remainder.
    entry.0.wait();
    revoke(&vm, &lifecycle);
    entry.1.wait();
    let (result, completion) = receiver.recv_timeout(RESULT_TIMEOUT).unwrap();
    assert!(completion.is_err());
    worker.join().unwrap();
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    lifecycle.finish_failed().unwrap();
    result.unwrap_err()
}

#[test]
fn sleep_external_stop_after_wait_entry_releases_all_work() {
    let error = exercise_revocation_during_wait(|vm, _| vm.request_stop());
    assert!(matches!(error, HostIoError::Lifecycle { .. }));
}

#[test]
fn sleep_draining_revokes_active_permission_after_wait_entry() {
    let error = exercise_revocation_during_wait(|_, lifecycle| lifecycle.begin_draining().unwrap());
    assert!(matches!(error, HostIoError::Permission { operation: "sleep", .. }));
}
