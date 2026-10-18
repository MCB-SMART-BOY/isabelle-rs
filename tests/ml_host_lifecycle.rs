use std::error::Error;
use std::sync::{Arc, Barrier, mpsc};
use std::thread;

use isabelle_rs::ml::host::lifecycle::{
    BuildLifecycle, LifecycleErrorKind, RuntimePhase, WorkKind,
};
use isabelle_rs::ml::{DenyHost, Vm};

fn create_lifecycle() -> (Vm, BuildLifecycle) {
    let vm = Vm::new(DenyHost);
    let lifecycle = BuildLifecycle::new(vm.stop_handle());
    (vm, lifecycle)
}

#[test]
fn lifecycle_draining_race_rejects_new_roots_and_accepts_live_children() {
    let (vm, lifecycle) = create_lifecycle();
    let root = lifecycle.start_root(WorkKind::Evaluation, "root").unwrap();
    let (ready_sender, ready_receiver) = mpsc::channel();
    let (resume_sender, resume_receiver) = mpsc::channel();
    let worker = thread::spawn(move || {
        ready_sender.send(()).unwrap();
        resume_receiver.recv().unwrap();
        let child = root.start_child(WorkKind::Future, "nested future").unwrap();
        root.complete().unwrap();
        let grandchild = child.start_child(WorkKind::Proof, "nested proof").unwrap();
        child.complete().unwrap();
        grandchild.check_active().unwrap();
        grandchild.complete().unwrap();
    });
    ready_receiver.recv().unwrap();
    lifecycle.begin_draining().unwrap();
    let refusal = lifecycle.start_root(WorkKind::Callback, "late root").err().unwrap();
    assert_eq!(refusal.kind, LifecycleErrorKind::InvalidPhase);
    assert_eq!(lifecycle.try_close().unwrap_err().kind, LifecycleErrorKind::PendingWork);
    resume_sender.send(()).unwrap();
    worker.join().unwrap();
    assert_eq!(lifecycle.pending_counts().unwrap().total(), 0);
    lifecycle.try_close().unwrap();
    assert!(vm.check_stop().is_err());
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Closed);
    lifecycle.cancel("late before publication".into()).unwrap();
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    lifecycle.finish_failed().unwrap();
}

#[test]
fn lifecycle_concurrent_root_and_draining_share_one_atomic_boundary() {
    let (_vm, lifecycle) = create_lifecycle();
    let start = Arc::new(Barrier::new(3));
    let starting_root = Arc::clone(&start);
    let building = lifecycle.clone();
    let root_worker = thread::spawn(move || {
        starting_root.wait();
        building.start_root(WorkKind::Evaluation, "racing root")
    });
    let starting_draining = Arc::clone(&start);
    let draining = lifecycle.clone();
    let drain_worker = thread::spawn(move || {
        starting_draining.wait();
        draining.begin_draining()
    });
    start.wait();
    drain_worker.join().unwrap().unwrap();
    match root_worker.join().unwrap() {
        Ok(lease) => {
            assert_eq!(lifecycle.pending_counts().unwrap().total(), 1);
            assert_eq!(lifecycle.try_close().unwrap_err().kind, LifecycleErrorKind::PendingWork);
            lease.complete().unwrap();
        },
        Err(error) => {
            assert_eq!(error.kind, LifecycleErrorKind::InvalidPhase);
            assert_eq!(lifecycle.pending_counts().unwrap().total(), 0);
        },
    }
    lifecycle.try_close().unwrap();
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Closed);
}

#[test]
fn lifecycle_foreign_lease_never_authorizes_another_build() {
    let (vm_a, lifecycle_a) = create_lifecycle();
    let (vm_b, lifecycle_b) = create_lifecycle();
    assert!(lifecycle_a.shares_build(&lifecycle_a.clone()));
    assert!(!lifecycle_a.shares_build(&lifecycle_b));
    assert!(lifecycle_a.matches_stop_handle(&vm_a.stop_handle()));
    assert!(!lifecycle_a.matches_stop_handle(&vm_b.stop_handle()));
    let lease_a = lifecycle_a.start_root(WorkKind::Evaluation, "A work").unwrap();
    let lease_b = lifecycle_b.start_root(WorkKind::Process, "B work").unwrap();

    assert_eq!(lifecycle_a.check_task(&lease_b).unwrap_err().kind, LifecycleErrorKind::WrongBuild);
    assert_eq!(lifecycle_b.check_task(&lease_a).unwrap_err().kind, LifecycleErrorKind::WrongBuild);
    lifecycle_a.check_task(&lease_a).unwrap();
    lifecycle_b.check_task(&lease_b).unwrap();
    assert_eq!(lifecycle_a.pending_counts().unwrap().count(WorkKind::Evaluation), 1);
    assert_eq!(lifecycle_b.pending_counts().unwrap().count(WorkKind::Process), 1);

    lease_a.complete().unwrap();
    lifecycle_a.begin_draining().unwrap();
    lifecycle_a.try_close().unwrap();
    assert!(vm_a.check_stop().is_err());
    let error = lifecycle_a.check_task(&lease_b).unwrap_err();
    assert_eq!(error.kind, LifecycleErrorKind::WrongBuild);
    assert_eq!(error.operation, "check_task");
    assert_eq!(error.origin, "B work");
    assert!(vm_b.check_stop().is_ok());
    lifecycle_b.check_task(&lease_b).unwrap();
    lease_b.complete().unwrap();
    lifecycle_b.begin_draining().unwrap();
    lifecycle_b.try_close().unwrap();
}

#[test]
fn lifecycle_every_work_kind_blocks_close_and_tracks_its_own_count() {
    const KINDS: [WorkKind; 6] = [
        WorkKind::Evaluation,
        WorkKind::Future,
        WorkKind::Callback,
        WorkKind::Stream,
        WorkKind::Process,
        WorkKind::Proof,
    ];
    for blocked_kind in KINDS {
        let (_vm, lifecycle) = create_lifecycle();
        let lease = lifecycle.start_root(blocked_kind, "pending work").unwrap();
        lifecycle.begin_draining().unwrap();
        let counts = lifecycle.pending_counts().unwrap();
        assert_eq!(counts.count(blocked_kind), 1);
        assert_eq!(counts.total(), 1);
        assert_eq!(lifecycle.try_close().unwrap_err().kind, LifecycleErrorKind::PendingWork);
        lease.complete().unwrap();
        lifecycle.try_close().unwrap();
        assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Closed);
    }
}

#[test]
fn lifecycle_cancellation_before_completion_drains_with_original_cause() {
    let (vm, lifecycle) = create_lifecycle();
    let lease = lifecycle.start_root(WorkKind::Process, "solver").unwrap();
    let child = lease.start_child(WorkKind::Stream, "output").unwrap();
    let cancellation = lifecycle.cancellation();
    let (resume_sender, resume_receiver) = mpsc::channel();
    let worker = thread::spawn(move || {
        resume_receiver.recv().unwrap();
        cancellation.check().unwrap_err().kind
    });
    lifecycle.cancel("solver timed out".into()).unwrap();
    resume_sender.send(()).unwrap();
    assert_eq!(worker.join().unwrap(), LifecycleErrorKind::Cancelled);
    assert!(lifecycle.cancellation().is_requested());
    assert!(vm.check_stop().is_err());
    let error = lease.complete().unwrap_err();
    assert_eq!(error.kind, LifecycleErrorKind::Cancelled);
    assert_eq!(
        error.source().unwrap().to_string(),
        "cancel at supervisor (Some(Active)): solver timed out"
    );
    assert_eq!(child.complete().unwrap_err().kind, LifecycleErrorKind::Cancelled);
    assert_eq!(lifecycle.finish_failed().unwrap(), ());
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Failed);
    assert!(lifecycle.start_root(WorkKind::Proof, "late").is_err());
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Failed);
}

#[test]
fn lifecycle_completion_before_cancellation_cannot_publish() {
    let (_vm, lifecycle) = create_lifecycle();
    lifecycle.start_root(WorkKind::Evaluation, "done").unwrap().complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.cancel("post-evaluation failure".into()).unwrap();
    assert_eq!(lifecycle.try_close().unwrap_err().kind, LifecycleErrorKind::Cancelled);
    lifecycle.finish_failed().unwrap();
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Failed);
}

#[test]
fn lifecycle_abandoned_lease_cancels_instead_of_counting_as_success() {
    let (vm, lifecycle) = create_lifecycle();
    let root = lifecycle.start_root(WorkKind::Evaluation, "root").unwrap();
    let child = root.start_child(WorkKind::Future, "lost child").unwrap();
    lifecycle.begin_draining().unwrap();
    drop(child);
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    assert!(lifecycle.cancellation().is_requested());
    assert!(vm.check_stop().is_err());
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Future), 0);
    assert_eq!(lifecycle.finish_failed().unwrap_err().kind, LifecycleErrorKind::PendingWork);
    let error = root.complete().unwrap_err();
    assert_eq!(
        error.source().unwrap().to_string(),
        "drop at lost child (Some(Draining)): lease dropped without complete"
    );
    lifecycle.finish_failed().unwrap();
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Failed);
}

#[test]
fn lifecycle_external_failure_from_closed_cancels_irrevocably() {
    let (vm, lifecycle) = create_lifecycle();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
    assert!(vm.check_stop().is_err());
    assert!(lifecycle.cancellation().is_requested());
    assert_eq!(
        lifecycle.cancellation().check().unwrap_err().kind,
        LifecycleErrorKind::InvalidPhase
    );
    lifecycle.cancel("report rename failed".into()).unwrap();
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    lifecycle.finish_failed().unwrap();
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Failed);
    assert!(lifecycle.begin_draining().is_err());
}

#[test]
fn lifecycle_cancel_after_close_prevents_success_without_publication() {
    let (vm, lifecycle) = create_lifecycle();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
    lifecycle.cancel("cancellation before filesystem commit".into()).unwrap();
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    lifecycle.finish_failed().unwrap();
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Failed);
    assert!(vm.check_stop().is_err());
}

#[test]
fn lifecycle_cancelled_cleanup_waits_for_all_kinds_and_never_resets_stop() {
    const KINDS: [WorkKind; 6] = [
        WorkKind::Evaluation,
        WorkKind::Future,
        WorkKind::Callback,
        WorkKind::Stream,
        WorkKind::Process,
        WorkKind::Proof,
    ];
    let (vm, lifecycle) = create_lifecycle();
    let mut leases: Vec<_> =
        KINDS.into_iter().map(|kind| lifecycle.start_root(kind, "work").unwrap()).collect();
    lifecycle.cancel("callback failed".into()).unwrap();
    lifecycle.cancel("secondary failure".into()).unwrap();
    for kind in KINDS {
        assert_eq!(lifecycle.pending_counts().unwrap().count(kind), 1);
    }
    while let Some(lease) = leases.pop() {
        assert_eq!(lifecycle.finish_failed().unwrap_err().kind, LifecycleErrorKind::PendingWork);
        assert_eq!(
            lease.complete().unwrap_err().source().unwrap().to_string(),
            "cancel at supervisor (Some(Active)): callback failed"
        );
    }
    lifecycle.finish_failed().unwrap();
    assert!(lifecycle.cancellation().is_requested());
    assert!(vm.check_stop().is_err());
    assert!(lifecycle.try_close().is_err());
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Failed);
}
