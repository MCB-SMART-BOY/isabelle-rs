use std::rc::Rc;

use isabelle_kernel::{CTerm, KernelThm, ProofContext, RawTerm, Signature, TrustedTheory, Ty};
use isabelle_rs::ml::host::lifecycle::{BuildLifecycle, RuntimePhase, WorkKind};
use isabelle_rs::ml::host::objects::{ObjectError, ObjectStore};
use isabelle_rs::ml::{DenyHost, Value, Vm};

fn create_term() -> CTerm {
    let signature = Signature::new().extend_const("P", Ty::prop()).unwrap();
    let owner = TrustedTheory::root("ObjectBoundary", signature);
    ProofContext::new(owner.snapshot().clone())
        .certify_term(RawTerm::const_("P", Ty::prop()))
        .unwrap()
}

fn create_store() -> (Vm, BuildLifecycle, ObjectStore) {
    let vm = Vm::new(DenyHost);
    let lifecycle = BuildLifecycle::new(vm.stop_handle());
    let store = ObjectStore::new(&vm, lifecycle.clone()).unwrap();
    (vm, lifecycle, store)
}

#[test]
fn logical_objects_same_build_preserves_certified_value_during_draining() {
    let (mut vm, lifecycle, store) = create_store();
    let lease = lifecycle.start_root(WorkKind::Evaluation, "logical operation").unwrap();
    let term = create_term();
    let value = store.insert(&mut vm, &lease, term.clone()).unwrap();
    lifecycle.begin_draining().unwrap();
    let recovered = store.get::<CTerm>(&vm, &lease, &value).unwrap();
    assert_eq!(*recovered, term);
    lease.complete().unwrap();
    lifecycle.try_close().unwrap();
    assert!(vm.check_stop().is_err());
}

#[test]
fn logical_objects_wrong_kind_and_plain_value_never_authorize_theorem() {
    let (mut vm, lifecycle, store) = create_store();
    let lease = lifecycle.start_root(WorkKind::Evaluation, "kind checking").unwrap();
    let term = store.insert(&mut vm, &lease, create_term()).unwrap();
    assert!(matches!(
        store.get::<KernelThm>(&vm, &lease, &term),
        Err(ObjectError::WrongKind { .. })
    ));
    assert!(matches!(
        store.get::<CTerm>(&vm, &lease, &Value::int(0)),
        Err(ObjectError::NotHostObject { .. })
    ));
    lease.complete().unwrap();
}

#[test]
fn logical_objects_unwrapped_host_value_cannot_impersonate_envelope() {
    let (mut vm, lifecycle, store) = create_store();
    let lease = lifecycle.start_root(WorkKind::Evaluation, "raw host input").unwrap();
    let raw = vm.insert_host_object(Rc::new(create_term())).unwrap();
    assert!(matches!(store.get::<CTerm>(&vm, &lease, &raw), Err(ObjectError::WrongKind { .. })));
    lease.complete().unwrap();
}

#[test]
fn logical_objects_same_vm_foreign_build_rejects_valid_handle() {
    let (mut vm, lifecycle, store) = create_store();
    let other_lifecycle = BuildLifecycle::new(vm.stop_handle());
    let other_store = ObjectStore::new(&vm, other_lifecycle.clone()).unwrap();
    let lease = lifecycle.start_root(WorkKind::Evaluation, "first build").unwrap();
    let other_lease = other_lifecycle.start_root(WorkKind::Evaluation, "second build").unwrap();
    let value = store.insert(&mut vm, &lease, create_term()).unwrap();
    assert!(matches!(
        other_store.get::<CTerm>(&vm, &other_lease, &value),
        Err(ObjectError::ForeignBuild)
    ));
    assert!(vm.check_stop().is_err());
    assert_eq!(other_lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    assert!(other_lifecycle.check_task(&other_lease).is_err());
    assert!(lifecycle.check_task(&lease).is_err());
    assert!(other_lifecycle.begin_draining().is_err());
    lease.complete().unwrap_err();
    other_lease.complete().unwrap_err();
    other_lifecycle.finish_failed().unwrap();
}

#[test]
fn logical_objects_foreign_vm_rejects_lookup_and_initialization() {
    let (mut vm, lifecycle, store) = create_store();
    let other_vm = Vm::new(DenyHost);
    assert!(matches!(
        ObjectStore::new(&other_vm, lifecycle.clone()),
        Err(ObjectError::ForeignRuntime)
    ));
    let lease = lifecycle.start_root(WorkKind::Evaluation, "foreign VM").unwrap();
    let value = store.insert(&mut vm, &lease, create_term()).unwrap();
    assert!(matches!(
        store.get::<CTerm>(&other_vm, &lease, &value),
        Err(ObjectError::ForeignRuntime)
    ));
    assert!(other_vm.check_stop().is_err());
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    assert!(lifecycle.check_task(&lease).is_err());
    lease.complete().unwrap_err();
    lifecycle.finish_failed().unwrap();
}

#[test]
fn logical_objects_cancelled_build_rejects_preexisting_value() {
    let (mut vm, lifecycle, store) = create_store();
    let lease = lifecycle.start_root(WorkKind::Evaluation, "cancelled lookup").unwrap();
    let value = store.insert(&mut vm, &lease, create_term()).unwrap();
    lifecycle.cancel("cancel before lookup".to_owned()).unwrap();
    assert!(matches!(store.get::<CTerm>(&vm, &lease, &value), Err(ObjectError::Vm(_))));
    lease.complete().unwrap_err();
    lifecycle.finish_failed().unwrap();
}

#[test]
fn logical_objects_foreign_lease_revokes_vm_without_returning_payload() {
    let (mut vm, lifecycle, store) = create_store();
    let other = BuildLifecycle::new(vm.stop_handle());
    let lease = lifecycle.start_root(WorkKind::Evaluation, "object owner").unwrap();
    let foreign = other.start_root(WorkKind::Evaluation, "foreign lease").unwrap();
    let value = store.insert(&mut vm, &lease, create_term()).unwrap();
    assert!(matches!(store.get::<CTerm>(&vm, &foreign, &value), Err(ObjectError::Lifecycle(_))));
    assert!(vm.check_stop().is_err());
    assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
    assert!(lifecycle.check_task(&lease).is_err());
    assert!(other.check_task(&foreign).is_err());
    lease.complete().unwrap_err();
    foreign.complete().unwrap_err();
    lifecycle.finish_failed().unwrap();
}

#[test]
fn logical_objects_foreign_build_wrong_payload_revokes_before_kind_check() {
    let (mut vm, lifecycle, store) = create_store();
    let other = BuildLifecycle::new(vm.stop_handle());
    let other_store = ObjectStore::new(&vm, other.clone()).unwrap();
    let lease = lifecycle.start_root(WorkKind::Evaluation, "object owner").unwrap();
    let other_lease = other.start_root(WorkKind::Evaluation, "foreign consumer").unwrap();
    let value = store.insert(&mut vm, &lease, create_term()).unwrap();
    assert!(matches!(
        other_store.get::<KernelThm>(&vm, &other_lease, &value),
        Err(ObjectError::ForeignBuild)
    ));
    assert!(vm.check_stop().is_err());
    assert_eq!(other.phase().unwrap(), RuntimePhase::Cancelling);
    assert!(other.check_task(&other_lease).is_err());
    lease.complete().unwrap_err();
    other_lease.complete().unwrap_err();
    other.finish_failed().unwrap();
}
