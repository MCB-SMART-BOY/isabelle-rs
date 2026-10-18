use super::*;
use isabelle_rs::ml::MlErrorKind;

#[test]
fn native_plugins_separate_builds_do_not_share_services_or_revocation() {
    let area = TestArea::new();
    let (vm_a, lifecycle_a, bridge_a) = make_build(&area, "build-a", effects());
    let (vm_b, lifecycle_b, bridge_b) = make_build(&area, "build-b", effects());
    let registry_a = registry(lifecycle_a.clone(), bridge_a);
    let registry_b = registry(lifecycle_b.clone(), bridge_b);
    vm_a.request_stop();
    assert!(registry_a.session_services(&vm_a).is_err());
    assert!(lifecycle_a.cancellation().is_requested());
    assert!(!lifecycle_b.cancellation().is_requested());
    assert_eq!(
        registry_b.invoke_service(&vm_b, "Base64.encode", &[b"b"]).unwrap(),
        PluginReply::Success(vec![b"Yg==".to_vec()])
    );
    assert!(registry_a.invoke_service(&vm_a, "Base64.encode", &[b"a"]).is_err());
}

#[test]
fn native_plugins_foreign_vm_catalogue_access_revokes_both_domains() {
    let area = TestArea::new();
    let (vm_a, lifecycle_a, bridge_a) = make_build(&area, "owner", effects());
    let (vm_b, lifecycle_b, bridge_b) = make_build(&area, "foreign-caller", effects());
    let registry_a = registry(lifecycle_a.clone(), bridge_a);
    let registry_b = registry(lifecycle_b.clone(), bridge_b);
    assert!(matches!(registry_a.session_services(&vm_b), Err(HostFailure::Permission { .. })));
    assert!(lifecycle_a.cancellation().is_requested());
    assert!(lifecycle_b.cancellation().is_requested());
    assert_eq!(vm_a.check_stop().unwrap_err().kind, MlErrorKind::Stopped);
    assert_eq!(vm_b.check_stop().unwrap_err().kind, MlErrorKind::Stopped);
    assert!(registry_a.invoke_service(&vm_a, "Base64.encode", &[b"a"]).is_err());
    assert!(registry_b.invoke_service(&vm_b, "Base64.encode", &[b"b"]).is_err());
}
