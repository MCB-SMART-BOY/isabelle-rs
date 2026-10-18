use super::{
    PluginRegistry, PluginReply, TestArea, WorkKind, budget, effects, make_build,
    native_core_plugin, registry,
};
use isabelle_rs::ml::HostFailure;
use std::fs;

#[test]
fn native_resource_permission_failure_preserves_classification_and_drains_children() {
    let area = TestArea::new();
    fs::write(area.0.join("resources/item"), b"resource").unwrap();
    let mut grants = effects();
    grants.read_resources.clear();
    let (vm, lifecycle, bridge) = make_build(&area, "permission", grants);
    let registry = registry(lifecycle.clone(), bridge);
    let result = registry.invoke_service(&vm, "File.read_resource", &[b"isabelle", b"item"]);
    assert!(matches!(result, Err(HostFailure::Permission { .. })), "{result:?}");
    assert!(lifecycle.cancellation().is_requested());
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Future), 0);
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Callback), 0);
}

#[test]
fn native_resource_oversize_failure_preserves_classification_and_drains_children() {
    let area = TestArea::new();
    fs::write(area.0.join("resources/item"), b"too large").unwrap();
    let (vm, lifecycle, bridge) = make_build(&area, "oversized", effects());
    let mut plugin = native_core_plugin();
    for spec in &mut plugin.manifest.services {
        if spec.name == "File.read_resource" {
            spec.max_response_bytes = 1;
        }
    }
    for service in &mut plugin.services {
        if service.spec.name == "File.read_resource" {
            service.spec.max_response_bytes = 1;
        }
    }
    let registry =
        PluginRegistry::register(lifecycle.clone(), bridge, budget(), vec![plugin]).unwrap();
    let result = registry.invoke_service(&vm, "File.read_resource", &[b"isabelle", b"item"]);
    assert!(matches!(result, Err(HostFailure::Failed { .. })), "{result:?}");
    assert!(lifecycle.cancellation().is_requested());
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Future), 0);
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Callback), 0);
}

#[test]
fn native_base64_stream_padding_ends_decode_before_trailing_bytes() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "stream-padding", effects());
    let registry = registry(lifecycle, bridge);
    for input in [b"Zg==Zg==".as_slice(), b"Zg==not-base64!", b"Zg==="] {
        assert_eq!(
            registry.invoke_service(&vm, "Base64.decode", &[input]).unwrap(),
            PluginReply::Success(vec![b"f".to_vec()])
        );
    }
}

#[test]
fn native_base64_stream_response_budget_counts_only_decoded_prefix() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "stream-budget", effects());
    let mut plugin = native_core_plugin();
    for spec in &mut plugin.manifest.services {
        if spec.name == "Base64.decode" {
            spec.max_response_bytes = 1;
        }
    }
    for service in &mut plugin.services {
        if service.spec.name == "Base64.decode" {
            service.spec.max_response_bytes = 1;
        }
    }
    let registry = PluginRegistry::register(lifecycle, bridge, budget(), vec![plugin]).unwrap();
    assert_eq!(
        registry.invoke_service(&vm, "Base64.decode", &[b"Zg==Zg=="]).unwrap(),
        PluginReply::Success(vec![b"f".to_vec()])
    );
    assert!(matches!(
        registry.invoke_service(&vm, "Base64.decode", &[b"Zm8="]),
        Ok(PluginReply::Fail(_))
    ));
}

fn compress_xz(registry: &PluginRegistry, vm: &isabelle_rs::ml::Vm, bytes: &[u8]) -> Vec<u8> {
    match registry.invoke_service(vm, "XZ.compress", &[bytes]).unwrap() {
        PluginReply::Success(mut items) if items.len() == 1 => items.remove(0),
        result => panic!("unexpected compression result: {result:?}"),
    }
}

#[test]
fn native_xz_incomplete_stream_padding_returns_catchable_failure() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "xz-padding", effects());
    let registry = registry(lifecycle.clone(), bridge);
    let encoded = compress_xz(&registry, &vm, b"abc");
    for padding in 1..=3 {
        let mut malformed = encoded.clone();
        malformed.resize(encoded.len() + padding, 0);
        assert!(
            matches!(
                registry.invoke_service(&vm, "XZ.uncompress", &[&malformed]),
                Ok(PluginReply::Fail(_))
            ),
            "accepted {padding} padding bytes"
        );
    }
    assert!(!lifecycle.cancellation().is_requested());
}

#[test]
fn native_xz_complete_padding_and_concatenated_streams_preserve_contents() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "xz-concatenation", effects());
    let registry = registry(lifecycle, bridge);
    let mut encoded = compress_xz(&registry, &vm, b"abc");
    encoded.extend_from_slice(&[0; 4]);
    assert_eq!(
        registry.invoke_service(&vm, "XZ.uncompress", &[&encoded]).unwrap(),
        PluginReply::Success(vec![b"abc".to_vec()])
    );
    encoded.extend_from_slice(&compress_xz(&registry, &vm, b"def"));
    assert_eq!(
        registry.invoke_service(&vm, "XZ.uncompress", &[&encoded]).unwrap(),
        PluginReply::Success(vec![b"abcdef".to_vec()])
    );
}
