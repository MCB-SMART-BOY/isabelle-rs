use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use isabelle_rs::ml::host::files::{
    EffectSet, FileHostBridge, HostIoError, HostRoots, PhaseEffects, RestrictedHost,
};
use isabelle_rs::ml::host::lifecycle::{BuildLifecycle, LifecycleErrorKind, WorkKind};
use isabelle_rs::ml::{HostFailure, Vm};
use isabelle_rs::native_plugins::builtins::native_core_plugin;
use isabelle_rs::native_plugins::{
    CancelOutcome, ExactDependency, NativePlugin, NativeService, NativeTool, OperationSpec,
    PluginEffects, PluginManifest, PluginRegistry, PluginReply, PluginVersion, RegistryBudget,
    ResponseSink, ServiceContext, ServiceError, SessionLinkStatus,
};

#[path = "native_plugins/codec_errors.rs"]
mod codec_errors;
#[path = "native_plugins/revocation.rs"]
mod revocation;

static NEXT_DIR: AtomicU64 = AtomicU64::new(0);
const VERSION: PluginVersion = PluginVersion { major: 1, minor: 0, patch: 0 };

struct TestArea(PathBuf);
impl TestArea {
    fn new() -> Self {
        let dir = std::env::temp_dir().join(format!(
            "native-plugins-{}-{}",
            std::process::id(),
            NEXT_DIR.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&dir).unwrap();
        for name in ["source", "resources", "staging"] {
            fs::create_dir(dir.join(name)).unwrap();
        }
        Self(dir)
    }
}
impl Drop for TestArea {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn budget() -> RegistryBudget {
    const MAX: usize = 1024 * 1024;
    RegistryBudget {
        max_argument_bytes: MAX,
        max_request_bytes: MAX,
        max_response_items: 1,
        max_response_bytes: MAX,
        max_active_invocations: 8,
    }
}

fn make_build(
    area: &TestArea,
    name: &str,
    grants: EffectSet,
) -> (Vm, BuildLifecycle, Arc<FileHostBridge>) {
    let mut binding = None;
    let vm = Vm::with_host_factory(|stop| -> Result<_, HostIoError> {
        let lifecycle = BuildLifecycle::new(stop);
        let lease = lifecycle.start_root(WorkKind::Evaluation, "plugin contract").unwrap();
        let host = RestrictedHost::new(
            lifecycle.clone(),
            &lease,
            HostRoots {
                source: area.0.join("source"),
                resources: BTreeMap::from([("isabelle".into(), area.0.join("resources"))]),
                staging_parent: area.0.join("staging"),
                staging_name: name.into(),
            },
            grants.clone(),
            grants.clone(),
            PhaseEffects { active: grants.clone(), draining: grants },
            BTreeMap::new(),
        )?;
        let bridge = Arc::new(FileHostBridge::new(host, lease));
        binding = Some((lifecycle, Arc::clone(&bridge)));
        Ok(bridge)
    })
    .unwrap();
    let (lifecycle, bridge) = binding.unwrap();
    (vm, lifecycle, bridge)
}

fn effects() -> EffectSet {
    EffectSet {
        read_source: true,
        read_resources: BTreeSet::from(["isabelle".into()]),
        read_clock: true,
        sleep: true,
        ..EffectSet::default()
    }
}

fn registry(lifecycle: BuildLifecycle, bridge: Arc<FileHostBridge>) -> PluginRegistry {
    PluginRegistry::register(lifecycle, bridge, budget(), vec![native_core_plugin()]).unwrap()
}

#[test]
fn native_plugins_base64_root_service_preserves_binary_and_catchable_errors() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "base64", effects());
    let registry = registry(lifecycle.clone(), bridge);
    let raw = [0, 0xff, 0x80, 0x01, 0];
    let encoded = registry.invoke_service(&vm, "Base64.encode", &[&raw]).unwrap();
    assert_eq!(encoded, PluginReply::Success(vec![b"AP+AAQA=".to_vec()]));
    assert_eq!(
        registry.invoke_service(&vm, "Base64.decode", &[b"AP+AAQA="]).unwrap(),
        PluginReply::Success(vec![raw.to_vec()])
    );
    assert!(matches!(
        registry.invoke_service(&vm, "Base64.decode", &[b"%%%"]),
        Ok(PluginReply::Fail(_))
    ));
    assert!(matches!(registry.invoke_service(&vm, "missing", &[]), Ok(PluginReply::Fail(_))));
    assert_eq!(
        registry.invoke_service(&vm, "Base64.decode", &[b"Zg"]).unwrap(),
        PluginReply::Success(vec![b"f".to_vec()])
    );
    assert!(registry.invoke_service(&vm, "Base64.encode", &[b"f"]).is_ok());
    assert!(
        registry
            .session_services(&vm)
            .unwrap()
            .iter()
            .any(|service| service.name == "Base64.decode" && service.single && service.bytes)
    );
}

#[test]
fn native_plugins_registration_rejects_invalid_graph_and_signatures_without_partial_registry() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "transaction", effects());
    let mut wrong_api = native_core_plugin();
    wrong_api.manifest.api_version += 1;
    assert!(
        PluginRegistry::register(lifecycle.clone(), Arc::clone(&bridge), budget(), vec![wrong_api])
            .is_err()
    );
    let mut missing = native_core_plugin();
    missing
        .manifest
        .dependencies
        .push(ExactDependency { identity: "missing".into(), version: VERSION });
    assert!(
        PluginRegistry::register(lifecycle.clone(), Arc::clone(&bridge), budget(), vec![missing])
            .is_err()
    );
    let mut duplicate = native_core_plugin();
    duplicate.manifest.services[0].name = "Scala.result".into();
    assert!(
        PluginRegistry::register(lifecycle.clone(), Arc::clone(&bridge), budget(), vec![duplicate])
            .is_err()
    );
    let mut wrong_signature = native_core_plugin();
    wrong_signature.manifest.services[0].wire = isabelle_rs::native_plugins::WireType::String;
    assert!(
        PluginRegistry::register(
            lifecycle.clone(),
            Arc::clone(&bridge),
            budget(),
            vec![wrong_signature]
        )
        .is_err()
    );
    let mut wrong_budget = budget();
    wrong_budget.max_request_bytes -= 1;
    assert!(
        PluginRegistry::register(
            lifecycle.clone(),
            Arc::clone(&bridge),
            wrong_budget,
            vec![native_core_plugin()]
        )
        .is_err()
    );
    let registry = registry(lifecycle, bridge);
    assert_eq!(
        registry.invoke_service(&vm, "Base64.encode", &[b"ok"]).unwrap(),
        PluginReply::Success(vec![b"b2s=".to_vec()])
    );
}

#[test]
fn native_plugins_registration_rejects_cycles_versions_and_duplicate_names() {
    let area = TestArea::new();
    let (_vm, lifecycle, bridge) = make_build(&area, "dependency", effects());
    let mut left = native_core_plugin();
    left.manifest.identity = "left".into();
    left.manifest.dependencies.push(ExactDependency { identity: "right".into(), version: VERSION });
    let mut right = native_core_plugin();
    right.manifest.identity = "right".into();
    right.manifest.dependencies.push(ExactDependency { identity: "left".into(), version: VERSION });
    right.manifest.services.clear();
    right.services.clear();
    assert!(
        PluginRegistry::register(
            lifecycle.clone(),
            Arc::clone(&bridge),
            budget(),
            vec![left, right]
        )
        .err()
        .unwrap()
        .to_string()
        .contains("dependency cycle")
    );
    let mut left = native_core_plugin();
    left.manifest.dependencies.push(ExactDependency {
        identity: "right".into(),
        version: PluginVersion { major: 2, minor: 0, patch: 0 },
    });
    let mut right = native_core_plugin();
    right.manifest.identity = "right".into();
    right.manifest.services.clear();
    right.services.clear();
    assert!(
        PluginRegistry::register(
            lifecycle.clone(),
            Arc::clone(&bridge),
            budget(),
            vec![left, right]
        )
        .is_err()
    );
    let mut same = native_core_plugin();
    same.manifest.identity = "other".into();
    assert!(
        PluginRegistry::register(lifecycle, bridge, budget(), vec![native_core_plugin(), same])
            .is_err()
    );
}

#[test]
fn native_plugins_file_and_time_services_use_real_supervised_effects() {
    let area = TestArea::new();
    fs::write(area.0.join("source/Pure.ML"), [0, 255, 1]).unwrap();
    fs::write(area.0.join("resources/item"), [7, 8, 9]).unwrap();
    let (vm, lifecycle, bridge) = make_build(&area, "effects", effects());
    let registry = registry(lifecycle.clone(), bridge);
    assert_eq!(
        registry.invoke_service(&vm, "File.read_source", &[b"Pure.ML"]).unwrap(),
        PluginReply::Success(vec![vec![0, 255, 1]])
    );
    assert_eq!(
        registry.invoke_service(&vm, "File.read_resource", &[b"isabelle", b"item"]).unwrap(),
        PluginReply::Success(vec![vec![7, 8, 9]])
    );
    assert!(matches!(registry.invoke_service(&vm, "sleep", &[b"0"]), Ok(PluginReply::Success(_))));
    let now = registry.invoke_service(&vm, "Clock.now", &[b""]).unwrap();
    assert!(matches!(now, PluginReply::Success(items) if items.len() == 1 && !items[0].is_empty()));
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Callback), 0);
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Future), 0);
    assert!(matches!(
        registry.invoke_service(&vm, "sleep", &[b"not a duration"]),
        Ok(PluginReply::Error(_))
    ));
    assert!(matches!(
        registry.invoke_service(&vm, "File.read_source", &[b"missing.ML"]),
        Ok(PluginReply::Fail(_))
    ));
    assert!(registry.invoke_service(&vm, "Base64.encode", &[b"still live"]).is_ok());
}

#[test]
fn native_plugins_wrong_build_revocation_and_budget_are_not_effects() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "restricted", EffectSet::default());
    assert!(
        PluginRegistry::register(
            BuildLifecycle::new(vm.stop_handle()),
            Arc::clone(&bridge),
            budget(),
            vec![native_core_plugin()]
        )
        .is_err()
    );
    let registry = registry(lifecycle.clone(), bridge);
    assert!(matches!(
        registry.invoke_service(&vm, "Base64.decode", &[&vec![b'A'; 1024 * 1024 + 1]]),
        Ok(PluginReply::Fail(_))
    ));
    assert_eq!(
        registry.invoke_service(&vm, "Base64.encode", &[b"ok"]).unwrap(),
        PluginReply::Success(vec![b"b2s=".to_vec()])
    );
    assert!(matches!(
        registry.invoke_service(&vm, "File.read_source", &[b"Pure.ML"]),
        Err(HostFailure::Permission { .. })
    ));
    assert!(lifecycle.cancellation().is_requested());
    assert!(registry.session_services(&vm).is_err());
}

#[test]
fn native_plugins_ended_build_and_foreign_vm_cannot_discover_operations() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "ended", effects());
    let registry = registry(lifecycle.clone(), Arc::clone(&bridge));
    let other = Vm::new(isabelle_rs::ml::DenyHost);
    assert!(registry.session_services(&other).is_err());
    assert!(registry.invoke_service(&vm, "Base64.encode", &[b"ok"]).is_err());
    assert!(lifecycle.cancellation().is_requested());
}

fn read_source_tool(
    context: &ServiceContext<'_>,
    args: &[&[u8]],
    sink: &mut ResponseSink,
) -> Result<(), ServiceError> {
    let relative =
        std::str::from_utf8(args[0]).map_err(|error| ServiceError::Fail(error.to_string()))?;
    let bytes = context.read_source(Path::new(relative), 1024)?;
    sink.push_owned(bytes)
}

fn read_optional_source(
    context: &ServiceContext<'_>,
    args: &[&[u8]],
    sink: &mut ResponseSink,
) -> Result<(), ServiceError> {
    let relative =
        std::str::from_utf8(args[0]).map_err(|error| ServiceError::Fail(error.to_string()))?;
    match context.read_source(Path::new(relative), 1024) {
        Ok(bytes) => sink.push_owned(bytes),
        Err(ServiceError::Host(HostIoError::Io { source, .. }))
            if source.kind() == std::io::ErrorKind::NotFound =>
        {
            Err(ServiceError::Null)
        },
        Err(error) => Err(error),
    }
}

#[test]
fn native_plugins_optional_file_returns_null_without_revoking_build() {
    let area = TestArea::new();
    fs::write(area.0.join("source/present"), b"real bytes").unwrap();
    let (vm, lifecycle, bridge) = make_build(&area, "nullable", effects());
    let mut plugin = native_core_plugin();
    let mut spec = plugin
        .manifest
        .services
        .iter()
        .find(|spec| spec.name == "File.read_source")
        .unwrap()
        .clone();
    spec.name = "File.optional_source".into();
    plugin.manifest.services.push(spec.clone());
    plugin.services.push(NativeService { spec, call: read_optional_source });
    let registry =
        PluginRegistry::register(lifecycle.clone(), bridge, budget(), vec![plugin]).unwrap();
    assert_eq!(
        registry.invoke_service(&vm, "File.optional_source", &[b"absent"]).unwrap(),
        PluginReply::Null
    );
    assert_eq!(
        registry.invoke_service(&vm, "File.optional_source", &[b"present"]).unwrap(),
        PluginReply::Success(vec![b"real bytes".to_vec()])
    );
    assert!(!lifecycle.cancellation().is_requested());
}

#[test]
fn native_plugins_response_budget_precedes_base64_output_allocation() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "bounded", effects());
    let mut plugin = native_core_plugin();
    let manifest =
        plugin.manifest.services.iter_mut().find(|spec| spec.name == "Base64.encode").unwrap();
    manifest.max_response_bytes = 2;
    let linked =
        plugin.services.iter_mut().find(|service| service.spec.name == "Base64.encode").unwrap();
    linked.spec.max_response_bytes = 2;
    let registry =
        PluginRegistry::register(lifecycle.clone(), bridge, budget(), vec![plugin]).unwrap();
    assert!(matches!(
        registry.invoke_service(&vm, "Base64.encode", &[b"f"]),
        Ok(PluginReply::Fail(_))
    ));
    assert_eq!(
        registry.invoke_service(&vm, "Base64.decode", &[b"Zg=="]).unwrap(),
        PluginReply::Success(vec![b"f".to_vec()])
    );
    assert!(!lifecycle.cancellation().is_requested());
}

#[test]
fn native_plugins_tool_uses_linked_callback_without_entering_scala_catalogue() {
    let area = TestArea::new();
    fs::write(area.0.join("source/tool.data"), [4, 5, 6]).unwrap();
    let (vm, lifecycle, bridge) = make_build(&area, "tool", effects());
    let spec = OperationSpec {
        name: "inspect_source".into(),
        wire: isabelle_rs::native_plugins::WireType::Bytes,
        single: true,
        min_arguments: 1,
        max_arguments: 1,
        max_argument_bytes: 1024,
        max_request_bytes: 1024,
        max_response_items: 1,
        max_response_bytes: 1024,
        position: isabelle_rs::native_plugins::SourcePosition {
            file: file!().into(),
            line: line!(),
        },
    };
    let plugin = NativePlugin {
        manifest: PluginManifest {
            identity: "native.source.tool".into(),
            version: VERSION,
            api_version: 1,
            dependencies: vec![],
            effects: PluginEffects { read_source: true, ..PluginEffects::default() },
            services: vec![],
            tools: vec![spec.clone()],
        },
        services: vec![],
        tools: vec![NativeTool { spec, call: read_source_tool }],
    };
    let registry =
        PluginRegistry::register(lifecycle, bridge, budget(), vec![native_core_plugin(), plugin])
            .unwrap();
    assert!(
        !registry
            .session_services(&vm)
            .unwrap()
            .iter()
            .any(|service| service.name == "inspect_source")
    );
    assert_eq!(registry.session_tools(&vm).unwrap()[0].name, "inspect_source");
    assert_eq!(
        registry.invoke_tool(&vm, "inspect_source", &[b"tool.data"]).unwrap(),
        PluginReply::Success(vec![vec![4, 5, 6]])
    );
    assert!(matches!(
        registry.invoke_service(&vm, "inspect_source", &[b"tool.data"]),
        Ok(PluginReply::Fail(_))
    ));
    let PluginReply::Success(catalogue) =
        registry.invoke_service(&vm, "isabelle_tools", &[b""]).unwrap()
    else {
        panic!("registered tool discovery must return a string");
    };
    assert_eq!(catalogue.len(), 1);
    assert!(catalogue[0].starts_with(b"\x05\x06:\x05"));
    assert!(catalogue[0].windows(b"inspect_source".len()).any(|part| part == b"inspect_source"));
    assert!(catalogue[0].windows(file!().len()).any(|part| part == file!().as_bytes()));
}

#[test]
fn native_plugins_root_only_static_links_deny_unimplemented_bibtex_and_doc_services() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "root-static-links", effects());
    let registry = registry(lifecycle.clone(), bridge);
    for name in ["bibtex_check_database", "bibtex_session_entries", "doc_names"] {
        let link = registry
            .linkable_services(&vm)
            .unwrap()
            .iter()
            .find(|service| service.name == name)
            .unwrap();
        assert!(matches!(&link.status, SessionLinkStatus::Disabled { .. }));
        assert!(
            !registry.session_services(&vm).unwrap().iter().any(|service| service.name == name)
        );
        assert!(matches!(registry.invoke_service(&vm, name, &[b""]), Ok(PluginReply::Fail(_))));
    }
    assert!(!lifecycle.cancellation().is_requested());
}

#[test]
fn native_plugins_manifest_effects_narrow_caller_authority() {
    let area = TestArea::new();
    fs::write(area.0.join("source/secret"), b"restricted").unwrap();
    let (vm, lifecycle, bridge) = make_build(&area, "narrow", effects());
    let mut plugin = native_core_plugin();
    plugin.manifest.effects.read_source = false;
    let registry =
        PluginRegistry::register(lifecycle.clone(), bridge, budget(), vec![plugin]).unwrap();
    assert!(matches!(
        registry.invoke_service(&vm, "File.read_source", &[b"secret"]),
        Err(HostFailure::Permission { .. })
    ));
    assert!(lifecycle.cancellation().is_requested());
}

#[test]
fn native_plugins_closed_build_does_not_expose_previous_session_catalogue() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "closed", effects());
    let registry = registry(lifecycle.clone(), Arc::clone(&bridge));
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    lifecycle.try_close().unwrap();
    assert!(registry.session_services(&vm).is_err());
    assert!(registry.invoke_service(&vm, "Base64.encode", &[b"late"]).is_err());
}

#[test]
fn native_plugins_queued_invocation_blocks_close_until_cancellation_acknowledges() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "queued", effects());
    let registry = registry(lifecycle.clone(), Arc::clone(&bridge));
    let id = registry.issue_service_invocation(&vm, "Base64.encode").unwrap();
    assert_eq!(registry.pending_service_invocations().unwrap(), 1);
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Callback), 1);
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    assert_eq!(lifecycle.try_close().unwrap_err().kind, LifecycleErrorKind::PendingWork);
    assert_eq!(registry.cancel_service_invocation(&id).unwrap(), CancelOutcome::CancelledReady);
    assert_eq!(registry.pending_service_invocations().unwrap(), 0);
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Callback), 0);
    lifecycle.try_close().unwrap();
    assert!(registry.invoke_service_managed(&vm, &id, &[b"late"]).unwrap().is_none());
    assert_eq!(registry.cancel_service_invocation(&id).unwrap(), CancelOutcome::AlreadyFinished);
}

#[test]
fn native_plugins_reserved_worker_drains_after_evaluation_and_acknowledges_running_cancel() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "reserved-worker", effects());
    let registry = registry(lifecycle.clone(), Arc::clone(&bridge));
    let id = registry.issue_service_invocation(&vm, "sleep").unwrap();
    bridge.complete().unwrap();
    lifecycle.begin_draining().unwrap();
    std::thread::scope(|scope| {
        let worker_id = id.clone();
        let worker_registry = &registry;
        let worker =
            scope.spawn(move || worker_registry.run_reserved_invocation(&worker_id, &[b"2"]));
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        while lifecycle.pending_counts().unwrap().count(WorkKind::Callback) < 2 {
            assert!(std::time::Instant::now() < deadline, "reserved callback did not start");
            std::thread::yield_now();
        }
        assert_eq!(lifecycle.try_close().unwrap_err().kind, LifecycleErrorKind::PendingWork);
        assert_eq!(registry.cancel_service_invocation(&id).unwrap(), CancelOutcome::Requested);
        assert_eq!(worker.join().unwrap().unwrap(), Some(PluginReply::Interrupt));
    });
    assert_eq!(registry.pending_service_invocations().unwrap(), 0);
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Callback), 0);
    lifecycle.try_close().unwrap();
}

#[test]
fn native_plugins_active_request_limit_rejects_before_issuing_a_second_id() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "request-limit", effects());
    let mut limits = budget();
    limits.max_active_invocations = 1;
    let registry =
        PluginRegistry::register(lifecycle.clone(), bridge, limits, vec![native_core_plugin()])
            .unwrap();
    let first = registry.issue_service_invocation(&vm, "Base64.decode").unwrap();
    assert!(matches!(
        registry.issue_service_invocation(&vm, "Base64.decode"),
        Err(HostFailure::Failed { .. })
    ));
    assert!(lifecycle.cancellation().is_requested());
    assert!(matches!(registry.cancel_service_invocation(&first), Err(HostFailure::Stopped { .. })));
    assert_eq!(registry.pending_service_invocations().unwrap(), 0);
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Callback), 0);
}

fn interrupted_service(
    context: &ServiceContext<'_>,
    _args: &[&[u8]],
    _sink: &mut ResponseSink,
) -> Result<(), ServiceError> {
    context.check_active()?;
    Err(ServiceError::Interrupted)
}

#[test]
fn native_plugins_managed_invocation_preserves_result_tags_and_retires_each_lease() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "managed-tags", effects());
    let mut plugin = native_core_plugin();
    let mut interrupt = plugin.manifest.services[0].clone();
    interrupt.name = "Test.interrupt".into();
    plugin.services.push(NativeService { spec: interrupt.clone(), call: interrupted_service });
    plugin.manifest.services.push(interrupt);
    let mut nullable = plugin
        .manifest
        .services
        .iter()
        .find(|spec| spec.name == "File.read_source")
        .unwrap()
        .clone();
    nullable.name = "File.optional_source".into();
    plugin.services.push(NativeService { spec: nullable.clone(), call: read_optional_source });
    plugin.manifest.services.push(nullable);
    let registry =
        PluginRegistry::register(lifecycle.clone(), bridge, budget(), vec![plugin]).unwrap();
    for (name, input, expected) in [
        ("Base64.encode", b"f".as_slice(), PluginReply::Success(vec![b"Zg==".to_vec()])),
        ("File.optional_source", b"absent".as_slice(), PluginReply::Null),
        ("sleep", b"bad".as_slice(), PluginReply::Error("invalid sleep duration".into())),
        ("Test.interrupt", b"x".as_slice(), PluginReply::Interrupt),
    ] {
        let id = registry.issue_service_invocation(&vm, name).unwrap();
        let reply = registry.invoke_service_managed(&vm, &id, &[input]).unwrap();
        match (reply, expected) {
            (Some(PluginReply::Error(_)), PluginReply::Error(_)) => {},
            (received, expected) => assert_eq!(received, Some(expected)),
        }
        assert!(registry.invoke_service_managed(&vm, &id, &[input]).unwrap().is_none());
        assert_eq!(
            registry.cancel_service_invocation(&id).unwrap(),
            CancelOutcome::AlreadyFinished
        );
        assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Callback), 0);
    }
    let unknown = registry.issue_service_invocation(&vm, "no.such.service").unwrap();
    assert!(matches!(
        registry.invoke_service_managed(&vm, &unknown, &[]),
        Ok(Some(PluginReply::Fail(_)))
    ));
    assert!(!lifecycle.cancellation().is_requested());
}

#[test]
fn native_plugins_stopped_invocation_releases_reserved_callback_without_ml_reply() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "stopped-callback", effects());
    let registry = registry(lifecycle.clone(), bridge);
    let id = registry.issue_service_invocation(&vm, "File.read_source").unwrap();
    vm.request_stop();
    assert!(matches!(
        registry.invoke_service_managed(&vm, &id, &[b"anything"]),
        Err(HostFailure::Stopped { .. })
    ));
    assert_eq!(registry.pending_service_invocations().unwrap(), 0);
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Callback), 0);
}

#[test]
fn native_plugins_foreign_vm_invocation_aborts_pending_lease_and_revokes_build() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "foreign-callback", effects());
    let registry = registry(lifecycle.clone(), bridge);
    let id = registry.issue_service_invocation(&vm, "Base64.decode").unwrap();
    let foreign_vm = Vm::new(isabelle_rs::ml::DenyHost);
    assert!(matches!(
        registry.invoke_service_managed(&foreign_vm, &id, &[b"Zg=="]),
        Err(HostFailure::Permission { .. })
    ));
    assert_eq!(registry.pending_service_invocations().unwrap(), 0);
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Callback), 0);
    assert!(lifecycle.cancellation().is_requested());
}

#[test]
fn native_plugins_foreign_request_id_cannot_cancel_another_registry() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "foreign-request", effects());
    let first = registry(lifecycle.clone(), Arc::clone(&bridge));
    let second = registry(lifecycle.clone(), bridge);
    let id = first.issue_service_invocation(&vm, "Base64.decode").unwrap();
    assert_eq!(second.cancel_service_invocation(&id).unwrap(), CancelOutcome::Unknown);
    assert_eq!(
        first.invoke_service_managed(&vm, &id, &[b"Zg=="]).unwrap(),
        Some(PluginReply::Success(vec![b"f".to_vec()]))
    );
    assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Callback), 0);
}

#[test]
fn native_plugins_zstd_fixed_raw_frame_and_both_codecs_enforce_output_bounds() {
    let area = TestArea::new();
    let (vm, lifecycle, bridge) = make_build(&area, "codecs", effects());
    let mut plugin = native_core_plugin();
    let frame = b"\x28\xb5\x2f\xfd\x20\x03\x19\x00\x00abc";
    let registry = registry(lifecycle.clone(), Arc::clone(&bridge));
    assert_eq!(
        registry.invoke_service(&vm, "Zstd.uncompress", &[frame]).unwrap(),
        PluginReply::Success(vec![b"abc".to_vec()])
    );
    for (compress, uncompress) in
        [("XZ.compress", "XZ.uncompress"), ("Zstd.compress", "Zstd.uncompress")]
    {
        let payload = vec![b'A'; 32 * 1024];
        let PluginReply::Success(mut compressed) =
            registry.invoke_service(&vm, compress, &[&payload]).unwrap()
        else {
            panic!("must compress");
        };
        let encoded = compressed.pop().unwrap();
        assert_eq!(
            registry.invoke_service(&vm, uncompress, &[&encoded]).unwrap(),
            PluginReply::Success(vec![payload])
        );
        assert!(matches!(
            registry.invoke_service(&vm, uncompress, &[&encoded[..encoded.len() / 2]]),
            Ok(PluginReply::Fail(_))
        ));
        let manifest =
            plugin.manifest.services.iter_mut().find(|spec| spec.name == uncompress).unwrap();
        manifest.max_response_bytes = 16;
        let linked =
            plugin.services.iter_mut().find(|service| service.spec.name == uncompress).unwrap();
        linked.spec.max_response_bytes = 16;
    }
    let limited =
        PluginRegistry::register(lifecycle.clone(), bridge, budget(), vec![plugin]).unwrap();
    for (compress, uncompress) in
        [("XZ.compress", "XZ.uncompress"), ("Zstd.compress", "Zstd.uncompress")]
    {
        let payload = vec![b'Z'; 1024];
        let PluginReply::Success(compressed) =
            registry.invoke_service(&vm, compress, &[&payload]).unwrap()
        else {
            panic!("must compress");
        };
        assert!(matches!(
            limited.invoke_service(&vm, uncompress, &[&compressed[0]]),
            Ok(PluginReply::Fail(_))
        ));
    }
    assert_eq!(
        registry.invoke_service(&vm, "Base64.decode", &[b"Zg=="]).unwrap(),
        PluginReply::Success(vec![b"f".to_vec()])
    );
    assert!(!lifecycle.cancellation().is_requested());
}
