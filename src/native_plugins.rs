//! Build-local, explicitly linked Rust services. Plugins are trusted in-process code, not a sandbox.
//! Service results are ordinary bytes; no service or tool receives theorem authority.
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime};

use crate::ml::host::files::{FileHostBridge, HostIoError, RestrictedHost};
use crate::ml::host::lifecycle::{BuildLifecycle, TaskLease, WorkKind};
use crate::ml::{HostFailure, Vm};
use invocations::{
    InvocationError, InvocationFinishError, InvocationTracker, ServiceCancellation, StartOutcome,
};

pub const HOST_API_VERSION: u32 = 1;
const RESERVED_SERVICES: &[&str] = &["Scala.result", "invoke_scala", "cancel_scala"];
const RESERVED_TOOLS: &[&str] = &["isabelle-build", "isabelle-rs"];
const SERVICE_SLEEP_CHECK_INTERVAL: Duration = Duration::from_millis(10);
const MAX_SERVICE_NAME_BYTES: usize = 256;

/// Exact linked-code version, independent of build or source-file identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PluginVersion {
    pub major: u32,
    pub minor: u32,
    pub patch: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactDependency {
    pub identity: String,
    pub version: PluginVersion,
}

/// Requests can only narrow the supervisor's existing caller/manifest/phase authority.
#[derive(Clone, Debug, Default)]
pub struct PluginEffects {
    pub read_source: bool,
    pub read_resources: BTreeSet<String>,
    pub read_clock: bool,
    pub sleep: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WireType {
    String,
    Bytes,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourcePosition {
    pub file: String,
    pub line: u32,
}

/// Every operation declares explicit cardinality, wire type and pre-allocation budgets.
#[derive(Clone, Debug)]
pub struct OperationSpec {
    pub name: String,
    pub wire: WireType,
    pub single: bool,
    pub min_arguments: usize,
    pub max_arguments: usize,
    pub max_argument_bytes: usize,
    pub max_request_bytes: usize,
    pub max_response_items: usize,
    pub max_response_bytes: usize,
    pub position: SourcePosition,
}

pub type ServiceFn =
    fn(&ServiceContext<'_>, &[&[u8]], &mut ResponseSink) -> Result<(), ServiceError>;
pub type ToolFn = fn(&ServiceContext<'_>, &[&[u8]], &mut ResponseSink) -> Result<(), ServiceError>;

pub struct NativeService {
    pub spec: OperationSpec,
    pub call: ServiceFn,
}
pub struct NativeTool {
    pub spec: OperationSpec,
    pub call: ToolFn,
}

pub struct PluginManifest {
    pub identity: String,
    pub version: PluginVersion,
    pub api_version: u32,
    pub dependencies: Vec<ExactDependency>,
    pub effects: PluginEffects,
    pub services: Vec<OperationSpec>,
    pub tools: Vec<OperationSpec>,
}

/// Constructed by explicit Rust linkage, never discovered from a filesystem or classpath.
pub struct NativePlugin {
    pub manifest: PluginManifest,
    pub services: Vec<NativeService>,
    pub tools: Vec<NativeTool>,
}

#[derive(Clone, Copy, Debug)]
pub struct RegistryBudget {
    pub max_argument_bytes: usize,
    pub max_request_bytes: usize,
    pub max_response_items: usize,
    pub max_response_bytes: usize,
    pub max_active_invocations: usize,
}

#[derive(Debug, thiserror::Error)]
pub enum RegistryError {
    /// The bridge belongs to another build, so none of its services may be installed.
    #[error("register plugins: file host belongs to a different build")]
    WrongBuild,
    /// A manifest's identity, dependency, declaration, signature or budget is invalid.
    #[error("register plugins: {0}")]
    Invalid(String),
}

/// Ordinary Scala.result tags; only `HostFailure` is allowed to revoke the build.
#[derive(Debug, PartialEq, Eq)]
pub enum PluginReply {
    Null,
    Success(Vec<Vec<u8>>),
    Error(String),
    Fail(String),
    Interrupt,
}

#[derive(Debug, thiserror::Error)]
pub enum ServiceError {
    #[error("service returned Null")]
    Null,
    #[error("service ERROR: {0}")]
    Error(String),
    #[error("service Fail: {0}")]
    Fail(String),
    #[error("service interrupted")]
    Interrupted,
    #[error("host effect failed: {0}")]
    Host(#[from] HostIoError),
}

/// Only completed registration produces metadata for Resources.init_session.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SessionService {
    pub name: String,
    pub single: bool,
    pub bytes: bool,
    pub position: SourcePosition,
}

/// Static antiquotation lookup is separate from the callable service catalogue.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SessionLinkStatus {
    Available,
    Disabled { reason: &'static str },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SessionLink {
    pub name: String,
    pub single: bool,
    pub bytes: bool,
    pub position: SourcePosition,
    pub status: SessionLinkStatus,
}

/// Public discovery data for actual linked tools; there is no PATH search.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SessionTool {
    pub name: String,
    pub position: SourcePosition,
}

struct Entry {
    plugin: usize,
    spec: OperationSpec,
    call: ServiceFn,
}

/// The sole public registry: immutable, bound to one lifecycle and its supervised file bridge.
pub struct PluginRegistry {
    lifecycle: BuildLifecycle,
    bridge: Arc<FileHostBridge>,
    plugins: Vec<PluginEffects>,
    services: BTreeMap<String, Entry>,
    tools: BTreeMap<String, Entry>,
    session_services: Vec<SessionService>,
    linkable_services: Vec<SessionLink>,
    session_tools: Vec<SessionTool>,
    tools_yxml: Vec<u8>,
    invocations: InvocationTracker,
}

impl PluginRegistry {
    pub fn register(
        lifecycle: BuildLifecycle,
        bridge: Arc<FileHostBridge>,
        budget: RegistryBudget,
        plugins: Vec<NativePlugin>,
    ) -> Result<Self, RegistryError> {
        if !bridge.shares_build(&lifecycle) {
            return Err(RegistryError::WrongBuild);
        }
        if budget.max_argument_bytes == 0
            || budget.max_request_bytes == 0
            || budget.max_response_items == 0
            || budget.max_response_bytes == 0
            || budget.max_active_invocations == 0
        {
            return Err(invalid("incomplete trusted caller resource budget"));
        }
        validate_manifests(&plugins, budget)?;
        let mut services = BTreeMap::new();
        let mut tools = BTreeMap::new();
        let mut session_services = Vec::new();
        let mut session_tools = Vec::new();
        let mut effects = Vec::with_capacity(plugins.len());
        for (index, plugin) in plugins.into_iter().enumerate() {
            effects.push(plugin.manifest.effects);
            for service in plugin.services {
                session_services.push(SessionService {
                    name: service.spec.name.clone(),
                    single: service.spec.single,
                    bytes: service.spec.wire == WireType::Bytes,
                    position: service.spec.position.clone(),
                });
                services.insert(
                    service.spec.name.clone(),
                    Entry { plugin: index, spec: service.spec, call: service.call },
                );
            }
            for tool in plugin.tools {
                session_tools.push(SessionTool {
                    name: tool.spec.name.clone(),
                    position: tool.spec.position.clone(),
                });
                tools.insert(
                    tool.spec.name.clone(),
                    Entry { plugin: index, spec: tool.spec, call: tool.call },
                );
            }
        }
        session_services.sort_by(|a, b| a.name.cmp(&b.name));
        session_tools.sort_by(|a, b| a.name.cmp(&b.name));
        let tools_yxml = if let Some(entry) = services.get("isabelle_tools") {
            builtins::encode_tools_yxml(&session_tools, entry.spec.max_response_bytes)?
        } else {
            Vec::new()
        };
        let mut linkable_services: Vec<_> = session_services
            .iter()
            .map(|service| SessionLink {
                name: service.name.clone(),
                single: service.single,
                bytes: service.bytes,
                position: service.position.clone(),
                status: SessionLinkStatus::Available,
            })
            .chain(disabled::disabled_links())
            .collect();
        linkable_services.sort_by(|a, b| a.name.cmp(&b.name));
        Ok(Self {
            lifecycle,
            bridge,
            plugins: effects,
            services,
            tools,
            session_services,
            linkable_services,
            session_tools,
            tools_yxml,
            invocations: InvocationTracker::new(budget.max_active_invocations),
        })
    }

    /// Returns the exact registered service table only while this VM/build is live.
    pub fn session_services(&self, vm: &Vm) -> Result<&[SessionService], HostFailure> {
        self.check_live(vm)?;
        Ok(&self.session_services)
    }
    /// Compile-time lookup for fixed ROOT antiquotations; disabled names never
    /// enter `session_services` and cannot authorize a runtime invocation.
    pub fn linkable_services(&self, vm: &Vm) -> Result<&[SessionLink], HostFailure> {
        self.check_live(vm)?;
        Ok(&self.linkable_services)
    }

    /// Discovery for explicitly linked Rust tools, without PATH scanning.
    pub fn session_tools(&self, vm: &Vm) -> Result<&[SessionTool], HostFailure> {
        self.check_live(vm)?;
        Ok(&self.session_tools)
    }

    pub fn invoke_service(
        &self,
        vm: &Vm,
        name: &str,
        args: &[&[u8]],
    ) -> Result<PluginReply, HostFailure> {
        self.check_live(vm)?;
        self.invoke_named_service(vm, name, args, None)
    }

    /// Native tools use the same explicit registration and build lease; they are not CLI search.
    pub fn invoke_tool(
        &self,
        vm: &Vm,
        name: &str,
        args: &[&[u8]],
    ) -> Result<PluginReply, HostFailure> {
        self.check_live(vm)?;
        let Some(entry) = self.tools.get(name) else {
            return Ok(PluginReply::Fail(format!("Unknown native tool: {name:?}")));
        };
        self.invoke_entry(vm, entry, args, None)
    }
    /// Reserve a same-build Callback lease before publishing a protocol request ID.
    /// The caller must dispatch or cancel it; pending IDs block build close.
    pub fn issue_service_invocation(
        &self,
        vm: &Vm,
        name: &str,
    ) -> Result<InvocationId, HostFailure> {
        self.check_live(vm)?;
        if name.len() > MAX_SERVICE_NAME_BYTES {
            return Err(
                self.fail_request("issue plugin service", "service name exceeds byte limit")
            );
        }
        let lease = self
            .bridge
            .reserve_plugin_task(vm, WorkKind::Callback, name)
            .map_err(|error| classify_host_error("issue plugin service", error))?;
        let mut reserved = Some(lease);
        match self.invocations.issue(name, &mut reserved) {
            Ok(id) => Ok(id),
            Err(error) => {
                if let Some(lease) = reserved
                    && let Err(cleanup) = lease.complete()
                {
                    tracing::error!(error = %cleanup, "cannot complete failed request reservation");
                }
                Err(self.fail_request("issue plugin service", error))
            },
        }
    }

    /// Unknown IDs have the original harmless cancel semantics; a queued
    /// cancellation completes its lease before this function returns.
    pub fn cancel_service_invocation(
        &self,
        id: &InvocationId,
    ) -> Result<CancelOutcome, HostFailure> {
        if !self.invocations.owns(id) {
            return Ok(CancelOutcome::Unknown);
        }
        let request = self
            .invocations
            .lookup(id)
            .map_err(|error| self.fail_request("cancel plugin service", error))?;
        let Some(request) = request else {
            return Ok(CancelOutcome::AlreadyFinished);
        };
        match request.cancel() {
            Ok(CancelOutcome::CancelledReady) => {
                self.invocations
                    .retire(id)
                    .map_err(|error| self.fail_request("cancel plugin service", error))?;
                Ok(CancelOutcome::CancelledReady)
            },
            Ok(outcome) => Ok(outcome),
            Err(error) => {
                let failure = self.classify_request_finish("cancel plugin service", error);
                self.abort_request(id, &request, None);
                Err(failure)
            },
        }
    }

    /// `None` means a duplicate or late callback: never send a second Scala.result.
    /// A running cancellation resolves to tag 4 only after both child leases complete.
    pub fn invoke_service_managed(
        &self,
        vm: &Vm,
        id: &InvocationId,
        args: &[&[u8]],
    ) -> Result<Option<PluginReply>, HostFailure> {
        if !self.invocations.owns(id) {
            return Err(self.fail_request("invoke plugin service", InvocationError::Unknown));
        }
        if !self.lifecycle.matches_stop_handle(&vm.stop_handle()) {
            let failure = match self.check_live(vm) {
                Err(error) => error,
                Ok(()) => self
                    .fail_request("invoke plugin service", "foreign VM authenticated unexpectedly"),
            };
            if let Ok(Some(request)) = self.invocations.lookup(id) {
                self.abort_request(id, &request, None);
            }
            return Err(failure);
        }
        self.run_reserved_invocation(id, args)
    }

    /// Invoke a request that was authenticated by `issue_service_invocation`.
    /// The opaque ID carries the reserved same-build lease: no VM crosses threads.
    pub fn run_reserved_invocation(
        &self,
        id: &InvocationId,
        args: &[&[u8]],
    ) -> Result<Option<PluginReply>, HostFailure> {
        if !self.invocations.owns(id) {
            return Err(self.fail_request("invoke reserved service", InvocationError::Unknown));
        }
        let request = self
            .invocations
            .lookup(id)
            .map_err(|error| self.fail_request("invoke reserved service", error))?;
        let Some(request) = request else {
            return Ok(None);
        };
        let lease = match request.start() {
            Ok(StartOutcome::CancelledReady) | Err(InvocationError::AlreadyStarted) => {
                return Ok(None);
            },
            Ok(StartOutcome::Running(lease)) => lease,
            Err(error) => {
                let failure = self.fail_request("invoke reserved service", error);
                self.abort_request(id, &request, None);
                return Err(failure);
            },
        };
        let result =
            self.invoke_reserved_named_service(&lease, &request.name, args, Some(&request));
        self.finish_request(id, &request, lease, result)
    }

    pub fn pending_service_invocations(&self) -> Result<usize, HostFailure> {
        self.invocations
            .pending_count()
            .map_err(|error| self.fail_request("inspect plugin tasks", error))
    }

    fn invoke_named_service(
        &self,
        vm: &Vm,
        name: &str,
        args: &[&[u8]],
        cancellation: Option<&ServiceCancellation>,
    ) -> Result<PluginReply, HostFailure> {
        let Some(entry) = self.services.get(name) else {
            return Ok(self.missing_service(name));
        };
        self.invoke_entry(vm, entry, args, cancellation)
    }

    fn invoke_reserved_named_service(
        &self,
        reservation: &TaskLease,
        name: &str,
        args: &[&[u8]],
        cancellation: Option<&ServiceCancellation>,
    ) -> Result<PluginReply, HostFailure> {
        self.lifecycle.check_task(reservation).map_err(|error| HostFailure::Stopped {
            cause: format!("check {name} reservation: {error}"),
        })?;
        self.lifecycle.cancellation().check().map_err(|error| HostFailure::Stopped {
            cause: format!("check {name} cancellation: {error}"),
        })?;
        let Some(entry) = self.services.get(name) else {
            return Ok(self.missing_service(name));
        };
        if let Err(message) = validate_request(&entry.spec, args) {
            return Ok(PluginReply::Fail(message));
        }
        self.bridge
            .with_reserved_plugin_task(reservation, WorkKind::Callback, name, |host, lease| {
                self.call_entry(host, lease, entry, args, cancellation)
            })
            .map_err(|error| classify_host_error(name, error))
    }

    fn missing_service(&self, name: &str) -> PluginReply {
        if let Some(reason) = disabled::is_disabled(name) {
            PluginReply::Fail(format!("Disabled native service {name}: {reason}"))
        } else {
            PluginReply::Fail(format!("Unknown Isabelle/Scala function: {name:?}"))
        }
    }

    fn abort_request(
        &self,
        id: &InvocationId,
        request: &ServiceCancellation,
        lease: Option<TaskLease>,
    ) {
        match request.abort(lease) {
            Ok(false) => return,
            Ok(true) => {},
            Err(error) => {
                tracing::error!(error = %error, "cannot complete aborted plugin reservation")
            },
        }
        if let Err(error) = self.invocations.retire(id) {
            tracing::error!(error = %error, "cannot retire aborted plugin request");
        }
    }

    fn finish_request(
        &self,
        id: &InvocationId,
        request: &ServiceCancellation,
        lease: TaskLease,
        result: Result<PluginReply, HostFailure>,
    ) -> Result<Option<PluginReply>, HostFailure> {
        let reply = match result {
            Ok(reply) => match request.settle(reply) {
                Ok(reply) => reply,
                Err(error) => {
                    let failure = self.classify_request_finish("finish plugin service", error);
                    self.abort_request(id, request, Some(lease));
                    return Err(failure);
                },
            },
            Err(error) => {
                self.abort_request(id, request, Some(lease));
                return Err(error);
            },
        };
        if let Err(error) = self.invocations.retire(id) {
            let failure = self.fail_request("finish plugin service", error);
            if let Err(cleanup) = lease.complete() {
                tracing::error!(error = %cleanup, "cannot complete untracked plugin reservation");
            }
            return Err(failure);
        }
        lease.complete().map_err(|source| HostFailure::Stopped {
            cause: format!("complete plugin service reservation: {source}"),
        })?;
        self.lifecycle.cancellation().check().map_err(|error| HostFailure::Stopped {
            cause: format!("finish plugin service: {error}"),
        })?;
        Ok(Some(reply))
    }

    fn classify_request_finish(
        &self,
        operation: &str,
        error: InvocationFinishError,
    ) -> HostFailure {
        match error {
            InvocationFinishError::Lifecycle(source) => {
                HostFailure::Stopped { cause: format!("{operation}: {source}") }
            },
            InvocationFinishError::State(source) => self.fail_request(operation, source),
        }
    }

    fn check_live(&self, vm: &Vm) -> Result<(), HostFailure> {
        self.bridge.check_vm(vm).map_err(|error| classify_host_error("inspect plugins", error))?;
        self.lifecycle
            .cancellation()
            .check()
            .map_err(|error| HostFailure::Stopped { cause: error.to_string() })
    }

    fn invoke_entry(
        &self,
        vm: &Vm,
        entry: &Entry,
        args: &[&[u8]],
        cancellation: Option<&ServiceCancellation>,
    ) -> Result<PluginReply, HostFailure> {
        if let Err(message) = validate_request(&entry.spec, args) {
            return Ok(PluginReply::Fail(message));
        }
        self.bridge
            .with_plugin_task(vm, WorkKind::Callback, &entry.spec.name, |host, lease| {
                self.call_entry(host, lease, entry, args, cancellation)
            })
            .map_err(|error| classify_host_error(&entry.spec.name, error))
    }

    fn call_entry(
        &self,
        host: &RestrictedHost,
        lease: &TaskLease,
        entry: &Entry,
        args: &[&[u8]],
        cancellation: Option<&ServiceCancellation>,
    ) -> Result<PluginReply, HostIoError> {
        let context = ServiceContext {
            host,
            lease,
            effects: &self.plugins[entry.plugin],
            max_read_bytes: entry.spec.max_response_bytes,
            tools_yxml: &self.tools_yxml,
            cancellation,
        };
        let mut response = ResponseSink::new(&entry.spec);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            (entry.call)(&context, args, &mut response)
        }))
        .map_err(|_| HostIoError::Io {
            operation: "invoke trusted plugin",
            path: Path::new(&entry.spec.name).to_path_buf(),
            source: std::io::Error::other("trusted Rust plugin callback panicked"),
        })?;
        let result = match result {
            Err(ServiceError::Host(error)) if !error.is_ordinary_ml_io() => return Err(error),
            other => other,
        };
        match context.check_active() {
            Ok(()) => {},
            Err(ServiceError::Interrupted) => return Ok(PluginReply::Interrupt),
            Err(ServiceError::Host(error)) => return Err(error),
            Err(error) => {
                return Err(HostIoError::Io {
                    operation: "check plugin task",
                    path: Path::new(&entry.spec.name).to_path_buf(),
                    source: std::io::Error::other(error),
                });
            },
        }
        match result {
            Ok(()) if entry.spec.single && response.items.len() != 1 => {
                Ok(PluginReply::Fail(format!("{}: expected one result", entry.spec.name)))
            },
            Ok(()) => Ok(PluginReply::Success(response.finish())),
            Err(ServiceError::Null) => Ok(PluginReply::Null),
            Err(ServiceError::Error(message)) => Ok(PluginReply::Error(message)),
            Err(ServiceError::Fail(message)) => Ok(PluginReply::Fail(message)),
            Err(ServiceError::Interrupted) => Ok(PluginReply::Interrupt),
            Err(ServiceError::Host(error)) => Ok(PluginReply::Fail(error.to_string())),
        }
    }

    fn fail_request(&self, operation: &str, error: impl std::fmt::Display) -> HostFailure {
        let cause = error.to_string();
        if let Err(record_error) = self.lifecycle.cancel(cause.clone()) {
            tracing::error!(error = %record_error, "cannot record fatal plugin request failure");
        }
        HostFailure::Failed {
            operation: operation.to_owned(),
            resource: "build-local service request".into(),
            cause,
        }
    }
}
impl Drop for PluginRegistry {
    fn drop(&mut self) {
        let pending = match self.invocations.pending_count() {
            Ok(pending) => pending,
            Err(error) => {
                tracing::error!(error = %error, "cannot inspect plugin requests during teardown");
                1
            },
        };
        if pending == 0 {
            return;
        }
        if let Err(error) =
            self.lifecycle.cancel("plugin registry dropped with pending requests".into())
        {
            tracing::error!(error = %error, "cannot cancel abandoned plugin requests");
        }
        if let Err(error) = self.invocations.abort_all() {
            tracing::error!(error = %error, "cannot explicitly finish abandoned plugin requests");
        }
    }
}
pub use invocations::{CancelOutcome, InvocationId};

fn classify_host_error(operation: &str, error: HostIoError) -> HostFailure {
    let resource = error.to_string();
    match error {
        HostIoError::Lifecycle { .. } | HostIoError::LeaseCompleted => {
            HostFailure::Stopped { cause: resource }
        },
        HostIoError::Permission { .. }
        | HostIoError::InvalidPath(_)
        | HostIoError::PathLimit { .. } => HostFailure::Permission {
            operation: operation.to_owned(),
            resource,
            cause: "capability denied".into(),
        },
        _ => HostFailure::Failed {
            operation: operation.to_owned(),
            resource,
            cause: "plugin host effect failed".into(),
        },
    }
}

fn validate_manifests(
    plugins: &[NativePlugin],
    budget: RegistryBudget,
) -> Result<(), RegistryError> {
    let mut indices = BTreeMap::new();
    let mut operation_names = BTreeSet::new();
    for (index, plugin) in plugins.iter().enumerate() {
        let manifest = &plugin.manifest;
        if !valid_name(&manifest.identity)
            || indices.insert(manifest.identity.clone(), index).is_some()
        {
            return Err(invalid(format!("invalid or duplicate plugin {}", manifest.identity)));
        }
        if manifest.api_version != HOST_API_VERSION {
            return Err(invalid(format!(
                "{}: unsupported host API {}",
                manifest.identity, manifest.api_version
            )));
        }
        validate_declared(&manifest.services, &plugin.services, &mut operation_names, budget)?;
        validate_declared(&manifest.tools, &plugin.tools, &mut operation_names, budget)?;
    }
    let mut visited = vec![0u8; plugins.len()];
    for index in 0..plugins.len() {
        visit_dependency(index, plugins, &indices, &mut visited)?;
    }
    Ok(())
}

fn validate_declared<T: RegisteredOperation>(
    declared: &[OperationSpec],
    registered: &[T],
    seen: &mut BTreeSet<String>,
    budget: RegistryBudget,
) -> Result<(), RegistryError> {
    let mut names = BTreeSet::new();
    for spec in declared {
        validate_spec(spec, budget)?;
        if RESERVED_SERVICES.contains(&spec.name.as_str())
            || RESERVED_TOOLS.contains(&spec.name.as_str())
            || disabled::is_disabled(&spec.name).is_some()
            || spec.name.starts_with("Native.")
            || !seen.insert(spec.name.clone())
            || !names.insert(spec.name.clone())
        {
            return Err(invalid(format!("duplicate or reserved operation {}", spec.name)));
        }
    }
    let actual: BTreeSet<_> =
        registered.iter().map(|operation| operation.spec().to_owned()).collect();
    if actual.len() != registered.len() || actual.len() != names.len() || actual != names {
        return Err(invalid("declared and linked operations differ"));
    }
    for operation in registered {
        let Some(spec) = declared.iter().find(|spec| spec.name == operation.spec()) else {
            return Err(invalid("undeclared operation"));
        };
        if !same_spec(spec, operation.declaration()) {
            return Err(invalid(format!("{}: signature differs from manifest", spec.name)));
        }
    }
    Ok(())
}

trait RegisteredOperation {
    fn spec(&self) -> &str;
    fn declaration(&self) -> &OperationSpec;
}
impl RegisteredOperation for NativeService {
    fn spec(&self) -> &str {
        &self.spec.name
    }
    fn declaration(&self) -> &OperationSpec {
        &self.spec
    }
}
impl RegisteredOperation for NativeTool {
    fn spec(&self) -> &str {
        &self.spec.name
    }
    fn declaration(&self) -> &OperationSpec {
        &self.spec
    }
}

fn same_spec(a: &OperationSpec, b: &OperationSpec) -> bool {
    a.name == b.name
        && a.wire == b.wire
        && a.single == b.single
        && a.min_arguments == b.min_arguments
        && a.max_arguments == b.max_arguments
        && a.max_argument_bytes == b.max_argument_bytes
        && a.max_request_bytes == b.max_request_bytes
        && a.max_response_items == b.max_response_items
        && a.max_response_bytes == b.max_response_bytes
        && a.position == b.position
}

fn validate_spec(spec: &OperationSpec, budget: RegistryBudget) -> Result<(), RegistryError> {
    if !valid_name(&spec.name)
        || spec.name.len() > MAX_SERVICE_NAME_BYTES
        || spec.position.file.is_empty()
        || spec.position.line == 0
        || spec.max_arguments == 0
        || spec.min_arguments > spec.max_arguments
        || (spec.single
            && (spec.min_arguments != 1 || spec.max_arguments != 1 || spec.max_response_items != 1))
        || spec.max_argument_bytes == 0
        || spec.max_request_bytes == 0
        || spec.max_response_items == 0
        || spec.max_response_bytes == 0
        || spec.max_argument_bytes > spec.max_request_bytes
        || spec.max_argument_bytes > budget.max_argument_bytes
        || spec.max_request_bytes > budget.max_request_bytes
        || spec.max_response_items > budget.max_response_items
        || spec.max_response_bytes > budget.max_response_bytes
    {
        return Err(invalid(format!("{}: incomplete signature or budget", spec.name)));
    }
    Ok(())
}

fn visit_dependency(
    index: usize,
    plugins: &[NativePlugin],
    indices: &BTreeMap<String, usize>,
    visited: &mut [u8],
) -> Result<(), RegistryError> {
    if visited[index] == 1 {
        return Err(invalid(format!("dependency cycle at {}", plugins[index].manifest.identity)));
    }
    if visited[index] == 2 {
        return Ok(());
    }
    visited[index] = 1;
    let manifest = &plugins[index].manifest;
    let mut direct = BTreeSet::new();
    for dependency in &manifest.dependencies {
        if !direct.insert(&dependency.identity) {
            return Err(invalid(format!(
                "{}: duplicate dependency {}",
                manifest.identity, dependency.identity
            )));
        }
        let Some(&parent) = indices.get(&dependency.identity) else {
            return Err(invalid(format!(
                "{}: missing dependency {}",
                manifest.identity, dependency.identity
            )));
        };
        if plugins[parent].manifest.version != dependency.version {
            return Err(invalid(format!(
                "{}: wrong dependency version {}",
                manifest.identity, dependency.identity
            )));
        }
        visit_dependency(parent, plugins, indices, visited)?;
    }
    visited[index] = 2;
    Ok(())
}

fn valid_name(name: &str) -> bool {
    !name.is_empty()
        && name.split('.').all(|part| {
            !part.is_empty()
                && part
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'-')
        })
}
fn invalid(message: impl Into<String>) -> RegistryError {
    RegistryError::Invalid(message.into())
}

fn validate_request(spec: &OperationSpec, args: &[&[u8]]) -> Result<(), String> {
    if args.len() < spec.min_arguments || args.len() > spec.max_arguments {
        return Err(format!("{}: incorrect argument count", spec.name));
    }
    let mut remaining = spec.max_request_bytes;
    for arg in args {
        if arg.len() > spec.max_argument_bytes || arg.len() > remaining {
            return Err(format!("{}: request byte budget exceeded", spec.name));
        }
        remaining -= arg.len();
        if spec.wire == WireType::String && std::str::from_utf8(arg).is_err() {
            return Err(format!("{}: expected UTF-8 string", spec.name));
        }
    }
    Ok(())
}

/// Bounded response writer: checks before allocating or copying any response bytes.
pub struct ResponseSink {
    wire: WireType,
    max_items: usize,
    remaining: usize,
    items: Vec<Vec<u8>>,
}
impl ResponseSink {
    fn new(spec: &OperationSpec) -> Self {
        Self {
            wire: spec.wire,
            max_items: spec.max_response_items,
            remaining: spec.max_response_bytes,
            items: Vec::new(),
        }
    }
    pub fn push(&mut self, bytes: &[u8]) -> Result<(), ServiceError> {
        self.validate(bytes)?;
        self.remaining -= bytes.len();
        self.items.push(bytes.to_vec());
        Ok(())
    }
    pub fn push_owned(&mut self, bytes: Vec<u8>) -> Result<(), ServiceError> {
        self.validate(&bytes)?;
        self.remaining -= bytes.len();
        self.items.push(bytes);
        Ok(())
    }
    fn validate(&self, bytes: &[u8]) -> Result<(), ServiceError> {
        if self.items.len() >= self.max_items || bytes.len() > self.remaining {
            return Err(ServiceError::Fail("response byte/item budget exceeded".into()));
        }
        if self.wire == WireType::String && std::str::from_utf8(bytes).is_err() {
            return Err(ServiceError::Fail("response is not UTF-8".into()));
        }
        Ok(())
    }
    fn finish(self) -> Vec<Vec<u8>> {
        self.items
    }
}

/// Only mediated effects, never VM internals, mutable kernel owners or publisher.
pub struct ServiceContext<'a> {
    host: &'a RestrictedHost,
    lease: &'a TaskLease,
    effects: &'a PluginEffects,
    max_read_bytes: usize,
    tools_yxml: &'a [u8],
    cancellation: Option<&'a invocations::ServiceCancellation>,
}
impl ServiceContext<'_> {
    /// Immutable YXML discovery payload made only from explicitly registered tools.
    pub fn tool_catalog_yxml(&self) -> &[u8] {
        self.tools_yxml
    }

    /// Check both the build's non-catchable stop and this call's ordinary cancellation.
    pub fn check_active(&self) -> Result<(), ServiceError> {
        self.lease.check_active().map_err(|source| {
            ServiceError::Host(HostIoError::Lifecycle { operation: "check plugin task", source })
        })?;
        if let Some(cancel) = self.cancellation {
            let is_cancelled = cancel.is_cancelled().map_err(|error| {
                ServiceError::Host(HostIoError::Io {
                    operation: "check plugin cancellation",
                    path: Path::new("request state").to_path_buf(),
                    source: std::io::Error::other(error),
                })
            })?;
            if is_cancelled {
                return Err(ServiceError::Interrupted);
            }
        }
        Ok(())
    }

    pub fn read_clock(&self) -> Result<SystemTime, ServiceError> {
        self.require(self.effects.read_clock, "read clock")?;
        let now = self.host.read_clock(self.lease)?;
        self.check_active()?;
        Ok(now)
    }
    pub fn sleep(&self, duration: Duration) -> Result<(), ServiceError> {
        self.require(self.effects.sleep, "sleep")?;
        let start = Instant::now();
        loop {
            self.check_active()?;
            let remaining = duration.saturating_sub(start.elapsed());
            self.host.sleep(self.lease, remaining.min(SERVICE_SLEEP_CHECK_INTERVAL))?;
            self.check_active()?;
            if start.elapsed() >= duration {
                return Ok(());
            }
        }
    }
    pub fn read_source(&self, path: &Path, limit: usize) -> Result<Vec<u8>, ServiceError> {
        self.require(self.effects.read_source, "read source")?;
        let bytes =
            self.host.read_source_bounded(self.lease, path, limit.min(self.max_read_bytes))?;
        self.check_active()?;
        Ok(bytes)
    }
    pub fn read_resource(
        &self,
        root: &str,
        path: &Path,
        limit: usize,
    ) -> Result<Vec<u8>, ServiceError> {
        self.require(self.effects.read_resources.contains(root), "read resource")?;
        let bytes = self.host.read_resource_bounded(
            self.lease,
            root,
            path,
            limit.min(self.max_read_bytes),
        )?;
        self.check_active()?;
        Ok(bytes)
    }
    /// One real concurrent task under this call's root. Scoped joining prevents a
    /// response, lease completion, or build close while the worker can still run.
    pub fn run_future<T: Send>(
        &self,
        operation: &str,
        work: impl FnOnce(&ServiceContext<'_>) -> Result<T, ServiceError> + Send,
    ) -> Result<T, ServiceError> {
        let child = self.lease.start_child(WorkKind::Future, operation).map_err(|source| {
            ServiceError::Host(HostIoError::Lifecycle { operation: "start plugin future", source })
        })?;
        let child_ref = &child;
        let outcome = std::thread::scope(|scope| {
            let handle = std::thread::Builder::new()
                .spawn_scoped(scope, move || {
                    let context = ServiceContext {
                        host: self.host,
                        lease: child_ref,
                        effects: self.effects,
                        max_read_bytes: self.max_read_bytes,
                        tools_yxml: self.tools_yxml,
                        cancellation: self.cancellation,
                    };
                    work(&context)
                })
                .map_err(|source| {
                    ServiceError::Host(HostIoError::Io {
                        operation: "spawn plugin future",
                        path: Path::new(operation).to_path_buf(),
                        source,
                    })
                })?;
            handle.join().map_err(|_| {
                ServiceError::Host(HostIoError::Io {
                    operation: "join plugin future",
                    path: Path::new(operation).to_path_buf(),
                    source: std::io::Error::other("trusted plugin worker panicked"),
                })
            })?
        });
        let completion = child.complete().map_err(|source| {
            ServiceError::Host(HostIoError::Lifecycle {
                operation: "complete plugin future",
                source,
            })
        });
        match outcome {
            Ok(value) => completion.map(|()| value),
            Err(error) => {
                if let Err(completion_error) = completion {
                    tracing::error!(error = %completion_error, "plugin future completion failed after service error");
                }
                Err(error)
            },
        }
    }
    fn require(&self, allowed: bool, operation: &'static str) -> Result<(), ServiceError> {
        self.check_active()?;
        if allowed {
            return Ok(());
        }
        Err(ServiceError::Host(HostIoError::Permission {
            operation,
            path: Path::new("plugin declaration").to_path_buf(),
            reason: "plugin did not declare this effect",
        }))
    }
}

pub mod builtins;
mod codecs;
mod disabled;
mod invocations;
