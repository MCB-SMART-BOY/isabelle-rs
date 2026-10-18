//! Native Standard ML execution boundary. This module has no theorem authority.
mod basis;
mod bootstrap;
mod environment;
mod eval;
mod gc;
pub mod host;
mod lexer;
mod native_context;
mod native_sha1;
mod parser;
mod pattern;
mod static_module;
mod syntax;
mod types;
mod value;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::{Rc, Weak};
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicBool, AtomicU64, Ordering},
};

pub use bootstrap::{
    LoadedMlSource, ML_ENVIRONMENT_PURPOSE, RootContextProgress, RootPrefixFailure,
    RootPrefixProgress,
};
pub use native_sha1::NativeSha1Transformation;
use syntax::SourceLocation;
pub use syntax::{Declaration, Expr, ModuleExpr, Pattern, SignatureExpr, Specification, TypeExpr};
pub use types::{Type, TypeScheme};
pub use value::{HostObjectId, NativeFunctionId, Value, WeakValue};

// A process-wide monotonically increasing domain prevents VM-local indices crossing runtimes.
static NEXT_RUNTIME_ID: AtomicU64 = AtomicU64::new(1);

struct StopDomain {
    requested: AtomicBool,
    // Serializes external cancellation with the final publication rename.
    cancelled: Mutex<bool>,
}

#[derive(Clone)]
pub struct StopHandle(Arc<StopDomain>);

#[derive(Clone, Copy, Debug)]
pub(crate) enum StopBarrierError {
    /// External cancellation won the publication boundary.
    Cancelled,
    /// A panic poisoned the boundary; publication must fail closed.
    Poisoned,
}

impl StopHandle {
    fn new() -> Self {
        Self(Arc::new(StopDomain {
            requested: AtomicBool::new(false),
            cancelled: Mutex::new(false),
        }))
    }

    pub fn request_stop(&self) {
        // A poisoned gate remains poisoned, so publication still refuses it.
        let mut cancelled = self.0.cancelled.lock().unwrap_or_else(|error| error.into_inner());
        *cancelled = true;
        self.0.requested.store(true, Ordering::Release);
    }

    pub(crate) fn shares_domain(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }

    pub(crate) fn is_stop_requested(&self) -> bool {
        self.0.requested.load(Ordering::Acquire)
    }

    pub(crate) fn revoke_for_close(&self) {
        self.0.requested.store(true, Ordering::Release);
    }

    pub(crate) fn with_publication_guard<T>(
        &self,
        publish: impl FnOnce() -> T,
    ) -> Result<T, StopBarrierError> {
        let cancelled = self.0.cancelled.lock().map_err(|_| StopBarrierError::Poisoned)?;
        if *cancelled {
            return Err(StopBarrierError::Cancelled);
        }
        Ok(publish())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Span {
    pub source_name: String,
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn new(source_name: &str, start: usize, end: usize) -> Self {
        Self { source_name: source_name.to_owned(), start, end }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MlErrorKind {
    Syntax,
    Type,
    Unbound,
    Match,
    Exception(u128),
    HostPermission,
    HostFailure,
    Stopped,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MlError {
    pub kind: MlErrorKind,
    pub span: Box<Span>,
    pub operation: Box<str>,
    pub cause: String,
    pub exception: Option<Value>,
    /// Dynamic source-backed frames of an ML exception, innermost first.
    pub trace: Vec<String>,
}

impl MlError {
    fn syntax(span: Span, cause: impl Into<String>) -> Self {
        Self::new(MlErrorKind::Syntax, span, "parse", cause)
    }

    fn new(kind: MlErrorKind, span: Span, operation: &str, cause: impl Into<String>) -> Self {
        Self {
            kind,
            span: Box::new(span),
            operation: operation.into(),
            cause: cause.into(),
            exception: None,
            trace: Vec::new(),
        }
    }
}

impl std::fmt::Display for MlError {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            fmt,
            "{}:{}-{}: {}: {}",
            self.span.source_name, self.span.start, self.span.end, self.operation, self.cause
        )
    }
}
impl std::error::Error for MlError {}

/// Supervisor errors never become catchable ML exceptions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HostFailure {
    Permission { operation: String, resource: String, cause: String },
    Failed { operation: String, resource: String, cause: String },
    Stopped { cause: String },
}

/// The VM clones its host Arc before callbacks: nested host calls remain reentrant.
/// All external effects, including IO and dynamic source reads, enter this bridge.
pub trait HostBridge {
    fn invoke(
        &self,
        vm: &mut Vm,
        operation: &str,
        arguments: &[Value],
    ) -> Result<Value, HostFailure> {
        let _ = (vm, arguments);
        Err(HostFailure::Permission {
            operation: operation.to_owned(),
            resource: "unregistered effect".to_owned(),
            cause: "no host capability supplied".to_owned(),
        })
    }
}

pub struct DenyHost;
impl HostBridge for DenyHost {}

pub type NativeFunction = fn(&mut Vm, &[Value]) -> Result<Value, MlError>;

#[derive(Clone)]
struct ExceptionOrigin {
    location: SourceLocation,
    trace: Vec<String>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TypedInvocationTarget {
    Native(value::NativeFunctionId),
    Value(usize),
}

struct TypedInvocation {
    target: TypedInvocationTarget,
    argument: Type,
    result: Option<Type>,
}

type ClosureDefinitionPath = (Vec<(usize, usize)>, Vec<String>);

pub struct Vm {
    host: Arc<dyn HostBridge>,
    context_host: Option<Rc<host::context::ContextHost>>,
    bootstrap_host: Option<Arc<host::files::FileHostBridge>>,
    loaded_sources: Vec<LoadedMlSource>,
    root_load: Option<bootstrap::RootLoadEvidence>,
    runtime_id: u64,
    generation: u64,
    stop: StopHandle,
    source_name: String,
    declaration_span: Span,
    values: environment::ValueEnvironment,
    type_environment: types::TypeEnvironment,
    elaborations: Rc<value::Elaborations>,
    expression_locations: Vec<(usize, usize)>,
    expression_sources: Vec<String>,
    typed_arguments: Vec<TypedInvocation>,
    type_substitutions: Vec<BTreeMap<u64, Type>>,
    untyped_apply_depth: usize,
    closure_weak_variables: HashMap<usize, BTreeSet<u64>>,
    closure_input_types: HashMap<usize, Vec<Type>>,
    closure_type_substitutions: HashMap<usize, BTreeMap<u64, Type>>,
    active_closure_type_views: Vec<BTreeMap<String, String>>,
    closure_type_views: HashMap<usize, BTreeMap<String, String>>,
    closure_definition_paths: HashMap<usize, ClosureDefinitionPath>,
    closure_creation_epoch: HashMap<usize, u64>,
    next_closure_epoch: u64,
    module_closure_scopes: Vec<u64>,
    module_printer_scopes: Vec<BTreeSet<String>>,
    fixities: parser::FixityEnvironment,
    structures: BTreeMap<String, value::Namespace>,
    signatures: BTreeMap<String, value::Signature>,
    functors: BTreeMap<String, value::Functor>,
    native_functions: Vec<(NativeFunction, usize)>,
    native_signatures: HashMap<value::NativeFunctionId, Type>,
    native_argument_types: Vec<Vec<Option<Type>>>,
    type_directed_natives: BTreeMap<value::NativeFunctionId, basis::printers::TypeDirectedNative>,
    parameter_printer_ids: BTreeMap<Type, value::NativeFunctionId>,
    printer_registry: BTreeMap<String, basis::printers::PrinterRegistration>,
    sealed_printers: BTreeMap<String, (String, basis::printers::PrinterRegistration)>,
    printer_aliases: BTreeMap<String, String>,
    pretty_constructors: basis::printers::PrettyConstructors,
    constructor_types: HashMap<u128, TypeScheme>,
    opaque_type_identities: BTreeSet<String>,
    printer_budget: Option<basis::printers::PrinterBudget>,
    basis_ref_constructor: Option<value::NativeFunctionId>,
    substring_trim_ids: [Option<value::NativeFunctionId>; 2],
    basis_exceptions: BTreeMap<String, Value>,
    basis_order: Option<[Value; 3]>,
    // VM-owned counters reflect actual user updates, never fabricated process telemetry.
    user_counters: [i64; basis::statistics::USER_COUNTER_SLOTS],
    thread_self: Option<Value>,
    thread_locals: HashMap<std::thread::ThreadId, BTreeMap<HostObjectId, Value>>,
    option_some_stamp: u128,
    option_none_stamp: u128,
    next_identity: u64,
    host_objects: Vec<(u64, Weak<dyn std::any::Any>)>,
    heap: Vec<Weak<value::ValueData>>,
    exception_origins: HashMap<usize, (Weak<value::ValueData>, ExceptionOrigin)>,
}

impl Vm {
    pub fn new(host: impl HostBridge + 'static) -> Self {
        Self::from_host(host, StopHandle::new())
    }

    /// Build the host with this VM's cancellation domain before evaluation can start.
    /// A failed factory returns its original error without publishing a live VM.
    pub fn with_host_factory<H: HostBridge + 'static, E>(
        create_host: impl FnOnce(StopHandle) -> Result<H, E>,
    ) -> Result<Self, E> {
        let stop = StopHandle::new();
        let host = create_host(stop.clone())?;
        Ok(Self::from_host(host, stop))
    }

    fn from_host(host: impl HostBridge + 'static, stop: StopHandle) -> Self {
        let mut vm = Self {
            host: Arc::new(host),
            context_host: None,
            bootstrap_host: None,
            loaded_sources: Vec::new(),
            root_load: None,
            stop,
            runtime_id: NEXT_RUNTIME_ID.fetch_add(1, Ordering::Relaxed),
            generation: 1,
            source_name: String::new(),
            declaration_span: Span::new("", 0, 0),
            values: environment::ValueEnvironment::default(),
            type_environment: types::TypeEnvironment::new(),
            elaborations: Rc::new(value::Elaborations::new()),
            expression_locations: Vec::new(),
            expression_sources: Vec::new(),
            typed_arguments: Vec::new(),
            type_substitutions: Vec::new(),
            untyped_apply_depth: 0,
            closure_input_types: HashMap::new(),
            closure_type_substitutions: HashMap::new(),
            closure_weak_variables: HashMap::new(),
            active_closure_type_views: Vec::new(),
            closure_definition_paths: HashMap::new(),
            closure_type_views: HashMap::new(),
            closure_creation_epoch: HashMap::new(),
            next_closure_epoch: 0,
            module_closure_scopes: Vec::new(),
            fixities: parser::basis_fixities(),
            structures: BTreeMap::new(),
            signatures: BTreeMap::new(),
            functors: BTreeMap::new(),
            basis_exceptions: BTreeMap::new(),
            basis_order: None,
            user_counters: [0; basis::statistics::USER_COUNTER_SLOTS],
            thread_self: None,
            thread_locals: HashMap::new(),
            option_some_stamp: 0,
            option_none_stamp: 0,
            native_argument_types: Vec::new(),
            native_functions: Vec::new(),
            native_signatures: HashMap::new(),
            type_directed_natives: BTreeMap::new(),
            parameter_printer_ids: BTreeMap::new(),
            printer_registry: BTreeMap::new(),
            sealed_printers: BTreeMap::new(),
            printer_aliases: BTreeMap::new(),
            module_printer_scopes: Vec::new(),
            pretty_constructors: basis::printers::PrettyConstructors::default(),
            printer_budget: None,
            basis_ref_constructor: None,
            constructor_types: HashMap::new(),
            substring_trim_ids: [None, None],
            opaque_type_identities: BTreeSet::new(),
            next_identity: 1,
            host_objects: Vec::new(),
            heap: Vec::new(),
            exception_origins: HashMap::new(),
        };
        vm.install_basis();
        vm
    }

    pub fn request_stop(&self) {
        self.stop.request_stop();
    }

    pub fn stop_handle(&self) -> StopHandle {
        self.stop.clone()
    }
    pub fn context_host(&self) -> Option<Rc<host::context::ContextHost>> {
        self.context_host.clone()
    }

    pub fn set_context_host(
        &mut self,
        host: Rc<host::context::ContextHost>,
    ) -> Result<(), MlError> {
        self.check_stop()?;
        if self.context_host.is_some() {
            return Err(self.error(MlErrorKind::Type, "install Context host", "already installed"));
        }
        self.context_host = Some(host);
        Ok(())
    }

    pub fn check_stop(&self) -> Result<(), MlError> {
        if self.stop.is_stop_requested() {
            return Err(self.error(MlErrorKind::Stopped, "supervisor", "evaluation cancelled"));
        }
        Ok(())
    }

    fn error(&self, kind: MlErrorKind, operation: &str, cause: impl Into<String>) -> MlError {
        MlError::new(kind, Span::new(&self.source_name, 0, 0), operation, cause)
    }

    fn resolve_typed_evidence(&self, typ: &Type) -> Type {
        self.type_substitutions
            .iter()
            .fold(typ.clone(), |resolved, substitutions| resolved.substitute(substitutions))
    }

    fn current_type_substitutions(&self) -> BTreeMap<u64, Type> {
        let mut combined = BTreeMap::new();
        for substitutions in &self.type_substitutions {
            for (id, typ) in substitutions {
                combined.insert(*id, self.resolve_typed_evidence(typ));
            }
        }
        combined
    }

    fn with_type_substitutions<T>(
        &mut self,
        substitutions: BTreeMap<u64, Type>,
        run: impl FnOnce(&mut Self) -> Result<T, MlError>,
    ) -> Result<T, MlError> {
        self.type_substitutions.push(substitutions);
        let result = run(self);
        self.type_substitutions.pop();
        result
    }

    fn typed_invocation_target(value: &Value) -> TypedInvocationTarget {
        match &*value.0 {
            value::ValueData::Native(id) | value::ValueData::NativePartial { id, .. } => {
                TypedInvocationTarget::Native(*id)
            },
            _ => TypedInvocationTarget::Value(Rc::as_ptr(&value.0) as usize),
        }
    }

    pub(super) fn native_argument_type(&self, index: usize) -> Option<Type> {
        self.native_argument_types.last()?.get(index)?.clone()
    }
    pub(super) fn native_argument_field_type(&self, index: usize, field: &str) -> Option<Type> {
        let Type::Record(fields, false) =
            self.native_argument_types.last()?.get(index)?.as_ref()?
        else {
            return None;
        };
        fields.get(field).cloned()
    }
    pub(super) fn native_result_type(&self) -> Option<Type> {
        self.typed_arguments
            .last()
            .and_then(|invocation| invocation.result.as_ref())
            .map(|result| self.resolve_typed_evidence(result))
    }

    pub(super) fn apply_with_type(
        &mut self,
        function: &Value,
        argument: &Value,
        argument_type: Type,
    ) -> Result<Value, MlError> {
        self.reject_foreign_argument(argument)?;
        self.typed_arguments.push(TypedInvocation {
            target: Self::typed_invocation_target(function),
            argument: argument_type,
            result: None,
        });
        let result = self.apply_certified(function, std::slice::from_ref(argument));
        self.typed_arguments.pop();
        result
    }
    fn certified_argument_for(&self, value: &Value) -> Option<Type> {
        let target = Self::typed_invocation_target(value);
        let mut argument = self
            .typed_arguments
            .last()
            .filter(|invocation| invocation.target == target)
            .map(|invocation| self.resolve_typed_evidence(&invocation.argument))?;
        if let Some(views) = self.closure_type_views.get(&(Rc::as_ptr(&value.0) as usize)) {
            for (public, internal) in views {
                argument.rename_constructor(public, internal);
            }
        }
        Some(argument)
    }

    fn merge_type_evidence(
        &self,
        template: &Type,
        actual: &Type,
        substitutions: &mut BTreeMap<u64, Type>,
    ) -> Result<(), MlError> {
        if merge_type_template(template, actual, substitutions) {
            Ok(())
        } else {
            Err(self.error(
                MlErrorKind::HostFailure,
                "apply typed closure",
                "compiler-certified argument does not match closure input template",
            ))
        }
    }

    fn rekey_printer(&mut self, from: &str, to: &str) {
        if from == to {
            return;
        }
        self.printer_aliases.insert(to.to_owned(), from.to_owned());
    }

    fn fresh_identity(&mut self) -> u128 {
        let id = self.next_identity;
        self.next_identity += 1;
        (u128::from(self.runtime_id) << 64) | u128::from(id)
    }

    pub fn insert_host_object(&mut self, object: Rc<dyn std::any::Any>) -> Result<Value, MlError> {
        self.check_stop()?;
        let vacant = self
            .host_objects
            .iter()
            .position(|(generation, weak)| *generation < u64::MAX && weak.strong_count() == 0);
        let (generation, index) = if let Some(index) = vacant {
            let slot = &mut self.host_objects[index];
            slot.0 += 1;
            slot.1 = Rc::downgrade(&object);
            (slot.0, index)
        } else {
            let index = self.host_objects.len();
            self.host_objects.push((self.generation, Rc::downgrade(&object)));
            (self.generation, index)
        };
        let id = HostObjectId::new(self.runtime_id, generation, index);
        Ok(self.track_value(Value::host(id, object)))
    }

    pub fn get_host_object(&self, id: HostObjectId) -> Result<Rc<dyn std::any::Any>, MlError> {
        self.check_stop()?;
        if !id.belongs_to(self.runtime_id) {
            self.request_stop();
            return Err(self.error(
                MlErrorKind::HostFailure,
                "lookup host object",
                "foreign runtime identity",
            ));
        }
        self.host_objects
            .get(id.index())
            .filter(|(generation, _)| *generation == id.generation())
            .and_then(|(_, weak)| weak.upgrade())
            .ok_or_else(|| {
                self.request_stop();
                self.error(
                    MlErrorKind::HostFailure,
                    "lookup host object",
                    "expired or stale host object",
                )
            })
    }

    pub fn register_host_type(
        &mut self,
        name: &str,
        arity: usize,
        equality: bool,
    ) -> Result<(), MlError> {
        self.check_stop()?;
        if name.is_empty() || self.type_environment.type_arity(name).is_some() {
            return Err(self.error(
                MlErrorKind::Type,
                "register host type",
                format!("invalid or duplicate type {name}"),
            ));
        }
        self.type_environment.register_type(name, arity, equality);
        if let Some((path, member)) = name.rsplit_once('.') {
            let mut segments = path.split('.');
            let root = segments.next().expect("nonempty qualified type root");
            let mut namespace = self.structures.entry(root.to_owned()).or_default();
            for segment in segments {
                namespace = namespace.structures.entry(segment.to_owned()).or_default();
            }
            namespace.type_environment.register_type(name, arity, equality);
            namespace.type_environment.register_alias(
                member,
                (0..arity as u64).collect(),
                Type::Constructor(name.to_owned(), (0..arity as u64).map(Type::Variable).collect()),
            );
            namespace.types.insert(member.to_owned(), 0);
        }
        Ok(())
    }
    /// Hide an approved bootstrap bridge after the public module captures its lexical environment.
    pub fn hide_host_structure(&mut self, name: &str) -> Result<(), MlError> {
        self.check_stop()?;
        if !matches!(name, "Native_Context" | "Native_SHA1")
            || self.structures.remove(name).is_none()
        {
            return Err(self.error(
                MlErrorKind::Type,
                "hide host structure",
                format!("not an installed private bridge: {name}"),
            ));
        }
        let prefix = format!("{name}.");
        self.values.retain(|key, _| !key.starts_with(&prefix));
        self.type_environment.values.retain(|key, _| !key.starts_with(&prefix));
        self.type_environment.constructor_values.retain(|key| !key.starts_with(&prefix));
        self.type_environment.constructors.retain(|key, _| !key.starts_with(&prefix));
        Ok(())
    }

    /// Resolve an already elaborated ML type to its actual generative identity or alias shape.
    pub fn resolve_host_type(&self, name: &str) -> Option<Type> {
        self.type_environment.type_shape(name)
    }

    pub fn register_native(
        &mut self,
        name: &str,
        scheme: TypeScheme,
        callback: NativeFunction,
    ) -> Result<NativeFunctionId, MlError> {
        self.check_stop()?;
        let id =
            NativeFunctionId::new(self.runtime_id, self.generation, self.native_functions.len());
        self.native_functions.push((callback, 1));
        self.register_value(name, scheme, Value::native(id));
        Ok(id)
    }

    pub fn register_host_effect(
        &mut self,
        name: &str,
        scheme: TypeScheme,
        operation: &str,
    ) -> Result<(), MlError> {
        self.check_stop()?;
        if operation.is_empty() {
            return Err(self.error(MlErrorKind::Type, "register host effect", "empty operation"));
        }
        self.register_value(
            name,
            scheme,
            Value(std::rc::Rc::new(value::ValueData::HostFunction {
                runtime: self.runtime_id,
                operation: operation.to_owned(),
            })),
        );
        Ok(())
    }

    fn register_value(&mut self, name: &str, scheme: TypeScheme, value: Value) {
        let is_constructor = matches!(
            &*value.0,
            value::ValueData::Constructor { .. }
                | value::ValueData::ConstructorFunction { .. }
                | value::ValueData::Exception { .. }
                | value::ValueData::ExceptionFunction { .. }
        );
        if let value::ValueData::Native(id) = &*value.0 {
            self.native_signatures.entry(*id).or_insert_with(|| scheme.body().clone());
        }
        self.record_constructor_type(&value, &scheme);
        if let Some((path, member)) = name.rsplit_once('.') {
            let mut segments = path.split('.');
            let root = segments.next().expect("nonempty qualified value root");
            let mut namespace = self.structures.entry(root.to_owned()).or_default();
            for segment in segments {
                namespace = namespace.structures.entry(segment.to_owned()).or_default();
            }
            namespace.values.insert(member.to_owned(), value.clone());
            namespace.type_environment.register(member, scheme.clone());
            if is_constructor {
                namespace.type_environment.register_value_constructor(member);
                namespace.values.mark_constructor(member);
            }
        }
        self.type_environment.register(name, scheme);
        if is_constructor {
            self.type_environment.register_value_constructor(name);
        }
        self.values.insert(name.to_owned(), value);
        if is_constructor {
            self.values.mark_constructor(name);
        }
    }

    fn record_constructor_type(&mut self, value: &Value, scheme: &TypeScheme) {
        let identity = match &*value.0 {
            value::ValueData::Constructor { stamp, .. }
            | value::ValueData::ConstructorFunction { stamp, .. } => *stamp,
            value::ValueData::Exception { identity, .. }
            | value::ValueData::ExceptionFunction { identity, .. } => *identity,
            _ => return,
        };
        self.constructor_types.entry(identity).or_insert_with(|| scheme.clone());
    }

    pub fn lookup_value(&self, name: &str) -> Result<Option<&Value>, MlError> {
        self.check_stop()?;
        Ok(self.values.get(name))
    }
    pub fn lookup_structure(&self, name: &str) -> Result<Option<&value::Namespace>, MlError> {
        self.check_stop()?;
        Ok(self.structures.get(name))
    }
    pub fn lookup_signature(&self, name: &str) -> Result<Option<&value::Signature>, MlError> {
        self.check_stop()?;
        Ok(self.signatures.get(name))
    }
    pub fn lookup_functor(&self, name: &str) -> Result<Option<&value::Functor>, MlError> {
        self.check_stop()?;
        Ok(self.functors.get(name))
    }

    pub(super) fn apply_captured_exception(
        &mut self,
        constructor: &Value,
        argument: &Value,
    ) -> Result<Value, MlError> {
        let value::ValueData::ExceptionFunction { identity, .. } = &*constructor.0 else {
            return Err(self.error(
                MlErrorKind::Type,
                "construct exception",
                "expected exception constructor",
            ));
        };
        if (*identity >> 64) != u128::from(self.runtime_id) {
            self.request_stop();
            return Err(self.error(
                MlErrorKind::HostFailure,
                "construct exception",
                "foreign runtime exception constructor",
            ));
        }
        let input = match self.constructor_types.get(identity).map(TypeScheme::body) {
            Some(Type::Function(input, _)) => (**input).clone(),
            _ => {
                return Err(self.error(
                    MlErrorKind::HostFailure,
                    "construct exception",
                    "missing certified exception payload type",
                ));
            },
        };
        self.apply_with_type(constructor, argument, input)
    }

    /// Raise an already registered ML exception, retaining its generative identity.
    pub fn raise_named_exception(
        &mut self,
        name: &str,
        argument: Option<Value>,
        operation: &str,
        cause: impl Into<String>,
    ) -> MlError {
        let Some(constructor) = self.values.get(name).cloned() else {
            return self.error(MlErrorKind::Type, operation, format!("unknown exception {name}"));
        };
        let packet = match (&*constructor.0, argument) {
            (value::ValueData::Exception { .. }, None) => constructor,
            (value::ValueData::ExceptionFunction { .. }, Some(argument)) => {
                match self.apply(&constructor, &[argument]) {
                    Ok(packet) => packet,
                    Err(error) => return error,
                }
            },
            _ => {
                return self.error(
                    MlErrorKind::Type,
                    operation,
                    format!("invalid exception argument for {name}"),
                );
            },
        };
        match self.raise_exception(&packet, None, false) {
            Ok(mut error) => {
                error.operation = operation.into();
                error.cause = cause.into();
                error.span = Box::new(self.declaration_span.clone());
                error
            },
            Err(error) => error,
        }
    }

    /// Install a VM-local nullary exception for a native Basis interface.
    pub fn register_exception_value(
        &mut self,
        name: &str,
        aliases: &[&str],
    ) -> Result<(), MlError> {
        self.check_stop()?;
        if self.values.get(name).is_some() {
            return Err(self.error(
                MlErrorKind::Type,
                "register exception",
                format!("{name} already exists"),
            ));
        }
        self.register_exception(name, aliases);
        Ok(())
    }

    pub fn evaluate(&mut self, source_name: &str, source: &str) -> Result<(), MlError> {
        self.check_stop()?;
        let declarations =
            parser::parse(source_name, source, &self.fixities, &self.stop.0.requested)?;
        self.source_name = source_name.to_owned();
        for declaration in declarations {
            self.evaluate_declaration(&declaration)?;
            self.apply_fixity_declaration(&declaration);
        }
        Ok(())
    }

    pub fn call_host(&mut self, operation: &str, arguments: &[Value]) -> Result<Value, MlError> {
        self.check_stop()?;
        let host = Arc::clone(&self.host);
        let result = host.invoke(self, operation, arguments).map_err(|error| {
            self.request_stop();
            match error {
                HostFailure::Permission { operation, resource, cause } => self.error(
                    MlErrorKind::HostPermission,
                    &operation,
                    format!("{resource}: {cause}"),
                ),
                HostFailure::Failed { operation, resource, cause } => {
                    self.error(MlErrorKind::HostFailure, &operation, format!("{resource}: {cause}"))
                },
                HostFailure::Stopped { cause } => {
                    self.error(MlErrorKind::Stopped, operation, cause)
                },
            }
        })?;
        self.check_stop()?;
        Ok(result)
    }
}

fn merge_type_template(
    template: &Type,
    actual: &Type,
    substitutions: &mut BTreeMap<u64, Type>,
) -> bool {
    match (template, actual) {
        (Type::Variable(id), actual) => {
            if let Some(previous) = substitutions.get(id) {
                previous == actual
            } else {
                substitutions.insert(*id, actual.clone());
                true
            }
        },
        (Type::Constructor(left, left_args), Type::Constructor(right, right_args))
            if left == right && left_args.len() == right_args.len() =>
        {
            left_args
                .iter()
                .zip(right_args)
                .all(|(left, right)| merge_type_template(left, right, substitutions))
        },
        (Type::Function(left_input, left_output), Type::Function(right_input, right_output)) => {
            merge_type_template(left_input, right_input, substitutions)
                && merge_type_template(left_output, right_output, substitutions)
        },
        (Type::Record(left, left_open), Type::Record(right, right_open))
            if left_open == right_open && left.len() == right.len() =>
        {
            left.iter().all(|(name, left_type)| {
                right.get(name).is_some_and(|right_type| {
                    merge_type_template(left_type, right_type, substitutions)
                })
            })
        },
        _ => template == actual,
    }
}
