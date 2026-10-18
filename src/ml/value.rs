use super::environment::ValueEnvironment;
use super::types::{Type, TypeEnvironment};
use super::{Expr, MlError, MlErrorKind, Pattern, SignatureExpr, Span, Specification};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HostObjectId {
    runtime: u64,
    generation: u64,
    index: usize,
}
impl HostObjectId {
    pub(super) fn new(runtime: u64, generation: u64, index: usize) -> Self {
        Self { runtime, generation, index }
    }
    pub(super) fn index(self) -> usize {
        self.index
    }
    pub(super) fn belongs_to(self, runtime: u64) -> bool {
        self.runtime == runtime
    }
    pub(super) fn generation(self) -> u64 {
        self.generation
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NativeFunctionId {
    runtime: u64,
    generation: u64,
    index: usize,
}
impl NativeFunctionId {
    pub(super) fn new(runtime: u64, generation: u64, index: usize) -> Self {
        Self { runtime, generation, index }
    }
    pub(super) fn index(self) -> usize {
        self.index
    }
    pub(super) fn belongs_to(self, runtime: u64, generation: u64) -> bool {
        self.runtime == runtime && self.generation == generation
    }
}

#[derive(Clone)]
pub struct Value(pub(super) Rc<ValueData>);
/// Non-owning reference for observing live VM values without keeping them alive.
#[derive(Clone)]
pub struct WeakValue(std::rc::Weak<ValueData>);

impl WeakValue {
    pub fn upgrade(&self) -> Option<Value> {
        self.0.upgrade().map(Value)
    }
}

pub(super) type ElaborationKey = (String, usize, usize);
pub(super) const BINDING_EXPRESSION_PATH: usize = usize::MAX;
pub(super) const CLOSURE_EXPRESSION_PATH: usize = usize::MAX - 1;
pub(super) const CLOSURE_CLAUSE_PATH: usize = usize::MAX - 2;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct ApplicationKey {
    pub declaration: ElaborationKey,
    pub module_path: Vec<u8>,
}

impl ApplicationKey {
    pub(super) fn at(span: &super::Span, module_path: &[u8]) -> Self {
        Self {
            declaration: (span.source_name.clone(), span.start, span.end),
            module_path: module_path.to_vec(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct ExpressionKey {
    pub source_name: String,
    pub locations: Vec<(usize, usize)>,
}

impl ExpressionKey {
    pub(super) fn new(source_name: &str, locations: &[(usize, usize)]) -> Self {
        Self { source_name: source_name.to_owned(), locations: locations.to_vec() }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct FunctionKey {
    pub declaration: ElaborationKey,
    pub name: String,
}

#[derive(Clone)]
pub(super) struct TypedCallEvidence {
    pub argument: Type,
    pub result: Type,
    pub weak_variables: BTreeSet<u64>,
}

#[derive(Clone, Default)]
pub(super) struct Elaborations {
    pub declarations: BTreeMap<ElaborationKey, TypeEnvironment>,
    pub applications: BTreeMap<ApplicationKey, Rc<Elaborations>>,
    pub typed_calls: BTreeMap<ExpressionKey, TypedCallEvidence>,
    pub closure_inputs: BTreeMap<ExpressionKey, Type>,
    pub closure_weak_variables: BTreeMap<ExpressionKey, BTreeSet<u64>>,
    pub function_weak_variables: BTreeMap<FunctionKey, BTreeSet<u64>>,
    pub function_inputs: BTreeMap<FunctionKey, Vec<Type>>,
    pub word32_literals: BTreeSet<ElaborationKey>,
}

impl Elaborations {
    pub(super) fn new() -> Self {
        Self::default()
    }
    pub(super) fn insert(&mut self, key: ElaborationKey, types: TypeEnvironment) {
        self.declarations.insert(key, types);
    }
    pub(super) fn get(&self, key: &ElaborationKey) -> Option<&TypeEnvironment> {
        self.declarations.get(key)
    }
    pub(super) fn application(&self, key: &ApplicationKey) -> Option<&Rc<Elaborations>> {
        self.applications.get(key)
    }
}

pub(super) struct ClosureStatic {
    pub(super) types: TypeEnvironment,
    pub(super) structures: BTreeMap<String, Namespace>,
    pub(super) signatures: BTreeMap<String, Signature>,
    pub(super) functors: BTreeMap<String, Functor>,
    pub(super) elaborations: Rc<Elaborations>,
}

pub(super) enum ValueData {
    Unit,
    Int(i64),
    Real(f64),
    Word32(u32),
    Word(u64),
    Bool(bool),
    Text(Vec<u8>),
    Character(u8),
    Tuple(Vec<Value>),
    List(Vec<Value>),
    Record(BTreeMap<String, Value>),
    Vector(Vec<Value>),
    Array(RefCell<Vec<Value>>),
    Constructor {
        stamp: u128,
        name: String,
        argument: Option<Value>,
    },
    Exception {
        identity: u128,
        name: String,
        argument: Option<Value>,
    },
    ConstructorFunction {
        stamp: u128,
        name: String,
    },
    ExceptionFunction {
        identity: u128,
        name: String,
    },
    Closure {
        runtime: u64,
        clauses: Vec<(Pattern, Expr)>,
        environment: Rc<RefCell<ValueEnvironment>>,
        lexical: Option<Rc<RefCell<ClosureStatic>>>,
    },
    CurriedClosure {
        runtime: u64,
        clauses: Rc<Vec<(Vec<Pattern>, Expr)>>,
        arguments: RefCell<Vec<Value>>,
        environment: Rc<RefCell<ValueEnvironment>>,
        lexical: Rc<RefCell<ClosureStatic>>,
    },
    Native(NativeFunctionId),
    NativePartial {
        id: NativeFunctionId,
        arguments: RefCell<Vec<Value>>,
        argument_types: RefCell<Vec<Option<Type>>>,
        result_type: RefCell<Option<Type>>,
    },
    HostFunction {
        runtime: u64,
        operation: String,
    },
    Host {
        id: HostObjectId,
        // Strong owner: VM host-object slots contain only Weak references.
        object: Rc<dyn std::any::Any>,
    },
    Reference(RefCell<Value>),
    /// Ordinary SML ref identity with an option slot inspected weakly by VM collection.
    WeakReference(RefCell<Value>),
}

impl Value {
    pub fn unit() -> Self {
        Self(Rc::new(ValueData::Unit))
    }
    pub fn downgrade(&self) -> WeakValue {
        WeakValue(Rc::downgrade(&self.0))
    }
    pub fn int(value: i64) -> Self {
        Self(Rc::new(ValueData::Int(value)))
    }
    pub fn real(value: f64) -> Self {
        Self(Rc::new(ValueData::Real(value)))
    }
    pub fn word(value: u64) -> Self {
        Self(Rc::new(ValueData::Word(value)))
    }
    pub fn word32(value: u32) -> Self {
        Self(Rc::new(ValueData::Word32(value)))
    }
    pub fn bool(value: bool) -> Self {
        Self(Rc::new(ValueData::Bool(value)))
    }
    pub fn text(value: impl Into<String>) -> Self {
        Self::bytes(value.into().into_bytes())
    }
    pub fn bytes(value: impl Into<Vec<u8>>) -> Self {
        Self(Rc::new(ValueData::Text(value.into())))
    }
    pub fn tuple(values: Vec<Value>) -> Self {
        Self(Rc::new(ValueData::Tuple(values)))
    }
    pub fn list(values: Vec<Value>) -> Self {
        Self(Rc::new(ValueData::List(values)))
    }
    pub fn character(value: u8) -> Self {
        Self(Rc::new(ValueData::Character(value)))
    }
    pub(super) fn native(id: NativeFunctionId) -> Self {
        Self(Rc::new(ValueData::Native(id)))
    }
    pub(super) fn host(id: HostObjectId, object: Rc<dyn std::any::Any>) -> Self {
        Self(Rc::new(ValueData::Host { id, object }))
    }
    pub(super) fn reference(value: Value) -> Self {
        Self(Rc::new(ValueData::Reference(RefCell::new(value))))
    }
    pub fn as_int(&self) -> Option<i64> {
        if let ValueData::Int(value) = &*self.0 { Some(*value) } else { None }
    }
    pub fn as_real(&self) -> Option<f64> {
        if let ValueData::Real(value) = &*self.0 { Some(*value) } else { None }
    }
    pub fn as_word(&self) -> Option<u64> {
        if let ValueData::Word(value) = &*self.0 { Some(*value) } else { None }
    }
    pub fn as_word32(&self) -> Option<u32> {
        if let ValueData::Word32(value) = &*self.0 { Some(*value) } else { None }
    }
    pub fn as_bool(&self) -> Option<bool> {
        if let ValueData::Bool(value) = &*self.0 { Some(*value) } else { None }
    }
    pub fn as_text(&self) -> Option<&str> {
        self.as_bytes().and_then(|value| std::str::from_utf8(value).ok())
    }
    pub fn as_bytes(&self) -> Option<&[u8]> {
        if let ValueData::Text(value) = &*self.0 { Some(value) } else { None }
    }
    pub fn as_tuple(&self) -> Option<&[Value]> {
        if let ValueData::Tuple(values) = &*self.0 { Some(values) } else { None }
    }
    pub fn as_list(&self) -> Option<&[Value]> {
        if let ValueData::List(values) = &*self.0 { Some(values) } else { None }
    }
    pub(super) fn record_length(&self) -> Option<usize> {
        match &*self.0 {
            ValueData::Record(fields) => Some(fields.len()),
            ValueData::Tuple(values) => Some(values.len()),
            ValueData::Unit => Some(0),
            _ => None,
        }
    }
    pub(super) fn record_field(&self, label: &str) -> Option<&Value> {
        match &*self.0 {
            ValueData::Record(fields) => fields.get(label),
            ValueData::Tuple(values) => label
                .parse::<usize>()
                .ok()
                .filter(|_| !label.starts_with('0'))
                .and_then(|index| index.checked_sub(1))
                .and_then(|index| values.get(index)),
            _ => None,
        }
    }
    pub fn as_host_object(&self) -> Option<HostObjectId> {
        if let ValueData::Host { id, .. } = &*self.0 { Some(*id) } else { None }
    }
    pub fn downcast_host_object<T: std::any::Any>(&self) -> Option<&T> {
        match &*self.0 {
            ValueData::Host { object, .. } => object.downcast_ref::<T>(),
            _ => None,
        }
    }
    pub fn is_unit(&self) -> bool {
        matches!(&*self.0, ValueData::Unit)
    }
    pub fn is_same_object(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl std::fmt::Debug for Value {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let kind = match &*self.0 {
            ValueData::Unit => "unit",
            ValueData::Int(_) => "int",
            ValueData::Real(_) => "real",
            ValueData::Word(_) => "word",
            ValueData::Word32(_) => "Word32.word",
            ValueData::Bool(_) => "bool",
            ValueData::Text(_) => "string",
            ValueData::Character(_) => "char",
            ValueData::Tuple(_) => "tuple",
            ValueData::List(_) => "list",
            ValueData::Vector(_) => "vector",
            ValueData::Array(_) => "array",
            ValueData::Record(_) => "record",
            ValueData::Constructor { name, .. } => {
                return formatter.debug_tuple("constructor").field(name).finish();
            },
            ValueData::ConstructorFunction { .. } => "constructor",
            ValueData::Exception { .. } | ValueData::ExceptionFunction { .. } => "exception",
            ValueData::Closure { .. } | ValueData::CurriedClosure { .. } => "closure",
            ValueData::Native(_) | ValueData::NativePartial { .. } => "native",
            ValueData::HostFunction { .. } => "host function",
            ValueData::Host { .. } => "host",
            ValueData::Reference(_) => "ref",
            ValueData::WeakReference(_) => "ref",
        };
        formatter.write_str(kind)
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for Value {}

#[derive(Clone, Debug, Default)]
pub struct Namespace {
    pub(super) values: ValueEnvironment,
    pub(super) structures: BTreeMap<String, Namespace>,
    pub(super) types: BTreeMap<String, u128>,
    pub(super) type_environment: TypeEnvironment,
}
impl Namespace {
    pub fn lookup_value(&self, name: &str) -> Option<&Value> {
        self.values.get(name)
    }
    pub fn lookup_structure(&self, name: &str) -> Option<&Namespace> {
        self.structures.get(name)
    }
    pub fn lookup_type_stamp(&self, name: &str) -> Option<u128> {
        self.types.get(name).copied()
    }
    pub(super) fn lookup_type_identity(&self, path: &str) -> Option<&str> {
        if let Some((structure, member)) = path.split_once('.') {
            return self.structures.get(structure)?.lookup_type_identity(member);
        }
        self.type_environment.type_identity(path)
    }
    pub(super) fn lookup_type_shape(&self, path: &str) -> Option<super::types::Type> {
        if let Some((structure, member)) = path.split_once('.') {
            return self.structures.get(structure)?.lookup_type_shape(member);
        }
        self.type_environment.type_shape(path)
    }
}

pub(super) struct SealingContext<'a> {
    pub opaque: bool,
    pub prefix: &'a str,
    pub shared: &'a mut BTreeMap<String, (String, u128)>,
}

#[derive(Clone, Debug)]
pub struct Signature {
    pub(super) specifications: Vec<Specification>,
    pub(super) type_environment: Rc<TypeEnvironment>,
}

impl Signature {
    pub(super) fn resolve(
        expression: &SignatureExpr,
        signatures: &BTreeMap<String, Self>,
        types: &TypeEnvironment,
        span: &Span,
    ) -> Result<Self, MlError> {
        let resolve_name = |name: &str| {
            signatures.get(name).ok_or_else(|| {
                MlError::new(
                    MlErrorKind::Type,
                    span.clone(),
                    "signature",
                    format!("unknown signature {name}"),
                )
            })
        };
        let mut signature = match &expression.base {
            Some(name) => resolve_name(name)?.clone(),
            None => Self { specifications: Vec::new(), type_environment: Rc::new(types.clone()) },
        };
        for spec in &expression.body {
            if let Specification::Include(name) = spec {
                signature.specifications.extend(resolve_name(name)?.specifications.iter().cloned());
            } else {
                signature.specifications.push(spec.clone());
            }
        }
        Ok(signature)
    }
}

#[derive(Clone, Debug)]
pub struct Functor {
    pub(super) parameter: String,
    pub(super) signature: SignatureExpr,
    pub(super) body: super::ModuleExpr,
    pub(super) environment: Namespace,
    pub(super) signatures: BTreeMap<String, Signature>,
    pub(super) functors: BTreeMap<String, Functor>,
}

impl Functor {
    pub fn parameter(&self) -> &str {
        &self.parameter
    }
    pub fn signature(&self) -> &SignatureExpr {
        &self.signature
    }
}
