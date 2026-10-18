use super::environment::ValueEnvironment;
use super::syntax::FunctionBinding;
use super::types::{Infer, Type, TypeEnvironment, TypeScheme};
use super::value::{
    ApplicationKey, BINDING_EXPRESSION_PATH, CLOSURE_CLAUSE_PATH, CLOSURE_EXPRESSION_PATH,
    ClosureStatic, Functor, Namespace, SealingContext, Signature, ValueData,
};
use super::{
    Declaration, Expr, MlError, MlErrorKind, ModuleExpr, Pattern, SignatureExpr, SourceLocation,
    Specification, Value, Vm,
};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

const MAX_HOST_TYPE_CHECK_DEPTH: usize = 256;
const MAX_HOST_TYPE_CHECK_NODES: usize = 16_384;

struct CurriedClosureInput<'a> {
    runtime: u64,
    clauses: &'a Rc<Vec<(Vec<Pattern>, Expr)>>,
    arguments: &'a RefCell<Vec<Value>>,
    environment: &'a Rc<RefCell<ValueEnvironment>>,
    lexical: &'a Rc<RefCell<ClosureStatic>>,
}

struct CertifiedValueCheck {
    validated: HashSet<(usize, usize, usize)>,
    owned_types: Vec<Rc<Type>>,
    remaining: usize,
}

impl CertifiedValueCheck {
    fn new() -> Self {
        Self {
            validated: HashSet::new(),
            owned_types: Vec::new(),
            remaining: MAX_HOST_TYPE_CHECK_NODES,
        }
    }
}

#[derive(Clone, Copy)]
enum CertifiedTypeReplacements<'a> {
    None,
    Owned(&'a BTreeMap<u64, Type>),
    Borrowed(&'a BTreeMap<u64, &'a Type>),
}

impl<'a> CertifiedTypeReplacements<'a> {
    fn get(self, id: u64) -> Option<&'a Type> {
        match self {
            Self::None => None,
            Self::Owned(types) => types.get(&id),
            Self::Borrowed(types) => types.get(&id).copied(),
        }
    }
}

#[derive(Default)]
struct ExportNames {
    values: BTreeSet<String>,
    structures: BTreeSet<String>,
    signatures: BTreeSet<String>,
    functors: BTreeSet<String>,
    types: BTreeSet<String>,
}

impl ExportNames {
    fn extend(&mut self, other: Self) {
        self.values.extend(other.values);
        self.structures.extend(other.structures);
        self.signatures.extend(other.signatures);
        self.functors.extend(other.functors);
        self.types.extend(other.types);
    }
}

impl Vm {
    pub(super) fn apply_fixity_declaration(&mut self, declaration: &Declaration) {
        match declaration {
            Declaration::Fixity { names, fixity, .. } => {
                for name in names {
                    match fixity {
                        Some(fixity) => {
                            self.fixities.insert(name.clone(), fixity.clone());
                        },
                        None => {
                            self.fixities.remove(name);
                        },
                    }
                }
            },
            Declaration::Local { body, .. } => {
                for declaration in body {
                    self.apply_fixity_declaration(declaration);
                }
            },
            _ => {},
        }
    }
    pub(super) fn evaluate_declaration(
        &mut self,
        declaration: &Declaration,
    ) -> Result<(), MlError> {
        self.check_stop()?;
        let previous = std::mem::replace(&mut self.declaration_span, declaration.span());
        let result = self.elaborate_and_execute_declaration(declaration);
        self.declaration_span = previous;
        result
    }

    fn elaborate_and_execute_declaration(
        &mut self,
        declaration: &Declaration,
    ) -> Result<(), MlError> {
        let span = declaration.span();
        let key = (span.source_name, span.start, span.end);
        if let Some(types) = self.elaborations.get(&key).cloned() {
            self.refine_weak_closure_types(&types)?;
            self.opaque_type_identities.extend(types.opaque_identities.iter().cloned());
            self.execute_declaration(declaration)?;
            self.type_environment = types;
            self.record_constructor_types(declaration);
            return Ok(());
        }
        let previous_types = self.type_environment.clone();
        let mut infer = Infer::new(previous_types.clone(), declaration.span());
        infer.modules = super::static_module::StaticModules::from_runtime(
            &self.structures,
            &self.signatures,
            &self.functors,
        );
        infer.declaration(declaration)?;
        infer.check_flexible_records()?;
        let constrained_previous = infer.resolve_existing(previous_types);
        let (types, mut elaborations) = infer.finish();
        elaborations.insert(key, types.clone());
        self.refine_weak_closure_types(&types)?;
        let previous = std::mem::replace(&mut self.elaborations, Rc::new(elaborations));
        self.opaque_type_identities.extend(types.opaque_identities.iter().cloned());
        let result = self.execute_declaration(declaration);
        self.elaborations = previous;
        match result {
            Ok(()) => {
                self.type_environment = types;
                self.record_constructor_types(declaration);
            },
            Err(error) => {
                if matches!(error.kind, MlErrorKind::Exception(_)) {
                    self.type_environment = constrained_previous;
                    self.synchronize_module_types();
                }
                return Err(error);
            },
        }
        self.synchronize_module_types();
        Ok(())
    }

    fn refine_weak_closure_types(&mut self, next: &TypeEnvironment) -> Result<(), MlError> {
        let mut refinements = BTreeMap::new();
        for (name, previous) in &self.type_environment.values {
            let Some(updated) = next.values.get(name) else {
                continue;
            };
            let mut candidates = BTreeMap::new();
            if !super::merge_type_template(previous.body(), updated.body(), &mut candidates) {
                continue;
            }
            for quantified in previous.quantified() {
                candidates.remove(quantified);
            }
            for (variable, typ) in candidates {
                if matches!(typ, Type::Variable(id) if id == variable) {
                    continue;
                }
                if refinements.get(&variable).is_some_and(|existing| existing != &typ) {
                    return Err(self.error(
                        MlErrorKind::HostFailure,
                        "type elaboration",
                        "conflicting weak type refinements",
                    ));
                }
                refinements.insert(variable, typ);
            }
        }
        for (pointer, weak_variables) in &self.closure_weak_variables {
            let substitutions = self.closure_type_substitutions.entry(*pointer).or_default();
            for typ in substitutions.values_mut() {
                *typ = typ.substitute(&refinements);
            }
            for variable in weak_variables {
                if let Some(typ) = refinements.get(variable) {
                    substitutions.insert(*variable, typ.clone());
                }
            }
        }
        Ok(())
    }

    fn record_constructor_types(&mut self, declaration: &Declaration) {
        match declaration {
            Declaration::Datatype { constructors, .. } => {
                for (name, _) in constructors {
                    self.record_declared_constructor_type(name);
                }
            },
            Declaration::Exception { name, .. } => self.record_declared_constructor_type(name),
            _ => {},
        }
    }

    fn record_declared_constructor_type(&mut self, name: &str) {
        let Some(value) = self.values.get(name).cloned() else { return };
        if let Some(scheme) = self.type_environment.lookup(name).cloned() {
            self.record_constructor_type(&value, &scheme);
        }
    }

    fn execute_declaration(&mut self, declaration: &Declaration) -> Result<(), MlError> {
        match declaration {
            Declaration::Fixity { .. } => Ok(()),
            Declaration::Value { recursive, bindings, .. } => {
                self.execute_value_bindings(*recursive, bindings)
            },
            Declaration::Function { bindings, .. } => self.execute_functions(bindings),
            Declaration::Datatype { constructors, .. } => {
                for (constructor, argument) in constructors {
                    let stamp = self.fresh_identity();
                    let value = if argument.is_some() {
                        Value(Rc::new(ValueData::ConstructorFunction {
                            stamp,
                            name: constructor.clone(),
                        }))
                    } else {
                        Value(Rc::new(ValueData::Constructor {
                            stamp,
                            name: constructor.clone(),
                            argument: None,
                        }))
                    };
                    self.values.insert(constructor.clone(), value);
                    self.values.mark_constructor(constructor);
                }
                Ok(())
            },
            Declaration::DatatypeReplication { source, .. } => {
                let constructors =
                    self.type_environment.replicated_constructors(source).ok_or_else(|| {
                        self.error(
                            MlErrorKind::Type,
                            "datatype",
                            format!("unknown datatype {source}"),
                        )
                    })?;
                let prefix = source.rsplit_once('.').map_or("", |(path, _)| path);
                for (name, _) in constructors {
                    let qualified =
                        if prefix.is_empty() { name.clone() } else { format!("{prefix}.{name}") };
                    let value = self.values.get(&qualified).cloned().ok_or_else(|| {
                        self.error(
                            MlErrorKind::Type,
                            "datatype",
                            format!("missing constructor {qualified}"),
                        )
                    })?;
                    self.values.insert(name.clone(), value);
                    self.values.mark_constructor(&name);
                }
                Ok(())
            },
            Declaration::Exception { name, alias, argument, .. } => {
                let constructor = if let Some(alias) = alias {
                    if !self.values.is_constructor(alias) {
                        return Err(self.error(
                            MlErrorKind::Type,
                            "exception",
                            format!("{alias} is not an exception constructor"),
                        ));
                    }
                    let constructor = self.resolve_name(alias, &self.values)?;
                    if !matches!(
                        &*constructor.0,
                        ValueData::Exception { .. } | ValueData::ExceptionFunction { .. }
                    ) {
                        return Err(self.error(
                            MlErrorKind::Type,
                            "exception",
                            format!("{alias} is not an exception constructor"),
                        ));
                    }
                    constructor
                } else {
                    let identity = self.fresh_identity();
                    if argument.is_some() {
                        Value(Rc::new(ValueData::ExceptionFunction {
                            identity,
                            name: name.clone(),
                        }))
                    } else {
                        Value(Rc::new(ValueData::Exception {
                            identity,
                            name: name.clone(),
                            argument: None,
                        }))
                    }
                };
                self.values.insert(name.clone(), constructor);
                self.values.mark_constructor(name);
                Ok(())
            },
            Declaration::Type { .. } => Ok(()),
            Declaration::Expression(expression, _) => {
                let environment = self.values.clone();
                let value = self.evaluate_expr(expression, &environment)?;
                self.values.insert("it".to_owned(), value);
                Ok(())
            },
            Declaration::Open { names, .. } => {
                for name in names {
                    let namespace = self.resolve_structure(name)?.clone();
                    self.type_environment.extend_exports(&namespace.type_environment);
                    for (name, child) in &namespace.structures {
                        self.type_environment.register_namespace(name, child);
                        self.values.bind_namespace(name, child);
                    }
                    self.values.extend_exports(namespace.values);
                    self.structures.extend(namespace.structures);
                }
                Ok(())
            },
            Declaration::Local { local, body, .. } => {
                self.execute_local(local, body, None).map(|_| ())
            },
            Declaration::Abstype { datatype, body, .. } => {
                self.execute_abstype(datatype, body).map(|_| ())
            },
            Declaration::Signature { name, base, body, .. } => {
                let mut specifications = Vec::new();
                if let Some(base) = base {
                    self.extend_signature(&mut specifications, base)?;
                }
                for specification in body {
                    if let Specification::Include(included) = specification {
                        self.extend_signature(&mut specifications, included)?;
                    } else {
                        specifications.push(specification.clone());
                    }
                }
                self.signatures.insert(
                    name.clone(),
                    Signature {
                        specifications,
                        type_environment: Rc::new(self.type_environment.clone()),
                    },
                );
                Ok(())
            },
            Declaration::Structure { name, signature, body, .. } => {
                self.with_module_closure_scope(|vm| {
                    let mut namespace = vm.evaluate_module(body)?;
                    if let Some((signature, opaque)) = signature {
                        vm.constrain_namespace(&mut namespace, signature, *opaque)?;
                    }
                    let preflight = vm
                        .elaborations
                        .get(&{
                            let span = declaration.span();
                            (span.source_name, span.start, span.end)
                        })
                        .map(|types| types.namespace_types(name));
                    if let Some(types) = preflight {
                        vm.apply_preflight_namespace(&mut namespace, &types);
                    }
                    vm.type_environment.register_namespace(name, &namespace);
                    vm.values.bind_namespace(name, &namespace);
                    vm.structures.insert(name.clone(), namespace);
                    Ok(())
                })
            },
            Declaration::Functor { name, parameter, signature, body, .. } => {
                Signature::resolve(
                    signature,
                    &self.signatures,
                    &self.type_environment,
                    &self.current_span(),
                )?;
                self.functors.insert(
                    name.clone(),
                    Functor {
                        parameter: parameter.clone(),
                        signature: signature.clone(),
                        body: body.clone(),
                        environment: self.snapshot_namespace(),
                        signatures: self.signatures.clone(),
                        functors: self.functors.clone(),
                    },
                );
                Ok(())
            },
        }
    }

    fn execute_abstype(
        &mut self,
        datatype: &Declaration,
        body: &[Declaration],
    ) -> Result<ExportNames, MlError> {
        let Declaration::Datatype { name, .. } = datatype else {
            return Err(self.error(MlErrorKind::Type, "abstype", "expected datatype binding"));
        };
        self.execute_local(std::slice::from_ref(datatype), body, Some(name))
    }

    fn execute_local(
        &mut self,
        local: &[Declaration],
        body: &[Declaration],
        extra_type: Option<&str>,
    ) -> Result<ExportNames, MlError> {
        let saved_values = self.values.clone();
        let saved_structures = self.structures.clone();
        let saved_signatures = self.signatures.clone();
        let saved_functors = self.functors.clone();
        let saved_types = self.type_environment.clone();
        let result = (|| {
            for declaration in local {
                self.evaluate_declaration(declaration)?;
            }
            let mut exports = ExportNames::default();
            for declaration in body {
                exports.extend(self.evaluate_scoped_declaration(declaration)?);
            }
            if let Some(name) = extra_type {
                exports.types.insert(name.to_owned());
            }
            let exported_types = self.type_environment.select(&exports.values, &exports.types);
            self.values.retain(|name, _| exports.values.contains(name));
            self.structures.retain(|name, _| exports.structures.contains(name));
            self.signatures.retain(|name, _| exports.signatures.contains(name));
            self.functors.retain(|name, _| exports.functors.contains(name));
            Ok((
                std::mem::take(&mut self.values),
                std::mem::take(&mut self.structures),
                std::mem::take(&mut self.signatures),
                std::mem::take(&mut self.functors),
                exported_types,
                exports,
            ))
        })();
        self.values = saved_values;
        self.structures = saved_structures;
        self.signatures = saved_signatures;
        self.functors = saved_functors;
        self.type_environment = saved_types;
        let (values, structures, signatures, functors, exported_types, exports) = result?;
        self.type_environment.extend_exports(&exported_types);
        for (name, namespace) in &structures {
            self.type_environment.register_namespace(name, namespace);
            self.values.bind_namespace(name, namespace);
        }
        self.values.extend_exports(values);
        self.structures.extend(structures);
        self.signatures.extend(signatures);
        self.functors.extend(functors);
        Ok(exports)
    }

    fn evaluate_scoped_declaration(
        &mut self,
        declaration: &Declaration,
    ) -> Result<ExportNames, MlError> {
        if matches!(declaration, Declaration::Local { .. } | Declaration::Abstype { .. }) {
            let previous = std::mem::replace(&mut self.declaration_span, declaration.span());
            let result = match declaration {
                Declaration::Local { local, body, .. } => self.execute_local(local, body, None),
                Declaration::Abstype { datatype, body, .. } => self.execute_abstype(datatype, body),
                _ => {
                    Err(self.error(MlErrorKind::HostFailure, "local", "invalid scoped declaration"))
                },
            };
            self.declaration_span = previous;
            return result;
        }
        let mut exports = ExportNames::default();
        if let Declaration::Open { names, .. } = declaration {
            for name in names {
                let namespace = self.resolve_structure(name)?;
                exports.values.extend(namespace.values.keys().cloned());
                exports.structures.extend(namespace.structures.keys().cloned());
                exports.types.extend(namespace.type_environment.type_names());
            }
        }
        self.evaluate_declaration(declaration)?;
        if let Declaration::DatatypeReplication { source, .. } = declaration {
            let constructors =
                self.type_environment.replicated_constructors(source).ok_or_else(|| {
                    self.error(MlErrorKind::Type, "datatype", format!("unknown datatype {source}"))
                })?;
            exports.values.extend(constructors.into_iter().map(|(name, _)| name));
        }
        declaration
            .collect_value_names(&mut exports.values, &|name| self.values.is_constructor(name));
        declaration.collect_type_names(&mut exports.types);
        collect_module_names(
            declaration,
            &mut exports.structures,
            &mut exports.signatures,
            &mut exports.functors,
        );
        Ok(exports)
    }

    fn record_anonymous_closure_input(&mut self, closure: &Value) -> Result<(), MlError> {
        let source_name = self
            .expression_sources
            .last()
            .map_or(self.declaration_span.source_name.as_str(), String::as_str);
        let key = super::value::ExpressionKey::new(source_name, &self.expression_locations);
        let input = self.elaborations.closure_inputs.get(&key).cloned().ok_or_else(|| {
            self.error(
                MlErrorKind::HostFailure,
                "create closure",
                "missing compiler-certified closure input type",
            )
        })?;
        let pointer = Rc::as_ptr(&closure.0) as usize;
        self.closure_input_types.insert(pointer, vec![input]);
        if let Some(weak) = self.elaborations.closure_weak_variables.get(&key) {
            self.closure_weak_variables.insert(pointer, weak.clone());
        }
        let substitutions = self.current_type_substitutions();
        if !substitutions.is_empty() {
            self.closure_type_substitutions.insert(pointer, substitutions);
        }
        self.record_active_closure_views(pointer);
        self.closure_definition_paths
            .insert(pointer, (self.expression_locations.clone(), self.expression_sources.clone()));
        Ok(())
    }

    fn execute_value_bindings(
        &mut self,
        recursive: bool,
        bindings: &[(Pattern, Expr)],
    ) -> Result<(), MlError> {
        let shared = Rc::new(RefCell::new(self.values.clone()));
        let lexical = self.capture_closure_static();
        let mut results = BTreeMap::new();
        for (binding_index, (pattern, expression)) in bindings.iter().enumerate() {
            self.expression_locations.push((BINDING_EXPRESSION_PATH, binding_index));
            let value = if recursive {
                self.create_recursive_closure(expression, &shared, &lexical)
            } else {
                self.evaluate_expr(expression, &self.values.clone())
            };
            self.expression_locations.pop();
            let value = value?;
            let environment = shared.borrow();
            let matches = self.match_pattern(pattern, &value, &environment)?.ok_or_else(|| {
                self.error(MlErrorKind::Match, "val", "binding pattern does not match")
            })?;
            for (name, value) in matches {
                results.insert(name, value);
            }
        }
        if recursive {
            shared.borrow_mut().extend(results.clone());
        }
        self.values.extend(results);
        Ok(())
    }

    fn create_recursive_closure(
        &mut self,
        expression: &Expr,
        shared: &Rc<RefCell<ValueEnvironment>>,
        lexical: &Rc<RefCell<ClosureStatic>>,
    ) -> Result<Value, MlError> {
        let clauses = expression.function_clauses().ok_or_else(|| {
            self.error(MlErrorKind::Type, "val rec", "recursive binding must be a function")
        })?;
        let location = match expression {
            Expr::Located(_, location) => Some(location),
            _ => None,
        };
        if let Some(location) = location {
            self.expression_locations.push((location.span.start, location.span.end));
            self.expression_sources.push(location.span.source_name.clone());
        }
        let marker = (CLOSURE_EXPRESSION_PATH, self.expression_locations.len());
        self.expression_locations.push(marker);
        let closure = self.track_value(Value(Rc::new(ValueData::Closure {
            runtime: self.runtime_id,
            clauses: clauses.to_vec(),
            environment: Rc::clone(shared),
            lexical: Some(Rc::clone(lexical)),
        })));
        let recorded = self.record_anonymous_closure_input(&closure);
        self.expression_locations.pop();
        if location.is_some() {
            self.expression_locations.pop();
            self.expression_sources.pop();
        }
        recorded?;
        Ok(closure)
    }

    fn execute_functions(&mut self, bindings: &[FunctionBinding]) -> Result<(), MlError> {
        let shared = Rc::new(RefCell::new(self.values.clone()));
        let lexical = self.capture_closure_static();
        let mut functions = BTreeMap::new();
        for (binding_index, (name, clauses)) in bindings.iter().enumerate() {
            let arity = clauses.first().map_or(0, |(patterns, _)| patterns.len());
            if arity == 0 || clauses.iter().any(|(patterns, _)| patterns.len() != arity) {
                return Err(self.error(
                    MlErrorKind::Syntax,
                    "fun",
                    format!("function {name} requires the same nonzero arity in every clause"),
                ));
            }
            let closure = self.track_value(Value(Rc::new(ValueData::CurriedClosure {
                runtime: self.runtime_id,
                clauses: Rc::new(clauses.clone()),
                arguments: RefCell::new(Vec::new()),
                environment: Rc::clone(&shared),
                lexical: Rc::clone(&lexical),
            })));
            let key = super::value::FunctionKey {
                declaration: (
                    self.declaration_span.source_name.clone(),
                    self.declaration_span.start,
                    self.declaration_span.end,
                ),
                name: name.clone(),
            };
            let inputs = self.elaborations.function_inputs.get(&key).cloned().ok_or_else(|| {
                self.error(
                    MlErrorKind::HostFailure,
                    "create function",
                    format!("missing compiler-certified input types for {name}"),
                )
            })?;
            let pointer = Rc::as_ptr(&closure.0) as usize;
            self.closure_input_types.insert(pointer, inputs);
            if let Some(weak) = self.elaborations.function_weak_variables.get(&key) {
                self.closure_weak_variables.insert(pointer, weak.clone());
            }
            let substitutions = self.current_type_substitutions();
            if !substitutions.is_empty() {
                self.closure_type_substitutions.insert(pointer, substitutions);
            }
            self.record_active_closure_views(pointer);
            let mut path = self.expression_locations.clone();
            path.extend([
                (self.declaration_span.start, self.declaration_span.end),
                (BINDING_EXPRESSION_PATH, binding_index),
            ]);
            self.closure_definition_paths.insert(pointer, (path, self.expression_sources.clone()));
            functions.insert(name.clone(), closure);
        }
        shared.borrow_mut().extend(functions.clone());
        self.values.extend(functions);
        Ok(())
    }

    pub(super) fn resolve_name(
        &self,
        name: &str,
        environment: &ValueEnvironment,
    ) -> Result<Value, MlError> {
        environment.get(name).cloned().ok_or_else(|| {
            self.error(MlErrorKind::Unbound, "lookup", format!("unbound value {name}"))
        })
    }

    fn resolve_structure(&self, path: &str) -> Result<&Namespace, MlError> {
        let mut segments = path.split('.');
        let root = segments
            .next()
            .ok_or_else(|| self.error(MlErrorKind::Unbound, "lookup", "empty structure name"))?;
        let mut namespace = self.structures.get(root).ok_or_else(|| {
            self.error(MlErrorKind::Unbound, "lookup", format!("unknown structure {root}"))
        })?;
        for segment in segments {
            namespace = namespace.lookup_structure(segment).ok_or_else(|| {
                self.error(MlErrorKind::Unbound, "lookup", format!("unknown structure {path}"))
            })?;
        }
        Ok(namespace)
    }

    fn evaluate_expr(
        &mut self,
        expression: &Expr,
        environment: &ValueEnvironment,
    ) -> Result<Value, MlError> {
        self.check_stop()?;
        match expression {
            Expr::Located(body, location) => {
                self.expression_locations.push((location.span.start, location.span.end));
                self.expression_sources.push(location.span.source_name.clone());
                let result = match &**body {
                    Expr::Raise(exception) => {
                        self.evaluate_raise(exception, environment, Some(location))
                    },
                    Expr::Apply(function, argument) => {
                        self.evaluate_application(function, argument, environment, Some(location))
                    },
                    _ => self.evaluate_expr(body, environment),
                };
                self.expression_sources.pop();
                self.expression_locations.pop();
                result
            },
            Expr::Name(name) => self.resolve_name(name, environment),
            Expr::Integer(value) => Ok(Value::int(*value)),
            Expr::Word { value, span } => {
                let key = (span.source_name.clone(), span.start, span.end);
                if self.elaborations.word32_literals.contains(&key) {
                    let value = u32::try_from(*value).map_err(|_| {
                        self.error(MlErrorKind::Type, "word literal", "Word32 literal out of range")
                    })?;
                    Ok(Value::word32(value))
                } else {
                    Ok(Value::word(*value))
                }
            },
            Expr::Real(value) => Ok(Value::real(*value)),
            Expr::Text(value) => Ok(Value::bytes(value.clone())),
            Expr::Character(value) => Ok(Value::character(*value)),
            Expr::Unit => Ok(Value::unit()),
            Expr::Tuple(values) => {
                let mut result = Vec::with_capacity(values.len());
                for value in values {
                    result.push(self.evaluate_expr(value, environment)?);
                }
                Ok(self.track_value(Value(Rc::new(ValueData::Tuple(result)))))
            },
            Expr::List(values) => {
                let mut result = Vec::with_capacity(values.len());
                for value in values {
                    result.push(self.evaluate_expr(value, environment)?);
                }
                Ok(self.track_value(Value(Rc::new(ValueData::List(result)))))
            },
            Expr::Record(fields) => {
                let mut result = BTreeMap::new();
                for (name, value) in fields {
                    result.insert(name.clone(), self.evaluate_expr(value, environment)?);
                }
                self.make_record(result)
            },
            Expr::Select(label) => {
                let label = label.clone();
                let clauses = vec![(
                    Pattern::Record(
                        vec![(label.clone(), Pattern::Variable("__selected".to_owned()))],
                        true,
                    ),
                    Expr::Name("__selected".to_owned()),
                )];
                Ok(self.track_value(Value(Rc::new(ValueData::Closure {
                    runtime: self.runtime_id,
                    clauses,
                    environment: Rc::new(RefCell::new(environment.clone())),
                    lexical: None,
                }))))
            },
            Expr::Fn(clauses) => {
                let marker = (CLOSURE_EXPRESSION_PATH, self.expression_locations.len());
                self.expression_locations.push(marker);
                let closure = self.track_value(Value(Rc::new(ValueData::Closure {
                    runtime: self.runtime_id,
                    clauses: clauses.clone(),
                    environment: Rc::new(RefCell::new(environment.clone())),
                    lexical: Some(self.capture_closure_static()),
                })));
                let recorded = self.record_anonymous_closure_input(&closure);
                self.expression_locations.pop();
                recorded?;
                Ok(closure)
            },
            Expr::Apply(function, argument) => {
                self.evaluate_application(function, argument, environment, None)
            },
            Expr::Let(declarations, body) => {
                let saved_values = std::mem::replace(&mut self.values, environment.clone());
                let saved_structures = self.structures.clone();
                let saved_signatures = self.signatures.clone();
                let saved_functors = self.functors.clone();
                let saved_types = self.type_environment.clone();
                let saved_elaborations = Rc::clone(&self.elaborations);
                let result = (|| {
                    for declaration in declarations {
                        self.evaluate_declaration(declaration)?;
                    }
                    self.evaluate_expr(body, &self.values.clone())
                })();
                self.values = saved_values;
                self.structures = saved_structures;
                self.signatures = saved_signatures;
                self.functors = saved_functors;
                self.type_environment = saved_types;
                self.elaborations = saved_elaborations;
                result
            },
            Expr::If(condition, yes, no) => {
                match self.evaluate_expr(condition, environment)?.as_bool() {
                    Some(true) => self.evaluate_expr(yes, environment),
                    Some(false) => self.evaluate_expr(no, environment),
                    None => Err(self.error(MlErrorKind::Type, "if", "condition is not bool")),
                }
            },
            Expr::While(condition, body) => loop {
                self.check_stop()?;
                match self.evaluate_expr(condition, environment)?.as_bool() {
                    Some(true) => {
                        self.evaluate_expr(body, environment)?;
                    },
                    Some(false) => return Ok(Value::unit()),
                    None => {
                        return Err(self.error(
                            MlErrorKind::Type,
                            "while",
                            "condition is not bool",
                        ));
                    },
                }
            },
            Expr::Case(target, clauses) => {
                let target = self.evaluate_expr(target, environment)?;
                self.apply_clauses(clauses, environment, &target)
            },
            Expr::Handle(body, clauses) => self.evaluate_handler(body, clauses, environment),
            Expr::Raise(body) => self.evaluate_raise(body, environment, None),
            Expr::Sequence(values) => {
                let mut output = Value::unit();
                for value in values {
                    output = self.evaluate_expr(value, environment)?;
                }
                Ok(output)
            },
            Expr::Typed(value, _) => self.evaluate_expr(value, environment),
            Expr::AndAlso(left, right) => {
                let value = self.evaluate_expr(left, environment)?;
                if value.as_bool() == Some(false) {
                    Ok(Value::bool(false))
                } else if value.as_bool() == Some(true) {
                    self.evaluate_expr(right, environment)
                } else {
                    Err(self.error(MlErrorKind::Type, "andalso", "left operand is not bool"))
                }
            },
            Expr::OrElse(left, right) => {
                let value = self.evaluate_expr(left, environment)?;
                if value.as_bool() == Some(true) {
                    Ok(Value::bool(true))
                } else if value.as_bool() == Some(false) {
                    self.evaluate_expr(right, environment)
                } else {
                    Err(self.error(MlErrorKind::Type, "orelse", "left operand is not bool"))
                }
            },
        }
    }

    fn evaluate_application(
        &mut self,
        function: &Expr,
        argument: &Expr,
        environment: &ValueEnvironment,
        location: Option<&SourceLocation>,
    ) -> Result<Value, MlError> {
        let function = self.evaluate_expr(function, environment)?;
        let (target, certified) = self.prepare_typed_application(&function)?;
        let argument = self.evaluate_expr(argument, environment)?;
        let result = if let Some(certified) = certified {
            self.typed_arguments.push(super::TypedInvocation {
                target,
                argument: certified.argument,
                result: Some(certified.result),
            });
            let result = self.apply_certified(&function, &[argument]);
            self.typed_arguments.pop();
            result
        } else {
            self.apply_certified(&function, &[argument])
        };
        result.map_err(|mut error| {
            if let Some(location) = location
                && matches!(error.kind, MlErrorKind::Exception(_))
            {
                self.append_exception_frame(&mut error, location);
            }
            error
        })
    }

    fn prepare_typed_application(
        &mut self,
        function: &Value,
    ) -> Result<(super::TypedInvocationTarget, Option<super::value::TypedCallEvidence>), MlError>
    {
        let source_name = self
            .expression_sources
            .last()
            .map_or(self.declaration_span.source_name.as_str(), String::as_str);
        let key = super::value::ExpressionKey::new(source_name, &self.expression_locations);
        let certified = self.elaborations.typed_calls.get(&key).cloned().map(|mut evidence| {
            evidence.argument = self.resolve_typed_evidence(&evidence.argument);
            evidence.result = self.resolve_typed_evidence(&evidence.result);
            evidence
        });
        let target = Self::typed_invocation_target(function);
        let intrinsic = match target {
            super::TypedInvocationTarget::Native(id) => {
                self.type_directed_natives.get(&id).cloned()
            },
            super::TypedInvocationTarget::Value(_) => None,
        };
        if let Some(intrinsic) = &intrinsic {
            if self.untyped_apply_depth > 0 {
                return Err(self.error(
                    MlErrorKind::Type,
                    "apply typed expression",
                    "untyped Vm::apply argument cannot reach a type-directed primitive",
                ));
            }
            let evidence = certified.as_ref().ok_or_else(|| {
                self.error(
                    MlErrorKind::HostFailure,
                    "apply typed expression",
                    "missing compiler-certified application type evidence",
                )
            })?;
            super::basis::printers::preflight(
                self,
                intrinsic,
                &evidence.argument,
                &evidence.weak_variables,
            )?;
        }
        Ok((target, certified))
    }

    fn evaluate_raise(
        &mut self,
        body: &Expr,
        environment: &ValueEnvironment,
        location: Option<&SourceLocation>,
    ) -> Result<Value, MlError> {
        let exception = self.evaluate_expr(body, environment)?;
        Err(self.raise_exception(&exception, location, false)?)
    }

    pub fn apply(&mut self, function: &Value, arguments: &[Value]) -> Result<Value, MlError> {
        self.untyped_apply_depth += 1;
        let result = self.apply_impl(function, arguments);
        self.untyped_apply_depth -= 1;
        result
    }

    pub(super) fn apply_certified(
        &mut self,
        function: &Value,
        arguments: &[Value],
    ) -> Result<Value, MlError> {
        self.apply_impl(function, arguments)
    }

    fn apply_impl(&mut self, function: &Value, arguments: &[Value]) -> Result<Value, MlError> {
        self.check_stop()?;
        let mut current = function.clone();
        for argument in arguments {
            self.check_stop()?;
            if self.untyped_apply_depth > 0 {
                self.validate_untyped_closure_argument(&current, argument)?;
            }
            let closure_pointer = Rc::as_ptr(&current.0) as usize;
            let certified_argument = self.certified_argument_for(&current);
            current = match &*current.0 {
                ValueData::Native(id) => {
                    self.apply_native(*id, &[], &[], None, certified_argument.as_ref(), argument)?
                },
                ValueData::NativePartial { id, arguments, argument_types, result_type } => self
                    .apply_native(
                        *id,
                        &arguments.borrow(),
                        &argument_types.borrow(),
                        result_type.borrow().as_ref(),
                        certified_argument.as_ref(),
                        argument,
                    )?,
                ValueData::HostFunction { runtime, operation } => {
                    if *runtime != self.runtime_id {
                        self.request_stop();
                        return Err(self.error(
                            MlErrorKind::HostFailure,
                            "apply",
                            "foreign runtime host function",
                        ));
                    }
                    self.call_host(operation, std::slice::from_ref(argument))?
                },
                ValueData::ConstructorFunction { stamp, name } => {
                    if (*stamp >> 64) != u128::from(self.runtime_id) {
                        self.request_stop();
                        return Err(self.error(
                            MlErrorKind::HostFailure,
                            "apply",
                            "foreign runtime constructor",
                        ));
                    }
                    self.track_value(Value(Rc::new(ValueData::Constructor {
                        stamp: *stamp,
                        name: name.clone(),
                        argument: Some(argument.clone()),
                    })))
                },
                ValueData::ExceptionFunction { identity, name } => {
                    if (*identity >> 64) != u128::from(self.runtime_id) {
                        self.request_stop();
                        return Err(self.error(
                            MlErrorKind::HostFailure,
                            "apply",
                            "foreign runtime exception",
                        ));
                    }
                    self.track_value(Value(Rc::new(ValueData::Exception {
                        identity: *identity,
                        name: name.clone(),
                        argument: Some(argument.clone()),
                    })))
                },
                ValueData::Closure { runtime, clauses, environment, lexical } => {
                    if *runtime != self.runtime_id {
                        self.request_stop();
                        return Err(self.error(
                            MlErrorKind::HostFailure,
                            "apply",
                            "foreign runtime closure",
                        ));
                    }
                    let substitutions = self.specialize_closure_argument(
                        closure_pointer,
                        0,
                        certified_argument.as_ref(),
                    )?;
                    self.with_closure_invocation(
                        closure_pointer,
                        substitutions,
                        |vm| match lexical {
                            Some(lexical) => vm.apply_lexical_clauses(
                                clauses,
                                &environment.borrow(),
                                lexical,
                                argument,
                            ),
                            None => vm.apply_clauses(clauses, &environment.borrow(), argument),
                        },
                    )?
                },
                ValueData::CurriedClosure { runtime, clauses, arguments, environment, lexical } => {
                    self.apply_curried_closure(
                        closure_pointer,
                        certified_argument.as_ref(),
                        CurriedClosureInput {
                            runtime: *runtime,
                            clauses,
                            arguments,
                            environment,
                            lexical,
                        },
                        argument,
                    )?
                },
                _ => return Err(self.error(MlErrorKind::Type, "apply", "value is not callable")),
            };
            self.check_stop()?;
        }
        Ok(current)
    }

    pub(super) fn validate_untyped_closure_argument(
        &self,
        function: &Value,
        argument: &Value,
    ) -> Result<(), MlError> {
        self.reject_foreign_value(function)?;
        self.reject_foreign_argument(argument)?;
        let pointer = Rc::as_ptr(&function.0) as usize;
        match &*function.0 {
            ValueData::Closure { .. } => self.validate_untyped_ml_argument(pointer, 0, argument),
            ValueData::CurriedClosure { arguments, .. } => {
                self.validate_untyped_ml_argument(pointer, arguments.borrow().len(), argument)
            },
            ValueData::Native(id) => {
                self.validate_untyped_function_argument(self.native_signatures.get(id), argument)
            },
            ValueData::NativePartial { result_type, .. } => {
                self.validate_untyped_function_argument(result_type.borrow().as_ref(), argument)
            },
            ValueData::ConstructorFunction { stamp, .. }
            | ValueData::ExceptionFunction { identity: stamp, .. } => {
                self.validate_untyped_constructor_argument(*stamp, argument)
            },
            _ => Ok(()),
        }
    }
    fn reject_foreign_value(&self, value: &Value) -> Result<(), MlError> {
        let is_foreign = match &*value.0 {
            ValueData::Host { id, .. } => !id.belongs_to(self.runtime_id),
            ValueData::HostFunction { runtime, .. }
            | ValueData::Closure { runtime, .. }
            | ValueData::CurriedClosure { runtime, .. } => *runtime != self.runtime_id,
            ValueData::Native(id) | ValueData::NativePartial { id, .. } => {
                !id.belongs_to(self.runtime_id, self.generation)
            },
            ValueData::Exception { identity, .. }
            | ValueData::ExceptionFunction { identity, .. }
            | ValueData::Constructor { stamp: identity, .. }
            | ValueData::ConstructorFunction { stamp: identity, .. } => {
                (*identity >> 64) != u128::from(self.runtime_id)
            },
            _ => false,
        };
        if is_foreign {
            self.request_stop();
            return Err(self.error(MlErrorKind::HostFailure, "Vm::apply", "foreign runtime value"));
        }
        Ok(())
    }

    pub(super) fn reject_foreign_argument(&self, argument: &Value) -> Result<(), MlError> {
        if matches!(
            &*argument.0,
            ValueData::Unit
                | ValueData::Int(_)
                | ValueData::Real(_)
                | ValueData::Word32(_)
                | ValueData::Word(_)
                | ValueData::Bool(_)
                | ValueData::Text(_)
                | ValueData::Character(_)
        ) {
            return Ok(());
        }
        let mut pending = vec![(argument, 0_usize)];
        let mut visited = HashSet::new();
        while let Some((value, depth)) = pending.pop() {
            self.check_stop()?;
            if depth >= MAX_HOST_TYPE_CHECK_DEPTH || visited.len() >= MAX_HOST_TYPE_CHECK_NODES {
                return Err(self.error(
                    MlErrorKind::Type,
                    "Vm::apply",
                    "argument identity check exceeded budget",
                ));
            }
            if !visited.insert(Rc::as_ptr(&value.0) as usize) {
                continue;
            }
            self.reject_foreign_value(value)?;
            match &*value.0 {
                ValueData::Tuple(values) | ValueData::List(values) | ValueData::Vector(values) => {
                    pending.extend(values.iter().map(|item| (item, depth + 1)))
                },
                ValueData::Record(values) => {
                    pending.extend(values.values().map(|item| (item, depth + 1)))
                },
                ValueData::Constructor { argument: Some(item), .. }
                | ValueData::Exception { argument: Some(item), .. } => {
                    pending.push((item, depth + 1))
                },
                _ => {},
            }
        }
        Ok(())
    }

    fn validate_untyped_ml_argument(
        &self,
        pointer: usize,
        index: usize,
        argument: &Value,
    ) -> Result<(), MlError> {
        let Some(formal) =
            self.closure_input_types.get(&pointer).and_then(|inputs| inputs.get(index))
        else {
            return Err(self.error(
                MlErrorKind::Type,
                "Vm::apply",
                "ML closure has no compiler-certified input type",
            ));
        };
        let substitutions = self.closure_type_substitutions.get(&pointer);
        let mut budget = CertifiedValueCheck::new();
        self.charge_certified_type_shape(
            formal,
            substitutions.map_or(CertifiedTypeReplacements::None, CertifiedTypeReplacements::Owned),
            0,
            &mut budget,
        )?;
        let mut formal = formal.substitute(substitutions.unwrap_or(&BTreeMap::new()));
        if let Some(views) = self.closure_type_views.get(&pointer) {
            for (public, internal) in views {
                formal.rename_constructor(public, internal);
            }
        }
        if self.closure_weak_variables.get(&pointer).is_some_and(|variables| {
            variables.iter().any(|id| type_contains_variable(&formal, *id))
        }) {
            return Err(self.error(
                MlErrorKind::Type,
                "Vm::apply",
                "closure input still depends on an unresolved weak type variable",
            ));
        }
        if type_has_variable(&formal) {
            return Err(self.error(
                MlErrorKind::Type,
                "Vm::apply",
                "untyped caller cannot instantiate a polymorphic ML closure",
            ));
        }
        if self.matches_host_value_type(argument, &formal)? {
            return Ok(());
        }
        Err(self.error(
            MlErrorKind::Type,
            "Vm::apply",
            "argument value does not match the compiler-certified closure input type",
        ))
    }

    fn validate_untyped_constructor_argument(
        &self,
        identity: u128,
        argument: &Value,
    ) -> Result<(), MlError> {
        if (identity >> 64) != u128::from(self.runtime_id) {
            self.request_stop();
            return Err(self.error(
                MlErrorKind::HostFailure,
                "Vm::apply",
                "foreign runtime constructor",
            ));
        }
        let signature = self.constructor_types.get(&identity).map(TypeScheme::body);
        self.validate_untyped_function_argument(signature, argument)
    }

    fn validate_untyped_function_argument(
        &self,
        signature: Option<&Type>,
        argument: &Value,
    ) -> Result<(), MlError> {
        let Some(Type::Function(input, result)) = signature else {
            return Err(self.error(
                MlErrorKind::Type,
                "Vm::apply",
                "function has no compiler-certified input type",
            ));
        };
        let mut budget = CertifiedValueCheck::new();
        self.charge_certified_type_shape(input, CertifiedTypeReplacements::None, 0, &mut budget)?;
        self.charge_certified_type_shape(result, CertifiedTypeReplacements::None, 0, &mut budget)?;
        if type_has_variable(input) || type_has_variable(result) {
            return Err(self.error(
                MlErrorKind::Type,
                "Vm::apply",
                "untyped caller cannot instantiate a polymorphic function",
            ));
        }
        if self.matches_host_value_type(argument, input)? {
            return Ok(());
        }
        Err(self.error(
            MlErrorKind::Type,
            "Vm::apply",
            "argument lacks compiler-certified type identity",
        ))
    }

    fn matches_host_value_type(&self, value: &Value, typ: &Type) -> Result<bool, MlError> {
        let mut check = CertifiedValueCheck::new();
        self.charge_certified_type_shape(typ, CertifiedTypeReplacements::None, 0, &mut check)?;
        self.value_matches_certified_type(value, typ, 0, &mut check)
    }

    fn charge_certified_work(
        &self,
        check: &mut CertifiedValueCheck,
        units: usize,
    ) -> Result<(), MlError> {
        self.check_stop()?;
        if units > check.remaining {
            return Err(self.error(
                MlErrorKind::Type,
                "Vm::apply",
                "argument graph exceeds certified type-check budget",
            ));
        }
        check.remaining -= units;
        Ok(())
    }

    fn charge_certified_type_shape(
        &self,
        typ: &Type,
        replacements: CertifiedTypeReplacements<'_>,
        depth: usize,
        check: &mut CertifiedValueCheck,
    ) -> Result<(), MlError> {
        if depth >= MAX_HOST_TYPE_CHECK_DEPTH {
            return Err(self.error(
                MlErrorKind::Type,
                "Vm::apply",
                "argument type exceeds certified type-check depth",
            ));
        }
        if let Type::Variable(id) = typ
            && let Some(replacement) = replacements.get(*id)
        {
            return self.charge_certified_type_shape(
                replacement,
                CertifiedTypeReplacements::None,
                depth,
                check,
            );
        }
        self.charge_certified_work(check, 1)?;
        match typ {
            Type::Variable(_) => {},
            Type::Constructor(_, types) => {
                for child in types {
                    self.charge_certified_type_shape(child, replacements, depth + 1, check)?;
                }
            },
            Type::Function(input, result) => {
                self.charge_certified_type_shape(input, replacements, depth + 1, check)?;
                self.charge_certified_type_shape(result, replacements, depth + 1, check)?;
            },
            Type::Record(fields, _) => {
                for child in fields.values() {
                    self.charge_certified_type_shape(child, replacements, depth + 1, check)?;
                }
            },
        }
        Ok(())
    }

    fn value_matches_certified_type(
        &self,
        value: &Value,
        typ: &Type,
        depth: usize,
        check: &mut CertifiedValueCheck,
    ) -> Result<bool, MlError> {
        self.check_stop()?;
        if depth >= MAX_HOST_TYPE_CHECK_DEPTH {
            return Ok(false);
        }
        self.charge_certified_work(check, 1)?;
        let key = (Rc::as_ptr(&value.0) as usize, depth, typ as *const Type as usize);
        if check.validated.contains(&key) {
            return Ok(true);
        }
        let is_valid = match typ {
            Type::Variable(_) | Type::Function(_, _) | Type::Record(_, true) => false,
            Type::Record(fields, false) => {
                self.value_matches_record_type(value, fields, depth + 1, check)?
            },
            Type::Constructor(identity, parameters) => {
                self.value_matches_constructor_type(value, identity, parameters, depth + 1, check)?
            },
        };
        if is_valid
            && matches!(
                &*value.0,
                ValueData::Tuple(_)
                    | ValueData::Record(_)
                    | ValueData::List(_)
                    | ValueData::Vector(_)
                    | ValueData::Constructor { .. }
                    | ValueData::Exception { .. }
            )
        {
            check.validated.insert(key);
        }
        Ok(is_valid)
    }

    fn value_matches_record_type(
        &self,
        value: &Value,
        fields: &BTreeMap<String, Type>,
        depth: usize,
        check: &mut CertifiedValueCheck,
    ) -> Result<bool, MlError> {
        match &*value.0 {
            ValueData::Tuple(values) => {
                if values.len() != fields.len() {
                    return Ok(false);
                }
                for (index, value) in values.iter().enumerate() {
                    let Some(typ) = fields.get(&(index + 1).to_string()) else {
                        return Ok(false);
                    };
                    if !self.value_matches_certified_type(value, typ, depth, check)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            },
            ValueData::Record(values) => {
                if values.len() != fields.len() {
                    return Ok(false);
                }
                for (name, typ) in fields {
                    let Some(value) = values.get(name) else {
                        return Ok(false);
                    };
                    if !self.value_matches_certified_type(value, typ, depth, check)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            },
            _ => Ok(false),
        }
    }
    fn value_matches_constructor_type(
        &self,
        value: &Value,
        identity: &str,
        parameters: &[Type],
        depth: usize,
        check: &mut CertifiedValueCheck,
    ) -> Result<bool, MlError> {
        match identity {
            "unit" => return Ok(matches!(&*value.0, ValueData::Unit)),
            "int" => return Ok(matches!(&*value.0, ValueData::Int(_))),
            "bool" => return Ok(matches!(&*value.0, ValueData::Bool(_))),
            "string" => return Ok(matches!(&*value.0, ValueData::Text(_))),
            "char" => return Ok(matches!(&*value.0, ValueData::Character(_))),
            "real" => return Ok(matches!(&*value.0, ValueData::Real(_))),
            "word" => return Ok(matches!(&*value.0, ValueData::Word(_))),
            "Word32.word" => return Ok(matches!(&*value.0, ValueData::Word32(_))),
            "exn" => return self.value_matches_exception_type(value, depth, check),
            "list" | "vector" | "array" | "ref" => {
                return self
                    .value_matches_container_type(value, identity, parameters, depth, check);
            },
            "option" => return self.value_matches_option_type(value, parameters, depth, check),
            _ => {},
        }
        self.value_matches_declared_constructor(value, identity, parameters, depth, check)
    }

    fn value_matches_exception_type(
        &self,
        value: &Value,
        depth: usize,
        check: &mut CertifiedValueCheck,
    ) -> Result<bool, MlError> {
        let ValueData::Exception { identity, argument, .. } = &*value.0 else {
            return Ok(false);
        };
        if (*identity >> 64) != u128::from(self.runtime_id) {
            return Ok(false);
        }
        let Some(scheme) = self.constructor_types.get(identity) else { return Ok(false) };
        match (scheme.body(), argument) {
            (Type::Constructor(name, parameters), None) => {
                Ok(name == "exn" && parameters.is_empty())
            },
            (Type::Function(input, output), Some(argument))
                if matches!(output.as_ref(), Type::Constructor(name, parameters)
                    if name == "exn" && parameters.is_empty()) =>
            {
                self.value_matches_certified_type(argument, input, depth, check)
            },
            _ => Ok(false),
        }
    }

    fn value_matches_container_type(
        &self,
        value: &Value,
        identity: &str,
        parameters: &[Type],
        depth: usize,
        check: &mut CertifiedValueCheck,
    ) -> Result<bool, MlError> {
        let [item_type] = parameters else { return Ok(false) };
        match (identity, &*value.0) {
            ("list", ValueData::List(values)) | ("vector", ValueData::Vector(values)) => {
                self.values_match_certified_type(values, item_type, depth, check)
            },
            ("array" | "ref", _) => Ok(false),
            _ => Ok(false),
        }
    }

    fn values_match_certified_type(
        &self,
        values: &[Value],
        typ: &Type,
        depth: usize,
        check: &mut CertifiedValueCheck,
    ) -> Result<bool, MlError> {
        for value in values {
            if !self.value_matches_certified_type(value, typ, depth, check)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn value_matches_option_type(
        &self,
        value: &Value,
        parameters: &[Type],
        depth: usize,
        check: &mut CertifiedValueCheck,
    ) -> Result<bool, MlError> {
        let [item_type] = parameters else { return Ok(false) };
        match &*value.0 {
            ValueData::Constructor { stamp, argument: None, .. }
                if *stamp == self.option_none_stamp =>
            {
                Ok(true)
            },
            ValueData::Constructor { stamp, argument: Some(value), .. }
                if *stamp == self.option_some_stamp =>
            {
                self.value_matches_certified_type(value, item_type, depth, check)
            },
            _ => Ok(false),
        }
    }

    fn value_matches_declared_constructor(
        &self,
        value: &Value,
        identity: &str,
        parameters: &[Type],
        depth: usize,
        check: &mut CertifiedValueCheck,
    ) -> Result<bool, MlError> {
        let ValueData::Constructor { stamp, argument, .. } = &*value.0 else {
            return Ok(false);
        };
        let Some(scheme) = self.constructor_types.get(stamp) else {
            return Ok(false);
        };
        let (input, result) = match scheme.body() {
            Type::Function(input, result) => (Some(input.as_ref()), result.as_ref()),
            result => (None, result),
        };
        let Type::Constructor(expected_identity, expected_parameters) = result else {
            return Ok(false);
        };
        if expected_identity != identity || expected_parameters.len() != parameters.len() {
            return Ok(false);
        }
        self.charge_certified_type_shape(result, CertifiedTypeReplacements::None, 0, check)?;
        let mut substitutions = BTreeMap::new();
        for (expected, actual) in expected_parameters.iter().zip(parameters) {
            if !self.merge_certified_type(expected, actual, &mut substitutions, check)? {
                return Ok(false);
            }
        }
        match (input, argument) {
            (None, None) => Ok(true),
            (Some(input), Some(argument)) => {
                let replacements = CertifiedTypeReplacements::Borrowed(&substitutions);
                self.charge_certified_type_shape(input, replacements, 0, check)?;
                for typ in substitutions.values() {
                    self.charge_certified_type_shape(
                        typ,
                        CertifiedTypeReplacements::None,
                        0,
                        check,
                    )?;
                }
                let owned_substitutions =
                    substitutions.iter().map(|(id, typ)| (*id, (*typ).clone())).collect();
                let input = Rc::new(input.substitute(&owned_substitutions));
                check.owned_types.push(Rc::clone(&input));
                self.value_matches_certified_type(argument, &input, depth, check)
            },
            _ => Ok(false),
        }
    }

    fn merge_certified_type<'a>(
        &self,
        template: &Type,
        actual: &'a Type,
        substitutions: &mut BTreeMap<u64, &'a Type>,
        check: &mut CertifiedValueCheck,
    ) -> Result<bool, MlError> {
        self.charge_certified_work(check, 1)?;
        match (template, actual) {
            (Type::Variable(id), actual) => {
                if let Some(previous) = substitutions.get(id) {
                    self.certified_types_equal(previous, actual, check)
                } else {
                    substitutions.insert(*id, actual);
                    Ok(true)
                }
            },
            (Type::Constructor(left, left_args), Type::Constructor(right, right_args)) => {
                if left != right || left_args.len() != right_args.len() {
                    return Ok(false);
                }
                for (left, right) in left_args.iter().zip(right_args) {
                    if !self.merge_certified_type(left, right, substitutions, check)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            },
            (
                Type::Function(left_input, left_output),
                Type::Function(right_input, right_output),
            ) => Ok(self.merge_certified_type(left_input, right_input, substitutions, check)?
                && self.merge_certified_type(left_output, right_output, substitutions, check)?),
            (Type::Record(left, left_open), Type::Record(right, right_open)) => {
                if left_open != right_open || left.len() != right.len() {
                    return Ok(false);
                }
                for ((left_name, left_type), (right_name, right_type)) in left.iter().zip(right) {
                    if left_name != right_name
                        || !self.merge_certified_type(
                            left_type,
                            right_type,
                            substitutions,
                            check,
                        )?
                    {
                        return Ok(false);
                    }
                }
                Ok(true)
            },
            _ => Ok(false),
        }
    }

    fn certified_types_equal(
        &self,
        left: &Type,
        right: &Type,
        check: &mut CertifiedValueCheck,
    ) -> Result<bool, MlError> {
        self.charge_certified_work(check, 1)?;
        match (left, right) {
            (Type::Variable(left), Type::Variable(right)) => Ok(left == right),
            (Type::Constructor(left_name, left), Type::Constructor(right_name, right)) => {
                if left_name != right_name || left.len() != right.len() {
                    return Ok(false);
                }
                for (left, right) in left.iter().zip(right) {
                    if !self.certified_types_equal(left, right, check)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            },
            (
                Type::Function(left_input, left_output),
                Type::Function(right_input, right_output),
            ) => Ok(self.certified_types_equal(left_input, right_input, check)?
                && self.certified_types_equal(left_output, right_output, check)?),
            (Type::Record(left, left_open), Type::Record(right, right_open)) => {
                if left_open != right_open || left.len() != right.len() {
                    return Ok(false);
                }
                for ((left_name, left_type), (right_name, right_type)) in left.iter().zip(right) {
                    if left_name != right_name
                        || !self.certified_types_equal(left_type, right_type, check)?
                    {
                        return Ok(false);
                    }
                }
                Ok(true)
            },
            _ => Ok(false),
        }
    }

    pub(super) fn capture_closure_static(&self) -> Rc<RefCell<ClosureStatic>> {
        Rc::new(RefCell::new(ClosureStatic {
            types: self.type_environment.clone(),
            structures: self.structures.clone(),
            signatures: self.signatures.clone(),
            functors: self.functors.clone(),
            elaborations: Rc::clone(&self.elaborations),
        }))
    }

    fn specialize_closure_argument(
        &self,
        pointer: usize,
        index: usize,
        actual: Option<&Type>,
    ) -> Result<BTreeMap<u64, Type>, MlError> {
        let mut substitutions =
            self.closure_type_substitutions.get(&pointer).cloned().unwrap_or_default();
        let Some(actual) = actual else {
            return Ok(substitutions);
        };
        let Some(formal) =
            self.closure_input_types.get(&pointer).and_then(|inputs| inputs.get(index))
        else {
            return Ok(substitutions);
        };
        let formal = formal.substitute(&substitutions);
        let mut actual = actual.clone();
        if let Some(views) = self.closure_type_views.get(&pointer) {
            for (public, internal) in views {
                actual.rename_constructor(public, internal);
            }
        }
        self.merge_type_evidence(&formal, &actual, &mut substitutions)?;
        Ok(substitutions)
    }

    fn with_closure_invocation<T>(
        &mut self,
        pointer: usize,
        substitutions: BTreeMap<u64, Type>,
        run: impl FnOnce(&mut Self) -> Result<T, MlError>,
    ) -> Result<T, MlError> {
        let definition_path = self.closure_definition_paths.get(&pointer).cloned();
        let previous_path = definition_path.as_ref().map(|(locations, sources)| {
            (
                std::mem::replace(&mut self.expression_locations, locations.clone()),
                std::mem::replace(&mut self.expression_sources, sources.clone()),
            )
        });
        let views = self.closure_type_views.get(&pointer).cloned().unwrap_or_default();
        self.active_closure_type_views.push(views);
        let result = self.with_type_substitutions(substitutions, run);
        self.active_closure_type_views.pop();
        if let Some((locations, sources)) = previous_path {
            self.expression_locations = locations;
            self.expression_sources = sources;
        }
        result
    }

    pub(super) fn record_active_closure_views(&mut self, pointer: usize) {
        let mut combined = BTreeMap::new();
        for views in &self.active_closure_type_views {
            combined.extend(views.clone());
        }
        if !combined.is_empty() {
            self.closure_type_views.insert(pointer, combined);
        }
    }

    fn apply_curried_closure(
        &mut self,
        pointer: usize,
        certified_argument: Option<&Type>,
        closure: CurriedClosureInput<'_>,
        argument: &Value,
    ) -> Result<Value, MlError> {
        if closure.runtime != self.runtime_id {
            self.request_stop();
            return Err(self.error(MlErrorKind::HostFailure, "apply", "foreign runtime closure"));
        }
        let argument_index = closure.arguments.borrow().len();
        let substitutions =
            self.specialize_closure_argument(pointer, argument_index, certified_argument)?;
        let mut supplied = closure.arguments.borrow().clone();
        supplied.push(argument.clone());
        if supplied.len() < closure.clauses[0].0.len() {
            let partial = self.track_value(Value(Rc::new(ValueData::CurriedClosure {
                runtime: closure.runtime,
                clauses: Rc::clone(closure.clauses),
                arguments: RefCell::new(supplied),
                environment: Rc::clone(closure.environment),
                lexical: Rc::clone(closure.lexical),
            })));
            let partial_pointer = Rc::as_ptr(&partial.0) as usize;
            if let Some(inputs) = self.closure_input_types.get(&pointer).cloned() {
                self.closure_input_types.insert(partial_pointer, inputs);
            }
            if let Some(path) = self.closure_definition_paths.get(&pointer).cloned() {
                self.closure_definition_paths.insert(partial_pointer, path);
            }
            if let Some(views) = self.closure_type_views.get(&pointer).cloned() {
                self.closure_type_views.insert(partial_pointer, views);
            }
            if let Some(weak) = self.closure_weak_variables.get(&pointer).cloned() {
                self.closure_weak_variables.insert(partial_pointer, weak);
            }
            self.closure_type_substitutions.insert(partial_pointer, substitutions);
            return Ok(partial);
        }
        self.with_closure_invocation(pointer, substitutions, |vm| {
            vm.with_closure_static(closure.lexical, |vm| {
                vm.apply_curried_clauses(closure.clauses, &closure.environment.borrow(), &supplied)
            })
        })
    }

    fn apply_curried_clauses(
        &mut self,
        clauses: &[(Vec<Pattern>, Expr)],
        environment: &ValueEnvironment,
        arguments: &[Value],
    ) -> Result<Value, MlError> {
        for (index, (patterns, body)) in clauses.iter().enumerate() {
            self.check_stop()?;
            let mut local = environment.clone();
            let mut matched = true;
            for (pattern, argument) in patterns.iter().zip(arguments) {
                match self.match_pattern(pattern, argument, &local)? {
                    Some(bindings) => local.extend(bindings),
                    None => {
                        matched = false;
                        break;
                    },
                }
            }
            if matched {
                let start = self.expression_locations.len();
                self.expression_locations.push((CLOSURE_CLAUSE_PATH, index));
                for _ in 1..patterns.len() {
                    self.expression_locations
                        .push((CLOSURE_EXPRESSION_PATH, self.expression_locations.len()));
                    self.expression_locations.push((CLOSURE_CLAUSE_PATH, 0));
                }
                let result = self.evaluate_expr(body, &local);
                self.expression_locations.truncate(start);
                return result;
            }
        }
        Err(self.raise_builtin("Match"))
    }

    fn apply_lexical_clauses(
        &mut self,
        clauses: &[(Pattern, Expr)],
        environment: &ValueEnvironment,
        lexical: &Rc<RefCell<ClosureStatic>>,
        argument: &Value,
    ) -> Result<Value, MlError> {
        self.with_closure_static(lexical, |vm| vm.apply_clauses(clauses, environment, argument))
    }

    fn with_closure_static(
        &mut self,
        lexical: &Rc<RefCell<ClosureStatic>>,
        evaluate: impl FnOnce(&mut Self) -> Result<Value, MlError>,
    ) -> Result<Value, MlError> {
        let snapshot = lexical.borrow();
        let previous_types = std::mem::replace(&mut self.type_environment, snapshot.types.clone());
        let previous_structures =
            std::mem::replace(&mut self.structures, snapshot.structures.clone());
        let previous_signatures =
            std::mem::replace(&mut self.signatures, snapshot.signatures.clone());
        let previous_functors = std::mem::replace(&mut self.functors, snapshot.functors.clone());
        let previous_elaborations =
            std::mem::replace(&mut self.elaborations, Rc::clone(&snapshot.elaborations));
        drop(snapshot);
        let result = evaluate(self);
        self.type_environment = previous_types;
        self.structures = previous_structures;
        self.signatures = previous_signatures;
        self.functors = previous_functors;
        self.elaborations = previous_elaborations;
        result
    }

    fn make_record(&mut self, mut fields: BTreeMap<String, Value>) -> Result<Value, MlError> {
        if fields.is_empty() {
            return Ok(Value::unit());
        }
        let is_tuple = fields.keys().all(|label| {
            !label.starts_with('0')
                && label.parse::<usize>().is_ok_and(|index| (1..=fields.len()).contains(&index))
        });
        if !is_tuple {
            return Ok(self.track_value(Value(Rc::new(ValueData::Record(fields)))));
        }
        let mut values = Vec::with_capacity(fields.len());
        for index in 1..=fields.len() {
            let value = fields.remove(&index.to_string()).ok_or_else(|| {
                self.error(MlErrorKind::HostFailure, "record", "numeric field disappeared")
            })?;
            values.push(value);
        }
        Ok(self.track_value(Value(Rc::new(ValueData::Tuple(values)))))
    }

    fn evaluate_handler(
        &mut self,
        body: &Expr,
        clauses: &[(Pattern, Expr)],
        environment: &ValueEnvironment,
    ) -> Result<Value, MlError> {
        let error = match self.evaluate_expr(body, environment) {
            Err(error) if matches!(error.kind, MlErrorKind::Exception(_)) => error,
            result => return result,
        };
        self.validate_exception_error(&error, "handle")?;
        let value = error.exception.as_ref().ok_or_else(|| {
            self.error(MlErrorKind::HostFailure, "handle", "exception lost value")
        })?;
        self.evaluate_matching_clause(clauses, environment, value)?.ok_or(error)
    }

    fn apply_clauses(
        &mut self,
        clauses: &[(Pattern, Expr)],
        environment: &ValueEnvironment,
        argument: &Value,
    ) -> Result<Value, MlError> {
        match self.evaluate_matching_clause(clauses, environment, argument)? {
            Some(value) => Ok(value),
            None => Err(self.raise_builtin("Match")),
        }
    }

    fn evaluate_matching_clause(
        &mut self,
        clauses: &[(Pattern, Expr)],
        environment: &ValueEnvironment,
        argument: &Value,
    ) -> Result<Option<Value>, MlError> {
        for (index, (pattern, expression)) in clauses.iter().enumerate() {
            self.check_stop()?;
            if let Some(bindings) = self.match_pattern(pattern, argument, environment)? {
                let mut local = environment.clone();
                local.extend(bindings);
                self.expression_locations.push((CLOSURE_CLAUSE_PATH, index));
                let result = self.evaluate_expr(expression, &local);
                self.expression_locations.pop();
                return result.map(Some);
            }
        }
        Ok(None)
    }

    fn snapshot_namespace(&self) -> Namespace {
        Namespace {
            values: self.values.clone(),
            structures: self.structures.clone(),
            types: BTreeMap::new(),
            type_environment: self.type_environment.clone(),
        }
    }

    fn synchronize_module_types(&mut self) {
        for (name, namespace) in &mut self.structures {
            Self::synchronize_namespace_values(namespace, &self.type_environment, name);
        }
    }

    fn synchronize_namespace_values(namespace: &mut Namespace, flat: &TypeEnvironment, path: &str) {
        namespace.type_environment.update_qualified_values(flat, path);
        for (name, child) in &mut namespace.structures {
            Self::synchronize_namespace_values(child, flat, &format!("{path}.{name}"));
        }
    }

    fn apply_preflight_namespace(&mut self, namespace: &mut Namespace, types: &TypeEnvironment) {
        let mappings = namespace
            .types
            .keys()
            .filter_map(|name| {
                let from = namespace.type_environment.type_identity(name)?;
                let to = types.type_identity(name)?;
                Some((from.to_owned(), to.to_owned()))
            })
            .collect::<Vec<_>>();
        namespace.type_environment = types.clone();
        for name in namespace.types.keys().cloned().collect::<Vec<_>>() {
            if let Some(stamp) = types.type_stamp(&name) {
                namespace.types.insert(name, stamp);
            }
        }
        for (name, child) in &mut namespace.structures {
            self.apply_preflight_namespace(child, &types.namespace_types(name));
        }
        for (from, to) in mappings {
            self.bind_closure_type_view(namespace, &to, &from);
            self.rekey_printer(&from, &to);
        }
    }

    fn with_module_closure_scope<T>(
        &mut self,
        run: impl FnOnce(&mut Self) -> Result<T, MlError>,
    ) -> Result<T, MlError> {
        self.module_closure_scopes.push(self.next_closure_epoch);
        self.module_printer_scopes.push(BTreeSet::new());
        let result = run(self);
        self.module_closure_scopes.pop();
        self.module_printer_scopes.pop();
        result
    }

    fn clone_borrowed_exported_callables(
        &mut self,
        exports: &mut Namespace,
    ) -> Result<(), MlError> {
        if self.module_closure_scopes.is_empty() {
            return Ok(());
        }
        let mut replacements = HashMap::new();
        let mut namespaces = vec![exports];
        while let Some(namespace) = namespaces.pop() {
            let mut changed = Vec::new();
            for (name, value) in namespace.values.iter() {
                let replacement = self.clone_exported_value(value, &mut replacements)?;
                if !Rc::ptr_eq(&value.0, &replacement.0) {
                    changed.push((name.clone(), replacement));
                }
            }
            namespace.values.extend(changed);
            namespaces.extend(namespace.structures.values_mut());
        }
        Ok(())
    }

    fn clone_exported_value(
        &mut self,
        root: &Value,
        replacements: &mut HashMap<usize, Value>,
    ) -> Result<Value, MlError> {
        let mut pending = vec![(root.clone(), false)];
        while let Some((value, is_ready)) = pending.pop() {
            self.check_stop()?;
            let pointer = Rc::as_ptr(&value.0) as usize;
            if replacements.contains_key(&pointer) {
                continue;
            }
            if !is_ready {
                pending.push((value.clone(), true));
                for_each_export_child(&value, |child| pending.push((child.clone(), false)));
                continue;
            }
            let replacement = self
                .clone_borrowed_callable(&value)
                .or_else(|| {
                    replace_export_children(&value, replacements)
                        .map(|value| self.track_value(value))
                })
                .unwrap_or(value);
            replacements.insert(pointer, replacement);
        }
        Ok(replacements
            .get(&(Rc::as_ptr(&root.0) as usize))
            .cloned()
            .unwrap_or_else(|| root.clone()))
    }

    fn clone_borrowed_callable(&mut self, value: &Value) -> Option<Value> {
        let original = Rc::as_ptr(&value.0) as usize;
        if self
            .closure_creation_epoch
            .get(&original)
            .is_some_and(|created| self.module_closure_scopes.iter().all(|start| created > start))
        {
            return None;
        }
        let replacement = self.track_value(clone_exported_callable(value)?);
        self.copy_closure_metadata(original, Rc::as_ptr(&replacement.0) as usize);
        Some(replacement)
    }

    fn copy_closure_metadata(&mut self, original: usize, pointer: usize) {
        if let Some(types) = self.closure_input_types.get(&original).cloned() {
            self.closure_input_types.insert(pointer, types);
        }
        if let Some(substitutions) = self.closure_type_substitutions.get(&original).cloned() {
            self.closure_type_substitutions.insert(pointer, substitutions);
        }
        if let Some(variables) = self.closure_weak_variables.get(&original).cloned() {
            self.closure_weak_variables.insert(pointer, variables);
        }
        if let Some(paths) = self.closure_definition_paths.get(&original).cloned() {
            self.closure_definition_paths.insert(pointer, paths);
        }
        if let Some(views) = self.closure_type_views.get(&original).cloned() {
            self.closure_type_views.entry(pointer).or_default().extend(views);
        }
    }

    fn adapt_dereferenced_callback(&mut self, value: Value) -> Value {
        if self.untyped_apply_depth > 0 {
            return value;
        }
        let Some(result_type) = self.native_result_type() else {
            return value;
        };
        let Some(Type::Constructor(reference, parameters)) = self.native_argument_type(0) else {
            return value;
        };
        if reference != "ref" || parameters.as_slice() != std::slice::from_ref(&result_type) {
            return value;
        }
        let Type::Function(actual_input, _) = result_type else {
            return value;
        };
        let original = Rc::as_ptr(&value.0) as usize;
        let Some(formal) =
            self.closure_input_types.get(&original).and_then(|inputs| inputs.first())
        else {
            return value;
        };
        let substitutions =
            self.closure_type_substitutions.get(&original).cloned().unwrap_or_default();
        let formal = formal.substitute(&substitutions);
        let (Type::Constructor(public, actual_args), Type::Constructor(internal, formal_args)) =
            (actual_input.as_ref(), &formal)
        else {
            return value;
        };
        if public == internal
            || actual_args != formal_args
            || !self.opaque_type_identities.contains(public)
        {
            return value;
        }
        if self.closure_type_views.get(&original).is_some_and(|views| views.contains_key(public)) {
            return value;
        }
        let Some(replacement) = clone_exported_callable(&value) else { return value };
        let replacement = self.track_value(replacement);
        let pointer = Rc::as_ptr(&replacement.0) as usize;
        self.copy_closure_metadata(original, pointer);
        self.closure_type_views
            .entry(pointer)
            .or_default()
            .insert(public.clone(), internal.clone());
        replacement
    }

    fn bind_closure_type_view(&mut self, namespace: &Namespace, public: &str, internal: &str) {
        let mut pending = Vec::new();
        collect_namespace_values(namespace, &mut pending);
        let mut visited = BTreeSet::new();
        while let Some(value) = pending.pop() {
            let pointer = Rc::as_ptr(&value.0) as usize;
            if !visited.insert(pointer) {
                continue;
            }
            if matches!(
                &*value.0,
                ValueData::Closure { .. }
                    | ValueData::CurriedClosure { .. }
                    | ValueData::NativePartial { .. }
            ) && self.closure_creation_epoch.get(&pointer).is_some_and(|created| {
                !self.module_closure_scopes.is_empty()
                    && self.module_closure_scopes.iter().all(|start| created > start)
            }) {
                let views = self.closure_type_views.entry(pointer).or_default();
                let mut resolved = internal.to_owned();
                for _ in 0..views.len() {
                    let Some(next) = views.get(&resolved) else { break };
                    resolved = next.clone();
                }
                views.insert(public.to_owned(), resolved);
            }
            append_closure_view_children(&value, &mut pending);
        }
    }

    fn evaluate_module(&mut self, module: &ModuleExpr) -> Result<Namespace, MlError> {
        let printer_registry = self.printer_registry.clone();
        let printer_aliases = self.printer_aliases.clone();
        let sealed_printers = self.sealed_printers.clone();
        let closure_type_views = self.closure_type_views.clone();
        let result = self.evaluate_module_at(module, &[]);
        if result.is_err() {
            self.printer_registry = printer_registry;
            self.printer_aliases = printer_aliases;
            self.sealed_printers = sealed_printers;
            self.closure_type_views = closure_type_views;
        }
        result
    }

    fn evaluate_module_at(
        &mut self,
        module: &ModuleExpr,
        path: &[u8],
    ) -> Result<Namespace, MlError> {
        match module {
            ModuleExpr::Name(name) => Ok(self.resolve_structure(name)?.clone()),
            ModuleExpr::Struct(body) => self.evaluate_struct(body),
            ModuleExpr::Apply(name, argument) => self.apply_functor(name, argument, path),
            ModuleExpr::Constrained(body, signature, opaque) => {
                self.with_module_closure_scope(|vm| {
                    let mut inner_path = path.to_vec();
                    inner_path.push(1);
                    let mut result = vm.evaluate_module_at(body, &inner_path)?;
                    vm.constrain_namespace(&mut result, signature, *opaque)?;
                    Ok(result)
                })
            },
        }
    }

    fn evaluate_struct(&mut self, body: &[Declaration]) -> Result<Namespace, MlError> {
        let saved_values = self.values.clone();
        let saved_structures = self.structures.clone();
        let saved_signatures = self.signatures.clone();
        let saved_functors = self.functors.clone();
        let saved_types = self.type_environment.clone();
        let result = (|| {
            let mut exports = ExportNames::default();
            for declaration in body {
                exports.extend(self.evaluate_scoped_declaration(declaration)?);
            }
            Ok(Namespace {
                values: self.values.select(&exports.values),
                structures: self
                    .structures
                    .iter()
                    .filter(|(name, _)| exports.structures.contains(*name))
                    .map(|(name, value)| (name.clone(), value.clone()))
                    .collect(),
                types: exports
                    .types
                    .iter()
                    .filter_map(|name| {
                        self.type_environment.type_stamp(name).map(|stamp| (name.clone(), stamp))
                    })
                    .collect(),
                type_environment: self.type_environment.select(&exports.values, &exports.types),
            })
        })();
        self.values = saved_values;
        self.structures = saved_structures;
        self.signatures = saved_signatures;
        self.functors = saved_functors;
        self.type_environment = saved_types;
        result
    }

    fn apply_functor(
        &mut self,
        name: &str,
        argument: &ModuleExpr,
        path: &[u8],
    ) -> Result<Namespace, MlError> {
        let functor = self.functors.get(name).cloned().ok_or_else(|| {
            self.error(MlErrorKind::Unbound, "functor", format!("unknown functor {name}"))
        })?;
        let key = ApplicationKey::at(&self.declaration_span, path);
        let Some(prepared) = self.elaborations.application(&key).cloned() else {
            self.request_stop();
            return Err(self.error(
                MlErrorKind::HostFailure,
                "functor",
                format!("missing preflight for application of {name} at {:?}", key.declaration),
            ));
        };
        let mut argument_path = path.to_vec();
        argument_path.push(0);
        let argument = self.evaluate_module_at(argument, &argument_path)?;
        let saved_values = std::mem::replace(&mut self.values, functor.environment.values);
        let saved_structures =
            std::mem::replace(&mut self.structures, functor.environment.structures);
        let saved_signatures = std::mem::replace(&mut self.signatures, functor.signatures);
        let saved_functors = std::mem::replace(&mut self.functors, functor.functors);
        let saved_types =
            std::mem::replace(&mut self.type_environment, functor.environment.type_environment);
        let saved_elaborations = std::mem::replace(&mut self.elaborations, prepared);
        let result = (|| {
            let mut checked = argument;
            self.constrain_namespace(&mut checked, &functor.signature, false)?;
            self.type_environment.register_namespace(&functor.parameter, &checked);
            self.values.bind_namespace(&functor.parameter, &checked);
            self.structures.insert(functor.parameter, checked);
            self.evaluate_module(&functor.body)
        })();
        self.values = saved_values;
        self.structures = saved_structures;
        self.signatures = saved_signatures;
        self.functors = saved_functors;
        self.type_environment = saved_types;
        self.elaborations = saved_elaborations;
        result
    }

    fn extend_signature(&self, output: &mut Vec<Specification>, name: &str) -> Result<(), MlError> {
        let signature = self.signatures.get(name).ok_or_else(|| {
            self.error(MlErrorKind::Type, "signature", format!("unknown included signature {name}"))
        })?;
        output.extend(signature.specifications.iter().cloned());
        Ok(())
    }

    fn constrain_namespace(
        &mut self,
        namespace: &mut Namespace,
        expression: &SignatureExpr,
        opaque: bool,
    ) -> Result<(), MlError> {
        let signature = Signature::resolve(
            expression,
            &self.signatures,
            &self.type_environment,
            &self.current_span(),
        )?;
        let printer_registry = self.printer_registry.clone();
        let printer_aliases = self.printer_aliases.clone();
        let sealed_printers = self.sealed_printers.clone();
        let closure_type_views = self.closure_type_views.clone();
        let result = self.constrain_namespace_with_seals(
            namespace,
            &signature,
            opaque,
            "",
            &mut BTreeMap::new(),
        );
        if result.is_err() {
            self.printer_registry = printer_registry;
            self.printer_aliases = printer_aliases;
            self.sealed_printers = sealed_printers;
            self.closure_type_views = closure_type_views;
        }
        result
    }

    fn constrain_namespace_with_seals(
        &mut self,
        namespace: &mut Namespace,
        signature: &Signature,
        opaque: bool,
        prefix: &str,
        shared: &mut BTreeMap<String, (String, u128)>,
    ) -> Result<(), MlError> {
        if opaque {
            self.collect_sharing_seals(namespace, &signature.specifications, prefix, shared)?;
        }
        let mut exports = Namespace::default();
        let mut manifest = BTreeSet::new();
        let mut check_types = signature.type_environment.as_ref().clone();
        check_types.extend_exports(&namespace.type_environment);
        for (child_name, child) in &namespace.structures {
            check_types.register_namespace(child_name, child);
        }
        for specification in &signature.specifications {
            self.check_signature_spec(
                namespace,
                &check_types,
                &mut exports,
                &mut manifest,
                specification,
                &mut SealingContext { opaque, prefix, shared: &mut *shared },
            )?;
        }
        let value_names = exports.values.keys().cloned().collect();
        let type_names = exports.types.keys().cloned().collect();
        exports.type_environment = namespace.type_environment.select(&value_names, &type_names);
        for name in &value_names {
            if !exports.values.is_constructor(name) {
                exports.type_environment.hide_value_constructor(name);
            }
        }
        let mut printer_seals = Vec::new();
        if opaque {
            for type_name in &type_names {
                if manifest.contains(type_name) {
                    continue;
                }
                let is_equality = signature
                    .specifications
                    .iter()
                    .find_map(|specification| match specification {
                        Specification::Type { name, equality, .. } if name == type_name => {
                            Some(*equality)
                        },
                        _ => None,
                    })
                    .unwrap_or_else(|| {
                        namespace.type_environment.type_admits_equality(type_name).unwrap_or(false)
                    });
                let internal_identity = exports
                    .type_environment
                    .type_identity(type_name)
                    .map(str::to_owned)
                    .ok_or_else(|| {
                        self.error(
                            MlErrorKind::Type,
                            "signature",
                            format!("missing type {type_name}"),
                        )
                    })?;
                let stamp = exports
                    .type_environment
                    .seal_type(
                        type_name,
                        is_equality,
                        shared.get(&format!("{prefix}{type_name}")).cloned(),
                    )
                    .ok_or_else(|| {
                        self.error(
                            MlErrorKind::Type,
                            "signature",
                            format!("missing type {type_name}"),
                        )
                    })?;
                exports.types.insert(type_name.clone(), stamp);
                let public_identity = exports
                    .type_environment
                    .type_identity(type_name)
                    .map(str::to_owned)
                    .ok_or_else(|| {
                        self.error(
                            MlErrorKind::HostFailure,
                            "signature",
                            format!("sealed type {type_name} lost its identity"),
                        )
                    })?;
                printer_seals.push((internal_identity, public_identity));
            }
        }
        self.export_constrained_schemes(namespace, signature, &mut exports)?;
        if !printer_seals.is_empty() {
            self.clone_borrowed_exported_callables(&mut exports)?;
        }
        for (from, to) in printer_seals {
            self.bind_closure_type_view(&exports, &to, &from);
            super::basis::printers::freeze_sealed_printer(self, &from, &to)?;
            self.rekey_printer(&from, &to);
        }
        *namespace = exports;
        Ok(())
    }

    // Keep every specification case here: export and manifest updates must follow source order.
    fn check_signature_spec(
        &mut self,
        namespace: &Namespace,
        types: &TypeEnvironment,
        exports: &mut Namespace,
        manifest: &mut BTreeSet<String>,
        specification: &Specification,
        sealing: &mut SealingContext<'_>,
    ) -> Result<(), MlError> {
        match specification {
            Specification::Value(name, typ) => {
                types.check_value_spec(name, typ, self.current_span())?;
                self.export_signature_value(namespace, exports, name, false)
            },
            Specification::Exception(name, argument) => {
                self.check_signature_exception(namespace, types, exports, name, argument)
            },
            Specification::Type { name, parameters, equality, definition } => {
                self.export_signature_type(namespace, exports, name, parameters.len(), *equality)?;
                if let Some(definition) = definition {
                    types.check_type_spec(name, parameters, definition, self.current_span())?;
                    manifest.insert(name.clone());
                }
                Ok(())
            },
            Specification::Datatype(name, parameters, constructors) => self
                .check_signature_datatype(
                    namespace,
                    types,
                    exports,
                    name,
                    parameters,
                    constructors,
                ),
            Specification::DatatypeReplication(name, source) => {
                self.check_signature_replication(namespace, types, exports, manifest, name, source)
            },
            Specification::Structure(name, signature) => {
                let mut structure = namespace.structures.get(name).cloned().ok_or_else(|| {
                    self.error(MlErrorKind::Type, "signature", format!("missing structure {name}"))
                })?;
                let signature =
                    Signature::resolve(signature, &self.signatures, types, &self.current_span())?;
                self.constrain_namespace_with_seals(
                    &mut structure,
                    &signature,
                    sealing.opaque,
                    &format!("{}{name}.", sealing.prefix),
                    &mut *sealing.shared,
                )?;
                exports.structures.insert(name.clone(), structure);
                Ok(())
            },
            Specification::Sharing(paths) => self.check_signature_sharing(namespace, paths),
            Specification::WhereType { name, parameters, definition } => {
                if !exports.types.contains_key(name) {
                    return Err(self.error(
                        MlErrorKind::Type,
                        "signature",
                        format!("where type requires signature type {name}"),
                    ));
                }
                types.check_type_spec(name, parameters, definition, self.current_span())?;
                manifest.insert(name.clone());
                Ok(())
            },
            Specification::Include(name) => Err(self.error(
                MlErrorKind::Type,
                "signature",
                format!("unresolved include {name}"),
            )),
        }
    }
    fn check_signature_exception(
        &self,
        namespace: &Namespace,
        types: &TypeEnvironment,
        exports: &mut Namespace,
        name: &str,
        argument: &Option<super::TypeExpr>,
    ) -> Result<(), MlError> {
        let typ = match argument {
            Some(argument) => super::TypeExpr::Function(
                Box::new(argument.clone()),
                Box::new(super::TypeExpr::Named("exn".to_owned(), Vec::new())),
            ),
            None => super::TypeExpr::Named("exn".to_owned(), Vec::new()),
        };
        types.check_value_spec(name, &typ, self.current_span())?;
        let value = namespace.values.get(name).ok_or_else(|| {
            self.error(MlErrorKind::Type, "signature", format!("missing exception {name}"))
        })?;
        if !matches!(&*value.0, ValueData::Exception { .. } | ValueData::ExceptionFunction { .. }) {
            return Err(self.error(
                MlErrorKind::Type,
                "signature",
                format!("{name} is not an exception constructor"),
            ));
        }
        self.export_signature_value(namespace, exports, name, true)
    }

    fn check_signature_datatype(
        &self,
        namespace: &Namespace,
        types: &TypeEnvironment,
        exports: &mut Namespace,
        name: &str,
        parameters: &[String],
        constructors: &[(String, Option<super::TypeExpr>)],
    ) -> Result<(), MlError> {
        self.export_signature_type(namespace, exports, name, parameters.len(), false)?;
        for (constructor, argument) in constructors {
            let typ = datatype_constructor_type(name, parameters, argument);
            types.check_value_spec(constructor, &typ, self.current_span())?;
            self.export_signature_value(namespace, exports, constructor, true)?;
        }
        Ok(())
    }

    fn check_signature_replication(
        &self,
        namespace: &Namespace,
        types: &TypeEnvironment,
        exports: &mut Namespace,
        manifest: &mut BTreeSet<String>,
        name: &str,
        source: &str,
    ) -> Result<(), MlError> {
        let arity = namespace
            .type_environment
            .type_arity(source)
            .or_else(|| types.type_arity(source))
            .ok_or_else(|| {
                self.error(
                    MlErrorKind::Type,
                    "signature",
                    format!("unknown replicated datatype {source}"),
                )
            })?;
        self.export_signature_type(namespace, exports, name, arity, false)?;
        let original = namespace.lookup_type_identity(name);
        let required =
            namespace.lookup_type_identity(source).or_else(|| types.type_identity(source));
        if original.is_none() || original != required {
            return Err(self.error(
                MlErrorKind::Type,
                "signature",
                format!("datatype {name} does not replicate {source}"),
            ));
        }
        let constructors =
            namespace.type_environment.replicated_constructors(name).ok_or_else(|| {
                self.error(MlErrorKind::Type, "signature", format!("unknown datatype {name}"))
            })?;
        for (constructor, _) in constructors {
            self.export_signature_value(namespace, exports, &constructor, true)?;
        }
        manifest.insert(name.to_owned());
        Ok(())
    }

    fn check_signature_sharing(
        &self,
        namespace: &Namespace,
        paths: &[String],
    ) -> Result<(), MlError> {
        let first = paths.first().and_then(|path| namespace.lookup_type_shape(path));
        if first.is_none()
            || paths.iter().skip(1).any(|path| namespace.lookup_type_shape(path) != first)
        {
            return Err(self.error(
                MlErrorKind::Type,
                "sharing",
                format!("type identities do not agree: {}", paths.join(" = ")),
            ));
        }
        Ok(())
    }

    fn collect_sharing_seals(
        &self,
        source: &Namespace,
        specifications: &[Specification],
        prefix: &str,
        shared: &mut BTreeMap<String, (String, u128)>,
    ) -> Result<(), MlError> {
        for specification in specifications {
            let Specification::Sharing(paths) = specification else { continue };
            let first = paths.first().and_then(|path| source.lookup_type_shape(path));
            if first.is_none()
                || paths.iter().skip(1).any(|path| source.lookup_type_shape(path) != first)
            {
                return Err(self.error(
                    MlErrorKind::Type,
                    "sharing",
                    format!("type identities do not agree: {}", paths.join(" = ")),
                ));
            }
            let existing = paths
                .iter()
                .filter_map(|path| shared.get(&format!("{prefix}{path}")).cloned())
                .collect::<Vec<_>>();
            let identity =
                existing.first().cloned().unwrap_or_else(super::types::fresh_type_identity);
            for previous in existing.into_iter().filter(|previous| previous != &identity) {
                for binding in shared.values_mut() {
                    if *binding == previous {
                        *binding = identity.clone();
                    }
                }
            }
            for path in paths {
                shared.insert(format!("{prefix}{path}"), identity.clone());
            }
        }
        Ok(())
    }

    fn current_span(&self) -> super::Span {
        self.declaration_span.clone()
    }

    fn export_constrained_schemes(
        &self,
        original: &Namespace,
        signature: &Signature,
        exports: &mut Namespace,
    ) -> Result<(), MlError> {
        let mut types = signature.type_environment.as_ref().clone();
        types.extend_exports(&original.type_environment);
        types.extend_exports(&exports.type_environment);
        for (name, structure) in &exports.structures {
            types.register_namespace(name, structure);
        }
        for specification in &signature.specifications {
            match specification {
                Specification::Value(name, typ) => {
                    let scheme = types.signature_scheme(typ, self.current_span())?;
                    exports.type_environment.install_signature_scheme(name, scheme);
                },
                Specification::Exception(name, argument) => {
                    let typ = match argument {
                        Some(argument) => super::TypeExpr::Function(
                            Box::new(argument.clone()),
                            Box::new(super::TypeExpr::Named("exn".to_owned(), Vec::new())),
                        ),
                        None => super::TypeExpr::Named("exn".to_owned(), Vec::new()),
                    };
                    let scheme = types.signature_scheme(&typ, self.current_span())?;
                    exports.type_environment.install_signature_scheme(name, scheme);
                },
                Specification::Datatype(name, parameters, constructors) => {
                    for (constructor, argument) in constructors {
                        let typ = datatype_constructor_type(name, parameters, argument);
                        let scheme = types.signature_scheme(&typ, self.current_span())?;
                        exports.type_environment.install_signature_scheme(constructor, scheme);
                    }
                },
                _ => {},
            }
        }
        Ok(())
    }

    fn export_signature_type(
        &self,
        source: &Namespace,
        exports: &mut Namespace,
        name: &str,
        arity: usize,
        equality: bool,
    ) -> Result<(), MlError> {
        let types = &source.type_environment;
        let actual_arity = types.type_arity(name).ok_or_else(|| {
            self.error(MlErrorKind::Type, "signature", format!("missing type {name}"))
        })?;
        if actual_arity != arity || (equality && types.type_admits_equality(name) != Some(true)) {
            return Err(self.error(
                MlErrorKind::Type,
                "signature",
                format!("incompatible type specification {name}"),
            ));
        }
        exports.types.insert(name.to_owned(), types.type_stamp(name).unwrap_or(0));
        Ok(())
    }

    fn export_signature_value(
        &self,
        source: &Namespace,
        exports: &mut Namespace,
        name: &str,
        is_constructor: bool,
    ) -> Result<(), MlError> {
        let value = source.values.get(name).cloned().ok_or_else(|| {
            self.error(MlErrorKind::Type, "signature", format!("missing value {name}"))
        })?;
        if is_constructor && !source.values.is_constructor(name) {
            return Err(self.error(
                MlErrorKind::Type,
                "signature",
                format!("{name} is not a constructor"),
            ));
        }
        exports.values.insert(name.to_owned(), value);
        if is_constructor {
            exports.values.mark_constructor(name);
        }
        Ok(())
    }

    fn register_basis_native(
        &mut self,
        name: &str,
        scheme: TypeScheme,
        callback: super::NativeFunction,
    ) -> super::NativeFunctionId {
        let id = super::NativeFunctionId::new(
            self.runtime_id,
            self.generation,
            self.native_functions.len(),
        );
        self.native_functions.push((callback, 1));
        self.type_environment.register(name, scheme);
        self.values.insert(name.to_owned(), Value::native(id));
        id
    }

    pub(super) fn install_basis(&mut self) {
        let int = Type::Constructor("int".to_owned(), vec![]);
        let bool_type = Type::Constructor("bool".to_owned(), vec![]);
        let number = Type::Variable(1);
        let binary_number = Type::Function(
            Box::new(Type::Record(
                BTreeMap::from([
                    ("1".to_owned(), number.clone()),
                    ("2".to_owned(), number.clone()),
                ]),
                false,
            )),
            Box::new(number.clone()),
        );
        for (name, callback) in
            [("+", add as super::NativeFunction), ("-", subtract), ("*", multiply)]
        {
            self.register_basis_native(
                name,
                TypeScheme::polymorphic(vec![1], binary_number.clone()),
                callback,
            );
        }
        self.register_basis_native(
            "~",
            TypeScheme::polymorphic(
                vec![1],
                Type::Function(Box::new(number.clone()), Box::new(number.clone())),
            ),
            negate,
        );
        for (name, callback) in [
            ("<", less as super::NativeFunction),
            ("<=", less_equal),
            (">", greater),
            (">=", greater_equal),
        ] {
            let Type::Function(input, _) = &binary_number else { unreachable!() };
            self.register_basis_native(
                name,
                TypeScheme::polymorphic(
                    vec![1],
                    Type::Function(input.clone(), Box::new(bool_type.clone())),
                ),
                callback,
            );
        }
        let binary_int = Type::Function(
            Box::new(Type::Record(
                BTreeMap::from([("1".to_owned(), int.clone()), ("2".to_owned(), int.clone())]),
                false,
            )),
            Box::new(int.clone()),
        );
        for (name, callback) in [("div", divide as super::NativeFunction), ("mod", modulo)] {
            self.register_basis_native(name, TypeScheme::mono(binary_int.clone()), callback);
        }
        let equality = TypeScheme::polymorphic(
            vec![1],
            Type::Function(
                Box::new(Type::Record(
                    BTreeMap::from([
                        ("1".to_owned(), Type::Variable(1)),
                        ("2".to_owned(), Type::Variable(1)),
                    ]),
                    false,
                )),
                Box::new(bool_type.clone()),
            ),
        )
        .requiring_equality(1);
        self.register_basis_native("=", equality.clone(), equal);
        self.register_basis_native("<>", equality, not_equal);
        self.install_pure_basis();
        let reference_constructor = self.register_basis_native(
            "ref",
            TypeScheme::polymorphic(
                vec![1],
                Type::Function(
                    Box::new(Type::Variable(1)),
                    Box::new(Type::Constructor("ref".to_owned(), vec![Type::Variable(1)])),
                ),
            ),
            make_ref,
        );
        self.basis_ref_constructor = Some(reference_constructor);
        self.type_environment.register_value_constructor("ref");
        self.values.mark_constructor("ref");
        self.register_basis_native(
            "!",
            TypeScheme::polymorphic(
                vec![1],
                Type::Function(
                    Box::new(Type::Constructor("ref".to_owned(), vec![Type::Variable(1)])),
                    Box::new(Type::Variable(1)),
                ),
            ),
            dereference,
        );
        self.register_basis_native(
            ":=",
            TypeScheme::polymorphic(
                vec![1],
                Type::Function(
                    Box::new(Type::Record(
                        BTreeMap::from([
                            (
                                "1".to_owned(),
                                Type::Constructor("ref".to_owned(), vec![Type::Variable(1)]),
                            ),
                            ("2".to_owned(), Type::Variable(1)),
                        ]),
                        false,
                    )),
                    Box::new(Type::Constructor("unit".to_owned(), vec![])),
                ),
            ),
            assign,
        );
        for name in ["true", "false"] {
            self.register_value(
                name,
                TypeScheme::mono(bool_type.clone()),
                Value::bool(name == "true"),
            );
            self.type_environment.register_value_constructor(name);
            self.values.mark_constructor(name);
        }
        let overflow = self.fresh_identity();
        let overflow_exception = Value(Rc::new(ValueData::Exception {
            identity: overflow,
            name: "Overflow".to_owned(),
            argument: None,
        }));
        self.basis_exceptions.insert("Overflow".to_owned(), overflow_exception.clone());
        self.values.insert("Overflow".to_owned(), overflow_exception);
        self.type_environment
            .register("Overflow", TypeScheme::mono(Type::Constructor("exn".to_owned(), vec![])));
        self.type_environment.register_value_constructor("Overflow");
        self.values.mark_constructor("Overflow");
        let div = self.fresh_identity();
        let div_exception = Value(Rc::new(ValueData::Exception {
            identity: div,
            name: "Div".to_owned(),
            argument: None,
        }));
        self.basis_exceptions.insert("Div".to_owned(), div_exception.clone());
        self.values.insert("Div".to_owned(), div_exception);
        self.type_environment
            .register("Div", TypeScheme::mono(Type::Constructor("exn".to_owned(), vec![])));
        self.type_environment.register_value_constructor("Div");
        self.values.mark_constructor("Div");
        let matched = self.fresh_identity();
        let match_exception = Value(Rc::new(ValueData::Exception {
            identity: matched,
            name: "Match".to_owned(),
            argument: None,
        }));
        self.basis_exceptions.insert("Match".to_owned(), match_exception.clone());
        self.values.insert("Match".to_owned(), match_exception);
        self.type_environment
            .register("Match", TypeScheme::mono(Type::Constructor("exn".to_owned(), vec![])));
        self.type_environment.register_value_constructor("Match");
        self.values.mark_constructor("Match");
    }

    pub(super) fn raise_builtin(&self, name: &str) -> MlError {
        let operation = if name == "Match" { "match" } else { "arithmetic" };
        let exception = self.basis_exceptions.get(name).cloned();
        let Some(exception) = exception else {
            return self.error(
                MlErrorKind::HostFailure,
                operation,
                format!("missing Basis exception {name}"),
            );
        };
        let ValueData::Exception { identity, .. } = &*exception.0 else {
            return self.error(
                MlErrorKind::HostFailure,
                operation,
                format!("invalid Basis exception {name}"),
            );
        };
        let mut error = self.error(MlErrorKind::Exception(*identity), operation, name);
        error.exception = Some(exception);
        error
    }
}

fn clone_exported_callable(value: &Value) -> Option<Value> {
    let replacement = match &*value.0 {
        ValueData::Closure { runtime, clauses, environment, lexical } => ValueData::Closure {
            runtime: *runtime,
            clauses: clauses.clone(),
            environment: Rc::clone(environment),
            lexical: lexical.clone(),
        },
        ValueData::CurriedClosure { runtime, clauses, arguments, environment, lexical } => {
            ValueData::CurriedClosure {
                runtime: *runtime,
                clauses: Rc::clone(clauses),
                arguments: RefCell::new(arguments.borrow().clone()),
                environment: Rc::clone(environment),
                lexical: Rc::clone(lexical),
            }
        },
        ValueData::NativePartial { id, arguments, argument_types, result_type } => {
            ValueData::NativePartial {
                id: *id,
                arguments: RefCell::new(arguments.borrow().clone()),
                argument_types: RefCell::new(argument_types.borrow().clone()),
                result_type: RefCell::new(result_type.borrow().clone()),
            }
        },
        _ => return None,
    };
    Some(Value(Rc::new(replacement)))
}

// Only immutable spines may be copied: refs/arrays retain their shared ML identity.
fn for_each_export_child(value: &Value, mut visit: impl FnMut(&Value)) {
    match &*value.0 {
        ValueData::Tuple(values) | ValueData::List(values) | ValueData::Vector(values) => {
            values.iter().for_each(visit);
        },
        ValueData::Record(values) => values.values().for_each(visit),
        ValueData::Constructor { argument, .. } | ValueData::Exception { argument, .. } => {
            if let Some(argument) = argument {
                visit(argument);
            }
        },
        _ => {},
    }
}

fn replace_export_children(value: &Value, replacements: &HashMap<usize, Value>) -> Option<Value> {
    let replacement = |child: &Value| {
        replacements.get(&(Rc::as_ptr(&child.0) as usize)).cloned().unwrap_or_else(|| child.clone())
    };
    let mut has_changes = false;
    for_each_export_child(value, |child| {
        has_changes |= replacements
            .get(&(Rc::as_ptr(&child.0) as usize))
            .is_some_and(|mapped| !Rc::ptr_eq(&child.0, &mapped.0));
    });
    if !has_changes {
        return None;
    }
    let updated = match &*value.0 {
        ValueData::Tuple(values) => ValueData::Tuple(values.iter().map(replacement).collect()),
        ValueData::List(values) => ValueData::List(values.iter().map(replacement).collect()),
        ValueData::Vector(values) => ValueData::Vector(values.iter().map(replacement).collect()),
        ValueData::Record(values) => ValueData::Record(
            values.iter().map(|(name, child)| (name.clone(), replacement(child))).collect(),
        ),
        ValueData::Constructor { stamp, name, argument } => ValueData::Constructor {
            stamp: *stamp,
            name: name.clone(),
            argument: argument.as_ref().map(replacement),
        },
        ValueData::Exception { identity, name, argument } => ValueData::Exception {
            identity: *identity,
            name: name.clone(),
            argument: argument.as_ref().map(replacement),
        },
        _ => return None,
    };
    Some(Value(Rc::new(updated)))
}

fn collect_namespace_values(namespace: &Namespace, output: &mut Vec<Value>) {
    output.extend(namespace.values.values().cloned());
    for child in namespace.structures.values() {
        collect_namespace_values(child, output);
    }
}

fn append_closure_view_children(value: &Value, output: &mut Vec<Value>) {
    match &*value.0 {
        ValueData::Tuple(values) | ValueData::List(values) | ValueData::Vector(values) => {
            output.extend(values.iter().cloned());
        },
        ValueData::Record(values) => output.extend(values.values().cloned()),
        ValueData::Array(values) => output.extend(values.borrow().iter().cloned()),
        ValueData::Constructor { argument, .. } | ValueData::Exception { argument, .. } => {
            output.extend(argument.iter().cloned());
        },
        ValueData::Closure { .. } | ValueData::CurriedClosure { .. } => {},
        ValueData::NativePartial { arguments, .. } => {
            output.extend(arguments.borrow().iter().cloned());
        },
        ValueData::Reference(value) => output.push(value.borrow().clone()),
        _ => {},
    }
}

fn type_has_variable(typ: &Type) -> bool {
    match typ {
        Type::Variable(_) => true,
        Type::Constructor(_, arguments) => arguments.iter().any(type_has_variable),
        Type::Function(input, output) => type_has_variable(input) || type_has_variable(output),
        Type::Record(fields, is_open) => *is_open || fields.values().any(type_has_variable),
    }
}

fn type_contains_variable(typ: &Type, target: u64) -> bool {
    match typ {
        Type::Variable(id) => *id == target,
        Type::Constructor(_, arguments) => {
            arguments.iter().any(|argument| type_contains_variable(argument, target))
        },
        Type::Function(input, output) => {
            type_contains_variable(input, target) || type_contains_variable(output, target)
        },
        Type::Record(fields, _) => {
            fields.values().any(|field| type_contains_variable(field, target))
        },
    }
}

fn datatype_constructor_type(
    name: &str,
    parameters: &[String],
    argument: &Option<super::TypeExpr>,
) -> super::TypeExpr {
    let result = super::TypeExpr::Named(
        name.to_owned(),
        parameters.iter().map(|parameter| super::TypeExpr::Var(parameter.clone())).collect(),
    );
    match argument {
        Some(argument) => super::TypeExpr::Function(Box::new(argument.clone()), Box::new(result)),
        None => result,
    }
}

fn collect_module_names(
    declaration: &Declaration,
    structures: &mut BTreeSet<String>,
    signatures: &mut BTreeSet<String>,
    functors: &mut BTreeSet<String>,
) {
    match declaration {
        Declaration::Structure { name, .. } => {
            structures.insert(name.clone());
        },
        Declaration::Signature { name, .. } => {
            signatures.insert(name.clone());
        },
        Declaration::Functor { name, .. } => {
            functors.insert(name.clone());
        },
        Declaration::Local { body, .. } | Declaration::Abstype { body, .. } => {
            for declaration in body {
                collect_module_names(declaration, structures, signatures, functors);
            }
        },
        _ => {},
    }
}

impl Declaration {
    pub(super) fn span(&self) -> super::Span {
        match self {
            Self::Fixity { span, .. }
            | Self::Value { span, .. }
            | Self::Function { span, .. }
            | Self::Datatype { span, .. }
            | Self::DatatypeReplication { span, .. }
            | Self::Abstype { span, .. }
            | Self::Exception { span, .. }
            | Self::Type { span, .. }
            | Self::Local { span, .. }
            | Self::Open { span, .. }
            | Self::Structure { span, .. }
            | Self::Signature { span, .. }
            | Self::Functor { span, .. }
            | Self::Expression(_, span) => span.clone(),
        }
    }
}

fn tuple_argument<'a>(vm: &Vm, args: &'a [Value]) -> Result<(&'a Value, &'a Value), MlError> {
    let Some(Value(value)) = args.first() else {
        return Err(vm.error(MlErrorKind::Type, "native", "expected pair"));
    };
    let ValueData::Tuple(values) = &**value else {
        return Err(vm.error(MlErrorKind::Type, "native", "expected pair"));
    };
    if values.len() != 2 {
        return Err(vm.error(MlErrorKind::Type, "native", "expected pair"));
    }
    Ok((&values[0], &values[1]))
}
fn arithmetic(
    vm: &mut Vm,
    args: &[Value],
    integer: fn(i64, i64) -> Option<i64>,
    word: fn(u64, u64) -> u64,
    word32: fn(u32, u32) -> u32,
    real: fn(f64, f64) -> f64,
) -> Result<Value, MlError> {
    let (left, right) = tuple_argument(vm, args)?;
    match (&*left.0, &*right.0) {
        (ValueData::Int(a), ValueData::Int(b)) => {
            integer(*a, *b).map(Value::int).ok_or_else(|| vm.raise_builtin("Overflow"))
        },
        (ValueData::Word(a), ValueData::Word(b)) => Ok(Value::word(word(*a, *b))),
        (ValueData::Word32(a), ValueData::Word32(b)) => Ok(Value::word32(word32(*a, *b))),
        (ValueData::Real(a), ValueData::Real(b)) => Ok(Value::real(real(*a, *b))),
        _ => Err(vm.error(MlErrorKind::Type, "arithmetic", "operand types differ")),
    }
}
fn add(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    arithmetic(vm, args, i64::checked_add, u64::wrapping_add, u32::wrapping_add, |a, b| a + b)
}
fn subtract(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    arithmetic(vm, args, i64::checked_sub, u64::wrapping_sub, u32::wrapping_sub, |a, b| a - b)
}
fn multiply(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    arithmetic(vm, args, i64::checked_mul, u64::wrapping_mul, u32::wrapping_mul, |a, b| a * b)
}
fn negate(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    match args.first().map(|value| &*value.0) {
        Some(ValueData::Int(value)) => {
            value.checked_neg().map(Value::int).ok_or_else(|| vm.raise_builtin("Overflow"))
        },
        Some(ValueData::Real(value)) => Ok(Value::real(-value)),
        Some(ValueData::Word(value)) => Ok(Value::word(value.wrapping_neg())),
        Some(ValueData::Word32(value)) => Ok(Value::word32(value.wrapping_neg())),
        _ => Err(vm.error(MlErrorKind::Type, "negate", "expected numeric operand")),
    }
}
fn compare_ordered(vm: &Vm, args: &[Value]) -> Result<Option<std::cmp::Ordering>, MlError> {
    let (left, right) = tuple_argument(vm, args)?;
    match (&*left.0, &*right.0) {
        (ValueData::Int(a), ValueData::Int(b)) => Ok(Some(a.cmp(b))),
        (ValueData::Word(a), ValueData::Word(b)) => Ok(Some(a.cmp(b))),
        (ValueData::Word32(a), ValueData::Word32(b)) => Ok(Some(a.cmp(b))),
        (ValueData::Real(a), ValueData::Real(b)) => Ok(a.partial_cmp(b)),
        (ValueData::Character(a), ValueData::Character(b)) => Ok(Some(a.cmp(b))),
        (ValueData::Text(a), ValueData::Text(b)) => Ok(Some(a.cmp(b))),
        (ValueData::Host { .. }, ValueData::Host { .. }) => {
            vm.compare_time_values(left, right).map(Some)
        },
        _ => Err(vm.error(MlErrorKind::Type, "compare", "operand types differ")),
    }
}
fn less(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bool(compare_ordered(vm, args)?.is_some_and(|order| order.is_lt())))
}
fn less_equal(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bool(compare_ordered(vm, args)?.is_some_and(|order| order.is_le())))
}
fn greater(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bool(compare_ordered(vm, args)?.is_some_and(|order| order.is_gt())))
}
fn greater_equal(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    Ok(Value::bool(compare_ordered(vm, args)?.is_some_and(|order| order.is_ge())))
}
fn divide(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (a, b) = integer_pair(vm, args)?;
    if b == 0 {
        return Err(vm.raise_builtin("Div"));
    }
    floor_division(a, b).map(Value::int).ok_or_else(|| vm.raise_builtin("Overflow"))
}
fn modulo(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (a, b) = integer_pair(vm, args)?;
    if b == 0 {
        return Err(vm.raise_builtin("Div"));
    }
    a.checked_rem(b)
        .and_then(|remainder| {
            if remainder != 0 && ((remainder < 0) != (b < 0)) {
                remainder.checked_add(b)
            } else {
                Some(remainder)
            }
        })
        .map(Value::int)
        .ok_or_else(|| vm.raise_builtin("Overflow"))
}
fn integer_pair(vm: &Vm, args: &[Value]) -> Result<(i64, i64), MlError> {
    let (left, right) = tuple_argument(vm, args)?;
    match (left.as_int(), right.as_int()) {
        (Some(a), Some(b)) => Ok((a, b)),
        _ => Err(vm.error(MlErrorKind::Type, "arithmetic", "expected integers")),
    }
}
fn floor_division(a: i64, b: i64) -> Option<i64> {
    let quotient = a.checked_div(b)?;
    let remainder = a.checked_rem(b)?;
    if remainder != 0 && ((remainder < 0) != (b < 0)) {
        quotient.checked_sub(1)
    } else {
        Some(quotient)
    }
}
fn equal(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (left, right) = tuple_argument(vm, args)?;
    Ok(Value::bool(equal_values(vm, left, right)?))
}
fn not_equal(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (left, right) = tuple_argument(vm, args)?;
    Ok(Value::bool(!equal_values(vm, left, right)?))
}
fn equal_values(vm: &Vm, left: &Value, right: &Value) -> Result<bool, MlError> {
    vm.check_stop()?;
    match (&*left.0, &*right.0) {
        (ValueData::Unit, ValueData::Unit) => Ok(true),
        (ValueData::Int(a), ValueData::Int(b)) => Ok(a == b),
        (ValueData::Word(a), ValueData::Word(b)) => Ok(a == b),
        (ValueData::Word32(a), ValueData::Word32(b)) => Ok(a == b),
        (ValueData::Bool(a), ValueData::Bool(b)) => Ok(a == b),
        (ValueData::Text(a), ValueData::Text(b)) => Ok(a == b),
        (ValueData::Character(a), ValueData::Character(b)) => Ok(a == b),
        (ValueData::Reference(_), ValueData::Reference(_))
        | (ValueData::WeakReference(_), ValueData::WeakReference(_))
        | (ValueData::Reference(_), ValueData::WeakReference(_))
        | (ValueData::WeakReference(_), ValueData::Reference(_))
        | (ValueData::Array(_), ValueData::Array(_)) => Ok(left.is_same_object(right)),
        (ValueData::Vector(a), ValueData::Vector(b))
        | (ValueData::List(a), ValueData::List(b))
        | (ValueData::Tuple(a), ValueData::Tuple(b)) => equal_sequence(vm, a, b),
        (ValueData::Record(a), ValueData::Record(b)) => {
            if a.len() != b.len() {
                return Ok(false);
            }
            for (name, value) in a {
                vm.check_stop()?;
                let Some(other) = b.get(name) else {
                    return Ok(false);
                };
                if !equal_values(vm, value, other)? {
                    return Ok(false);
                }
            }
            Ok(true)
        },
        (
            ValueData::Constructor { stamp: a, argument: x, .. },
            ValueData::Constructor { stamp: b, argument: y, .. },
        ) => {
            if a != b {
                return Ok(false);
            }
            match (x, y) {
                (None, None) => Ok(true),
                (Some(a), Some(b)) => equal_values(vm, a, b),
                _ => Ok(false),
            }
        },
        _ => Ok(false),
    }
}
fn equal_sequence(vm: &Vm, left: &[Value], right: &[Value]) -> Result<bool, MlError> {
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left.iter().zip(right) {
        vm.check_stop()?;
        if !equal_values(vm, left, right)? {
            return Ok(false);
        }
    }
    Ok(true)
}
fn make_ref(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let value = args
        .first()
        .cloned()
        .ok_or_else(|| vm.error(MlErrorKind::Type, "ref", "missing argument"))?;
    Ok(vm.track_value(Value::reference(value)))
}
fn dereference(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let value = match args.first().map(|value| &*value.0) {
        Some(ValueData::Reference(cell) | ValueData::WeakReference(cell)) => cell.borrow().clone(),
        _ => return Err(vm.error(MlErrorKind::Type, "!", "expected reference")),
    };
    Ok(vm.adapt_dereferenced_callback(value))
}
fn assign(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let (reference, value) = tuple_argument(vm, args)?;
    if matches!(&*reference.0, ValueData::WeakReference(_)) {
        vm.validate_weak_contents(value, ":=")?;
    }
    match &*reference.0 {
        ValueData::Reference(cell) | ValueData::WeakReference(cell) => {
            *cell.borrow_mut() = value.clone();
            Ok(Value::unit())
        },
        _ => Err(vm.error(MlErrorKind::Type, ":=", "expected reference")),
    }
}
