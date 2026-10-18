use super::static_module::StaticModules;
use super::value::{
    BINDING_EXPRESSION_PATH, CLOSURE_CLAUSE_PATH, CLOSURE_EXPRESSION_PATH, Elaborations,
};
use super::{Declaration, Expr, MlError, MlErrorKind, Pattern, Span, TypeExpr};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Variable(u64),
    Constructor(String, Vec<Type>),
    Function(Box<Type>, Box<Type>),
    Record(BTreeMap<String, Type>, bool),
}

impl Type {
    pub(super) fn substitute(&self, replacements: &BTreeMap<u64, Type>) -> Self {
        substitute(self, replacements)
    }
    pub(super) fn rename_constructor(&mut self, from: &str, to: &str) {
        rename_type_constructor(self, from, to);
    }
}

#[derive(Clone, Debug)]
pub struct TypeScheme {
    quantified: Vec<u64>,
    equality: BTreeSet<u64>,
    // Row constraints are part of the scheme, not the inference state of its definition.
    flexible_records: BTreeMap<u64, BTreeMap<String, Type>>,
    body: Type,
}
impl TypeScheme {
    pub fn mono(body: Type) -> Self {
        Self {
            quantified: Vec::new(),
            equality: BTreeSet::new(),
            flexible_records: BTreeMap::new(),
            body,
        }
    }
    pub fn polymorphic(quantified: Vec<u64>, body: Type) -> Self {
        Self { quantified, equality: BTreeSet::new(), flexible_records: BTreeMap::new(), body }
    }
    pub fn requiring_equality(mut self, variable: u64) -> Self {
        self.equality.insert(variable);
        self
    }
    pub(super) fn body(&self) -> &Type {
        &self.body
    }
    pub(super) fn quantified(&self) -> &[u64] {
        &self.quantified
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct TypeConstructor {
    arity: usize,
    equality: bool,
    identity: String,
    stamp: u128,
    alias: Option<(Vec<u64>, Type)>,
}

static NEXT_TYPE_ID: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

pub(super) fn fresh_type_identity() -> (String, u128) {
    let id = NEXT_TYPE_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed) as u128;
    (format!("\u{0}type{id}"), id)
}

#[derive(Clone, Debug, Default)]
pub struct TypeEnvironment {
    pub(super) values: BTreeMap<String, TypeScheme>,
    pub(super) constructors: BTreeMap<String, TypeConstructor>,
    pub(super) identities: BTreeMap<String, bool>,
    pub(super) opaque_identities: BTreeSet<String>,
    pub(super) constructor_values: BTreeSet<String>,
    pub(super) equality: BTreeSet<u64>,
    pub(super) next_variable: u64,
    pub(super) reserved_variables: BTreeSet<u64>,
    pub(super) external_free: BTreeMap<u64, u64>,
}
impl TypeEnvironment {
    pub fn new() -> Self {
        let mut environment = Self { next_variable: 2, ..Self::default() };
        for name in
            ["int", "bool", "string", "char", "unit", "list", "ref", "array", "exn", "real", "word"]
        {
            environment.constructors.insert(
                name.to_owned(),
                TypeConstructor {
                    arity: usize::from(["list", "ref", "array"].contains(&name)),
                    equality: !matches!(name, "exn" | "real"),
                    identity: name.to_owned(),
                    stamp: 0,
                    alias: None,
                },
            );
            environment.identities.insert(name.to_owned(), !matches!(name, "exn" | "real"));
        }
        environment
    }
    pub fn register(&mut self, name: &str, mut scheme: TypeScheme) {
        let mut variables = BTreeSet::new();
        collect_variables(&scheme.body, &mut variables);
        variables.extend(&scheme.equality);
        for (id, fields) in &scheme.flexible_records {
            variables.insert(*id);
            for field in fields.values() {
                collect_variables(field, &mut variables);
            }
        }
        let quantified = scheme.quantified.iter().copied().collect::<BTreeSet<_>>();
        let mut replacements = BTreeMap::new();
        for id in variables.difference(&quantified) {
            let fresh = if let Some(&fresh) = self.external_free.get(id) {
                fresh
            } else {
                let fresh = self.fresh_id();
                self.external_free.insert(*id, fresh);
                fresh
            };
            replacements.insert(*id, Type::Variable(fresh));
        }
        for id in &quantified {
            replacements.insert(*id, Type::Variable(self.fresh_id()));
        }
        scheme.body = substitute(&scheme.body, &replacements);
        scheme.equality = scheme
            .equality
            .iter()
            .map(|id| match replacements.get(id) {
                Some(Type::Variable(fresh)) => *fresh,
                _ => *id,
            })
            .collect();
        scheme.flexible_records = scheme
            .flexible_records
            .iter()
            .map(|(id, fields)| {
                let new_id = match replacements.get(id) {
                    Some(Type::Variable(fresh)) => *fresh,
                    _ => *id,
                };
                (
                    new_id,
                    fields
                        .iter()
                        .map(|(name, field)| (name.clone(), substitute(field, &replacements)))
                        .collect(),
                )
            })
            .collect();
        scheme.quantified = quantified
            .iter()
            .filter_map(|id| match replacements.get(id) {
                Some(Type::Variable(fresh)) => Some(*fresh),
                _ => None,
            })
            .collect();
        self.register_inferred(name, scheme);
    }
    fn register_inferred(&mut self, name: &str, scheme: TypeScheme) {
        self.constructor_values.remove(name);
        self.values.insert(name.to_owned(), scheme);
    }
    pub(super) fn register_value_constructor(&mut self, name: &str) {
        self.constructor_values.insert(name.to_owned());
    }
    pub(super) fn is_value_constructor(&self, name: &str) -> bool {
        self.constructor_values.contains(name)
    }
    pub(super) fn hide_value_constructor(&mut self, name: &str) {
        self.constructor_values.remove(name);
    }
    fn fresh_id(&mut self) -> u64 {
        while self.reserved_variables.contains(&self.next_variable) {
            self.next_variable = self.next_variable.wrapping_add(1);
        }
        let id = self.next_variable;
        self.reserved_variables.insert(id);
        self.next_variable = id.wrapping_add(1);
        id
    }
    pub fn lookup(&self, name: &str) -> Option<&TypeScheme> {
        self.values.get(name)
    }
    pub fn register_type(&mut self, name: &str, arity: usize, equality: bool) {
        self.identities.insert(name.to_owned(), equality);
        self.constructors.insert(
            name.to_owned(),
            TypeConstructor { arity, equality, identity: name.to_owned(), stamp: 0, alias: None },
        );
    }
    pub(super) fn register_datatype(&mut self, name: &str, arity: usize) {
        let (identity, stamp) = fresh_type_identity();
        self.identities.insert(identity.clone(), true);
        self.constructors.insert(
            name.to_owned(),
            TypeConstructor { arity, equality: true, identity, stamp, alias: None },
        );
    }
    pub(super) fn register_signature_type(&mut self, name: &str, arity: usize, equality: bool) {
        self.register_datatype(name, arity);
        self.set_datatype_equality(name, equality);
    }
    pub(super) fn register_manifest_type(
        &mut self,
        name: &str,
        parameters: &[String],
        definition: &TypeExpr,
        span: Span,
    ) -> Result<(), MlError> {
        let mut infer = Infer::new(self.clone(), span);
        let mut variables = parameters
            .iter()
            .map(|name| (name.clone(), infer.variable()))
            .collect::<BTreeMap<_, _>>();
        if variables.len() != parameters.len() {
            return Err(infer.error(format!("duplicate parameter in type {name}")));
        }
        let defined = infer.annotation(definition, &mut variables)?;
        if variables.len() != parameters.len() {
            return Err(infer.error(format!("undeclared type variable in type {name}")));
        }
        let parameters = parameters
            .iter()
            .filter_map(|name| match variables.get(name) {
                Some(Type::Variable(id)) => Some(*id),
                _ => None,
            })
            .collect();
        self.next_variable = self.next_variable.max(infer.environment.next_variable);
        self.reserved_variables.extend(&infer.environment.reserved_variables);
        self.register_alias(name, parameters, defined);
        Ok(())
    }
    pub(super) fn register_alias(&mut self, name: &str, parameters: Vec<u64>, definition: Type) {
        let direct = if let Type::Constructor(identity, args) = &definition {
            if args.iter().cloned().eq(parameters.iter().map(|id| Type::Variable(*id))) {
                self.constructors.values().find(|info| info.identity == *identity).cloned()
            } else {
                None
            }
        } else {
            None
        };
        if let Some(info) = direct {
            self.constructors.insert(name.to_owned(), info);
            return;
        }
        let equality = self.admits_equality(&definition);
        let (identity, _) = fresh_type_identity();
        self.identities.insert(identity.clone(), equality);
        self.constructors.insert(
            name.to_owned(),
            TypeConstructor {
                arity: parameters.len(),
                equality,
                identity,
                stamp: 0,
                alias: Some((parameters, definition)),
            },
        );
    }
    fn admits_equality(&self, typ: &Type) -> bool {
        match typ {
            Type::Variable(_) => true,
            Type::Constructor(identity, args) => {
                self.identities.get(identity) == Some(&true)
                    && (identity == "ref"
                        || identity == "array"
                        || args.iter().all(|arg| self.admits_equality(arg)))
            },
            Type::Function(..) => false,
            Type::Record(fields, _) => fields.values().all(|field| self.admits_equality(field)),
        }
    }
    fn set_datatype_equality(&mut self, name: &str, equality: bool) {
        if let Some(info) = self.constructors.get_mut(name) {
            info.equality = equality;
            self.identities.insert(info.identity.clone(), equality);
        }
    }
    pub(super) fn replace_type_identity(&mut self, from: &str, to: &str, stamp: u128) {
        if from == to {
            return;
        }
        let is_equality = self.identities.get(from).copied().unwrap_or(false);
        self.identities
            .entry(to.to_owned())
            .and_modify(|admitted| *admitted |= is_equality)
            .or_insert(is_equality);
        if self.opaque_identities.contains(from) {
            self.opaque_identities.insert(to.to_owned());
        }
        for constructor in self.constructors.values_mut() {
            if constructor.identity == from {
                constructor.identity = to.to_owned();
                constructor.stamp = stamp;
            }
            if let Some((_, body)) = &mut constructor.alias {
                rename_type_constructor(body, from, to);
            }
        }
        for scheme in self.values.values_mut() {
            rename_type_constructor(&mut scheme.body, from, to);
            for fields in scheme.flexible_records.values_mut() {
                for field in fields.values_mut() {
                    rename_type_constructor(field, from, to);
                }
            }
        }
    }
    pub(super) fn bind_type_identity_to_shape(&mut self, from: &str, shape: &Type) {
        let admits_equality = self.admits_equality(shape);
        for constructor in self.constructors.values_mut() {
            if constructor.identity == from {
                constructor.alias = Some(((0..constructor.arity as u64).collect(), shape.clone()));
                constructor.equality = admits_equality;
                constructor.stamp = 0;
            } else if let Some((_, body)) = &mut constructor.alias {
                expand_type_constructor(body, from, shape);
            }
        }
        self.identities.insert(from.to_owned(), admits_equality);
        for scheme in self.values.values_mut() {
            expand_type_constructor(&mut scheme.body, from, shape);
            for fields in scheme.flexible_records.values_mut() {
                for field in fields.values_mut() {
                    expand_type_constructor(field, from, shape);
                }
            }
        }
    }
    pub(super) fn type_stamp(&self, name: &str) -> Option<u128> {
        self.constructors.get(name).map(|info| info.stamp)
    }
    pub(super) fn type_identity(&self, name: &str) -> Option<&str> {
        self.constructors.get(name).map(|info| info.identity.as_str())
    }
    pub(super) fn type_shape(&self, name: &str) -> Option<Type> {
        let info = self.constructors.get(name)?;
        if let Some((parameters, definition)) = &info.alias {
            let mapping = parameters
                .iter()
                .enumerate()
                .map(|(index, id)| (*id, Type::Variable(index as u64)))
                .collect();
            return Some(substitute(definition, &mapping));
        }
        Some(Type::Constructor(
            info.identity.clone(),
            (0..info.arity as u64).map(Type::Variable).collect(),
        ))
    }
    pub(super) fn type_arity(&self, name: &str) -> Option<usize> {
        self.constructors.get(name).map(|info| info.arity)
    }
    pub(super) fn type_admits_equality(&self, name: &str) -> Option<bool> {
        self.constructors.get(name).map(|info| info.equality)
    }

    pub(super) fn seal_type(
        &mut self,
        name: &str,
        equality: bool,
        shared: Option<(String, u128)>,
    ) -> Option<u128> {
        let (identity, stamp) = shared.unwrap_or_else(fresh_type_identity);
        let info = self.constructors.get_mut(name)?;
        info.identity = identity.clone();
        info.stamp = stamp;
        info.alias = None;
        info.equality = equality;
        self.identities.insert(identity.clone(), equality);
        self.opaque_identities.insert(identity);
        Some(stamp)
    }
    pub(super) fn signature_scheme(
        &self,
        typ: &TypeExpr,
        span: super::Span,
    ) -> Result<TypeScheme, MlError> {
        let mut infer = Infer::new(self.clone(), span);
        let body = infer.annotation(typ, &mut BTreeMap::new())?;
        let mut quantified = BTreeSet::new();
        collect_variables(&body, &mut quantified);
        let equality =
            quantified.iter().filter(|id| infer.equality.contains(id)).copied().collect();
        Ok(TypeScheme {
            quantified: quantified.into_iter().collect(),
            equality,
            flexible_records: BTreeMap::new(),
            body,
        })
    }
    pub(super) fn install_signature_scheme(&mut self, name: &str, scheme: TypeScheme) {
        let is_constructor = self.is_value_constructor(name);
        self.register(name, scheme);
        if is_constructor {
            self.register_value_constructor(name);
        }
    }
    pub(super) fn check_value_spec(
        &self,
        name: &str,
        specification: &TypeExpr,
        span: super::Span,
    ) -> Result<(), MlError> {
        let actual = self.values.get(name).cloned().ok_or_else(|| {
            MlError::new(
                MlErrorKind::Type,
                span.clone(),
                "signature",
                format!("missing type for value {name}"),
            )
        })?;
        let mut infer = Infer::new(self.clone(), span);
        let expected = infer.annotation(specification, &mut BTreeMap::new())?;
        let mut variables = BTreeSet::new();
        collect_variables(&expected, &mut variables);
        let rigid = variables
            .iter()
            .map(|id| {
                let (identity, _) = fresh_type_identity();
                infer.environment.register_type(&identity, 0, infer.equality.contains(id));
                (*id, Type::Constructor(identity, Vec::new()))
            })
            .collect::<BTreeMap<_, _>>();
        let mut free = BTreeSet::new();
        collect_variables(&actual.body, &mut free);
        let quantified = actual.quantified.iter().copied().collect::<BTreeSet<_>>();
        let fixed = free
            .difference(&quantified)
            .map(|id| {
                let (identity, _) = fresh_type_identity();
                infer.environment.register_type(&identity, 0, true);
                (*id, Type::Constructor(identity, Vec::new()))
            })
            .collect::<BTreeMap<_, _>>();
        let actual_type = infer.instantiate(&actual)?;
        infer.unify(substitute(&actual_type, &fixed), substitute(&expected, &rigid))
    }
    pub(super) fn check_type_spec(
        &self,
        name: &str,
        parameters: &[String],
        definition: &TypeExpr,
        span: super::Span,
    ) -> Result<(), MlError> {
        let mut infer = Infer::new(self.clone(), span);
        let mut variables = parameters
            .iter()
            .map(|name| (name.clone(), infer.variable()))
            .collect::<BTreeMap<_, _>>();
        let expected = infer.annotation(definition, &mut variables)?;
        let applied = TypeExpr::Named(
            name.to_owned(),
            parameters.iter().map(|name| TypeExpr::Var(name.clone())).collect(),
        );
        let actual = infer.annotation(&applied, &mut variables)?;
        infer.unify(actual, expected)
    }
    pub(super) fn replicated_constructors(
        &self,
        source: &str,
    ) -> Option<Vec<(String, TypeScheme)>> {
        let identity = self.type_identity(source)?;
        let prefix = source.rsplit_once('.').map_or("", |(path, _)| path);
        let qualified_prefix = if prefix.is_empty() { String::new() } else { format!("{prefix}.") };
        let constructors = self
            .constructor_values
            .iter()
            .filter_map(|name| {
                let local_name = name.strip_prefix(&qualified_prefix)?;
                if local_name.contains('.') {
                    return None;
                }
                let scheme = self.values.get(name)?;
                let result = match &scheme.body {
                    Type::Function(_, output) => &**output,
                    other => other,
                };
                if !matches!(result, Type::Constructor(found, _) if found == identity) {
                    return None;
                }
                Some((local_name.to_owned(), scheme.clone()))
            })
            .collect::<Vec<_>>();
        (!constructors.is_empty()).then_some(constructors)
    }
    pub(super) fn replicate_datatype(&mut self, name: &str, source: &str) -> Option<Vec<String>> {
        let info = self.constructors.get(source)?.clone();
        let constructors = self.replicated_constructors(source)?;
        self.constructors.insert(name.to_owned(), info);
        let names = constructors.iter().map(|(name, _)| name.clone()).collect();
        for (constructor, scheme) in constructors {
            self.register_inferred(&constructor, scheme);
            self.register_value_constructor(&constructor);
        }
        Some(names)
    }
    pub(super) fn select(
        &self,
        value_names: &BTreeSet<String>,
        type_names: &BTreeSet<String>,
    ) -> Self {
        Self {
            values: self
                .values
                .iter()
                .filter(|(name, _)| value_names.contains(*name))
                .map(|(name, scheme)| (name.clone(), scheme.clone()))
                .collect(),
            constructors: self
                .constructors
                .iter()
                .filter(|(name, _)| type_names.contains(*name))
                .map(|(name, info)| (name.clone(), info.clone()))
                .collect(),
            constructor_values: self
                .constructor_values
                .iter()
                .filter(|name| value_names.contains(*name))
                .cloned()
                .collect(),
            identities: self.identities.clone(),
            opaque_identities: self.opaque_identities.clone(),
            equality: self.equality.clone(),
            next_variable: self.next_variable,
            reserved_variables: self.reserved_variables.clone(),
            external_free: self.external_free.clone(),
        }
    }

    pub(super) fn extend_exports(&mut self, exports: &Self) {
        self.values.extend(exports.values.clone());
        for name in exports.values.keys() {
            self.constructor_values.remove(name);
        }
        self.constructor_values.extend(exports.constructor_values.iter().cloned());
        self.constructors.extend(exports.constructors.clone());
        self.identities.extend(exports.identities.iter().map(|(name, flag)| (name.clone(), *flag)));
        self.next_variable = self.next_variable.max(exports.next_variable);
        self.opaque_identities.extend(exports.opaque_identities.iter().cloned());
        self.reserved_variables.extend(&exports.reserved_variables);
        self.external_free.extend(&exports.external_free);
        self.equality.extend(&exports.equality);
    }

    pub(super) fn type_names(&self) -> impl Iterator<Item = String> + '_ {
        self.constructors.keys().cloned()
    }

    pub(super) fn value_specifications(&self) -> impl Iterator<Item = super::Specification> + '_ {
        self.values.iter().map(|(name, scheme)| {
            super::Specification::Value(
                name.clone(),
                make_type_expression(&scheme.body, &scheme.equality),
            )
        })
    }

    pub(super) fn namespace_types(&self, path: &str) -> Self {
        let prefix = format!("{path}.");
        let mut types = self.clone();
        types.values = self
            .values
            .iter()
            .filter_map(|(name, scheme)| {
                name.strip_prefix(&prefix).map(|member| (member.to_owned(), scheme.clone()))
            })
            .collect();
        types.constructors = self
            .constructors
            .iter()
            .filter_map(|(name, info)| {
                name.strip_prefix(&prefix).map(|member| (member.to_owned(), info.clone()))
            })
            .collect();
        types.constructor_values = self
            .constructor_values
            .iter()
            .filter_map(|name| name.strip_prefix(&prefix).map(str::to_owned))
            .collect();
        types
    }
    pub(super) fn update_qualified_values(&mut self, flat: &Self, path: &str) {
        let prefix = format!("{path}.");
        for (name, scheme) in &mut self.values {
            if let Some(updated) = flat.values.get(&format!("{prefix}{name}")) {
                *scheme = updated.clone();
            }
        }
        self.equality = flat.equality.clone();
        self.next_variable = self.next_variable.max(flat.next_variable);
        self.reserved_variables.extend(&flat.reserved_variables);
    }

    pub(super) fn register_namespace_types(&mut self, path: &str, types: &Self) {
        let prefix = format!("{path}.");
        self.values.retain(|name, _| !name.starts_with(&prefix));
        self.constructor_values.retain(|name| !name.starts_with(&prefix));
        self.constructors.retain(|name, _| !name.starts_with(&prefix));
        for (name, scheme) in &types.values {
            self.values.insert(format!("{prefix}{name}"), scheme.clone());
            if types.constructor_values.contains(name) {
                self.constructor_values.insert(format!("{prefix}{name}"));
            }
        }
        for (name, info) in &types.constructors {
            self.constructors.insert(format!("{prefix}{name}"), info.clone());
        }
        self.identities.extend(types.identities.iter().map(|(name, flag)| (name.clone(), *flag)));
        self.next_variable = self.next_variable.max(types.next_variable);
        self.reserved_variables.extend(&types.reserved_variables);
        self.opaque_identities.extend(types.opaque_identities.iter().cloned());
        self.external_free.extend(&types.external_free);
        self.equality.extend(&types.equality);
    }
    pub(super) fn register_static_namespace(
        &mut self,
        path: &str,
        namespace: &super::static_module::StaticNamespace,
    ) {
        self.register_namespace_types(path, &namespace.types);
        for (name, child) in &namespace.structures {
            self.register_static_namespace(&format!("{path}.{name}"), child);
        }
    }

    pub(super) fn register_namespace(&mut self, path: &str, namespace: &super::value::Namespace) {
        self.register_namespace_types(path, &namespace.type_environment);
        for (name, nested) in &namespace.structures {
            self.register_namespace(&format!("{path}.{name}"), nested);
        }
    }
}

fn make_type_expression(ty: &Type, equality: &BTreeSet<u64>) -> TypeExpr {
    match ty {
        Type::Variable(id) => {
            let prefix = if equality.contains(id) { "''" } else { "'" };
            TypeExpr::Var(format!("{prefix}t{id}"))
        },
        Type::Constructor(name, arguments) => TypeExpr::Named(
            name.clone(),
            arguments.iter().map(|ty| make_type_expression(ty, equality)).collect(),
        ),
        Type::Function(input, output) => TypeExpr::Function(
            Box::new(make_type_expression(input, equality)),
            Box::new(make_type_expression(output, equality)),
        ),
        Type::Record(fields, _) => TypeExpr::Record(
            fields
                .iter()
                .map(|(label, ty)| (label.clone(), make_type_expression(ty, equality)))
                .collect(),
        ),
    }
}

pub(super) struct Infer {
    pub environment: TypeEnvironment,
    substitutions: BTreeMap<u64, Type>,
    // A row belongs to an inference variable, not to a structural Record snapshot.
    // Every alias of that variable therefore observes later field constraints.
    flexible_records: BTreeMap<u64, BTreeMap<String, Type>>,
    private_flexible_records: BTreeSet<u64>,
    pub(super) scope_depth: usize,
    let_depth: usize,
    equality: BTreeSet<u64>,
    pub(super) span: Span,
    pub(super) elaborations: Elaborations,
    expression_locations: Vec<(usize, usize)>,
    expression_sources: Vec<String>,
    word_literals: Vec<(Span, u64, Type)>,
    numeric_constraints: BTreeSet<u64>,
    ordered_constraints: BTreeSet<u64>,
    pub(super) modules: StaticModules,
}

impl Infer {
    pub fn new(environment: TypeEnvironment, span: Span) -> Self {
        let equality = environment.equality.clone();
        Self {
            environment,
            substitutions: BTreeMap::new(),
            flexible_records: BTreeMap::new(),
            private_flexible_records: BTreeSet::new(),
            scope_depth: 0,
            let_depth: 0,
            equality,
            span,
            elaborations: Elaborations::new(),
            expression_locations: Vec::new(),
            expression_sources: Vec::new(),
            word_literals: Vec::new(),
            numeric_constraints: BTreeSet::new(),
            ordered_constraints: BTreeSet::new(),
            modules: StaticModules::default(),
        }
    }
    pub(super) fn error(&self, description: impl Into<String>) -> MlError {
        MlError::new(MlErrorKind::Type, self.span.clone(), "elaborate", description)
    }
    fn variable(&mut self) -> Type {
        Type::Variable(self.environment.fresh_id())
    }
    pub(super) fn restore_environment(&mut self, mut previous: TypeEnvironment) {
        previous.next_variable = self.environment.next_variable;
        previous.reserved_variables.extend(&self.environment.reserved_variables);
        previous
            .identities
            .extend(self.environment.identities.iter().map(|(name, flag)| (name.clone(), *flag)));
        previous.opaque_identities.extend(self.environment.opaque_identities.iter().cloned());
        self.environment = previous;
    }
    fn resolve(&self, typ: Type) -> Type {
        match typ {
            Type::Variable(id) => match self.substitutions.get(&id) {
                Some(value) => self.resolve(value.clone()),
                None => Type::Variable(id),
            },
            Type::Constructor(name, arguments) => {
                Type::Constructor(name, arguments.into_iter().map(|t| self.resolve(t)).collect())
            },
            Type::Function(input, output) => {
                Type::Function(Box::new(self.resolve(*input)), Box::new(self.resolve(*output)))
            },
            Type::Record(fields, open) => Type::Record(
                fields.into_iter().map(|(name, typ)| (name, self.resolve(typ))).collect(),
                open,
            ),
        }
    }
    fn resolve_scheme(&self, typ: Type, quantified: &BTreeSet<u64>) -> Type {
        match typ {
            Type::Variable(id) if quantified.contains(&id) => Type::Variable(id),
            Type::Variable(id) => match self.substitutions.get(&id) {
                Some(value) => self.resolve_scheme(value.clone(), quantified),
                None => Type::Variable(id),
            },
            Type::Constructor(name, arguments) => Type::Constructor(
                name,
                arguments.into_iter().map(|t| self.resolve_scheme(t, quantified)).collect(),
            ),
            Type::Function(input, output) => Type::Function(
                Box::new(self.resolve_scheme(*input, quantified)),
                Box::new(self.resolve_scheme(*output, quantified)),
            ),
            Type::Record(fields, open) => Type::Record(
                fields
                    .into_iter()
                    .map(|(name, t)| (name, self.resolve_scheme(t, quantified)))
                    .collect(),
                open,
            ),
        }
    }
    fn occurs(&self, id: u64, typ: &Type) -> bool {
        let mut visited = BTreeSet::new();
        let mut pending = vec![typ];
        while let Some(current) = pending.pop() {
            match current {
                Type::Variable(found) => {
                    if *found == id {
                        return true;
                    }
                    if !visited.insert(*found) {
                        continue;
                    }
                    if let Some(replacement) = self.substitutions.get(found) {
                        pending.push(replacement);
                    }
                    if let Some(fields) = self.flexible_records.get(found) {
                        pending.extend(fields.values());
                    }
                },
                Type::Constructor(_, args) => pending.extend(args),
                Type::Function(input, output) => {
                    pending.push(input);
                    pending.push(output);
                },
                Type::Record(fields, _) => pending.extend(fields.values()),
            }
        }
        false
    }
    fn require_equality(&mut self, typ: Type) -> Result<(), MlError> {
        let mut visited = BTreeSet::new();
        let mut pending = vec![&typ];
        while let Some(current) = pending.pop() {
            match current {
                Type::Variable(id) => {
                    if !visited.insert(*id) {
                        continue;
                    }
                    if let Some(replacement) = self.substitutions.get(id) {
                        pending.push(replacement);
                    } else {
                        self.equality.insert(*id);
                        if let Some(fields) = self.flexible_records.get(id) {
                            pending.extend(fields.values());
                        }
                    }
                },
                Type::Constructor(name, arguments) => {
                    if self.environment.identities.get(name) != Some(&true) {
                        return Err(self.error(format!("type {name} does not admit equality")));
                    }
                    if name != "ref" && name != "array" {
                        pending.extend(arguments);
                    }
                },
                Type::Record(fields, _) => pending.extend(fields.values()),
                Type::Function(..) => return Err(self.error("functions do not admit equality")),
            }
        }
        Ok(())
    }
    fn add_flexible_fields(
        &mut self,
        id: u64,
        fields: BTreeMap<String, Type>,
    ) -> Result<(), MlError> {
        for field in fields.values() {
            if self.occurs(id, field) {
                return Err(self.error("infinite type"));
            }
            if self.equality.contains(&id) {
                self.require_equality(field.clone())?;
            }
        }
        // Even an empty open row constrains its argument to a record.
        self.flexible_records.entry(id).or_default();
        for (name, field) in fields {
            if let Some(existing) =
                self.flexible_records.get(&id).and_then(|row| row.get(&name)).cloned()
            {
                self.unify(existing, field)?;
            } else {
                self.flexible_records.entry(id).or_default().insert(name, field);
            }
        }
        Ok(())
    }
    fn require_overloaded(&mut self, typ: Type, is_ordered: bool) -> Result<(), MlError> {
        match self.resolve(typ) {
            Type::Variable(id) => {
                if is_ordered {
                    self.ordered_constraints.insert(id);
                } else {
                    self.numeric_constraints.insert(id);
                }
                Ok(())
            },
            Type::Constructor(name, args)
                if args.is_empty()
                    && (matches!(name.as_str(), "int" | "word" | "Word32.word" | "real")
                        || is_ordered
                            && matches!(name.as_str(), "char" | "string" | "Time.time")) =>
            {
                Ok(())
            },
            typ => Err(self.error(format!("invalid overloaded operand type {typ:?}"))),
        }
    }

    fn bind(&mut self, id: u64, typ: Type) -> Result<(), MlError> {
        if typ == Type::Variable(id) {
            return Ok(());
        }
        if self.occurs(id, &typ) {
            return Err(self.error("infinite type"));
        }
        if let Type::Record(fields, true) = &typ {
            return self.add_flexible_fields(id, fields.clone());
        }
        if let Some(fields) = self.flexible_records.get(&id).cloned() {
            match &typ {
                Type::Variable(other) => self.add_flexible_fields(*other, fields)?,
                _ => self.unify(Type::Record(fields, true), typ.clone())?,
            }
        }
        if self.equality.contains(&id) {
            self.require_equality(typ.clone())?;
        }
        let is_numeric = self.numeric_constraints.remove(&id);
        let is_ordered = self.ordered_constraints.remove(&id);
        if is_numeric {
            self.require_overloaded(typ.clone(), false)?;
        }
        if is_ordered {
            self.require_overloaded(typ.clone(), true)?;
        }
        self.flexible_records.remove(&id);
        self.substitutions.insert(id, typ);
        Ok(())
    }
    fn unify(&mut self, left: Type, right: Type) -> Result<(), MlError> {
        match (self.resolve(left), self.resolve(right)) {
            (Type::Variable(id), typ) | (typ, Type::Variable(id)) => self.bind(id, typ),
            (Type::Constructor(name, args), Type::Record(fields, _))
            | (Type::Record(fields, _), Type::Constructor(name, args))
                if name == "unit" && args.is_empty() && fields.is_empty() =>
            {
                Ok(())
            },
            (Type::Constructor(left, a), Type::Constructor(right, b))
                if left == right && a.len() == b.len() =>
            {
                for (a, b) in a.into_iter().zip(b) {
                    self.unify(a, b)?;
                }
                Ok(())
            },
            (Type::Function(a, b), Type::Function(c, d)) => {
                self.unify(*a, *c)?;
                self.unify(*b, *d)
            },
            (Type::Record(a, open_a), Type::Record(b, open_b)) => {
                for (name, a_type) in &a {
                    if let Some(b_type) = b.get(name) {
                        self.unify(a_type.clone(), b_type.clone())?;
                    } else if !open_b {
                        return Err(self.error(format!("missing record field {name}")));
                    }
                }
                if !open_a {
                    for name in b.keys() {
                        if !a.contains_key(name) {
                            return Err(self.error(format!("extra record field {name}")));
                        }
                    }
                }
                Ok(())
            },
            (a, b) => Err(self.error(format!("type mismatch: {a:?} versus {b:?}"))),
        }
    }
    fn instantiate(&mut self, scheme: &TypeScheme) -> Result<Type, MlError> {
        let replacement =
            scheme.quantified.iter().map(|id| (*id, self.variable())).collect::<BTreeMap<_, _>>();
        for (id, fields) in &scheme.flexible_records {
            let fresh_id = match replacement.get(id) {
                Some(Type::Variable(fresh)) => *fresh,
                _ => return Err(self.error("unquantified flexible record in type scheme")),
            };
            let fresh_fields = fields
                .iter()
                .map(|(name, field)| (name.clone(), substitute(field, &replacement)))
                .collect();
            self.add_flexible_fields(fresh_id, fresh_fields)?;
        }
        for id in &scheme.equality {
            self.require_equality(replacement.get(id).cloned().unwrap_or(Type::Variable(*id)))?;
        }
        Ok(substitute(&scheme.body, &replacement))
    }
    fn collect_flexible_variables(&self, typ: &Type, output: &mut BTreeSet<u64>) {
        let mut visited = BTreeSet::new();
        let mut pending = vec![typ];
        while let Some(current) = pending.pop() {
            match current {
                Type::Variable(id) => {
                    if !visited.insert(*id) {
                        continue;
                    }
                    if let Some(replacement) = self.substitutions.get(id) {
                        pending.push(replacement);
                    } else {
                        output.insert(*id);
                        if let Some(fields) = self.flexible_records.get(id) {
                            pending.extend(fields.values());
                        }
                    }
                },
                Type::Constructor(_, arguments) => pending.extend(arguments),
                Type::Function(input, result) => {
                    pending.push(input);
                    pending.push(result);
                },
                Type::Record(fields, _) => pending.extend(fields.values()),
            }
        }
    }
    fn default_overloaded(&mut self) -> Result<(), MlError> {
        let unresolved = self
            .numeric_constraints
            .iter()
            .chain(&self.ordered_constraints)
            .copied()
            .collect::<BTreeSet<_>>();
        for id in unresolved {
            if matches!(self.resolve(Type::Variable(id)), Type::Variable(_)) {
                self.unify(Type::Variable(id), constructor("int"))?;
            }
        }
        Ok(())
    }
    fn environment_free_variables(&self) -> BTreeSet<u64> {
        let mut environment_free = BTreeSet::new();
        for scheme in self.environment.values.values() {
            let quantified = scheme.quantified.iter().copied().collect::<BTreeSet<_>>();
            let mut scheme_free = BTreeSet::new();
            collect_variables(
                &self.resolve_scheme(scheme.body.clone(), &quantified),
                &mut scheme_free,
            );
            for fields in scheme.flexible_records.values() {
                for field in fields.values() {
                    collect_variables(
                        &self.resolve_scheme(field.clone(), &quantified),
                        &mut scheme_free,
                    );
                }
            }
            scheme_free.retain(|id| !quantified.contains(id));
            for id in scheme_free {
                self.collect_flexible_variables(&Type::Variable(id), &mut environment_free);
            }
        }
        environment_free
    }

    fn generalize(&mut self, typ: Type, is_nonexpansive: bool) -> Result<TypeScheme, MlError> {
        if self.let_depth == 0 {
            self.resolve_word_literals()?;
        }
        self.default_overloaded()?;
        let body = self.resolve(typ);
        if !is_nonexpansive {
            return Ok(TypeScheme::mono(body));
        }
        let mut free = BTreeSet::new();
        self.collect_flexible_variables(&body, &mut free);
        let environment_free = self.environment_free_variables();
        let mut deferred_words = BTreeSet::new();
        if self.let_depth > 0 {
            for (_, _, literal_type) in &self.word_literals {
                self.collect_flexible_variables(literal_type, &mut deferred_words);
            }
        }
        let quantified = free
            .difference(&environment_free)
            .filter(|id| !deferred_words.contains(id))
            .copied()
            .collect::<Vec<_>>();
        let equality = quantified.iter().filter(|id| self.equality.contains(id)).copied().collect();
        let flexible_records = quantified
            .iter()
            .filter_map(|id| {
                self.flexible_records.get(id).map(|fields| {
                    (
                        *id,
                        fields
                            .iter()
                            .map(|(name, field)| (name.clone(), self.resolve(field.clone())))
                            .collect(),
                    )
                })
            })
            .collect::<BTreeMap<_, _>>();
        if self.scope_depth > 0 {
            self.private_flexible_records.extend(flexible_records.keys());
        }
        Ok(TypeScheme { quantified, equality, body, flexible_records })
    }
    fn resolve_word_literals(&mut self) -> Result<(), MlError> {
        for (span, value, literal_type) in std::mem::take(&mut self.word_literals) {
            let resolved = match self.resolve(literal_type.clone()) {
                Type::Variable(_) => {
                    self.unify(literal_type.clone(), constructor("word"))?;
                    self.resolve(literal_type)
                },
                resolved => resolved,
            };
            match resolved {
                Type::Constructor(name, args) if name == "word" && args.is_empty() => {},
                Type::Constructor(name, args)
                    if name == "Word32.word" && args.is_empty() && u32::try_from(value).is_ok() =>
                {
                    self.elaborations.word32_literals.insert((
                        span.source_name,
                        span.start,
                        span.end,
                    ));
                },
                _ => {
                    return Err(MlError::new(
                        MlErrorKind::Type,
                        span,
                        "elaborate word literal",
                        format!(
                            "word literal {value} is not representable at its contextual word type"
                        ),
                    ));
                },
            }
        }
        Ok(())
    }

    fn annotation(
        &mut self,
        typ: &TypeExpr,
        variables: &mut BTreeMap<String, Type>,
    ) -> Result<Type, MlError> {
        match typ {
            TypeExpr::Var(name) => {
                if let Some(typ) = variables.get(name) {
                    return Ok(typ.clone());
                }
                let typ = self.variable();
                if name.starts_with("''") {
                    self.require_equality(typ.clone())?;
                }
                variables.insert(name.clone(), typ.clone());
                Ok(typ)
            },
            TypeExpr::Named(name, arguments) => {
                let Some(info) = self.environment.constructors.get(name) else {
                    return Err(self.error(format!("unknown type constructor {name}")));
                };
                if info.arity != arguments.len() {
                    return Err(self.error(format!("wrong arity for type {name}")));
                }
                let identity = info.identity.clone();
                let alias = info.alias.clone();
                let args = arguments
                    .iter()
                    .map(|arg| self.annotation(arg, variables))
                    .collect::<Result<Vec<_>, _>>()?;
                if let Some((parameters, definition)) = alias {
                    let mapping = parameters.into_iter().zip(args).collect();
                    return Ok(substitute(&definition, &mapping));
                }
                Ok(Type::Constructor(identity, args))
            },
            TypeExpr::Tuple(types) => {
                let fields = types
                    .iter()
                    .enumerate()
                    .map(|(index, typ)| {
                        Ok(((index + 1).to_string(), self.annotation(typ, variables)?))
                    })
                    .collect::<Result<_, MlError>>()?;
                Ok(Type::Record(fields, false))
            },
            TypeExpr::Function(input, output) => Ok(Type::Function(
                Box::new(self.annotation(input, variables)?),
                Box::new(self.annotation(output, variables)?),
            )),
            TypeExpr::Record(fields) => {
                let fields = fields
                    .iter()
                    .map(|(name, typ)| Ok((name.clone(), self.annotation(typ, variables)?)))
                    .collect::<Result<_, MlError>>()?;
                Ok(closed_record_type(fields))
            },
        }
    }
    fn infer_pattern(
        &mut self,
        pattern: &Pattern,
        expected: Type,
        bindings: &mut BTreeMap<String, Type>,
    ) -> Result<(), MlError> {
        match pattern {
            Pattern::Wildcard => Ok(()),
            Pattern::Variable(name) => {
                if self.environment.constructor_values.contains(name)
                    && let Some(scheme) = self.environment.lookup(name).cloned()
                {
                    let constructor_type = self.instantiate(&scheme)?;
                    return self.unify(expected, constructor_type);
                }
                if name.contains('.') {
                    return Err(self.error(format!("{name} is not a constructor pattern")));
                }
                if bindings.insert(name.clone(), expected).is_some() {
                    return Err(self.error(format!("duplicate pattern variable {name}")));
                }
                Ok(())
            },
            Pattern::Integer(_) => self.unify(expected, constructor("int")),
            Pattern::Word { value, span } => {
                let numeric = self.variable();
                self.word_literals.push((span.clone(), *value, numeric.clone()));
                self.unify(expected, numeric)
            },
            Pattern::Text(_) => self.unify(expected, constructor("string")),
            Pattern::Character(_) => self.unify(expected, constructor("char")),
            Pattern::Unit => self.unify(expected, constructor("unit")),
            Pattern::Tuple(patterns) => {
                let mut fields = patterns
                    .iter()
                    .enumerate()
                    .map(|(index, _)| ((index + 1).to_string(), self.variable()))
                    .collect::<BTreeMap<_, _>>();
                self.unify(expected, Type::Record(fields.clone(), false))?;
                for (index, pattern) in patterns.iter().enumerate() {
                    let typ = fields
                        .remove(&(index + 1).to_string())
                        .ok_or_else(|| self.error("tuple pattern lost numeric label"))?;
                    self.infer_pattern(pattern, typ, bindings)?;
                }
                Ok(())
            },
            Pattern::List(patterns) => {
                let item = self.variable();
                self.unify(expected, Type::Constructor("list".to_owned(), vec![item.clone()]))?;
                for pattern in patterns {
                    self.infer_pattern(pattern, item.clone(), bindings)?;
                }
                Ok(())
            },
            Pattern::Record(fields, open) => {
                let field_types = fields
                    .iter()
                    .map(|(name, _)| (name.clone(), self.variable()))
                    .collect::<BTreeMap<_, _>>();
                self.unify(expected, Type::Record(field_types.clone(), *open))?;
                for (name, pattern) in fields {
                    self.infer_pattern(pattern, field_types[name].clone(), bindings)?;
                }
                Ok(())
            },
            Pattern::Constructor(name, argument) => {
                if !self.environment.constructor_values.contains(name) {
                    return Err(self.error(format!("{name} is not a constructor pattern")));
                }
                let scheme = self
                    .environment
                    .lookup(name)
                    .cloned()
                    .ok_or_else(|| self.error(format!("unknown constructor {name}")))?;
                let typ = self.instantiate(&scheme)?;
                if let Some(argument) = argument {
                    let input = self.variable();
                    self.unify(typ, Type::Function(Box::new(input.clone()), Box::new(expected)))?;
                    self.infer_pattern(argument, input, bindings)
                } else {
                    self.unify(typ, expected)
                }
            },
            Pattern::Typed(pattern, annotation) => {
                let typ = self.annotation(annotation, &mut BTreeMap::new())?;
                self.unify(expected, typ.clone())?;
                self.infer_pattern(pattern, typ, bindings)
            },
            Pattern::As(name, pattern) => {
                if bindings.insert(name.clone(), expected.clone()).is_some() {
                    return Err(self.error(format!("duplicate pattern variable {name}")));
                }
                self.infer_pattern(pattern, expected, bindings)
            },
        }
    }
    fn clauses(&mut self, clauses: &[(Pattern, Expr)]) -> Result<Type, MlError> {
        let input = self.variable();
        let output = self.variable();
        for (index, (pattern, expression)) in clauses.iter().enumerate() {
            let previous = self.environment.clone();
            let mut bindings = BTreeMap::new();
            self.infer_pattern(pattern, input.clone(), &mut bindings)?;
            for (name, typ) in bindings {
                self.environment.register_inferred(&name, TypeScheme::mono(typ));
            }
            self.expression_locations.push((CLOSURE_CLAUSE_PATH, index));
            let result = self.infer(expression);
            self.expression_locations.pop();
            self.unify(output.clone(), result?)?;
            self.restore_environment(previous);
        }
        Ok(Type::Function(Box::new(input), Box::new(output)))
    }
    pub fn infer(&mut self, expression: &Expr) -> Result<Type, MlError> {
        match expression {
            Expr::Located(body, location) => {
                self.expression_locations.push((location.span.start, location.span.end));
                self.expression_sources.push(location.span.source_name.clone());
                let result = self.infer(body);
                self.expression_sources.pop();
                self.expression_locations.pop();
                result
            },
            Expr::Name(name) => {
                let scheme = self
                    .environment
                    .lookup(name)
                    .cloned()
                    .ok_or_else(|| self.error(format!("unbound value {name}")))?;
                let typ = self.instantiate(&scheme)?;
                if matches!(name.as_str(), "+" | "-" | "*" | "~" | "<" | "<=" | ">" | ">=") {
                    let Type::Function(input, _) = &typ else { return Ok(typ) };
                    let operand = match &**input {
                        Type::Record(fields, _) => fields.get("1"),
                        other => Some(other),
                    };
                    if let Some(operand) = operand {
                        self.require_overloaded(
                            operand.clone(),
                            matches!(name.as_str(), "<" | "<=" | ">" | ">="),
                        )?;
                    }
                }
                Ok(typ)
            },
            Expr::Integer(_) => Ok(constructor("int")),
            Expr::Word { value, span } => {
                let numeric = self.variable();
                self.word_literals.push((span.clone(), *value, numeric.clone()));
                Ok(numeric)
            },
            Expr::Real(_) => Ok(constructor("real")),
            Expr::Text(_) => Ok(constructor("string")),
            Expr::Character(_) => Ok(constructor("char")),
            Expr::Unit => Ok(constructor("unit")),
            Expr::Tuple(values) => {
                self.infer_record(values.iter().enumerate().map(|(n, e)| ((n + 1).to_string(), e)))
            },
            Expr::List(values) => {
                let item = self.variable();
                for value in values {
                    let value_type = self.infer(value)?;
                    self.unify(item.clone(), value_type)?;
                }
                Ok(Type::Constructor("list".to_owned(), vec![item]))
            },
            Expr::Record(fields) => {
                self.infer_record(fields.iter().map(|(name, value)| (name.clone(), value)))
            },
            Expr::Select(name) => {
                let input = self.variable();
                let output = self.variable();
                self.unify(
                    input.clone(),
                    Type::Record(BTreeMap::from([(name.clone(), output.clone())]), true),
                )?;
                Ok(Type::Function(Box::new(input), Box::new(output)))
            },
            Expr::Fn(clauses) => {
                let marker = (CLOSURE_EXPRESSION_PATH, self.expression_locations.len());
                self.expression_locations.push(marker);
                let typ = self.clauses(clauses);
                let result = (|| {
                    let typ = typ?;
                    let source_name = self
                        .expression_sources
                        .last()
                        .map_or(self.span.source_name.as_str(), String::as_str);
                    let key =
                        super::value::ExpressionKey::new(source_name, &self.expression_locations);
                    let input = match &typ {
                        Type::Function(input, _) => (**input).clone(),
                        _ => return Err(self.error("function expression lost its input type")),
                    };
                    if self.elaborations.closure_inputs.insert(key.clone(), input).is_some() {
                        return Err(self.error("ambiguous closure evidence at one expression path"));
                    }
                    let weak_variables = self.environment_free_variables();
                    self.elaborations.closure_weak_variables.insert(key, weak_variables);
                    Ok(typ)
                })();
                self.expression_locations.pop();
                result
            },
            Expr::Apply(function, argument) => {
                let function_type = self.infer(function)?;
                let argument_type = self.infer(argument)?;
                let output = self.variable();
                self.unify(
                    function_type,
                    Type::Function(Box::new(argument_type.clone()), Box::new(output.clone())),
                )?;
                let source_name = self
                    .expression_sources
                    .last()
                    .map_or(self.span.source_name.as_str(), String::as_str);
                let key = super::value::ExpressionKey::new(source_name, &self.expression_locations);
                let weak_variables = self.environment_free_variables();
                if let Some(previous) = self.elaborations.typed_calls.insert(
                    key,
                    super::value::TypedCallEvidence {
                        argument: argument_type,
                        result: output.clone(),
                        weak_variables,
                    },
                ) {
                    return Err(self.error(format!(
                        "ambiguous application evidence at one nested expression path: {:?}",
                        previous.argument,
                    )));
                }
                Ok(self.resolve(output))
            },
            Expr::Let(declarations, body) => {
                let previous = self.environment.clone();
                self.scope_depth += 1;
                self.let_depth += 1;
                let output = (|| {
                    for declaration in declarations {
                        self.elaborate_local_declaration(declaration)?;
                    }
                    self.infer(body)
                })();
                self.scope_depth -= 1;
                self.let_depth -= 1;
                self.restore_environment(previous);
                output
            },
            Expr::If(condition, yes, no) => {
                let condition_type = self.infer(condition)?;
                self.unify(condition_type, constructor("bool"))?;
                let yes_type = self.infer(yes)?;
                let no_type = self.infer(no)?;
                self.unify(yes_type.clone(), no_type)?;
                Ok(self.resolve(yes_type))
            },
            Expr::While(condition, body) => {
                let condition_type = self.infer(condition)?;
                self.unify(condition_type, constructor("bool"))?;
                let body_type = self.infer(body)?;
                self.unify(body_type, constructor("unit"))?;
                Ok(constructor("unit"))
            },
            Expr::Case(target, clauses) => {
                let target_type = self.infer(target)?;
                let clause_type = self.clauses(clauses)?;
                let output = self.variable();
                self.unify(
                    clause_type,
                    Type::Function(Box::new(target_type), Box::new(output.clone())),
                )?;
                Ok(self.resolve(output))
            },
            Expr::Handle(body, clauses) => {
                let body_type = self.infer(body)?;
                let handler_type = self.clauses(clauses)?;
                self.unify(
                    handler_type,
                    Type::Function(Box::new(constructor("exn")), Box::new(body_type.clone())),
                )?;
                Ok(body_type)
            },
            Expr::Raise(body) => {
                let typ = self.infer(body)?;
                self.unify(typ, constructor("exn"))?;
                Ok(self.variable())
            },
            Expr::Sequence(values) => {
                let mut output = constructor("unit");
                for value in values {
                    output = self.infer(value)?;
                }
                Ok(output)
            },
            Expr::Typed(body, annotation) => {
                let given = self.annotation(annotation, &mut BTreeMap::new())?;
                let actual = self.infer(body)?;
                self.unify(given.clone(), actual)?;
                Ok(self.resolve(given))
            },
            Expr::AndAlso(a, b) | Expr::OrElse(a, b) => {
                let a_type = self.infer(a)?;
                let b_type = self.infer(b)?;
                self.unify(a_type, constructor("bool"))?;
                self.unify(b_type, constructor("bool"))?;
                Ok(constructor("bool"))
            },
        }
    }
    fn infer_record<'a>(
        &mut self,
        fields: impl Iterator<Item = (String, &'a Expr)>,
    ) -> Result<Type, MlError> {
        let mut types = BTreeMap::new();
        for (label, expression) in fields {
            let typ = self.infer(expression)?;
            if types.insert(label.clone(), typ).is_some() {
                return Err(self.error(format!("duplicate label {label}")));
            }
        }
        Ok(closed_record_type(types))
    }
    fn is_nonexpansive(&self, expression: &Expr) -> bool {
        match expression {
            Expr::Located(body, _) => self.is_nonexpansive(body),
            Expr::Apply(function, argument) => {
                self.is_nonexpansive_constructor(function) && self.is_nonexpansive(argument)
            },
            Expr::Tuple(values) | Expr::List(values) => {
                values.iter().all(|value| self.is_nonexpansive(value))
            },
            Expr::Record(fields) => fields.iter().all(|(_, value)| self.is_nonexpansive(value)),
            Expr::Typed(value, _) => self.is_nonexpansive(value),
            _ => expression.is_nonexpansive(),
        }
    }
    fn is_nonexpansive_constructor(&self, expression: &Expr) -> bool {
        match expression {
            Expr::Located(body, _) => self.is_nonexpansive_constructor(body),
            Expr::Name(name) => {
                if !self.environment.is_value_constructor(name) {
                    return false;
                }
                !matches!(
                    self.environment.lookup(name).map(|scheme| &scheme.body),
                    Some(Type::Function(_, result))
                        if matches!(&**result, Type::Constructor(identity, _) if identity == "ref")
                )
            },
            Expr::Typed(value, _) => self.is_nonexpansive_constructor(value),
            _ => false,
        }
    }
    pub fn declaration(&mut self, declaration: &Declaration) -> Result<(), MlError> {
        match declaration {
            Declaration::Fixity { .. } => Ok(()),
            Declaration::Value { recursive, bindings, .. } => {
                let mut recursive_types = BTreeMap::new();
                if *recursive {
                    for (pattern, _) in bindings {
                        let Pattern::Variable(name) = pattern else {
                            return Err(self.error("val rec requires variable pattern"));
                        };
                        let typ = self.variable();
                        recursive_types.insert(name.clone(), typ.clone());
                        self.environment.register_inferred(name, TypeScheme::mono(typ));
                    }
                }
                let mut all_bindings = BTreeMap::new();
                for (binding_index, (pattern, expression)) in bindings.iter().enumerate() {
                    if *recursive && expression.function_clauses().is_none() {
                        return Err(self.error("val rec requires function expression"));
                    }
                    self.expression_locations.push((BINDING_EXPRESSION_PATH, binding_index));
                    let typ = self.infer(expression);
                    self.expression_locations.pop();
                    let typ = typ?;
                    let mut bound = BTreeMap::new();
                    self.infer_pattern(pattern, typ, &mut bound)?;
                    for (name, typ) in bound {
                        if let Some(recursive_type) = recursive_types.get(&name) {
                            self.unify(recursive_type.clone(), typ.clone())?;
                        }
                        if all_bindings
                            .insert(name.clone(), (typ, self.is_nonexpansive(expression)))
                            .is_some()
                        {
                            return Err(self.error(format!("duplicate binding {name}")));
                        }
                    }
                }
                for name in recursive_types.keys() {
                    self.environment.values.remove(name);
                }
                for (name, (typ, is_nonexpansive)) in all_bindings {
                    let scheme = self.generalize(typ, is_nonexpansive)?;
                    self.environment.register_inferred(&name, scheme);
                }
                Ok(())
            },
            Declaration::Function { bindings, .. } => {
                let outer_free = self.environment_free_variables();
                let mut placeholders = BTreeMap::new();
                for (name, _) in bindings {
                    let typ = self.variable();
                    placeholders.insert(name.clone(), typ.clone());
                    self.environment.register_inferred(name, TypeScheme::mono(typ));
                }
                let mut inferred = Vec::new();
                for (binding_index, (name, clauses)) in bindings.iter().enumerate() {
                    let arity = clauses.first().map_or(0, |(patterns, _)| patterns.len());
                    let clauses = super::syntax::curry_clauses(clauses)
                        .ok_or_else(|| self.error("function requires at least one argument"))?;
                    let previous_path = self.expression_locations.len();
                    self.expression_locations.extend([
                        (self.span.start, self.span.end),
                        (BINDING_EXPRESSION_PATH, binding_index),
                    ]);
                    let typ = self.clauses(&clauses);
                    self.expression_locations.truncate(previous_path);
                    let typ = typ?;
                    self.unify(placeholders[name].clone(), typ.clone())?;
                    let inputs = function_input_types(&self.resolve(typ.clone()), arity)
                        .ok_or_else(|| {
                            self.error(format!("function {name} lost its curried input types"))
                        })?;
                    let key = super::value::FunctionKey {
                        declaration: (
                            self.span.source_name.clone(),
                            self.span.start,
                            self.span.end,
                        ),
                        name: name.clone(),
                    };
                    self.elaborations.function_inputs.insert(key.clone(), inputs);
                    self.elaborations.function_weak_variables.insert(key, outer_free.clone());
                    inferred.push((name.clone(), typ));
                }
                for name in placeholders.keys() {
                    self.environment.values.remove(name);
                }
                for (name, typ) in inferred {
                    let scheme = self.generalize(typ, true)?;
                    self.environment.register_inferred(&name, scheme);
                }
                Ok(())
            },
            Declaration::Expression(expression, _) => {
                let typ = self.infer(expression)?;
                let scheme = self.generalize(typ, self.is_nonexpansive(expression))?;
                self.environment.register_inferred("it", scheme);
                Ok(())
            },
            Declaration::Exception { name, argument, alias, .. } => {
                let typ = if let Some(target) = alias {
                    if !self.environment.is_value_constructor(target) {
                        return Err(self.error(format!("{target} is not an exception constructor")));
                    }
                    let scheme = self
                        .environment
                        .lookup(target)
                        .cloned()
                        .ok_or_else(|| self.error(format!("unbound exception {target}")))?;
                    let is_exception = match &scheme.body {
                        Type::Constructor(name, arguments)
                            if name == "exn" && arguments.is_empty() =>
                        {
                            true
                        },
                        Type::Function(_, result) => {
                            matches!(&**result, Type::Constructor(name, arguments)
                                if name == "exn" && arguments.is_empty())
                        },
                        _ => false,
                    };
                    if !is_exception {
                        return Err(self.error(format!("{target} is not an exception constructor")));
                    }
                    scheme
                } else if let Some(argument) = argument {
                    let input = self.annotation(argument, &mut BTreeMap::new())?;
                    TypeScheme::mono(Type::Function(Box::new(input), Box::new(constructor("exn"))))
                } else {
                    TypeScheme::mono(constructor("exn"))
                };
                self.environment.register_inferred(name, typ);
                self.environment.register_value_constructor(name);
                Ok(())
            },
            Declaration::Datatype { name, parameters, constructors, .. } => {
                let parameter_count = parameters.len();
                self.environment.register_datatype(name, parameter_count);
                let parameters = parameters
                    .iter()
                    .map(|name| (name.clone(), self.variable()))
                    .collect::<BTreeMap<_, _>>();
                if parameters.len() != parameter_count {
                    return Err(self.error(format!("duplicate parameter in datatype {name}")));
                }
                let identity = self
                    .environment
                    .type_identity(name)
                    .ok_or_else(|| self.error(format!("missing datatype {name}")))?;
                let result =
                    Type::Constructor(identity.to_owned(), parameters.values().cloned().collect());
                for (constructor_name, argument) in constructors {
                    let typ = if let Some(argument) = argument {
                        let mut declared = parameters.clone();
                        let input = self.annotation(argument, &mut declared)?;
                        if declared.len() != parameters.len() {
                            return Err(
                                self.error(format!("undeclared type variable in datatype {name}"))
                            );
                        }
                        if !self.environment.admits_equality(&input) {
                            self.environment.set_datatype_equality(name, false);
                        }
                        Type::Function(Box::new(input), Box::new(result.clone()))
                    } else {
                        result.clone()
                    };
                    self.environment.register_inferred(
                        constructor_name,
                        TypeScheme::polymorphic(
                            parameters
                                .values()
                                .filter_map(|typ| {
                                    if let Type::Variable(id) = typ { Some(*id) } else { None }
                                })
                                .collect(),
                            typ,
                        ),
                    );
                    self.environment.register_value_constructor(constructor_name);
                }
                Ok(())
            },
            Declaration::DatatypeReplication { name, source, .. } => {
                self.environment
                    .replicate_datatype(name, source)
                    .ok_or_else(|| self.error(format!("unknown datatype {source}")))?;
                Ok(())
            },
            Declaration::Type { name, parameters, definition, .. } => {
                let mut variables: BTreeMap<String, Type> =
                    parameters.iter().map(|name| (name.clone(), self.variable())).collect();
                if variables.len() != parameters.len() {
                    return Err(self.error(format!("duplicate parameter in type {name}")));
                }
                let definition = self.annotation(definition, &mut variables)?;
                if variables.len() != parameters.len() {
                    return Err(self.error(format!("undeclared type variable in type {name}")));
                }
                let ids = parameters
                    .iter()
                    .filter_map(|name| match variables.get(name) {
                        Some(Type::Variable(id)) => Some(*id),
                        _ => None,
                    })
                    .collect();
                self.environment.register_alias(name, ids, definition);
                Ok(())
            },
            Declaration::Open { names, .. } => {
                for name in names {
                    self.modules
                        .open(name, &mut self.environment)
                        .ok_or_else(|| self.error(format!("unknown structure {name}")))?;
                }
                Ok(())
            },
            Declaration::Abstype { datatype, body, span } => {
                if !matches!(&**datatype, Declaration::Datatype { .. }) {
                    return Err(self.error("abstype requires a datatype binding"));
                }
                let before = self.environment.clone();
                let saved_modules = self.modules.clone();
                self.scope_depth += 1;
                let result = (|| {
                    self.elaborate_local_declaration(datatype)?;
                    for declaration in body {
                        self.elaborate_local_declaration(declaration)?;
                    }
                    let mut exports = self.collect_structure_exports(body);
                    let mut types = BTreeSet::new();
                    datatype.collect_type_names(&mut types);
                    exports.extend_exports(&self.environment.select(&BTreeSet::new(), &types));
                    Ok(exports)
                })();
                self.scope_depth -= 1;
                let exports = result?;
                let exceptions = self.modules.collect_exception_exports(body);
                let modules = self.modules.select_exports(body);
                self.restore_environment(before);
                self.environment.extend_exports(&exports);
                self.modules = saved_modules;
                self.modules.extend(modules.clone());
                self.modules.record_local_exports(span, &exports, &modules, exceptions);
                Ok(())
            },
            Declaration::Local { local, body, span } => {
                let before = self.environment.clone();
                let saved_modules = self.modules.clone();
                self.scope_depth += 1;
                let result = (|| {
                    for declaration in local {
                        self.elaborate_local_declaration(declaration)?;
                    }
                    for declaration in body {
                        self.elaborate_local_declaration(declaration)?;
                    }
                    Ok(self.collect_structure_exports(body))
                })();
                self.scope_depth -= 1;
                let exports = result?;
                let exceptions = self.modules.collect_exception_exports(body);
                let modules = self.modules.select_exports(body);
                self.restore_environment(before);
                self.environment.extend_exports(&exports);
                self.modules = saved_modules;
                self.modules.extend(modules.clone());
                self.modules.record_local_exports(span, &exports, &modules, exceptions);
                Ok(())
            },
            Declaration::Structure { name, signature, body, .. } => {
                let mut namespace = self.infer_module(body)?;
                if let Some((signature, opaque)) = signature {
                    self.constrain_static_namespace(&mut namespace, signature, *opaque)?;
                }
                self.environment.register_static_namespace(name, &namespace);
                self.modules.structures.insert(name.clone(), namespace);
                Ok(())
            },
            Declaration::Signature { name, base, body, .. } => {
                self.register_static_signature(name, base.as_deref(), body)
            },
            Declaration::Functor { name, parameter, signature, body, .. } => {
                self.register_static_functor(name, parameter, signature, body)
            },
        }
    }

    pub(super) fn collect_structure_exports(&self, body: &[Declaration]) -> TypeEnvironment {
        let mut values = BTreeSet::new();
        let mut types = BTreeSet::new();
        for declaration in body {
            declaration.collect_value_names(&mut values, &|name| {
                self.environment.constructor_values.contains(name)
            });
            declaration.collect_type_names(&mut types);
            if let Declaration::DatatypeReplication { name, .. } = declaration
                && let Some(constructors) = self.environment.replicated_constructors(name)
            {
                values.extend(constructors.into_iter().map(|(constructor, _)| constructor));
            }
            let path = match declaration {
                Declaration::Structure { name, .. } => Some(name),
                Declaration::Open { names, .. } => {
                    for name in names {
                        let opened = self.modules.resolve(name).map(|ns| &ns.types);
                        if let Some(opened) = opened {
                            values.extend(opened.values.keys().cloned());
                            types.extend(opened.constructors.keys().cloned());
                            for child in self
                                .modules
                                .resolve(name)
                                .into_iter()
                                .flat_map(|ns| ns.structures.keys())
                            {
                                Self::collect_namespace_members(
                                    &self.environment,
                                    child,
                                    &mut values,
                                    &mut types,
                                );
                            }
                        }
                    }
                    None
                },
                Declaration::Local { span, .. } | Declaration::Abstype { span, .. } => {
                    if let Some(local) = self.modules.local_exports.get(&(
                        span.source_name.clone(),
                        span.start,
                        span.end,
                    )) {
                        values.extend(local.0.values.keys().cloned());
                        types.extend(local.0.constructors.keys().cloned());
                    }
                    None
                },
                _ => None,
            };
            if let Some(path) = path {
                Self::collect_namespace_members(&self.environment, path, &mut values, &mut types);
            }
        }
        self.environment.select(&values, &types)
    }

    fn collect_namespace_members(
        environment: &TypeEnvironment,
        path: &str,
        values: &mut BTreeSet<String>,
        types: &mut BTreeSet<String>,
    ) {
        let prefix = format!("{path}.");
        values.extend(environment.values.keys().filter(|name| name.starts_with(&prefix)).cloned());
        types.extend(
            environment.constructors.keys().filter(|name| name.starts_with(&prefix)).cloned(),
        );
    }

    pub(super) fn elaborate_local_declaration(
        &mut self,
        declaration: &Declaration,
    ) -> Result<(), MlError> {
        let span = declaration.span();
        let previous = std::mem::replace(&mut self.span, span.clone());
        let result = self.declaration(declaration);
        self.span = previous;
        result?;
        self.elaborations
            .insert((span.source_name, span.start, span.end), self.environment.clone());
        Ok(())
    }

    pub fn check_flexible_records(&self) -> Result<(), MlError> {
        let has_unresolved_row =
            self.flexible_records.keys().any(|id| !self.private_flexible_records.contains(id));
        let has_public_row = self.environment.values.values().any(|scheme| {
            scheme.flexible_records.keys().any(|id| self.flexible_records.contains_key(id))
        });
        if has_unresolved_row || has_public_row {
            Err(self.error("unresolved flexible record: a fixed record type is required"))
        } else {
            Ok(())
        }
    }
    pub(super) fn resolve_existing(&self, environment: TypeEnvironment) -> TypeEnvironment {
        self.resolve_environment(environment)
    }
    pub fn finish(mut self) -> (TypeEnvironment, Elaborations) {
        let environment = std::mem::take(&mut self.environment);
        self.environment = self.resolve_environment(environment);
        let pending = std::mem::take(&mut self.elaborations);
        let elaborations = self.resolve_elaborations(pending);
        (self.environment, elaborations)
    }
    fn resolve_elaborations(&self, mut elaborations: Elaborations) -> Elaborations {
        for environment in elaborations.declarations.values_mut() {
            *environment = self.resolve_environment(std::mem::take(environment));
        }
        for evidence in elaborations.typed_calls.values_mut() {
            evidence.argument = self.resolve(evidence.argument.clone());
            evidence.result = self.resolve(evidence.result.clone());
            let mut resolved_weak = BTreeSet::new();
            for id in &evidence.weak_variables {
                collect_variables(&self.resolve(Type::Variable(*id)), &mut resolved_weak);
            }
            evidence.weak_variables = resolved_weak;
        }
        for typ in elaborations.closure_inputs.values_mut() {
            *typ = self.resolve(typ.clone());
        }
        for inputs in elaborations.function_inputs.values_mut() {
            for typ in inputs {
                *typ = self.resolve(typ.clone());
            }
        }
        for variables in elaborations
            .closure_weak_variables
            .values_mut()
            .chain(elaborations.function_weak_variables.values_mut())
        {
            let mut resolved = BTreeSet::new();
            for id in variables.iter() {
                collect_variables(&self.resolve(Type::Variable(*id)), &mut resolved);
            }
            *variables = resolved;
        }
        for child in elaborations.applications.values_mut() {
            let pending = std::mem::take(std::rc::Rc::make_mut(child));
            *std::rc::Rc::make_mut(child) = self.resolve_elaborations(pending);
        }
        elaborations
    }
    fn resolve_environment(&self, mut environment: TypeEnvironment) -> TypeEnvironment {
        environment.equality = self.equality.clone();
        for scheme in environment.values.values_mut() {
            let quantified = scheme.quantified.iter().copied().collect::<BTreeSet<_>>();
            scheme.body = self.resolve_scheme(scheme.body.clone(), &quantified);
            for fields in scheme.flexible_records.values_mut() {
                for field in fields.values_mut() {
                    *field = self.resolve_scheme(field.clone(), &quantified);
                }
            }
        }
        environment
    }
}

fn rename_type_constructor(typ: &mut Type, from: &str, to: &str) {
    match typ {
        Type::Variable(_) => {},
        Type::Constructor(name, arguments) => {
            if name.as_str() == from {
                *name = to.to_owned();
            }
            for argument in arguments {
                rename_type_constructor(argument, from, to);
            }
        },
        Type::Function(input, output) => {
            rename_type_constructor(input, from, to);
            rename_type_constructor(output, from, to);
        },
        Type::Record(fields, _) => {
            for field in fields.values_mut() {
                rename_type_constructor(field, from, to);
            }
        },
    }
}

fn expand_type_constructor(typ: &mut Type, from: &str, shape: &Type) {
    match typ {
        Type::Variable(_) => {},
        Type::Constructor(name, arguments) if name.as_str() == from => {
            let parameters = arguments
                .iter()
                .cloned()
                .enumerate()
                .map(|(index, argument)| (index as u64, argument))
                .collect();
            *typ = substitute(shape, &parameters);
        },
        Type::Constructor(_, arguments) => {
            for argument in arguments {
                expand_type_constructor(argument, from, shape);
            }
        },
        Type::Function(input, output) => {
            expand_type_constructor(input, from, shape);
            expand_type_constructor(output, from, shape);
        },
        Type::Record(fields, _) => {
            for field in fields.values_mut() {
                expand_type_constructor(field, from, shape);
            }
        },
    }
}

fn constructor(name: &str) -> Type {
    Type::Constructor(name.to_owned(), Vec::new())
}
fn closed_record_type(fields: BTreeMap<String, Type>) -> Type {
    if fields.is_empty() {
        Type::Constructor("unit".to_owned(), Vec::new())
    } else {
        Type::Record(fields, false)
    }
}
fn collect_variables(typ: &Type, output: &mut BTreeSet<u64>) {
    match typ {
        Type::Variable(id) => {
            output.insert(*id);
        },
        Type::Constructor(_, args) => {
            for arg in args {
                collect_variables(arg, output);
            }
        },
        Type::Function(input, output_type) => {
            collect_variables(input, output);
            collect_variables(output_type, output);
        },
        Type::Record(fields, _) => {
            for typ in fields.values() {
                collect_variables(typ, output);
            }
        },
    }
}
fn substitute(typ: &Type, substitutions: &BTreeMap<u64, Type>) -> Type {
    match typ {
        Type::Variable(id) => substitutions.get(id).cloned().unwrap_or(Type::Variable(*id)),
        Type::Constructor(name, args) => Type::Constructor(
            name.clone(),
            args.iter().map(|arg| substitute(arg, substitutions)).collect(),
        ),
        Type::Function(input, output) => Type::Function(
            Box::new(substitute(input, substitutions)),
            Box::new(substitute(output, substitutions)),
        ),
        Type::Record(fields, open) => Type::Record(
            fields
                .iter()
                .map(|(name, typ)| (name.clone(), substitute(typ, substitutions)))
                .collect(),
            *open,
        ),
    }
}

fn function_input_types(typ: &Type, arity: usize) -> Option<Vec<Type>> {
    let mut current = typ;
    let mut inputs = Vec::with_capacity(arity);
    for _ in 0..arity {
        let Type::Function(input, output) = current else {
            return None;
        };
        inputs.push((**input).clone());
        current = output;
    }
    Some(inputs)
}
