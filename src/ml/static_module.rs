//! Type-only elaboration of ML modules; no expressions or host callbacks are evaluated here.
use super::types::{Infer, TypeEnvironment};
use super::value::{ApplicationKey, Functor, Namespace, SealingContext, Signature, ValueData};
use super::{Declaration, MlError, ModuleExpr, SignatureExpr, Span, Specification, TypeExpr};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Default)]
pub(super) struct StaticNamespace {
    pub types: TypeEnvironment,
    pub structures: BTreeMap<String, StaticNamespace>,
    exceptions: BTreeSet<String>,
}

impl StaticNamespace {
    fn from_runtime(namespace: &Namespace) -> Self {
        Self {
            types: namespace.type_environment.clone(),
            structures: namespace
                .structures
                .iter()
                .map(|(name, child)| (name.clone(), Self::from_runtime(child)))
                .collect(),
            exceptions: namespace
                .values
                .iter()
                .filter(|(_, value)| {
                    matches!(
                        &*value.0,
                        ValueData::Exception { .. } | ValueData::ExceptionFunction { .. }
                    )
                })
                .map(|(name, _)| name.clone())
                .collect(),
        }
    }

    fn lookup_shape(&self, path: &str) -> Option<super::types::Type> {
        match path.split_once('.') {
            Some((name, suffix)) => self.structures.get(name)?.lookup_shape(suffix),
            None => self.types.type_shape(path),
        }
    }

    fn lookup_identity(&self, path: &str) -> Option<&str> {
        match path.split_once('.') {
            Some((name, suffix)) => self.structures.get(name)?.lookup_identity(suffix),
            None => self.types.type_identity(path),
        }
    }
    fn lookup_stamp(&self, path: &str) -> Option<u128> {
        match path.split_once('.') {
            Some((name, suffix)) => self.structures.get(name)?.lookup_stamp(suffix),
            None => self.types.type_stamp(path),
        }
    }
    fn lookup_arity(&self, path: &str) -> Option<usize> {
        match path.split_once('.') {
            Some((name, suffix)) => self.structures.get(name)?.lookup_arity(suffix),
            None => self.types.type_arity(path),
        }
    }

    fn replace_type_identity(&mut self, from: &str, to: &str, stamp: u128) {
        self.types.replace_type_identity(from, to, stamp);
        for child in self.structures.values_mut() {
            child.replace_type_identity(from, to, stamp);
        }
    }
    fn bind_identity_to_shape(&mut self, from: &str, shape: &super::types::Type) {
        self.types.bind_type_identity_to_shape(from, shape);
        for child in self.structures.values_mut() {
            child.bind_identity_to_shape(from, shape);
        }
    }
}

#[derive(Clone)]
pub(super) struct StaticFunctor {
    parameter: String,
    signature: SignatureExpr,
    body: ModuleExpr,
    types: TypeEnvironment,
    modules: Box<StaticModules>,
}

impl StaticFunctor {
    fn from_runtime(functor: &Functor) -> Self {
        let mut modules = StaticModules::from_runtime(
            &functor.environment.structures,
            &functor.signatures,
            &functor.functors,
        );
        modules.structures.extend(
            functor
                .environment
                .structures
                .iter()
                .map(|(name, ns)| (name.clone(), StaticNamespace::from_runtime(ns))),
        );
        Self {
            parameter: functor.parameter.clone(),
            signature: functor.signature.clone(),
            body: functor.body.clone(),
            types: functor.environment.type_environment.clone(),
            modules: Box::new(modules),
        }
    }
}

pub(super) type ScopeKey = (String, usize, usize);
#[derive(Clone, Default)]
pub(super) struct StaticModules {
    pub structures: BTreeMap<String, StaticNamespace>,
    signatures: BTreeMap<String, Signature>,
    functors: BTreeMap<String, StaticFunctor>,
    pub local_exports: BTreeMap<ScopeKey, (TypeEnvironment, Box<StaticModules>, BTreeSet<String>)>,
}

impl StaticModules {
    pub fn from_runtime(
        structures: &BTreeMap<String, Namespace>,
        signatures: &BTreeMap<String, Signature>,
        functors: &BTreeMap<String, Functor>,
    ) -> Self {
        Self {
            structures: structures
                .iter()
                .map(|(name, ns)| (name.clone(), StaticNamespace::from_runtime(ns)))
                .collect(),
            signatures: signatures.clone(),
            functors: functors
                .iter()
                .map(|(name, functor)| (name.clone(), StaticFunctor::from_runtime(functor)))
                .collect(),
            local_exports: BTreeMap::new(),
        }
    }

    pub fn resolve(&self, path: &str) -> Option<&StaticNamespace> {
        let mut segments = path.split('.');
        let mut namespace = self.structures.get(segments.next()?)?;
        for segment in segments {
            namespace = namespace.structures.get(segment)?;
        }
        Some(namespace)
    }

    pub fn open(&mut self, path: &str, environment: &mut TypeEnvironment) -> Option<()> {
        let opened = self.resolve(path)?.clone();
        environment.extend_exports(&opened.types);
        for (name, child) in &opened.structures {
            environment.register_namespace_types(name, &child.types);
        }
        self.structures.extend(opened.structures);
        Some(())
    }

    pub fn record_local_exports(
        &mut self,
        span: &Span,
        types: &TypeEnvironment,
        modules: &StaticModules,
        exceptions: BTreeSet<String>,
    ) {
        self.local_exports.insert(
            (span.source_name.clone(), span.start, span.end),
            (types.clone(), Box::new(modules.clone()), exceptions),
        );
    }

    pub fn select_exports(&self, body: &[Declaration]) -> Self {
        let mut names = (BTreeSet::new(), BTreeSet::new(), BTreeSet::new());
        for declaration in body {
            match declaration {
                Declaration::Structure { name, .. } => {
                    names.0.insert(name.clone());
                },
                Declaration::Signature { name, .. } => {
                    names.1.insert(name.clone());
                },
                Declaration::Functor { name, .. } => {
                    names.2.insert(name.clone());
                },
                Declaration::Open { names: paths, .. } => {
                    for path in paths {
                        if let Some(namespace) = self.resolve(path) {
                            names.0.extend(namespace.structures.keys().cloned());
                        }
                    }
                },
                Declaration::Local { span, .. } | Declaration::Abstype { span, .. } => {
                    if let Some((_, exported, _)) =
                        self.local_exports.get(&(span.source_name.clone(), span.start, span.end))
                    {
                        names.0.extend(exported.structures.keys().cloned());
                        names.1.extend(exported.signatures.keys().cloned());
                        names.2.extend(exported.functors.keys().cloned());
                    }
                },
                _ => {},
            }
        }
        Self {
            structures: self
                .structures
                .iter()
                .filter(|(name, _)| names.0.contains(*name))
                .map(|(name, ns)| (name.clone(), ns.clone()))
                .collect(),
            signatures: self
                .signatures
                .iter()
                .filter(|(name, _)| names.1.contains(*name))
                .map(|(name, sig)| (name.clone(), sig.clone()))
                .collect(),
            functors: self
                .functors
                .iter()
                .filter(|(name, _)| names.2.contains(*name))
                .map(|(name, functor)| (name.clone(), functor.clone()))
                .collect(),
            local_exports: self.local_exports.clone(),
        }
    }

    pub fn extend(&mut self, other: Self) {
        self.structures.extend(other.structures);
        self.signatures.extend(other.signatures);
        self.functors.extend(other.functors);
        self.local_exports.extend(other.local_exports);
    }

    pub fn collect_exception_exports(&self, body: &[Declaration]) -> BTreeSet<String> {
        let mut exceptions = BTreeSet::new();
        for declaration in body {
            match declaration {
                Declaration::Exception { name, .. } => {
                    exceptions.insert(name.clone());
                },
                Declaration::Open { names, .. } => {
                    for name in names {
                        if let Some(namespace) = self.resolve(name) {
                            exceptions.extend(namespace.exceptions.iter().cloned());
                        }
                    }
                },
                Declaration::Local { span, .. } => {
                    if let Some((_, _, exported)) =
                        self.local_exports.get(&(span.source_name.clone(), span.start, span.end))
                    {
                        exceptions.extend(exported.iter().cloned());
                    }
                },
                _ => {},
            }
        }
        exceptions
    }
}

impl Infer {
    pub(super) fn register_static_signature(
        &mut self,
        name: &str,
        base: Option<&str>,
        body: &[Specification],
    ) -> Result<(), MlError> {
        let mut specifications = Vec::new();
        if let Some(base) = base {
            specifications.extend(
                self.modules
                    .signatures
                    .get(base)
                    .ok_or_else(|| self.error(format!("unknown included signature {base}")))?
                    .specifications
                    .iter()
                    .cloned(),
            );
        }
        for specification in body {
            if let Specification::Include(included) = specification {
                specifications.extend(
                    self.modules
                        .signatures
                        .get(included)
                        .ok_or_else(|| {
                            self.error(format!("unknown included signature {included}"))
                        })?
                        .specifications
                        .iter()
                        .cloned(),
                );
            } else {
                specifications.push(specification.clone());
            }
        }
        let signature = Signature {
            specifications,
            type_environment: std::rc::Rc::new(self.environment.clone()),
        };
        self.check_signature_declarations(&signature)?;
        self.modules.signatures.insert(name.to_owned(), signature);
        Ok(())
    }

    pub(super) fn register_static_functor(
        &mut self,
        name: &str,
        parameter: &str,
        signature: &SignatureExpr,
        body: &ModuleExpr,
    ) -> Result<(), MlError> {
        let argument = self.formal_signature(signature)?;
        let saved_types = self.environment.clone();
        let saved_modules = self.modules.clone();
        self.environment.register_static_namespace(parameter, &argument);
        self.modules.structures.insert(parameter.to_owned(), argument);
        let saved_elaborations = std::mem::take(&mut self.elaborations);
        let checked = self.infer_module(body);
        self.elaborations = saved_elaborations;
        self.restore_environment(saved_types);
        self.modules = saved_modules;
        checked?;
        self.modules.functors.insert(
            name.to_owned(),
            StaticFunctor {
                parameter: parameter.to_owned(),
                signature: signature.to_owned(),
                body: body.clone(),
                types: self.environment.clone(),
                modules: Box::new(self.modules.clone()),
            },
        );
        Ok(())
    }

    fn check_signature_declarations(&mut self, signature: &Signature) -> Result<(), MlError> {
        self.formal_signature_from(signature).map(|_| ())
    }

    fn formal_signature(&mut self, expression: &SignatureExpr) -> Result<StaticNamespace, MlError> {
        let signature = Signature::resolve(
            expression,
            &self.modules.signatures,
            &self.environment,
            &self.span,
        )?;
        self.formal_signature_from(&signature)
    }

    fn formal_signature_from(&mut self, signature: &Signature) -> Result<StaticNamespace, MlError> {
        let mut namespace = StaticNamespace {
            types: signature.type_environment.as_ref().clone(),
            ..StaticNamespace::default()
        };
        let mut values = BTreeSet::new();
        let mut types = BTreeSet::new();
        for spec in &signature.specifications {
            self.declare_formal_type(spec, &mut namespace, &mut types)?;
        }
        for spec in &signature.specifications {
            self.declare_formal_value(spec, &mut namespace, &mut values)?;
        }
        namespace.types = namespace.types.select(&values, &types);
        Ok(namespace)
    }

    fn declare_formal_type(
        &mut self,
        spec: &Specification,
        namespace: &mut StaticNamespace,
        names: &mut BTreeSet<String>,
    ) -> Result<(), MlError> {
        match spec {
            Specification::Type { name, parameters, equality, definition } => {
                if let Some(definition) = definition {
                    namespace.types.register_manifest_type(
                        name,
                        parameters,
                        definition,
                        self.span.clone(),
                    )?;
                } else {
                    namespace.types.register_signature_type(name, parameters.len(), *equality);
                }
                names.insert(name.clone());
            },
            Specification::Datatype(name, parameters, _) => {
                namespace.types.register_signature_type(name, parameters.len(), true);
                names.insert(name.clone());
            },
            Specification::DatatypeReplication(name, source) => {
                namespace
                    .types
                    .replicate_datatype(name, source)
                    .ok_or_else(|| self.error(format!("unknown replicated datatype {source}")))?;
                names.insert(name.clone());
            },
            Specification::WhereType { name, parameters, definition } => {
                if !names.contains(name) {
                    return Err(self.error(format!("where type requires signature type {name}")));
                }
                namespace.types.register_manifest_type(
                    name,
                    parameters,
                    definition,
                    self.span.clone(),
                )?;
            },
            Specification::Structure(name, signature) => {
                let signature = Signature::resolve(
                    signature,
                    &self.modules.signatures,
                    &namespace.types,
                    &self.span,
                )?;
                let child = self.formal_signature_from(&signature)?;
                namespace.types.register_static_namespace(name, &child);
                namespace.structures.insert(name.clone(), child);
            },
            Specification::Sharing(paths) => {
                let mut first = paths
                    .first()
                    .and_then(|path| namespace.lookup_shape(path))
                    .ok_or_else(|| self.error("empty or unknown sharing type"))?;
                let mut stamp = namespace
                    .lookup_stamp(&paths[0])
                    .ok_or_else(|| self.error("unknown sharing type stamp"))?;
                let arity = namespace
                    .lookup_arity(&paths[0])
                    .ok_or_else(|| self.error("unknown sharing type arity"))?;
                for path in paths.iter().skip(1) {
                    let other = namespace
                        .lookup_shape(path)
                        .ok_or_else(|| self.error(format!("unknown sharing type {path}")))?;
                    if namespace.lookup_arity(path) != Some(arity) {
                        return Err(self.error(format!("sharing type arity mismatch {path}")));
                    }
                    if first == other {
                        continue;
                    }
                    match (&first, &other) {
                        (
                            super::types::Type::Constructor(identity, _),
                            super::types::Type::Constructor(old, _),
                        ) if identity.starts_with('\0') && old.starts_with('\0') => {
                            namespace.replace_type_identity(old, identity, stamp);
                        },
                        (_, super::types::Type::Constructor(old, _)) if old.starts_with('\0') => {
                            namespace.bind_identity_to_shape(old, &first);
                        },
                        (super::types::Type::Constructor(old, _), _) if old.starts_with('\0') => {
                            namespace.bind_identity_to_shape(old, &other);
                            stamp = namespace
                                .lookup_stamp(path)
                                .ok_or_else(|| self.error("unknown sharing type stamp"))?;
                            first = other;
                        },
                        _ => return Err(self.error(format!("incompatible sharing type {path}"))),
                    }
                }
            },
            _ => {},
        }
        Ok(())
    }

    fn declare_formal_value(
        &mut self,
        spec: &Specification,
        namespace: &mut StaticNamespace,
        names: &mut BTreeSet<String>,
    ) -> Result<(), MlError> {
        let mut declarations = Vec::new();
        match spec {
            Specification::Value(name, typ) => {
                declarations.push((name.clone(), typ.clone(), false, false))
            },
            Specification::Exception(name, argument) => {
                declarations.push((name.clone(), exception_type(argument), true, true))
            },
            Specification::Datatype(name, parameters, constructors) => {
                for (constructor, argument) in constructors {
                    declarations.push((
                        constructor.clone(),
                        datatype_type(name, parameters, argument),
                        true,
                        false,
                    ));
                }
            },
            Specification::DatatypeReplication(name, _) => {
                for (constructor, _) in namespace
                    .types
                    .replicated_constructors(name)
                    .ok_or_else(|| self.error(format!("unknown replicated datatype {name}")))?
                {
                    names.insert(constructor);
                }
            },
            _ => {},
        }
        for (name, typ, constructor, exception) in declarations {
            let scheme = namespace.types.signature_scheme(&typ, self.span.clone())?;
            namespace.types.install_signature_scheme(&name, scheme);
            if constructor {
                namespace.types.register_value_constructor(&name);
            }
            if exception {
                namespace.exceptions.insert(name.clone());
            }
            names.insert(name);
        }
        Ok(())
    }

    pub(super) fn infer_module(&mut self, module: &ModuleExpr) -> Result<StaticNamespace, MlError> {
        self.infer_module_at(module, &[])
    }

    fn infer_module_at(
        &mut self,
        module: &ModuleExpr,
        path: &[u8],
    ) -> Result<StaticNamespace, MlError> {
        match module {
            ModuleExpr::Name(name) => self
                .modules
                .resolve(name)
                .cloned()
                .ok_or_else(|| self.error(format!("unknown structure {name}"))),
            ModuleExpr::Struct(body) => self.infer_struct_module(body),
            ModuleExpr::Apply(name, argument) => {
                self.infer_functor_application(name, argument, path)
            },
            ModuleExpr::Constrained(body, name, opaque) => {
                let mut inner_path = path.to_vec();
                inner_path.push(1);
                let mut namespace = self.infer_module_at(body, &inner_path)?;
                self.constrain_static_namespace(&mut namespace, name, *opaque)?;
                Ok(namespace)
            },
        }
    }

    fn infer_struct_module(&mut self, body: &[Declaration]) -> Result<StaticNamespace, MlError> {
        let before = self.environment.clone();
        let modules = self.modules.clone();
        self.scope_depth += 1;
        let result = (|| {
            for declaration in body {
                self.elaborate_local_declaration(declaration)?;
            }
            let types = self.collect_structure_exports(body);
            let exported = self.modules.select_exports(body);
            Ok(StaticNamespace {
                exceptions: self.modules.collect_exception_exports(body),
                types,
                structures: exported.structures,
            })
        })();
        self.scope_depth -= 1;
        self.restore_environment(before);
        self.modules = modules;
        result
    }

    fn infer_functor_application(
        &mut self,
        name: &str,
        argument: &ModuleExpr,
        path: &[u8],
    ) -> Result<StaticNamespace, MlError> {
        let functor = self
            .modules
            .functors
            .get(name)
            .cloned()
            .ok_or_else(|| self.error(format!("unknown functor {name}")))?;
        let mut argument_path = path.to_vec();
        argument_path.push(0);
        let mut argument = self.infer_module_at(argument, &argument_path)?;
        let key = ApplicationKey::at(&self.span, path);
        let before = self.environment.clone();
        let modules = self.modules.clone();
        let parent_elaborations = std::mem::take(&mut self.elaborations);
        self.environment = functor.types;
        self.modules = *functor.modules;
        let result = (|| {
            self.constrain_static_namespace(&mut argument, &functor.signature, false)?;
            self.environment.register_static_namespace(&functor.parameter, &argument);
            self.modules.structures.insert(functor.parameter, argument);
            self.infer_module(&functor.body)
        })();
        let child_elaborations = std::mem::replace(&mut self.elaborations, parent_elaborations);
        self.restore_environment(before);
        self.modules = modules;
        if result.is_ok() {
            self.elaborations.applications.insert(key, std::rc::Rc::new(child_elaborations));
        }
        result
    }

    pub(super) fn constrain_static_namespace(
        &mut self,
        namespace: &mut StaticNamespace,
        expression: &SignatureExpr,
        opaque: bool,
    ) -> Result<(), MlError> {
        let signature = Signature::resolve(
            expression,
            &self.modules.signatures,
            &self.environment,
            &self.span,
        )?;
        self.constrain_static_with_seals(namespace, &signature, opaque, "", &mut BTreeMap::new())
    }

    fn constrain_static_with_seals(
        &mut self,
        namespace: &mut StaticNamespace,
        signature: &Signature,
        opaque: bool,
        prefix: &str,
        shared: &mut BTreeMap<String, (String, u128)>,
    ) -> Result<(), MlError> {
        if opaque {
            self.collect_static_sharing(namespace, &signature.specifications, prefix, shared)?;
        }
        let mut exports = StaticNamespace::default();
        let mut manifest = BTreeSet::new();
        let mut check_types = signature.type_environment.as_ref().clone();
        check_types.extend_exports(&namespace.types);
        for (child_name, child) in &namespace.structures {
            check_types.register_namespace_types(child_name, &child.types);
        }
        for specification in &signature.specifications {
            self.check_static_spec(
                namespace,
                &check_types,
                &mut exports,
                &mut manifest,
                specification,
                &mut SealingContext { opaque, prefix, shared: &mut *shared },
            )?;
        }
        let values: BTreeSet<_> = exports.types.values.keys().cloned().collect();
        let types = exports.types.constructors.keys().cloned().collect();
        let constructors = exports.types.constructor_values.clone();
        exports.types = namespace.types.select(&values, &types);
        for value in values.difference(&constructors) {
            exports.types.hide_value_constructor(value);
        }
        if opaque {
            for type_name in &types {
                if manifest.contains(type_name) {
                    continue;
                }
                let equality = signature
                    .specifications
                    .iter()
                    .find_map(|specification| match specification {
                        Specification::Type { name, equality, .. } if name == type_name => {
                            Some(*equality)
                        },
                        _ => None,
                    })
                    .unwrap_or_else(|| {
                        namespace.types.type_admits_equality(type_name).unwrap_or(false)
                    });
                exports.types.seal_type(
                    type_name,
                    equality,
                    shared.get(&format!("{prefix}{type_name}")).cloned(),
                );
            }
        }
        self.install_static_signature_schemes(namespace, signature, &mut exports)?;
        *namespace = exports;
        Ok(())
    }

    // Keep the specification cases together: each exports into the state read by later cases.
    fn check_static_spec(
        &mut self,
        source: &StaticNamespace,
        types: &TypeEnvironment,
        exports: &mut StaticNamespace,
        manifest: &mut BTreeSet<String>,
        spec: &Specification,
        sealing: &mut SealingContext<'_>,
    ) -> Result<(), MlError> {
        match spec {
            Specification::Value(name, typ) => {
                types.check_value_spec(name, typ, self.span.clone())?;
                self.select_static_value(source, exports, name, false)
            },
            Specification::Exception(name, argument) => {
                let typ = exception_type(argument);
                types.check_value_spec(name, &typ, self.span.clone())?;
                if !source.exceptions.contains(name) {
                    return Err(self.error(format!("{name} is not an exception constructor")));
                }
                self.select_static_value(source, exports, name, true)
            },
            Specification::Type { name, parameters, equality, definition } => {
                self.select_static_type(source, exports, name, parameters.len(), *equality)?;
                if let Some(definition) = definition {
                    types.check_type_spec(name, parameters, definition, self.span.clone())?;
                    manifest.insert(name.clone());
                }
                Ok(())
            },
            Specification::Datatype(name, parameters, constructors) => {
                self.select_static_type(source, exports, name, parameters.len(), false)?;
                for (constructor, argument) in constructors {
                    let typ = datatype_type(name, parameters, argument);
                    types.check_value_spec(constructor, &typ, self.span.clone())?;
                    self.select_static_value(source, exports, constructor, true)?;
                }
                Ok(())
            },
            Specification::DatatypeReplication(name, original) => {
                let arity = source
                    .types
                    .type_arity(original)
                    .or_else(|| types.type_arity(original))
                    .ok_or_else(|| self.error(format!("unknown replicated datatype {original}")))?;
                self.select_static_type(source, exports, name, arity, false)?;
                if source.lookup_identity(name).is_none()
                    || source.lookup_identity(name)
                        != source
                            .lookup_identity(original)
                            .or_else(|| types.type_identity(original))
                {
                    return Err(
                        self.error(format!("datatype {name} does not replicate {original}"))
                    );
                }
                let constructors = source
                    .types
                    .replicated_constructors(name)
                    .ok_or_else(|| self.error(format!("unknown datatype {name}")))?;
                for (constructor, _) in constructors {
                    self.select_static_value(source, exports, &constructor, true)?;
                }
                manifest.insert(name.clone());
                Ok(())
            },
            Specification::Structure(name, signature) => {
                let mut child = source
                    .structures
                    .get(name)
                    .cloned()
                    .ok_or_else(|| self.error(format!("missing structure {name}")))?;
                let signature =
                    Signature::resolve(signature, &self.modules.signatures, types, &self.span)?;
                self.constrain_static_with_seals(
                    &mut child,
                    &signature,
                    sealing.opaque,
                    &format!("{}{name}.", sealing.prefix),
                    &mut *sealing.shared,
                )?;
                exports.structures.insert(name.clone(), child);
                Ok(())
            },
            Specification::Sharing(paths) => self.check_static_sharing(source, paths),
            Specification::WhereType { name, parameters, definition } => {
                if !exports.types.constructors.contains_key(name) {
                    return Err(self.error(format!("where type requires signature type {name}")));
                }
                types.check_type_spec(name, parameters, definition, self.span.clone())?;
                manifest.insert(name.clone());
                Ok(())
            },
            Specification::Include(name) => Err(self.error(format!("unresolved include {name}"))),
        }
    }

    fn select_static_type(
        &self,
        source: &StaticNamespace,
        exports: &mut StaticNamespace,
        name: &str,
        arity: usize,
        equality: bool,
    ) -> Result<(), MlError> {
        if source.types.type_arity(name) != Some(arity)
            || (equality && source.types.type_admits_equality(name) != Some(true))
        {
            return Err(self.error(format!("incompatible type specification {name}")));
        }
        let selected = source.types.select(&BTreeSet::new(), &BTreeSet::from([name.to_owned()]));
        exports.types.extend_exports(&selected);
        Ok(())
    }

    fn select_static_value(
        &self,
        source: &StaticNamespace,
        exports: &mut StaticNamespace,
        name: &str,
        constructor: bool,
    ) -> Result<(), MlError> {
        if !source.types.values.contains_key(name)
            || (constructor && !source.types.is_value_constructor(name))
        {
            return Err(self.error(format!("missing constructor or value {name}")));
        }
        let mut selected =
            source.types.select(&BTreeSet::from([name.to_owned()]), &BTreeSet::new());
        if !constructor {
            selected.hide_value_constructor(name);
        }
        exports.types.extend_exports(&selected);
        if constructor && source.exceptions.contains(name) {
            exports.exceptions.insert(name.to_owned());
        }
        Ok(())
    }

    fn check_static_sharing(
        &self,
        namespace: &StaticNamespace,
        paths: &[String],
    ) -> Result<(), MlError> {
        let first = paths.first().and_then(|path| namespace.lookup_shape(path));
        if first.is_none() || paths.iter().skip(1).any(|path| namespace.lookup_shape(path) != first)
        {
            return Err(self.error(format!("type identities do not agree: {}", paths.join(" = "))));
        }
        Ok(())
    }

    fn collect_static_sharing(
        &self,
        source: &StaticNamespace,
        specs: &[Specification],
        prefix: &str,
        shared: &mut BTreeMap<String, (String, u128)>,
    ) -> Result<(), MlError> {
        for spec in specs {
            let Specification::Sharing(paths) = spec else { continue };
            self.check_static_sharing(source, paths)?;
            let previous = paths
                .iter()
                .filter_map(|path| shared.get(&format!("{prefix}{path}")).cloned())
                .collect::<Vec<_>>();
            let identity =
                previous.first().cloned().unwrap_or_else(super::types::fresh_type_identity);
            for old in previous.into_iter().filter(|old| old != &identity) {
                for binding in shared.values_mut() {
                    if *binding == old {
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

    fn install_static_signature_schemes(
        &self,
        source: &StaticNamespace,
        signature: &Signature,
        exports: &mut StaticNamespace,
    ) -> Result<(), MlError> {
        let mut types = signature.type_environment.as_ref().clone();
        types.extend_exports(&source.types);
        types.extend_exports(&exports.types);
        for (name, structure) in &exports.structures {
            types.register_namespace_types(name, &structure.types);
        }
        for specification in &signature.specifications {
            let declared = match specification {
                Specification::Value(name, typ) => Some((name.as_str(), typ.clone())),
                Specification::Exception(name, argument) => {
                    Some((name.as_str(), exception_type(argument)))
                },
                _ => None,
            };
            if let Some((name, typ)) = declared {
                let scheme = types.signature_scheme(&typ, self.span.clone())?;
                exports.types.install_signature_scheme(name, scheme);
            }
            if let Specification::Datatype(name, parameters, constructors) = specification {
                for (constructor, argument) in constructors {
                    let typ = datatype_type(name, parameters, argument);
                    let scheme = types.signature_scheme(&typ, self.span.clone())?;
                    exports.types.install_signature_scheme(constructor, scheme);
                }
            }
        }
        Ok(())
    }
}

fn exception_type(argument: &Option<TypeExpr>) -> TypeExpr {
    let result = TypeExpr::Named("exn".to_owned(), Vec::new());
    match argument {
        Some(arg) => TypeExpr::Function(Box::new(arg.clone()), Box::new(result)),
        None => result,
    }
}

fn datatype_type(name: &str, parameters: &[String], argument: &Option<TypeExpr>) -> TypeExpr {
    let result = TypeExpr::Named(
        name.to_owned(),
        parameters.iter().map(|name| TypeExpr::Var(name.clone())).collect(),
    );
    match argument {
        Some(arg) => TypeExpr::Function(Box::new(arg.clone()), Box::new(result)),
        None => result,
    }
}
