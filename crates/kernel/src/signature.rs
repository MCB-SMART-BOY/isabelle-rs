use std::{collections::BTreeMap, sync::Arc};

use super::{
    KernelError, Name, Sort, Ty,
    identity::{CanonicalEncoder, SIGNATURE_DOMAIN, SignatureId},
    logic::{PolyType, PolyTypeParam, TypeInstantiation, TypeVarId},
    sorts::ClassAlgebra,
};

// A constructor arity is public input and later sizes semantic-model proof
// vectors. Bound that fanout before recording the declaration or allocating.
const MAX_TYPE_CONSTRUCTOR_ARITY: usize = 256;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ConstScheme {
    Monomorphic(Ty),
    Polymorphic(PolyType),
}

/// Certificate for the one axiom-free, superclass-free object carrier class.
/// This declaration alone provides no class relation, arity, or OFCLASS proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EmptyClassDeclCert {
    class: (),
}

impl EmptyClassDeclCert {
    pub fn hol_type() -> Self {
        Self { class: () }
    }
}

/// Immutable theory-level signature for strict certification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    id: SignatureId,
    consts: Arc<BTreeMap<Name, ConstScheme>>,
    type_constructors: Arc<BTreeMap<Name, usize>>,
    classes: Arc<ClassAlgebra>,
}

impl Signature {
    pub fn new() -> Self {
        let types = BTreeMap::from([(Name::from("prop"), 0), (Name::from("fun"), 2)]);
        Self::from_map(Arc::new(types), BTreeMap::new(), Arc::new(ClassAlgebra::empty()))
    }

    pub fn id(&self) -> SignatureId {
        self.id
    }

    /// Extend the type namespace without changing existing declarations.
    pub fn extend_type_constructor(
        &self,
        name: impl Into<Name>,
        arity: usize,
    ) -> Result<Self, KernelError> {
        let name = name.into();
        Self::validate_constructor_arity(&name, arity)?;
        if self.type_constructors.contains_key(&name) {
            return Err(KernelError::DuplicateDeclaration { name });
        }
        let mut types = (*self.type_constructors).clone();
        types.insert(name, arity);
        let types = Arc::new(types);
        let id = compute_signature_id(&types, &self.consts, &self.classes);
        Ok(Self {
            id,
            type_constructors: types,
            consts: Arc::clone(&self.consts),
            classes: Arc::clone(&self.classes),
        })
    }

    pub(crate) fn validate_constructor_arity(name: &Name, arity: usize) -> Result<(), KernelError> {
        if arity > MAX_TYPE_CONSTRUCTOR_ARITY {
            return Err(KernelError::TypeConstructorArityOutOfRange {
                name: name.clone(),
                arity,
                max: MAX_TYPE_CONSTRUCTOR_ARITY,
            });
        }
        Ok(())
    }

    pub fn type_constructor_arity(&self, name: &Name) -> Option<usize> {
        self.type_constructors.get(name).copied()
    }
    pub(crate) fn type_constructors(&self) -> impl Iterator<Item = (&Name, &usize)> {
        self.type_constructors.iter()
    }

    /// Validate every constructor and variable annotation against this signature.
    pub fn validate_type(&self, ty: &Ty) -> Result<(), KernelError> {
        if let Some((name, args)) = ty.dest_type() {
            let expected = self
                .type_constructor_arity(name)
                .ok_or_else(|| KernelError::UndeclaredTypeConstructor(name.clone()))?;
            if expected != args.len() {
                return Err(KernelError::TypeConstructorArityMismatch {
                    name: name.clone(),
                    expected,
                    actual: args.len(),
                });
            }
            for arg in args {
                self.validate_type(arg)?;
            }
        } else {
            ty.validate_type_variable()?;
            if let (Some(sort), Some(name)) = (ty.atomic_sort(), ty.atomic_name()) {
                self.classes.validate_sort(sort).map_err(|_| KernelError::UnsupportedTypeSort {
                    name: name.clone(),
                    sort: sort.clone(),
                })?;
            }
        }
        Ok(())
    }

    pub fn extend_const(&self, name: impl Into<Name>, ty: Ty) -> Result<Self, KernelError> {
        let name = name.into();
        if self.consts.contains_key(&name) {
            return Err(KernelError::DuplicateDeclaration { name });
        }
        self.validate_type(&ty)?;
        Self::reject_local_type(&name, &ty)?;
        let mut consts = (*self.consts).clone();
        consts.insert(name, ConstScheme::Monomorphic(ty));
        Ok(Self::from_map(Arc::clone(&self.type_constructors), consts, Arc::clone(&self.classes)))
    }

    /// Like `extend_const`, but rejects types containing type variables.
    /// Intended for judgment operators that must be monomorphic.
    pub fn extend_judgment_const(
        &self,
        name: impl Into<Name>,
        ty: Ty,
    ) -> Result<Self, KernelError> {
        if !ty.is_concrete_type() {
            return Err(KernelError::Invariant(
                "judgment constant type must be monomorphic (no type variables)".into(),
            ));
        }
        self.extend_const(name, ty)
    }

    pub fn extend_const_scheme(
        &self,
        name: impl Into<Name>,
        scheme: PolyType,
    ) -> Result<Self, KernelError> {
        let name = name.into();
        if self.consts.contains_key(&name) {
            return Err(KernelError::DuplicateDeclaration { name });
        }
        self.validate_type(scheme.body())?;
        Self::reject_local_type(&name, scheme.body())?;
        let mut consts = (*self.consts).clone();
        consts.insert(name, ConstScheme::Polymorphic(scheme));
        Ok(Self::from_map(Arc::clone(&self.type_constructors), consts, Arc::clone(&self.classes)))
    }

    fn reject_local_type(name: &Name, ty: &Ty) -> Result<(), KernelError> {
        if let Some((fixed, sort)) = ty.first_type_free() {
            return Err(KernelError::LocalTypeInSignature {
                name: name.clone(),
                fixed: fixed.clone(),
                sort: sort.clone(),
            });
        }
        Ok(())
    }

    pub fn get_const(&self, name: &Name) -> Option<&ConstScheme> {
        self.consts.get(name)
    }

    /// Returns the type only for [`ConstScheme::Monomorphic`] entries.
    /// Returns `None` for [`ConstScheme::Polymorphic`] entries.
    /// Prefer [`Signature::get_const`] or [`Signature::certify_const_instance`]
    /// for code that needs to handle both cases.
    pub fn const_type(&self, name: &Name) -> Option<&Ty> {
        match self.consts.get(name) {
            Some(ConstScheme::Monomorphic(ty)) => Some(ty),
            _ => None,
        }
    }

    /// Check whether a constant may be used at `requested_ty` and return the
    /// [`TypeInstantiation`] for polymorphic constants.
    ///
    /// - `Monomorphic(declared)` → `requested_ty == declared` (structurally equal).
    /// - `Polymorphic(scheme)` → structural matching followed by sort authorization.
    pub fn certify_const_instance(
        &self,
        name: &Name,
        requested_ty: &Ty,
    ) -> Result<TypeInstantiation, KernelError> {
        self.validate_type(requested_ty)?;
        match self.consts.get(name) {
            Some(ConstScheme::Monomorphic(declared)) => {
                if declared != requested_ty {
                    return Err(KernelError::TypeMismatch {
                        expected: declared.clone(),
                        actual: requested_ty.clone(),
                    });
                }
                Ok(TypeInstantiation::empty())
            },
            Some(ConstScheme::Polymorphic(scheme)) => {
                let instance = scheme.match_instance(requested_ty).ok_or_else(|| {
                    KernelError::TypeMismatch {
                        expected: scheme.body().clone(),
                        actual: requested_ty.clone(),
                    }
                })?;
                self.validate_type_instantiation(&instance)?;
                Ok(instance)
            },
            None => Err(KernelError::UndeclaredConst(name.clone())),
        }
    }

    /// Validate even replacements erased by subsequent term-binder instantiation.
    pub fn validate_type_instantiation(
        &self,
        instance: &TypeInstantiation,
    ) -> Result<(), KernelError> {
        let mut identities = crate::typ::TypeIdentityMap::default();
        for (id, replacement) in instance.iter() {
            self.validate_type(replacement)?;
            identities.validate(replacement)?;
            for class in id.sort.classes() {
                self.classes.validate_sort(&Sort::new(vec![class.clone()])).map_err(|_| {
                    KernelError::UnsupportedTypeSort {
                        name: id.name.clone(),
                        sort: id.sort.clone(),
                    }
                })?;
            }
            if !self.classes.has_type_sort(replacement, &id.sort).map_err(|error| {
                KernelError::Invariant(format!(
                    "class graph precheck failed for {replacement:?}: {error}"
                ))
            })? {
                return Err(KernelError::TypeSortMismatch {
                    ty: replacement.clone(),
                    required: id.sort.clone(),
                });
            }
        }
        Ok(())
    }

    pub(crate) fn has_certificate_edges(&self) -> bool {
        self.classes.has_certificate_edges()
    }

    pub(crate) fn has_class(&self, name: &Name) -> bool {
        self.classes.has_class(name)
    }
    pub(crate) fn declared_classes(&self) -> impl Iterator<Item = &Name> {
        self.classes.declared_classes()
    }

    pub(crate) fn is_protected_class_predicate(&self, name: &Name) -> bool {
        self.classes
            .declared_classes()
            .any(|class| name.as_str().strip_suffix("_class") == Some(class.as_str()))
    }

    pub(crate) fn validate_sort(&self, sort: &Sort) -> Result<(), KernelError> {
        self.classes
            .validate_sort(sort)
            .map_err(|error| KernelError::InvalidClassEvidence(error.to_string()))
    }
    /// Witness-search precheck only: undeclared sorts give no candidate.
    /// The eventual class proof is replayed independently before authorization.
    pub(crate) fn is_sort_le(&self, stronger: &Sort, weaker: &Sort) -> bool {
        self.classes.is_sort_le(stronger, weaker).unwrap_or(false)
    }
    pub(crate) fn minimize_sort(&self, sort: &Sort) -> Result<Sort, KernelError> {
        self.validate_sort(sort)?;
        let mut classes = Vec::new();
        for class in sort.classes() {
            let is_redundant = sort.classes().iter().any(|other| {
                other != class && self.classes.is_class_le(other, class).unwrap_or(false)
            });
            if !is_redundant {
                classes.push(class.clone());
            }
        }
        Ok(Sort::new(classes))
    }

    pub(crate) fn install_class_relation(
        &self,
        lower: &Name,
        upper: &Name,
    ) -> Result<Self, KernelError> {
        let classes = self
            .classes
            .add_relation(lower, upper)
            .map_err(|error| KernelError::InvalidClassEvidence(error.to_string()))?;
        Ok(Self::from_map(
            Arc::clone(&self.type_constructors),
            (*self.consts).clone(),
            Arc::new(classes),
        ))
    }

    pub(crate) fn install_class_arity(
        &self,
        tycon: &Name,
        arg_sorts: &[Sort],
        result: &Name,
    ) -> Result<Self, KernelError> {
        let arity = self
            .type_constructor_arity(tycon)
            .ok_or_else(|| KernelError::UndeclaredTypeConstructor(tycon.clone()))?;
        let classes = self
            .classes
            .add_arity(tycon, arity, arg_sorts, result)
            .map_err(|error| KernelError::InvalidClassEvidence(error.to_string()))?;
        Ok(Self::from_map(
            Arc::clone(&self.type_constructors),
            (*self.consts).clone(),
            Arc::new(classes),
        ))
    }

    /// Declare only the approved empty `HOL.type` class and the Pure type-tag
    /// syntax used to state OFCLASS. Declaring a constant is not a theorem or
    /// class fact; its proof still requires a checked class derivation.
    pub fn install_empty_class(&self, _cert: EmptyClassDeclCert) -> Result<Self, KernelError> {
        let classes = self
            .classes
            .declare_class(Name::from("HOL.type"), &[])
            .map_err(|error| KernelError::InvalidClassEvidence(error.to_string()))?;
        let signature = Self::from_map(
            Arc::clone(&self.type_constructors),
            (*self.consts).clone(),
            Arc::new(classes),
        );
        let signature = signature.extend_type_constructor("itself", 1)?;
        let alpha = Ty::tvar("a", 0, Sort::empty());
        let tag = Ty::apply("itself", vec![alpha])?;
        let parameter = PolyTypeParam { id: TypeVarId::new("a", 0, Sort::empty()) };
        let tag_scheme = PolyType::new(vec![parameter.clone()], tag.clone())?;
        let class_scheme = PolyType::new(vec![parameter], Ty::arrow(tag, Ty::prop()))?;
        signature
            .extend_const_scheme("Pure.type", tag_scheme)?
            .extend_const_scheme("HOL.type_class", class_scheme)
    }

    pub(crate) fn merge(&self, other: &Self) -> Result<Self, KernelError> {
        if self.id == other.id {
            return Ok(self.clone());
        }
        let mut types = (*self.type_constructors).clone();
        for (name, arity) in other.type_constructors.iter() {
            if let Some(previous) = types.insert(name.clone(), *arity)
                && previous != *arity
            {
                return Err(KernelError::TypeConstructorArityMismatch {
                    name: name.clone(),
                    expected: previous,
                    actual: *arity,
                });
            }
        }
        let mut consts = (*self.consts).clone();
        for (name, scheme) in other.consts.iter() {
            if let Some(previous) = consts.insert(name.clone(), scheme.clone())
                && previous != *scheme
            {
                return Err(KernelError::DuplicateDeclaration { name: name.clone() });
            }
        }
        let classes = self
            .classes
            .merge(&other.classes)
            .map_err(|error| KernelError::Invariant(format!("merging class graph: {error}")))?;
        Ok(Self::from_map(Arc::new(types), consts, Arc::new(classes)))
    }

    pub fn from_untrusted_snapshot(
        claimed_digest: [u8; 32],
        type_constructors: Vec<(Name, usize)>,
        declarations: Vec<(Name, Ty)>,
    ) -> Result<Self, KernelError> {
        let mut signature = Self::new();
        for (name, arity) in type_constructors {
            signature = signature.extend_type_constructor(name, arity)?;
        }
        for (name, ty) in declarations {
            signature = signature.extend_const(name, ty)?;
        }
        if signature.id.to_bytes() != claimed_digest {
            return Err(KernelError::SignatureDigestMismatch);
        }
        Ok(signature)
    }

    pub fn len(&self) -> usize {
        self.consts.len()
    }
    pub fn is_empty(&self) -> bool {
        self.consts.is_empty()
    }

    fn from_map(
        types: Arc<BTreeMap<Name, usize>>,
        consts: BTreeMap<Name, ConstScheme>,
        classes: Arc<ClassAlgebra>,
    ) -> Self {
        let id = compute_signature_id(&types, &consts, &classes);
        Self { id, type_constructors: types, consts: Arc::new(consts), classes }
    }
}

impl Default for Signature {
    fn default() -> Self {
        Self::new()
    }
}

fn compute_signature_id(
    types: &BTreeMap<Name, usize>,
    consts: &BTreeMap<Name, ConstScheme>,
    classes: &ClassAlgebra,
) -> SignatureId {
    let mut encoder = CanonicalEncoder::new(SIGNATURE_DOMAIN);
    encoder.write_u64(types.len() as u64);
    for (name, arity) in types {
        encoder.write_name(name);
        encoder.write_u64(*arity as u64);
    }
    encoder.write_u64(consts.len() as u64);
    for (name, scheme) in consts {
        encoder.write_u8(0);
        encoder.write_name(name);
        match scheme {
            ConstScheme::Monomorphic(ty) => {
                encoder.write_u8(0);
                ty.write_canonical(&mut encoder);
            },
            ConstScheme::Polymorphic(scheme) => {
                encoder.write_u8(1);
                scheme.write_canonical(&mut encoder);
            },
        }
    }
    classes.write_canonical(&mut encoder);
    SignatureId::from_digest(encoder.finish())
}
