//! Immutable data-only logic basis — declares type constructors, judgments,
//! polymorphic constants, and axiom schemas for an object logic.
//!
//! A `LogicBasis` is a content-addressed manifest. It has no executable code,
//! no theorem constructors, and no privileged access to the kernel. The kernel
//! validates the basis against a `Signature` and authorizes axiom instances
//! and definition extensions only when the basis is installed.
//!
//! ## Trust status
//!
//! `HOLBasisV1` is checked against the thirteen fixed source schemas,
//! including complete term and type structure; this kernel-side transcription
//! is the reviewed bootstrap policy, not a runtime source-hash check.
//! `GenericResearch` remains an isolated, caller-trusted research basis and
//! is not a native HOL production policy.

use std::fmt;

use super::{
    KernelError, Name, ProofContext, RawTerm, Signature, TheorySnapshot, Ty,
    identity::CanonicalEncoder,
};
use crate::Sort;
use crate::signature::ConstScheme;
use std::collections::BTreeMap;

#[path = "hol_basis_policy.rs"]
mod hol_basis_policy;

/// Kernel-recognized initial assumption policy. Research owners never
/// inherit or merge into the checked HOLBasisV1 owner lineage.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LogicPolicyId {
    GenericResearch,
    HOLBasisV1,
}

impl LogicPolicyId {
    fn write_canonical(self, encoder: &mut CanonicalEncoder) {
        encoder.write_u8(match self {
            Self::GenericResearch => 0,
            Self::HOLBasisV1 => 1,
        });
    }
}

// ── PolyType ──────────────────────────────────────────────────────────

/// A type-variable identity carrying a sort.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeVarId {
    pub name: Name,
    pub index: u32,
    pub sort: Sort,
}

impl TypeVarId {
    pub fn new(name: impl Into<Name>, index: u32, sort: Sort) -> Self {
        Self { name: name.into(), index, sort }
    }
}

/// One bound schematic type parameter of a polymorphic scheme.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PolyTypeParam {
    pub id: TypeVarId,
}

/// A finite, simultaneous type substitution; signature/sort authority is checked at use.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeInstantiation {
    bindings: BTreeMap<TypeVarId, Ty>,
}

impl TypeInstantiation {
    pub fn empty() -> Self {
        TypeInstantiation { bindings: BTreeMap::new() }
    }

    pub fn try_new(bindings: BTreeMap<TypeVarId, Ty>) -> Result<Self, KernelError> {
        let mut last: Option<&TypeVarId> = None;
        for id in bindings.keys() {
            if let Some(previous) = last
                && previous.name == id.name
                && previous.index == id.index
            {
                return Err(KernelError::Invariant(format!(
                    "schematic type variable {}.{} has conflicting sort keys",
                    id.name, id.index
                )));
            }
            last = Some(id);
        }
        Ok(TypeInstantiation { bindings })
    }

    pub fn get(&self, id: &TypeVarId) -> Option<&Ty> {
        self.bindings.get(id)
    }
    pub fn iter(&self) -> impl Iterator<Item = (&TypeVarId, &Ty)> {
        self.bindings.iter()
    }
}

/// A polymorphic type scheme: `forall 'a 'b ... . body`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PolyType {
    params: Box<[PolyTypeParam]>,
    /// The body type, which may reference the bound variables.
    body: Ty,
}

impl PolyType {
    pub fn new(params: Vec<PolyTypeParam>, body: Ty) -> Result<Self, KernelError> {
        for (position, param) in params.iter().enumerate() {
            if params[..position].iter().any(|previous| previous.id == param.id) {
                return Err(KernelError::Invariant(format!(
                    "duplicate type variable parameter {:?}",
                    param.id
                )));
            }
        }
        let mut body_vars: Vec<(Name, usize, Sort)> = Vec::new();
        let mut has_conflicting_sort = false;
        body.for_each_type_var(&mut |name, index, sort| {
            if let Some((_, _, previous_sort)) =
                body_vars.iter().find(|(previous_name, previous_index, _)| {
                    previous_name == name && *previous_index == index
                })
            {
                has_conflicting_sort |= previous_sort != sort;
            } else {
                body_vars.push((name.clone(), index, sort.clone()));
            }
        });
        if has_conflicting_sort {
            return Err(KernelError::Invariant(
                "type scheme contains inconsistent sort annotations".into(),
            ));
        }
        for (name, index, sort) in &body_vars {
            let index = u32::try_from(*index).map_err(|_| {
                KernelError::TypeVariableIndexOutOfRange { name: name.clone(), index: *index }
            })?;
            if !params.iter().any(|param| {
                param.id.name == *name && param.id.index == index && param.id.sort == *sort
            }) {
                return Err(KernelError::Invariant(format!(
                    "unbound or incorrectly sorted type variable {name}.{index}::{sort:?} in scheme"
                )));
            }
        }
        for param in &params {
            if !body_vars.iter().any(|(name, index, sort)| {
                *name == param.id.name
                    && *index == param.id.index as usize
                    && *sort == param.id.sort
            }) {
                return Err(KernelError::Invariant(format!(
                    "type variable parameter {:?} does not appear in body",
                    param.id
                )));
            }
        }
        Ok(PolyType { params: params.into_boxed_slice(), body })
    }

    pub fn params(&self) -> &[PolyTypeParam] {
        &self.params
    }
    pub fn body(&self) -> &Ty {
        &self.body
    }

    /// Match a type instance structurally. The signature must still authorize its sorts.
    pub fn match_instance(&self, instance: &Ty) -> Option<TypeInstantiation> {
        let inst = self.body().match_instance(instance)?;
        // Verify all instantiated variables are declared in params
        for (tvid, _) in inst.iter() {
            if !self.params().iter().any(|p| p.id == *tvid) {
                return None;
            }
        }
        Some(inst)
    }

    pub(crate) fn write_canonical(&self, encoder: &mut CanonicalEncoder) {
        encoder.write_u64(self.params().len() as u64);
        for param in self.params() {
            encoder.write_name(&param.id.name);
            encoder.write_u64(param.id.index as u64);
            param.id.sort.write_canonical(encoder);
        }
        self.body().write_canonical(encoder);
    }
}

// ── BasisDeclaration ──────────────────────────────────────────────────

/// A single declaration in a logic basis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BasisDeclaration {
    /// `typedecl` — introduce a new type constructor with arity.
    TypeConstructor { name: Name, arity: usize },
    /// `judgment` — the propositional judgment operator (e.g. `HOL.Trueprop`).
    Judgment { const_name: Name, ty: Ty },
    /// `consts` — a polymorphic constant with its type scheme.
    Constant { name: Name, scheme: PolyType },
}

impl BasisDeclaration {
    pub(crate) fn write_canonical(&self, encoder: &mut CanonicalEncoder) {
        match self {
            Self::TypeConstructor { name, arity } => {
                encoder.write_u8(0); // discriminant
                encoder.write_name(name);
                encoder.write_u64(*arity as u64);
            },
            Self::Judgment { const_name, ty } => {
                encoder.write_u8(1);
                encoder.write_name(const_name);
                ty.write_canonical(encoder);
            },
            Self::Constant { name, scheme } => {
                encoder.write_u8(2);
                encoder.write_name(name);
                scheme.write_canonical(encoder);
            },
        }
    }
}

// ── AxiomSchema ───────────────────────────────────────────────────────

/// An axiom schema declared in a logic basis.
///
/// The proposition may contain schematic type and term variables. These are
/// instantiated when the axiom is used in a derivation (`Derivation::AxiomInstance`).
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct AxiomSchemaId(pub(crate) [u8; 32]);

impl AxiomSchemaId {
    pub fn to_bytes(self) -> [u8; 32] {
        self.0
    }
}

impl fmt::Debug for AxiomSchemaId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AxiomSchemaId({:x?})", &self.0[..4])
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AxiomSchema {
    pub name: Name,
    /// The proposition with schematic variables.
    pub prop: RawTerm,
}

impl AxiomSchema {
    pub fn id(&self) -> AxiomSchemaId {
        let mut encoder = CanonicalEncoder::new(b"isabelle-rs/axiom-schema/v2");
        encoder.write_name(&self.name);
        self.write_canonical(&mut encoder);
        AxiomSchemaId(encoder.finish())
    }

    pub(crate) fn write_canonical(&self, encoder: &mut CanonicalEncoder) {
        encoder.write_name(&self.name);
        // prop canonical encoding: serialize the RawTerm structure
        self.prop.write_canonical(encoder);
    }
}

/// Content-addressed pairing of a specific logic basis with a specific axiom schema.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AxiomDependencyId([u8; 32]);

impl AxiomDependencyId {
    pub fn compute(basis_id: LogicBasisId, schema_id: AxiomSchemaId) -> Self {
        let mut encoder = CanonicalEncoder::new(b"isabelle-rs/dep-axiom-pair/v2");
        encoder.write_fixed_bytes(&basis_id.to_bytes());
        encoder.write_fixed_bytes(&schema_id.to_bytes());
        Self(encoder.finish())
    }
    pub fn to_bytes(self) -> [u8; 32] {
        self.0
    }
}

impl fmt::Debug for AxiomDependencyId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AxiomDependencyId({:x?})", &self.0[..8])
    }
}

// ── LogicBasisId ──────────────────────────────────────────────────────

/// Domain tag for logic-basis identity digests.
pub(crate) const LOGIC_BASIS_DOMAIN: &[u8] = b"isabelle-rs/logic-basis/v3";

/// Content-addressed identity of a `LogicBasis`.
///
/// ```compile_fail
/// use isabelle_kernel::LogicBasisId;
/// let _forged = LogicBasisId([0; 32]);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LogicBasisId([u8; 32]);

impl LogicBasisId {
    pub fn to_bytes(self) -> [u8; 32] {
        self.0
    }
    #[allow(dead_code)] // part of CanonicalEncoder protocol, used by other modules
    pub(crate) fn from_digest(digest: [u8; 32]) -> Self {
        Self(digest)
    }

    #[allow(dead_code)] // part of CanonicalEncoder protocol
    pub(crate) fn write_canonical(self, encoder: &mut CanonicalEncoder) {
        encoder.write_fixed_bytes(&self.0);
    }

    /// Compute a policy-scoped identity from complete declaration and axiom ASTs.
    pub(crate) fn compute(
        policy: LogicPolicyId,
        declarations: &[BasisDeclaration],
        axioms: &[AxiomSchema],
    ) -> Self {
        let mut encoder = CanonicalEncoder::new(LOGIC_BASIS_DOMAIN);
        policy.write_canonical(&mut encoder);
        encoder.write_u64(declarations.len() as u64);
        for declaration in declarations {
            declaration.write_canonical(&mut encoder);
        }
        encoder.write_u64(axioms.len() as u64);
        for axiom in axioms {
            axiom.write_canonical(&mut encoder);
        }
        Self(encoder.finish())
    }
}

impl fmt::Debug for LogicBasisId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "LogicBasisId({:x?})", &self.0[..8])
    }
}

// ── LogicBasis ────────────────────────────────────────────────────────

/// An immutable, content-addressed logic basis.
///
/// The basis is pure data — it has no executable methods that return theorems.
/// It exists to be validated against a `Signature` and to authorize axiom
/// instances and definition extensions.
#[derive(Clone, Debug)]
pub struct LogicBasis {
    id: LogicBasisId,
    policy: LogicPolicyId,
    declarations: Box<[BasisDeclaration]>,
    axioms: Box<[AxiomSchema]>,
}

impl LogicBasis {
    pub fn try_new(
        declarations: Vec<BasisDeclaration>,
        axioms: Vec<AxiomSchema>,
    ) -> Result<Self, KernelError> {
        Self::try_with_policy(LogicPolicyId::GenericResearch, declarations, axioms)
    }

    /// Check every field of an approved HOLBasisV1 subset before installation.
    /// Subsets may be introduced on different branches, but their slots cannot
    /// be edited, renamed, repeated, or installed in a different source order.
    pub fn try_hol_basis(
        declarations: Vec<BasisDeclaration>,
        axioms: Vec<AxiomSchema>,
    ) -> Result<Self, KernelError> {
        Self::try_with_policy(LogicPolicyId::HOLBasisV1, declarations, axioms)
    }

    /// Reference ASTs for the thirteen fixed HOL slots and their initial
    /// declarations. These data do not install axiom authority.
    pub fn hol_v1_manifest() -> Result<(Vec<BasisDeclaration>, Vec<AxiomSchema>), KernelError> {
        Ok((hol_basis_policy::declarations()?, hol_basis_policy::axioms()?))
    }

    fn try_with_policy(
        policy: LogicPolicyId,
        declarations: Vec<BasisDeclaration>,
        axioms: Vec<AxiomSchema>,
    ) -> Result<Self, KernelError> {
        hol_basis_policy::check_subset(policy, &declarations, &axioms)?;
        let mut seen = std::collections::HashSet::new();
        for d in &declarations {
            let key = match d {
                BasisDeclaration::TypeConstructor { name, .. } => (true, name),
                BasisDeclaration::Judgment { const_name, .. } => (false, const_name),
                BasisDeclaration::Constant { name, .. } => (false, name),
            };
            let name = key.1;
            if !seen.insert(key) {
                return Err(KernelError::Invariant(format!(
                    "duplicate basis declaration `{}`",
                    name
                )));
            }
        }
        let mut ax_seen = std::collections::HashSet::new();
        for a in &axioms {
            if !ax_seen.insert(a.name.clone()) {
                return Err(KernelError::Invariant(format!("duplicate axiom name `{}`", a.name)));
            }
        }
        let id = LogicBasisId::compute(policy, &declarations, &axioms);
        Ok(LogicBasis {
            id,
            policy,
            declarations: declarations.into_boxed_slice(),
            axioms: axioms.into_boxed_slice(),
        })
    }

    pub fn from_untrusted_snapshot(
        declarations: Vec<BasisDeclaration>,
        axioms: Vec<AxiomSchema>,
    ) -> Result<Self, KernelError> {
        Self::try_new(declarations, axioms)
    }

    pub fn policy(&self) -> LogicPolicyId {
        self.policy
    }

    pub(crate) fn union(&self, other: &Self) -> Result<Self, KernelError> {
        if self.policy != other.policy {
            return Err(KernelError::Invariant(
                "incompatible logic policies in parent merge".into(),
            ));
        }
        if self.policy == LogicPolicyId::GenericResearch {
            if self.id != other.id {
                return Err(KernelError::Invariant("incompatible research logic bases".into()));
            }
            return Ok(self.clone());
        }
        let mut declarations = self.declarations.to_vec();
        for declaration in other.declarations() {
            if !declarations.contains(declaration) {
                declarations.push(declaration.clone());
            }
        }
        let mut axioms = self.axioms.to_vec();
        for axiom in other.axioms() {
            if !axioms.contains(axiom) {
                axioms.push(axiom.clone());
            }
        }
        hol_basis_policy::order_subset(&mut declarations, &mut axioms);
        Self::try_hol_basis(declarations, axioms)
    }
    pub fn id(&self) -> LogicBasisId {
        self.id
    }
    pub fn declarations(&self) -> &[BasisDeclaration] {
        &self.declarations
    }
    pub fn axioms(&self) -> &[AxiomSchema] {
        &self.axioms
    }

    /// Validate declarations and every complete axiom before installing this basis.
    pub fn validate_against(&self, signature: &Signature) -> Result<(), KernelError> {
        for declaration in self.declarations() {
            validate_basis_declaration(declaration, signature)?;
        }
        let context =
            ProofContext::new(TheorySnapshot::root("basis-validation", signature.clone()));
        for axiom in self.axioms() {
            context.validate_axiom_schema(axiom.prop.clone()).map_err(|source| {
                KernelError::InvalidAxiomSchema {
                    name: axiom.name.clone(),
                    source: Box::new(source),
                }
            })?;
        }
        Ok(())
    }

    /// Look up an axiom schema by name.
    pub fn get_axiom(&self, name: &Name) -> Option<&AxiomSchema> {
        self.axioms.iter().find(|a| &a.name == name)
    }
}

fn validate_basis_declaration(
    declaration: &BasisDeclaration,
    signature: &Signature,
) -> Result<(), KernelError> {
    match declaration {
        BasisDeclaration::TypeConstructor { name, arity } => {
            let actual = signature
                .type_constructor_arity(name)
                .ok_or_else(|| KernelError::UndeclaredTypeConstructor(name.clone()))?;
            if actual != *arity {
                return Err(KernelError::TypeConstructorArityMismatch {
                    name: name.clone(),
                    expected: *arity,
                    actual,
                });
            }
        },
        BasisDeclaration::Judgment { const_name, ty } => {
            signature.validate_type(ty)?;
            if !ty.is_concrete_type() {
                return Err(KernelError::Invariant(format!(
                    "judgment type for {const_name:?} must be monomorphic"
                )));
            }
            let declared = signature
                .const_type(const_name)
                .ok_or_else(|| KernelError::UndeclaredConst(const_name.clone()))?;
            if declared != ty {
                return Err(KernelError::TypeMismatch {
                    expected: ty.clone(),
                    actual: declared.clone(),
                });
            }
        },
        BasisDeclaration::Constant { name, scheme } => {
            validate_basis_constant(name, scheme, signature)?;
        },
    }
    Ok(())
}

fn validate_basis_constant(
    name: &Name,
    scheme: &PolyType,
    signature: &Signature,
) -> Result<(), KernelError> {
    signature.validate_type(scheme.body())?;
    let actual = match signature.get_const(name) {
        Some(ConstScheme::Monomorphic(ty)) => {
            let instance = scheme.match_instance(ty).ok_or_else(|| KernelError::TypeMismatch {
                expected: scheme.body().clone(),
                actual: ty.clone(),
            })?;
            return signature.validate_type_instantiation(&instance);
        },
        Some(ConstScheme::Polymorphic(declared)) if scheme == declared => return Ok(()),
        Some(ConstScheme::Polymorphic(declared)) => declared.body(),
        None => return Err(KernelError::UndeclaredConst(name.clone())),
    };
    Err(KernelError::TypeMismatch { expected: scheme.body().clone(), actual: actual.clone() })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn logic_basis_id_is_deterministic() {
        let decls = vec![BasisDeclaration::TypeConstructor { name: Name::from("bool"), arity: 0 }];
        let axioms = vec![];
        let id1 = LogicBasisId::compute(LogicPolicyId::GenericResearch, &decls, &axioms);
        let id2 = LogicBasisId::compute(LogicPolicyId::GenericResearch, &decls, &axioms);
        assert_eq!(id1, id2);
    }

    #[test]
    fn logic_basis_id_changes_with_content() {
        let decls1 = vec![BasisDeclaration::TypeConstructor { name: Name::from("bool"), arity: 0 }];
        let decls2 = vec![BasisDeclaration::TypeConstructor { name: Name::from("nat"), arity: 0 }];
        let axioms = vec![];
        let id1 = LogicBasisId::compute(LogicPolicyId::GenericResearch, &decls1, &axioms);
        let id2 = LogicBasisId::compute(LogicPolicyId::GenericResearch, &decls2, &axioms);
        assert_ne!(id1, id2);
    }

    #[test]
    fn validate_judgment_rejects_wrong_type() {
        let mut sig = Signature::new();
        sig = sig.extend_type_constructor("bool", 0).unwrap();
        sig = sig.extend_type_constructor("nat", 0).unwrap();
        sig = sig
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()))
            .unwrap();
        let basis = LogicBasis::try_new(
            vec![BasisDeclaration::Judgment {
                const_name: Name::from("HOL.Trueprop"),
                ty: Ty::arrow(Ty::base("nat").unwrap(), Ty::prop()), // wrong!
            }],
            vec![],
        )
        .unwrap();
        assert!(basis.validate_against(&sig).is_err());
    }

    #[test]
    fn validate_judgment_accepts_correct_type() {
        let mut sig = Signature::new();
        sig = sig.extend_type_constructor("bool", 0).unwrap();
        sig = sig
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()))
            .unwrap();
        let basis = LogicBasis::try_new(
            vec![BasisDeclaration::Judgment {
                const_name: Name::from("HOL.Trueprop"),
                ty: Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()),
            }],
            vec![],
        )
        .unwrap();
        assert!(basis.validate_against(&sig).is_ok());
    }

    #[test]
    fn polymorphic_scheme_mismatch_is_rejected() {
        // Declare eq in logic basis: 'a -> 'a -> prop
        let basis_scheme = PolyType::new(
            vec![PolyTypeParam { id: TypeVarId::new("'a", 0, crate::Sort::hol_type()) }],
            Ty::arrow(
                Ty::tvar("'a", 0, crate::Sort::hol_type()),
                Ty::arrow(Ty::tvar("'a", 0, crate::Sort::hol_type()), Ty::prop()),
            ),
        )
        .unwrap();
        let basis = LogicBasis::try_new(
            vec![BasisDeclaration::Constant {
                name: Name::from("eq"),
                scheme: basis_scheme.clone(),
            }],
            vec![],
        )
        .unwrap();

        // Install a DIFFERENT scheme in the signature: 'b -> 'b -> prop
        // Same arity (1 param), different body (uses 'b not 'a).
        // Under the old param-count check, this would pass.
        let sig_scheme = PolyType::new(
            vec![PolyTypeParam { id: TypeVarId::new("'b", 0, crate::Sort::hol_type()) }],
            Ty::arrow(
                Ty::tvar("'b", 0, crate::Sort::hol_type()),
                Ty::arrow(Ty::tvar("'b", 0, crate::Sort::hol_type()), Ty::prop()),
            ),
        )
        .unwrap();
        let sig = Signature::new()
            .install_empty_class(crate::EmptyClassDeclCert::hol_type())
            .unwrap()
            .extend_const_scheme("eq", sig_scheme)
            .unwrap();

        // Must reject: 'a -> 'a -> prop != 'b -> 'b -> prop
        assert!(
            basis.validate_against(&sig).is_err(),
            "must reject polymorphic scheme mismatch (different type-var names)"
        );
    }

    #[test]
    fn polymorphic_scheme_accepts_matching_sorts_and_rejects_mismatch() {
        let params = vec![PolyTypeParam { id: TypeVarId::new("'a", 0, Sort::hol_type()) }];
        // Matching sorts: accepted
        let body_match =
            Ty::arrow(Ty::tvar("'a", 0, Sort::hol_type()), Ty::tvar("'a", 0, Sort::hol_type()));
        assert!(
            PolyType::new(params.clone(), body_match).is_ok(),
            "matching sorts must be accepted"
        );

        // Mismatched sort: rejected
        let body_mismatch = Ty::tvar("'a", 0, Sort::arbitrary("other"));
        let result = PolyType::new(params, body_mismatch);
        assert!(result.is_err(), "sort mismatch must be rejected, got: {result:?}");
    }

    #[test]
    fn type_instantiation_conflicting_sort_identity_rejects() {
        let mut bindings = BTreeMap::new();
        bindings.insert(TypeVarId::new("a", 0, Sort::empty()), Ty::prop());
        bindings.insert(TypeVarId::new("a", 0, Sort::hol_type()), Ty::prop());
        assert!(TypeInstantiation::try_new(bindings).is_err());
    }

    #[test]
    fn polymorphic_scheme_rejects_unused_param() {
        let params = vec![
            PolyTypeParam { id: TypeVarId::new("'a", 0, Sort::hol_type()) },
            PolyTypeParam { id: TypeVarId::new("'b", 0, Sort::hol_type()) },
        ];
        // Body only uses 'a, not 'b
        let body = Ty::tvar("'a", 0, Sort::hol_type());
        assert!(PolyType::new(params, body).is_err(), "unused param must be rejected");
    }
}
