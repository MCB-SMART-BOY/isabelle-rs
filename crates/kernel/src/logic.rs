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
//! The basis data itself is trusted bootstrap input — it must correctly
//! transcribe the logic's declarations (e.g., `HOL.thy`).  The kernel
//! performs structural and type validation but does not machine-check the
//! basis against an external source file.

use std::fmt;

use super::{KernelError, Name, RawTerm, Signature, Ty, identity::CanonicalEncoder};
use crate::signature::ConstScheme;
use crate::Sort;
use std::collections::BTreeMap;

// ── PolyType ──────────────────────────────────────────────────────────

/// A type-variable identity carrying a sort.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeVarId {
    pub name: Name,
    pub index: u32,
}

impl TypeVarId {
    pub fn new(name: impl Into<Name>, index: u32) -> Self {
        TypeVarId { name: name.into(), index }
    }
}

/// One parameter of a polymorphic type scheme.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PolyTypeParam {
    pub id: TypeVarId,
    pub sort: Sort,
}

/// A monomorphic instantiation of a polymorphic scheme.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeInstantiation {
    bindings: BTreeMap<TypeVarId, Ty>,
}

impl TypeInstantiation {
    pub fn empty() -> Self {
        TypeInstantiation { bindings: BTreeMap::new() }
    }

    pub fn try_new(bindings: BTreeMap<TypeVarId, Ty>) -> Result<Self, KernelError> {
        for (id, ty) in &bindings {
            if ty.has_type_vars() {
                return Err(KernelError::Invariant(
                    format!("non-concrete replacement for {:?}: {:?}", id, ty).into(),
                ));
            }
        }
        Ok(TypeInstantiation { bindings })
    }

    pub fn get(&self, id: &TypeVarId) -> Option<&Ty> { self.bindings.get(id) }
    pub fn iter(&self) -> impl Iterator<Item = (&TypeVarId, &Ty)> { self.bindings.iter() }
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
        // Check for duplicate params
        let mut seen: std::collections::HashSet<TypeVarId> = std::collections::HashSet::new();
        for p in &params {
            if !seen.insert(p.id.clone()) {
                return Err(KernelError::Invariant(
                    format!("duplicate type variable parameter {:?}", p.id).into(),
                ));
            }
        }
        // Check that all free type variables in body are bound in params
        let mut body_vars: std::collections::HashSet<(Name, usize)> = std::collections::HashSet::new();
        body.for_each_type_var(&mut |name, index| {
            body_vars.insert((name.clone(), index));
        });
        for (name, index) in &body_vars {
            let id = TypeVarId::new(name.clone(), *index as u32);
            if !params.iter().any(|p| p.id == id) {
                return Err(KernelError::Invariant(
                    format!("free type variable {:?} in body not bound in params", id).into(),
                ));
            }
        }
        Ok(PolyType { params: params.into_boxed_slice(), body })
    }

    pub fn params(&self) -> &[PolyTypeParam] { &self.params }
    pub fn body(&self) -> &Ty { &self.body }

    /// Check whether a monomorphic type is a valid instance of this scheme.
    pub fn monomorphic_instance_matches(&self, instance: &Ty) -> Option<TypeInstantiation> {
        let inst = self.body().is_monomorphic_instance_of(instance)?;
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
            encoder.write_name(param.sort.name()); // Sort is a Name newtype
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

impl AxiomSchemaId { pub fn to_bytes(self) -> [u8; 32] { self.0 } }

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
        let mut encoder = CanonicalEncoder::new(b"isabelle-rs/axiom-schema/v1");
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
        let mut encoder = CanonicalEncoder::new(b"isabelle-rs/dep-axiom-pair/v1");
        encoder.write_fixed_bytes(&basis_id.to_bytes());
        encoder.write_fixed_bytes(&schema_id.to_bytes());
        Self(encoder.finish())
    }
    pub fn to_bytes(self) -> [u8; 32] { self.0 }
}

impl fmt::Debug for AxiomDependencyId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AxiomDependencyId({:x?})", &self.0[..8])
    }
}

// ── LogicBasisId ──────────────────────────────────────────────────────

/// Domain tag for logic-basis identity digests.
pub(crate) const LOGIC_BASIS_DOMAIN: &[u8] = b"isabelle-rs/logic-basis/v1";

/// Content-addressed identity of a `LogicBasis`.
///
/// ```compile_fail
/// use isabelle_rs::kernel::LogicBasisId;
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

    /// Compute the identity digest from declarations and axioms.
    pub(crate) fn compute(
        declarations: &[BasisDeclaration],
        axioms: &[AxiomSchema],
    ) -> Self {
        let mut encoder = CanonicalEncoder::new(LOGIC_BASIS_DOMAIN);
        encoder.write_u64(declarations.len() as u64);
        for d in declarations {
            d.write_canonical(&mut encoder);
        }
        encoder.write_u64(axioms.len() as u64);
        for a in axioms {
            a.write_canonical(&mut encoder);
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
    declarations: Box<[BasisDeclaration]>,
    axioms: Box<[AxiomSchema]>,
}

impl LogicBasis {
    pub fn try_new(declarations: Vec<BasisDeclaration>, axioms: Vec<AxiomSchema>) -> Result<Self, KernelError> {
        let mut seen = std::collections::HashSet::new();
        for d in &declarations {
            let name = match d {
                BasisDeclaration::TypeConstructor { name, .. } => name,
                BasisDeclaration::Judgment { const_name, .. } => const_name,
                BasisDeclaration::Constant { name, .. } => name,
            };
            if !seen.insert(name.clone()) {
                return Err(KernelError::Invariant(
                    format!("duplicate basis declaration `{}`", name).into(),
                ));
            }
        }
        let mut ax_seen = std::collections::HashSet::new();
        for a in &axioms {
            if !ax_seen.insert(a.name.clone()) {
                return Err(KernelError::Invariant(
                    format!("duplicate axiom name `{}`", a.name).into(),
                ));
            }
        }
        let id = LogicBasisId::compute(&declarations, &axioms);
        Ok(LogicBasis { id, declarations: declarations.into_boxed_slice(), axioms: axioms.into_boxed_slice() })
    }

    pub fn from_untrusted_snapshot(declarations: Vec<BasisDeclaration>, axioms: Vec<AxiomSchema>) -> Result<Self, KernelError> {
        Self::try_new(declarations, axioms)
    }

    pub fn id(&self) -> LogicBasisId { self.id }
    pub fn declarations(&self) -> &[BasisDeclaration] { &self.declarations }
    pub fn axioms(&self) -> &[AxiomSchema] { &self.axioms }

    /// Validate that this basis's declarations are compatible with a signature.
    pub fn validate_against(&self, signature: &Signature) -> Result<(), KernelError> {
        for decl in self.declarations() {
            match decl {
                BasisDeclaration::TypeConstructor { name, arity: _ } => {
                    // Type constructors are not yet represented in Signature.
                    // Accept for now; arity checking deferred.
                    let _ = name;
                },
                BasisDeclaration::Judgment { const_name, ty } => {
                    // Judgment operators must be monomorphic (no type variables).
                    let declared = signature
                        .const_type(const_name)
                        .ok_or_else(|| KernelError::UndeclaredConst(const_name.clone()))?;
                    if !declared.is_concrete_type() {
                        return Err(KernelError::Invariant(
                            format!("judgment type for {const_name:?} must be monomorphic").into(),
                        ));
                    }
                    if declared != ty {
                        return Err(KernelError::TypeMismatch {
                            expected: ty.clone(),
                            actual: declared.clone(),
                        });
                    }
                },
                BasisDeclaration::Constant { name, scheme } => {
                    match signature.get_const(name) {
                        Some(ConstScheme::Monomorphic(ty)) => {
                            if scheme.monomorphic_instance_matches(ty).is_none() {
                                return Err(KernelError::TypeMismatch {
                                    expected: Ty::prop(),
                                    actual: ty.clone(),
                                });
                            }
                        },
                        Some(ConstScheme::Polymorphic(sig_scheme)) => {
                            // Require exact scheme equality — same params and body.
                            // This rejects mismatched type-variable names, indices,
                            // and body types even when arities match.
                            if scheme != sig_scheme {
                                return Err(KernelError::TypeMismatch {
                                    expected: Ty::prop(),
                                    actual: Ty::prop(),
                                });
                            }
                        },
                        None => return Err(KernelError::UndeclaredConst(name.clone())),
                    }
                },
            }
        }
        // Axiom schemas are validated at instantiation time (Phase 4).
        Ok(())
    }

    /// Look up an axiom schema by name.
    pub fn get_axiom(&self, name: &Name) -> Option<&AxiomSchema> {
        self.axioms.iter().find(|a| &a.name == name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn logic_basis_id_is_deterministic() {
        let decls = vec![BasisDeclaration::TypeConstructor { name: Name::from("bool"), arity: 0 }];
        let axioms = vec![];
        let id1 = LogicBasisId::compute(&decls, &axioms);
        let id2 = LogicBasisId::compute(&decls, &axioms);
        assert_eq!(id1, id2);
    }

    #[test]
    fn logic_basis_id_changes_with_content() {
        let decls1 = vec![BasisDeclaration::TypeConstructor { name: Name::from("bool"), arity: 0 }];
        let decls2 = vec![BasisDeclaration::TypeConstructor { name: Name::from("nat"), arity: 0 }];
        let axioms = vec![];
        let id1 = LogicBasisId::compute(&decls1, &axioms);
        let id2 = LogicBasisId::compute(&decls2, &axioms);
        assert_ne!(id1, id2);
    }

    #[test]
    fn validate_judgment_rejects_wrong_type() {
        let mut sig = Signature::new();
        sig = sig
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()))
            .unwrap();
        let basis = LogicBasis::try_new(
            vec![BasisDeclaration::Judgment {
                const_name: Name::from("HOL.Trueprop"),
                ty: Ty::arrow(Ty::base("nat").unwrap(), Ty::prop()), // wrong!
            }],
            vec![],
        ).unwrap();
        assert!(basis.validate_against(&sig).is_err());
    }

    #[test]
    fn validate_judgment_accepts_correct_type() {
        let mut sig = Signature::new();
        sig = sig
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()))
            .unwrap();
        let basis = LogicBasis::try_new(
            vec![BasisDeclaration::Judgment {
                const_name: Name::from("HOL.Trueprop"),
                ty: Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()),
            }],
            vec![],
        ).unwrap();
        assert!(basis.validate_against(&sig).is_ok());
    }

    #[test]
    fn polymorphic_scheme_mismatch_is_rejected() {
        // Declare eq in logic basis: 'a -> 'a -> prop
        let basis_scheme = PolyType::new(
            vec![PolyTypeParam { id: TypeVarId::new("'a", 0), sort: crate::Sort::typ() }],
            Ty::arrow(
                Ty::tvar("'a", 0, crate::Sort::typ()),
                Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::prop()),
            ),
        ).unwrap();
        let basis = LogicBasis::try_new(
            vec![BasisDeclaration::Constant {
                name: Name::from("eq"),
                scheme: basis_scheme.clone(),
            }],
            vec![],
        ).unwrap();

        // Install a DIFFERENT scheme in the signature: 'b -> 'b -> prop
        // Same arity (1 param), different body (uses 'b not 'a).
        // Under the old param-count check, this would pass.
        let sig_scheme = PolyType::new(
            vec![PolyTypeParam { id: TypeVarId::new("'b", 0), sort: crate::Sort::typ() }],
            Ty::arrow(
                Ty::tvar("'b", 0, crate::Sort::typ()),
                Ty::arrow(Ty::tvar("'b", 0, crate::Sort::typ()), Ty::prop()),
            ),
        ).unwrap();
        let sig = Signature::new()
            .extend_const_scheme("eq", sig_scheme)
            .unwrap();

        // Must reject: 'a -> 'a -> prop != 'b -> 'b -> prop
        assert!(
            basis.validate_against(&sig).is_err(),
            "must reject polymorphic scheme mismatch (different type-var names)"
        );
    }
}
