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

// ── PolyType ──────────────────────────────────────────────────────────

/// A polymorphic type scheme: `forall 'a 'b ... . body`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PolyType {
    /// Type variable binders (e.g. `['a, 'b]`).
    pub params: Vec<Name>,
    /// The body type, which may reference the bound variables.
    pub body: Ty,
}

impl PolyType {
    pub fn new(params: Vec<Name>, body: Ty) -> Self {
        PolyType { params, body }
    }

    /// Check whether a monomorphic type is a valid instance of this scheme.
    /// Currently accepts any type — full polymorphic checking requires a
    /// substitution engine (deferred to Phase 4).
    pub fn monomorphic_instance_matches(&self, instance: &Ty) -> bool {
        self.body.is_monomorphic_instance_of(instance)
    }

    pub(crate) fn write_canonical(&self, encoder: &mut CanonicalEncoder) {
        encoder.write_u64(self.params.len() as u64);
        for param in &self.params {
            encoder.write_name(param);
        }
        self.body.write_canonical(encoder);
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

    pub(crate) fn from_digest(digest: [u8; 32]) -> Self {
        Self(digest)
    }

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
    pub id: LogicBasisId,
    pub declarations: Vec<BasisDeclaration>,
    pub axioms: Vec<AxiomSchema>,
}

impl LogicBasis {
    /// Create a new basis and compute its identity.
    pub fn new(declarations: Vec<BasisDeclaration>, axioms: Vec<AxiomSchema>) -> Self {
        let id = LogicBasisId::compute(&declarations, &axioms);
        LogicBasis { id, declarations, axioms }
    }

    /// Validate that this basis's declarations are compatible with a signature.
    pub fn validate_against(&self, signature: &Signature) -> Result<(), KernelError> {
        for decl in &self.declarations {
            match decl {
                BasisDeclaration::TypeConstructor { name, arity: _ } => {
                    // Type constructors are not yet represented in Signature.
                    // Accept for now; arity checking deferred.
                    let _ = name;
                },
                BasisDeclaration::Judgment { const_name, ty } => {
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
                    let declared = signature
                        .const_type(name)
                        .ok_or_else(|| KernelError::UndeclaredConst(name.clone()))?;
                    if !scheme.monomorphic_instance_matches(declared) {
                        return Err(KernelError::TypeMismatch {
                            expected: Ty::prop(), // placeholder
                            actual: declared.clone(),
                        });
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
        let basis = LogicBasis::new(
            vec![BasisDeclaration::Judgment {
                const_name: Name::from("HOL.Trueprop"),
                ty: Ty::arrow(Ty::base("nat").unwrap(), Ty::prop()), // wrong!
            }],
            vec![],
        );
        assert!(basis.validate_against(&sig).is_err());
    }

    #[test]
    fn validate_judgment_accepts_correct_type() {
        let mut sig = Signature::new();
        sig = sig
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()))
            .unwrap();
        let basis = LogicBasis::new(
            vec![BasisDeclaration::Judgment {
                const_name: Name::from("HOL.Trueprop"),
                ty: Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()),
            }],
            vec![],
        );
        assert!(basis.validate_against(&sig).is_ok());
    }
}
