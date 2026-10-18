//! Strict Isabelle/Pure-inspired kernel nucleus.
//!
//! This module is intentionally separate from the legacy `core` module. It is
//! the new TCB experiment: no compatibility certification, no dummy type, no
//! fallback theorem construction, and no goal-as-theorem API.

mod bound_proof;
mod class_proof;
pub mod context;
pub mod cterm;
pub mod derivation;
mod hol_basis_origin;
pub mod identity;
pub mod invariant;
pub mod logic;
pub mod name;
mod obligations;
#[cfg(test)]
mod reference;
pub mod rules;
pub mod search_fact;
pub mod signature;
mod sorts;
pub mod term;
pub mod theorem_builder;
pub mod theory;
pub mod thm;
pub mod typ;
pub mod unify;

pub use bound_proof::{
    BoundProof, BoundProofError, CompositionCandidate, CompositionFlags, CompositionOptions,
};
pub use class_proof::{
    ArityCert, ClassRelCert, ClosedOfClassProof, OfClassCandidate, SemanticArityCert,
    prove_of_class,
};
pub use context::{ProofContext, ProofObligation, ProofScope};
pub use cterm::{CProp, CTerm, CType, InstEntry};
pub use derivation::Derivation;
pub use identity::{ContextStamp, SignatureId, TheoryId};
pub use logic::{
    AxiomDependencyId, AxiomSchema, AxiomSchemaId, BasisDeclaration, LogicBasis, LogicBasisId,
    LogicPolicyId, PolyType, PolyTypeParam, TypeInstantiation, TypeVarId,
};
pub use name::Name;
pub use obligations::PayloadError;
pub use rules::KernelRules;
pub use search_fact::{SearchFact, SearchFactDb};
pub use signature::{ConstScheme, EmptyClassDeclCert, Signature};
pub use term::{RawTerm, Term};
pub use theory::{
    DefinitionId, DependencyKind, DependencySet, TheoremId, TheorySnapshot, TrustedTheorem,
    TrustedTheory, accept_closed_theorem,
};
pub use thm::{ClosedThm, KernelThm, OpenThm};
pub use typ::Sort;
pub use typ::Ty;

use thiserror::Error;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DefinitionCertificateError {
    /// The certificate's ID does not match the recomputed ID from its payload fields.
    IdMismatch { stored: DefinitionId, recomputed: DefinitionId },
    /// The certificate's parent field does not match the expected parent theory.
    ParentMismatch { stored: TheoryId, expected: TheoryId },
    /// The RHS references the constant being defined (self-reference).
    SelfReference { name: Name },
    /// The RHS contains free variables (must be closed).
    RhsNotClosed { name: Name },
    /// The RHS type does not match the declared type.
    RhsTypeMismatch { name: Name, declared: Ty, actual: Ty },
    /// The bound scheme disagrees with the type declaration.
    InvalidScheme { name: Name },
    /// An RHS annotation has a type atom not bound by the declared scheme.
    RhsContainsTypeVariables { name: Name, ty: Ty },
}

impl std::fmt::Display for DefinitionCertificateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IdMismatch { stored, recomputed } => {
                write!(
                    f,
                    "definition certificate id mismatch: stored {stored:?} != recomputed {recomputed:?}"
                )
            },
            Self::ParentMismatch { stored, expected } => {
                write!(
                    f,
                    "definition certificate parent mismatch: stored {stored:?} != expected {expected:?}"
                )
            },
            Self::SelfReference { name } => {
                write!(f, "definition RHS for `{name}` references itself")
            },
            Self::RhsNotClosed { name } => {
                write!(f, "definition RHS for `{name}` is not closed")
            },
            Self::RhsTypeMismatch { name, declared, actual } => {
                write!(
                    f,
                    "definition RHS type mismatch for `{name}`: declared {declared:?}, actual {actual:?}"
                )
            },
            Self::InvalidScheme { name } => {
                write!(f, "definition {name:?} has an invalid polymorphic scheme")
            },
            Self::RhsContainsTypeVariables { name, ty } => {
                write!(f, "definition {name:?} has an unbound RHS type annotation {ty:?}")
            },
        }
    }
}

/// Errors from the strict kernel nucleus.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum KernelError {
    /// A scoped proof failed its binder, source authorization, or instance contract.
    #[error("bound proof: {0}")]
    BoundProof(#[from] BoundProofError),

    /// A proof retains unresolved or inconsistent sort, flex, scope, or staging obligations.
    #[error("theorem obligations: {0}")]
    TheoremObligations(#[from] PayloadError),

    #[error("reserved dummy type name is not allowed in the strict kernel")]
    ReservedDummyType,

    /// A type annotation names a constructor absent from the signature.
    #[error("undeclared type constructor `{0}`")]
    UndeclaredTypeConstructor(Name),
    /// A declared constructor was applied to the wrong number of arguments.
    #[error("type constructor `{name}` expects {expected} arguments, got {actual}")]
    TypeConstructorArityMismatch { name: Name, expected: usize, actual: usize },
    /// A public constructor arity exceeds the bounded semantic-model fanout.
    #[error("type constructor `{name}` arity {arity} exceeds maximum {max}")]
    TypeConstructorArityOutOfRange { name: Name, arity: usize, max: usize },
    /// No exact checked class proof/certificate exists in this owner.
    #[error("class proof lacks an exact certificate or a scoped premise")]
    UnknownClassEvidence,
    /// Invalid class declaration, relation, or arity at an owner boundary.
    #[error("invalid class evidence: {0}")]
    InvalidClassEvidence(String),
    /// An atomic fixed or schematic type has no trusted class derivation in this owner.
    #[error("unsupported sort `{sort:?}` for atomic type `{name}`")]
    UnsupportedTypeSort { name: Name, sort: Sort },
    /// A type substitution does not preserve the source variable's sort requirement.
    #[error("type instance `{ty:?}` does not satisfy required sort `{required:?}`")]
    TypeSortMismatch { ty: Ty, required: Sort },
    /// Repeated occurrences of the same atomic type identity disagree on their class sort.
    #[error("type `{name}` index {index:?} has conflicting sorts: `{expected:?}` and `{actual:?}`")]
    TypeIdentityMismatch { name: Name, index: Option<usize>, expected: Sort, actual: Sort },
    /// The variable identity cannot be represented without truncation.
    #[error("type variable `{name}` index {index} exceeds the schema identity range")]
    TypeVariableIndexOutOfRange { name: Name, index: usize },
    /// A fixed type has not been declared in this exact proof context.
    #[error("undeclared local fixed type `{name}` with sort `{sort:?}`")]
    UndeclaredTypeFree { name: Name, sort: Sort },
    /// Local type-scope identity allocation exhausted its non-repeating range.
    #[error("cannot declare local fixed type `{name}`: type-scope identity exhausted")]
    LocalTypeScopeExhausted { name: Name },
    /// Permanent theory constants and schemas cannot capture local fixed types.
    #[error(
        "permanent constant `{name}` cannot capture local fixed type `{fixed}` with sort `{sort:?}`"
    )]
    LocalTypeInSignature { name: Name, fixed: Name, sort: Sort },
    /// Closing an ordinary theorem cannot export an unbound local fixed-type scope.
    #[error("cannot close theorem with local fixed-type scope `{context:?}`")]
    LocalTypeScopeEscape { context: Box<ContextStamp> },
    /// A basis axiom failed declaration-aware schema certification at installation.
    #[error("invalid axiom schema `{name}`: {source}")]
    InvalidAxiomSchema { name: Name, source: Box<KernelError> },
    /// The requested axiom is not an exact schema permitted by the installed logic policy.
    #[error("axiom `{name}` is not approved by the logic policy")]
    UnapprovedAxiom { name: Name },
    /// A fixed HOL basis symbol lacks its authorized owner declaration or definition.
    #[error("HOL basis symbol `{name}` lacks its approved owner origin")]
    InvalidLogicBasisOrigin { name: Name },

    #[error("undeclared constant `{0}`")]
    UndeclaredConst(Name),

    #[error("undeclared local free `{0}`")]
    UndeclaredFree(Name),
    #[error("strict signature declaration `{name}` already exists")]
    DuplicateDeclaration { name: Name },

    #[error("trusted theorem name `{name}` already exists in the theory ancestry")]
    DuplicateTheorem { name: Name },

    /// A real hypothesis cannot contain schematic term or type variables.
    #[error("theorem hypothesis contains a schematic term or type variable")]
    SchematicHypothesis,

    /// User-fixable: choose an index above the complete source bound.
    #[error("generalization index {index} is not above source max index {max_index}")]
    GeneralizeIndexNotFresh { index: usize, max_index: usize },

    /// User-fixable: discharge hypotheses containing the selected fixed type.
    #[error("fixed type `{name}` occurs in a real hypothesis")]
    TypeFreeInHypotheses { name: Name },

    #[error("theorem candidate still has {hypotheses} undischarged hypotheses")]
    TheoremNotClosed { hypotheses: usize },

    #[error("accepting derivation replay does not exactly reproduce the theorem candidate")]
    AcceptanceReplayMismatch,

    #[error("accepting replay produced a dependency absent from the trusted theory ancestry")]
    UnknownTheoremDependency,

    #[error("derivation is unsupported by context-bound accepting replay")]
    UnsupportedAcceptanceDerivation,

    #[error("untrusted signature snapshot digest does not match its declarations")]
    SignatureDigestMismatch,

    #[error("mixed strict-kernel contexts: expected `{expected:?}`, got `{actual:?}`")]
    MixedContext { expected: Box<ContextStamp>, actual: Box<ContextStamp> },

    #[error("unbound de Bruijn index `{0}`")]
    UnboundBound(usize),

    #[error("type mismatch: expected `{expected:?}`, got `{actual:?}`")]
    TypeMismatch { expected: Ty, actual: Ty },

    #[error("expected a function type, got `{0:?}`")]
    NotFunctionType(Ty),

    #[error("expected a proposition, got `{0:?}`")]
    NotProposition(Ty),

    #[error("expected an equality proposition")]
    NotEquality,

    #[error("expected an implication proposition")]
    NotImplication,

    #[error("hypothesis not found")]
    HypothesisNotFound,

    #[error("antecedent mismatch")]
    AntecedentMismatch,

    #[error("middle terms are not strict alpha-equivalent")]
    MiddleMismatch,

    #[error("kernel invariant violation: {0}")]
    Invariant(String),

    #[error("expected a beta redex ((λx. body) arg), got `{0:?}`")]
    BetaRedexExpected(Ty),

    /// User-fixable: eta conversion requires a typed, capture-free `λx. f x`.
    #[error("expected an eta redex (λx. f x) with x absent from f, got `{0:?}`")]
    EtaRedexExpected(Ty),

    #[error("free variable `{name}` appears in hypotheses; cannot generalise")]
    FreeVarInHypotheses { name: Name },

    /// Schematic generalization cannot represent `index + offset` in `usize`.
    #[error("generalize variable index {index} plus offset {offset} overflows")]
    GeneralizeIndexOverflow { index: usize, offset: usize },

    #[error("expected a free or schematic variable, got `{0:?}`")]
    NotAbstractable(Ty),

    #[error("expected a forall proposition (⋀x. P)")]
    NotForall,

    #[error("forall binder/argument type mismatch: expected `{expected:?}`, got `{actual:?}`")]
    ForallBinderMismatch { expected: Ty, actual: Ty },

    #[error("duplicate substitution for Var `{name}` at index {index}")]
    DuplicateSubstitution { name: Name, index: usize },

    #[error("replacement contains Bound variable — not supported in strict instantiate")]
    BoundInSubstitution,

    #[error("subgoal index {index} out of range (goal has {nprems} subgoals)")]
    SubgoalIndexOutOfRange { index: usize, nprems: usize },

    #[error(
        "variable collision between rule and goal requires lifting: \
             rule has `{rule_var:?}`, goal has `{goal_var:?}`"
    )]
    RequiresLifting { rule_var: Name, goal_var: Name },
    #[error("definition certificate error: {0}")]
    DefinitionCertificate(DefinitionCertificateError),
}

impl From<DefinitionCertificateError> for KernelError {
    fn from(err: DefinitionCertificateError) -> Self {
        KernelError::DefinitionCertificate(err)
    }
}
