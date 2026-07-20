//! Strict Isabelle/Pure-inspired kernel nucleus.
//!
//! This module is intentionally separate from the legacy `core` module. It is
//! the new TCB experiment: no compatibility certification, no dummy type, no
//! fallback theorem construction, and no goal-as-theorem API.

pub mod context;
pub mod cterm;
pub mod derivation;
pub mod identity;
pub mod invariant;
pub mod logic;
pub mod name;
pub mod rules;
pub mod search_fact;
pub mod signature;
pub mod term;
pub(crate) mod theorem_builder;
pub mod theory;
pub mod thm;
pub mod typ;
pub mod unify;

pub use context::{ProofContext, ProofObligation};
pub use cterm::{CProp, CTerm, InstEntry};
pub use derivation::Derivation;
pub use identity::{ContextStamp, SignatureId, TheoryId};
pub use logic::{AxiomSchema, BasisDeclaration, LogicBasis, LogicBasisId, PolyType};
pub use name::Name;
pub use rules::KernelRules;
pub use search_fact::{SearchFact, SearchFactDb};
pub use signature::Signature;
pub use term::{RawTerm, Term};
pub use theory::{
    DependencyKind, DependencySet, TheoremId, TheorySnapshot, TrustedTheorem, TrustedTheory,
    accept_closed_theorem,
};
pub use thm::{ClosedThm, KernelThm, OpenThm};
pub use typ::Ty;

use thiserror::Error;

/// Errors from the strict kernel nucleus.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum KernelError {
    #[error("reserved dummy type name is not allowed in the strict kernel")]
    ReservedDummyType,

    #[error("undeclared constant `{0}`")]
    UndeclaredConst(Name),

    #[error("undeclared local free `{0}`")]
    UndeclaredFree(Name),
    #[error("strict signature declaration `{name}` already exists")]
    DuplicateDeclaration { name: Name },

    #[error("trusted theorem name `{name}` already exists in the theory ancestry")]
    DuplicateTheorem { name: Name },

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
    MixedContext { expected: ContextStamp, actual: ContextStamp },

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

    #[error("free variable `{name}` appears in hypotheses; cannot generalise")]
    FreeVarInHypotheses { name: Name },

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
}
