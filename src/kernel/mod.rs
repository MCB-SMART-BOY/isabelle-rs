//! Strict kernel nucleus — re-exports from the `isabelle-kernel` crate.
//!
//! The kernel is now a separate crate with zero dependencies on core, isar,
//! hol, theory, tools, lsp, server, session, syntax, or wasm.

pub mod convert;

pub use isabelle_kernel::KernelError;
pub use isabelle_kernel::context::{ProofContext, ProofObligation};
pub use isabelle_kernel::cterm::{CProp, CTerm, InstEntry};
pub use isabelle_kernel::derivation::Derivation;
pub use isabelle_kernel::identity::{ContextStamp, SignatureId, TheoryId};
pub use isabelle_kernel::invariant;
pub use isabelle_kernel::logic;
pub use isabelle_kernel::logic::{
    AxiomSchema, BasisDeclaration, LogicBasis, LogicBasisId, PolyType, PolyTypeParam,
    TypeInstantiation, TypeVarId,
};
pub use isabelle_kernel::name::Name;
pub use isabelle_kernel::rules::KernelRules;
pub use isabelle_kernel::search_fact::{SearchFact, SearchFactDb};
pub use isabelle_kernel::signature::{ConstScheme, Signature};
pub use isabelle_kernel::term::{RawTerm, Term};
pub(crate) use isabelle_kernel::theorem_builder;
pub use isabelle_kernel::DefinitionCertificateError;
pub use isabelle_kernel::theory::{
    DefinitionId, DependencyKind, DependencySet, TheoremId,
    TheorySnapshot, TrustedTheorem, TrustedTheory, accept_closed_theorem,
};
pub use isabelle_kernel::thm::{ClosedThm, KernelThm, OpenThm};
pub use isabelle_kernel::typ::{Sort, Ty};
pub use isabelle_kernel::theorem_id_v2_reference;
