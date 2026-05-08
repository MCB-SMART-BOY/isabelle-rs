//! Isabelle-rs core: the foundational data types and trusted kernel.
//!
//! This module corresponds to `src/Pure/` in the Isabelle distribution.
//!
//! ## Architecture (aligned with Isabelle Pure)
//!
//! ```text
//! core/
//! ├── types.rs    — Sorts, type classes, type expressions (type.ML, sorts.ML)
//! ├── term.rs     — Lambda terms; de Bruijn representation (term.ML)
//! ├── logic.rs    — Pure meta-logic: !!, ==>, == (logic.ML)
//! ├── sign.rs     — Signatures: constant table + type checking (sign.ML)
//! ├── theory.rs   — Theories: signature + axioms + theorems (theory.ML)
//! │                └── ProofContext: fix/assume (context.ML)
//! └── thm.rs      — LCF trusted kernel (thm.ML)
//! ```
//!
//! ## Isabelle Philosophy
//!
//! 1. **Every constant must be declared in the signature** before use
//! 2. **The LCF kernel is the only way to create theorems**
//! 3. **Theories are immutable** — extension creates a new theory
//! 4. **Pure is the minimal bootstrap** — no axioms, just inference rules

pub mod types;
pub mod term;
pub mod logic;
pub mod sign;
pub mod theory;
pub mod thm;
pub mod envir;
pub mod term_subst;
pub mod unify;
pub mod tactic;
pub mod drule;
pub mod simplifier;
pub mod variable;
pub mod pattern;
pub mod more_thm;
pub mod consts;
pub mod facts;
pub mod net;
pub mod conjunction;
pub mod bires;
pub mod global_theory;

// Re-export the most commonly used types
pub use types::{Sort, Typ, ClassAlgebra};
pub use term::Term;
pub use logic::Pure;
pub use sign::Signature;
pub use theory::{Theory, ProofContext};
pub use thm::{CTerm, Thm, ThmKernel, Derivation};
pub use error::{IsabelleError, KernelError, TypeError, ProofError, Result};
pub use envir::Envir;
pub use term_subst::{subst_bounds, instantiate, beta_norm, generalize};

pub mod axclass;
pub mod proofterm;
pub mod error;