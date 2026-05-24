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

pub mod bires;
pub mod conjunction;
pub mod consts;
pub mod drule;
pub mod envir;
pub mod facts;
pub mod global_theory;
pub mod logic;
pub mod more_thm;
pub mod net;
pub mod pattern;
pub mod sign;
pub mod simplifier;
pub mod tactic;
pub mod term;
pub mod term_subst;
pub mod theory;
pub mod thm;
pub mod types;
pub mod unify;
pub mod variable;

// Re-export the most commonly used types
pub use envir::Envir;
pub use error::{IsabelleError, KernelError, ProofError, Result, TypeError};
pub use logic::Pure;
pub use sign::Signature;
pub use term::Term;
pub use term_subst::{beta_norm, generalize, instantiate, subst_bounds};
pub use theory::{ProofContext, Theory};
pub use thm::{CTerm, Derivation, Thm, ThmKernel};
pub use types::{ClassAlgebra, Sort, Typ};

pub mod axclass;
pub mod error;
pub mod proofterm;
