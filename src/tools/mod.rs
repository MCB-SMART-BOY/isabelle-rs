//! Proof automation tools.
//!
//! These are the "heavy lifters" of proof search, corresponding to
//! Isabelle's `src/Tools/` and various tactic implementations.
//!
//! ## Architecture
//!
//! ```text
//! tools/
//! ├── simp.rs    — Simplifier (term rewriting)
//! ├── auto.rs    — Auto method (heuristic proof search)
//! ├── blast.rs   — Tableau prover (classical logic)
//! ├── argo.rs    — Linear arithmetic solver
//! └── codegen.rs — Code generation (HOL → SML/OCaml/Haskell/Scala)
//! ```
//!
//! ## Relationship to kernel
//!
//! Tools use the LCF kernel's inference rules to produce theorems.
//! They never bypass the kernel — all results are certified.

pub mod auto;
pub mod blast;
pub mod reconstruct;
pub mod simp;
pub mod sledgehammer;
pub mod tptp;

// Future:
// pub mod argo;
// pub mod codegen;
