//! Proof automation tools.
//!
//! These are the "heavy lifters" of proof search, corresponding to
//! Isabelle's `src/Tools/` and various tactic implementations.
//!
//! ## Architecture
//!
//! ```text
//! tools/
//! ├── simp.rs        — HOL Simplifier (conditional rewriting + solver plugins)
//! ├── metis.rs       — Metis resolution prover + SAT solver (DPLL/CDCL)
//! ├── reconstruct.rs — ATP proof reconstruction (TSTP → LCF)
//! ├── sledgehammer.rs — Sledgehammer ATP invocation framework
//! └── tptp.rs        — TPTP FOF format export
//! ```
//!
//! ## Relationship to kernel
//!
//! Tools use the LCF kernel's inference rules to produce theorems.
//! They never bypass the kernel — all results are certified.
//!
//! Note: `auto` and `blast` proof methods are implemented directly in
//! `src/isar/method.rs` as part of the method dispatch system.

pub mod meson;
pub mod metis;
pub mod reconstruct;
pub mod simp;
pub mod sledgehammer;
pub mod tptp;
