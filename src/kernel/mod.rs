//! Isabelle kernel — the trusted core.
//!
//! This module corresponds to `src/Pure/` in the Isabelle distribution.
//! It provides the LCF-style trusted kernel: types, terms, signatures,
//! theories, theorems, and the 9 primitive inference rules.
//!
//! ## Architecture
//!
//! ```text
//! kernel/
//! ├── arena.rs         — GlobalArena, TermId, TypeId, Symbol (V3 memory model)
//! ├── types.rs         — Sort, Typ, ClassAlgebra
//! ├── term.rs          — Lambda terms (de Bruijn)
//! ├── logic.rs         — Pure meta-logic (!!, ==>, ==)
//! ├── sign.rs          — Signatures
//! ├── theory.rs        — Theories & proof contexts
//! ├── thm.rs           — LCF trusted kernel (9 inference rules)
//! ├── envir.rs         — Variable environments
//! ├── unify.rs         — Higher-order unification
//! ├── tactic.rs        — Tactics & tacticals
//! ├── simplifier.rs    — Rewriting engine
//! ├── derived.rs       — Derived rules (forall, implies, compose, conjunction, bires)
//! ├── data.rs          — Facts, consts, discrimination nets
//! ├── proofterm.rs     — Proof terms
//! ├── axclass.rs       — Axiomatic type classes
//! ├── variable.rs      — Variable operations
//! ├── pattern.rs       — Higher-order pattern matching
//! ├── global_theory.rs — Global theory operations
//! └── error.rs         — Structured error types
//! ```

// Re-export everything from the existing core/ modules
pub use crate::core::*;

// Arena infrastructure (V3 memory model — currently dormant)
pub mod arena;

// Consolidated modules (Phase 2)
pub mod derived;  // drule + more_thm + conjunction + bires
pub mod data;     // facts + consts + net
