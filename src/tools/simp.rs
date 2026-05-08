//! HOL Simplifier — conditional term rewriting for HOL.
//!
//! Extends the kernel simplifier (`kernel/simplifier.rs`) with
//! HOL-specific rewrite rules: boolean connectives, quantifier
//! reasoning, arithmetic normalisation.
//!
//! ## Status: Stub
//!
//! The kernel simplifier already handles beta-reduction and basic
//! rewriting. This module will add:
//! - Conditional rewriting (`P ⟹ A = B`)
//! - Contextual simplification
//! - Solver plugins (decision procedures for subgoals)

/// HOL simplifier (extends kernel Simplifier).
pub struct HolSimplifier;

impl HolSimplifier {
    pub fn new() -> Self {
        HolSimplifier
    }
}

impl Default for HolSimplifier {
    fn default() -> Self {
        Self::new()
    }
}
