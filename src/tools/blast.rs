//! Blast — tableau prover for classical logic.
//!
//! `blast` is Isabelle's tableau-based classical reasoning method.
//! It works by:
//! 1. Negating the goal
//! 2. Building a tableau (closed branches = contradiction)
//! 3. Using unification to close branches
//!
//! ## Status: Stub

/// Tableau prover.
pub struct Blast;

impl Default for Blast {
    fn default() -> Self {
        Self::new()
    }
}

impl Blast {
    pub fn new() -> Self {
        Blast
    }

    /// Run blast on a goal.
    pub fn prove(&self, _goal: ()) -> Option<()> {
        None
    }
}
