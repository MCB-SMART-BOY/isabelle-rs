//! Auto method — heuristic proof search.
//!
//! `auto` is Isabelle's most used proof method. It combines:
//! - Classical reasoning (tableau)
//! - Simplification
//! - Introduction/elimination rule application
//! - Limited search depth
//!
//! ## Status: Stub

/// Auto proof search.
pub struct Auto;

impl Default for Auto {
    fn default() -> Self {
        Self::new()
    }
}

impl Auto {
    pub fn new() -> Self {
        Auto
    }

    /// Run auto on a goal.
    pub fn search(&self, _goal: ()) -> Option<()> {
        None
    }
}
