//! Generic context switching: theory and proof contexts.
//!
//! Corresponds to `src/Pure/context.ML` in the Isabelle/ML sources.
//!
//! # Context Architecture
//!
//! Isabelle maintains two fundamental context types:
//!
//! | Context      | Mutability | Purpose                                    |
//! |--------------|------------|--------------------------------------------|
//! | `Theory`     | Immutable  | Global declarations, constants, axioms     |
//! | `Proof`      | Mutable    | Local state for an open proof block        |
//!
//! This module models them as a single Rust [`Context`] enum that can hold
//! either variant, mirroring Isabelle's `Context.generic` ML type.
//!
//! # The [`Context`] Enum
//!
//! [`Context::Theory`] wraps an `Arc<Theory>` — a reference-counted
//! pointer to an immutable theory. Each theory update (e.g., adding a
//! new definition) produces a *new* `Theory` object, which is why we
//! use `Arc`: existing proof contexts continue to reference old theories
//! until explicitly transferred.
//!
//! [`Context::Proof`] wraps a boxed [`ProofState`] that holds:
//! - A reference to the underlying theory (`ProofState::theory`)
//! - Locally fixed variables (`fixes`)
//! - Local assumptions (`assumptions`)
//! - Let-bindings (`binds`)
//! - An optional current goal (`goal`)
//!
//! # Context Switching (`enter_proof` / `exit_proof`)
//!
//! The [`Context::enter_proof`] method transitions from a theory context
//! into a proof context, initializing a fresh [`ProofState`]. If already
//! in proof mode, it is a no-op.
//!
//! The [`Context::exit_proof`] method does the reverse: it discards the
//! proof-local state and returns the underlying theory context. This
//! matches Isabelle's `qed` command, which closes a proof block.
//!
//! The [`Context::transfer`] method propagates a theory update into an
//! open proof context, so that the proof sees the new definitions or
//! axioms without leaving proof mode.
//!
//! # Examples
//!
//! ```rust
//! use std::sync::Arc;
//!
//! use isabelle_rs::core::{context::Context, theory::Theory};
//!
//! let thy = Arc::new(Theory::pure());
//!
//! // Enter proof mode
//! let ctx = Context::theory(Arc::clone(&thy)).enter_proof();
//! assert!(ctx.is_proof());
//!
//! // Exit back to theory
//! let ctx = ctx.exit_proof();
//! assert!(ctx.is_theory());
//! ```

use std::sync::Arc;

use super::{
    term::Term,
    theory::Theory,
    types::{Symbol, Typ},
};

// =========================================================================
// Context — the generic context type
// =========================================================================

/// A generic context — either a theory or a proof context.
///
/// Corresponds to Isabelle's `Context.generic`.
#[derive(Clone, Debug)]
pub enum Context {
    /// Theory-level context (immutable, global).
    Theory(Arc<Theory>),
    /// Proof-level context (mutable, local to a proof block).
    Proof(Box<ProofState>),
}

/// Proof-local state that extends a theory context.
///
/// This struct holds everything that is scoped to a single proof block.
/// When `Context::exit_proof` is called, the entire `ProofState` is
/// discarded, so anything not explicitly recorded in the theory (e.g.,
/// proved theorems via `Tactic.prove`) is lost.
///
/// # Fields
///
/// - **`theory`** — A reference to the immutable theory that this proof block operates within.
///   Newly-proved theorems contribute to a new theory snapshot produced at `exit_proof` time.
/// - **`fixes`** — Locally-fixed term variables (e.g., `fix x::nat`). Each entry is a `(name,
///   type)` pair.
/// - **`assumptions`** — Propositions temporarily assumed true (e.g., from `assume "A"`).  These
///   are discharged when the proof is closed.
/// - **`binds`** — Local let-bindings introduced with `define`.
/// - **`goal`** — The current statement being proved (if the proof is in backward/refinement mode).
///   `None` when in forward/apply mode.
#[derive(Clone, Debug)]
pub struct ProofState {
    /// The underlying theory context.
    pub theory: Arc<Theory>,
    /// Locally fixed variables: name → (type, is_fixed).
    pub fixes: Vec<(Symbol, Typ)>,
    /// Local assumptions (propositions assumed true).
    pub assumptions: Vec<Term>,
    /// Local definitions (let bindings).
    pub binds: Vec<(Symbol, Term)>,
    /// The goal being proved (if in backward mode).
    pub goal: Option<Term>,
}

impl ProofState {
    /// Create a new proof state from a theory.
    pub fn init(theory: &Arc<Theory>) -> Self {
        ProofState {
            theory: Arc::clone(theory),
            fixes: Vec::new(),
            assumptions: Vec::new(),
            binds: Vec::new(),
            goal: None,
        }
    }
}

impl Context {
    // =================================================================
    // Construction
    // =================================================================

    /// Create a theory context.
    pub fn theory(theory: Arc<Theory>) -> Self {
        Context::Theory(theory)
    }

    /// Create a proof context from a theory.
    pub fn proof(theory: Arc<Theory>) -> Self {
        Context::Proof(Box::new(ProofState::init(&theory)))
    }

    /// Create a proof context with a goal.
    pub fn proof_with_goal(theory: Arc<Theory>, goal: Term) -> Self {
        let mut state = ProofState::init(&theory);
        state.goal = Some(goal);
        Context::Proof(Box::new(state))
    }

    // =================================================================
    // Accessors
    // =================================================================

    /// Get the underlying theory, regardless of context type.
    pub fn theory_of(&self) -> &Arc<Theory> {
        match self {
            Context::Theory(thy) => thy,
            Context::Proof(state) => &state.theory,
        }
    }

    /// Test if this is a theory context.
    pub fn is_theory(&self) -> bool {
        matches!(self, Context::Theory(_))
    }

    /// Test if this is a proof context.
    pub fn is_proof(&self) -> bool {
        matches!(self, Context::Proof(_))
    }

    /// Get the theory name.
    pub fn theory_name(&self) -> &str {
        self.theory_of().name()
    }

    // =================================================================
    // Context switching
    // =================================================================

    /// Enter proof mode: `Theory → Proof`.
    ///
    /// Returns a new proof context initialized from the theory.
    /// The theory remains unchanged.
    ///
    /// If the context is already a [`Proof`](Context::Proof), this is a
    /// no-op and the existing proof state is returned unchanged.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let thy = Arc::new(Theory::pure());
    /// let ctx = Context::theory(Arc::clone(&thy));
    /// let proof_ctx = ctx.enter_proof();
    /// assert!(proof_ctx.is_proof());
    /// assert_eq!(proof_ctx.theory_of().name(), thy.name());
    /// ```
    pub fn enter_proof(self) -> Context {
        match self {
            Context::Theory(thy) => Context::proof(thy),
            proof @ Context::Proof(_) => proof,
        }
    }

    /// Enter proof mode with a specific goal.
    pub fn enter_proof_with_goal(self, goal: Term) -> Context {
        match self {
            Context::Theory(thy) => Context::proof_with_goal(thy, goal),
            Context::Proof(mut state) => {
                state.goal = Some(goal);
                Context::Proof(state)
            },
        }
    }

    /// Exit proof mode: `Proof → Theory`.
    ///
    /// Discards local proof state (fixes, assumptions, binds, and goal)
    /// and returns the underlying theory context.
    ///
    /// If the context is already a [`Theory`](Context::Theory), this is a
    /// no-op.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let thy = Arc::new(Theory::pure());
    /// let ctx = Context::proof(Arc::clone(&thy)).exit_proof();
    /// assert!(ctx.is_theory());
    /// ```
    pub fn exit_proof(self) -> Context {
        match self {
            theory @ Context::Theory(_) => theory,
            Context::Proof(state) => Context::Theory(state.theory),
        }
    }

    /// Transfer context: apply a theory update to both modes.
    ///
    /// In Isabelle, this is used when a theory is extended (e.g., new definition)
    /// and all open proof contexts need to see the update.
    pub fn transfer(self, new_theory: Arc<Theory>) -> Context {
        match self {
            Context::Theory(_) => Context::Theory(new_theory),
            Context::Proof(mut state) => {
                state.theory = new_theory;
                Context::Proof(state)
            },
        }
    }

    // =================================================================
    // Proof operations
    // =================================================================

    /// Fix a variable in the proof context.
    pub fn fix(&mut self, name: impl Into<Symbol>, typ: Typ) {
        if let Context::Proof(state) = self {
            state.fixes.push((name.into(), typ));
        }
    }

    /// Assume a proposition in the proof context.
    pub fn assume(&mut self, prop: Term) {
        if let Context::Proof(state) = self {
            state.assumptions.push(prop);
        }
    }

    /// Bind a term to a name (let binding).
    pub fn define(&mut self, name: impl Into<Symbol>, term: Term) {
        if let Context::Proof(state) = self {
            state.binds.push((name.into(), term));
        }
    }

    /// Set the current goal.
    pub fn set_goal(&mut self, goal: Term) {
        if let Context::Proof(state) = self {
            state.goal = Some(goal);
        }
    }

    /// Get the current goal (if in proof mode).
    pub fn goal(&self) -> Option<&Term> {
        match self {
            Context::Proof(state) => state.goal.as_ref(),
            Context::Theory(_) => None,
        }
    }

    /// Get the list of fixed variables.
    pub fn fixes(&self) -> &[(Symbol, Typ)] {
        match self {
            Context::Proof(state) => &state.fixes,
            Context::Theory(_) => &[],
        }
    }

    /// Get the list of assumptions.
    pub fn assumptions(&self) -> &[Term] {
        match self {
            Context::Proof(state) => &state.assumptions,
            Context::Theory(_) => &[],
        }
    }
}

// =========================================================================
// Convenience conversions
// =========================================================================

impl From<Arc<Theory>> for Context {
    fn from(thy: Arc<Theory>) -> Self {
        Context::Theory(thy)
    }
}

/// Convert back from Context to Option<Arc<Theory>>
impl Context {
    pub fn into_theory(self) -> Option<Arc<Theory>> {
        match self {
            Context::Theory(thy) => Some(thy),
            Context::Proof(_) => None,
        }
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_context_theory_of() {
        let thy = Theory::pure();
        let ctx = Context::theory(Arc::clone(&thy));
        assert!(ctx.is_theory());
        assert_eq!(ctx.theory_of().name(), thy.name());
    }

    #[test]
    fn test_context_enter_exit_proof() {
        let thy = Theory::pure();
        let ctx = Context::theory(Arc::clone(&thy));

        // Enter proof mode
        let ctx = ctx.enter_proof();
        assert!(ctx.is_proof());

        // Set a goal
        let goal = Term::const_("A", Typ::base("prop"));
        let ctx = ctx.enter_proof_with_goal(goal.clone());
        assert_eq!(ctx.goal(), Some(&goal));

        // Exit proof mode
        let ctx = ctx.exit_proof();
        assert!(ctx.is_theory());
    }

    #[test]
    fn test_context_transfer() {
        let thy1 = Theory::pure();
        let ctx = Context::proof(Arc::clone(&thy1));

        let mut thy2 = Theory::begin("Test", vec![Arc::clone(&thy1)]);
        thy2.declare_const("c", Typ::base("bool"));
        let thy2 = Arc::new(thy2);

        let ctx = ctx.transfer(Arc::clone(&thy2));
        assert_eq!(ctx.theory_of().name(), "Test");
    }

    #[test]
    fn test_context_fix_assume() {
        let thy = Theory::pure();
        let mut ctx = Context::proof(Arc::clone(&thy));

        ctx.fix("x", Typ::base("nat"));
        ctx.assume(Term::const_("P(x)", Typ::base("prop")));

        assert_eq!(ctx.fixes().len(), 1);
        assert_eq!(ctx.assumptions().len(), 1);
    }
}
