//! Theory management — the top-level container.
//!
//! Corresponds to `src/Pure/theory.ML`.
//!
//! ## Isabelle's Theory Philosophy
//!
//! In Isabelle, a **theory** is a self-contained world of:
//! - A **signature** (declared types and constants with their most-general types)
//! - A set of **axioms** (named propositions that are accepted as true)
//! - A collection of **theorems** (proved from axioms via the trusted kernel)
//! - Parent theories (inheritance via `imports`)
//!
//! Theories are **immutable** once built. Extending a theory creates a new theory.
//! This ensures that reasoning in theory `T1` cannot be invalidated by changes in `T2`.
//!
//! ## The Pure Theory
//!
//! Isabelle always starts with theory `Pure`, which declares:
//! - The type `prop` (type of propositions)
//! - The three meta-logic constants: `Pure.all`, `Pure.imp`, `Pure.eq`
//! - No axioms — Pure has no axioms; soundness comes from the inference rules alone
//!
//! All other theories (HOL, FOL, ZF) are built on top of Pure.

use std::{collections::HashMap, sync::Arc};

use super::{
    sign::Signature,
    term::Term,
    thm::Thm,
    types::{Symbol, Typ},
};

// =========================================================================
// Theory
// =========================================================================

/// A named constant with its defining term (for definitions).
#[derive(Clone, Debug)]
pub struct Definition {
    pub name: Symbol,
    pub term: Arc<Term>, // the definiens (right-hand side)
}

/// A theory: a name, a signature, axioms, and theorems.
///
/// Theories form a DAG via `imports`. The root is always theory `Pure`.
#[derive(Clone, Debug)]
pub struct Theory {
    /// Theory name (e.g., "Pure", "HOL", "MyTheory").
    name: Symbol,
    /// Parent theories (the `imports` chain).
    parents: Vec<Arc<Theory>>,
    /// The theory's signature.
    signature: Signature,
    /// Named axioms (unproved; accepted as true).
    axioms: HashMap<Symbol, Arc<Term>>,
    /// Named definitions (constants introduced by definition).
    definitions: HashMap<Symbol, Definition>,
    /// Named theorems (proved via the kernel).
    theorems: HashMap<Symbol, Arc<Thm>>,
}

impl Theory {
    // =================================================================
    // Construction
    // =================================================================

    /// Create the root Pure theory.
    ///
    /// This is the minimal bootstrap theory: no parents, no axioms,
    /// only the Pure signature with the three meta-logic constants.
    pub fn pure() -> Arc<Theory> {
        Arc::new(Theory {
            name: Arc::from("Pure"),
            parents: Vec::new(),
            signature: Signature::pure(),
            axioms: HashMap::new(),
            definitions: HashMap::new(),
            theorems: HashMap::new(),
        })
    }

    /// Create a new theory extending existing theories.
    ///
    /// The new theory inherits all declarations and theorems from its parents.
    pub fn begin(name: impl Into<Symbol>, parents: Vec<Arc<Theory>>) -> Theory {
        // Build the extended signature by inheriting from parents
        let sig = if let Some(first) = parents.first() {
            first.signature.extend()
        } else {
            Signature::pure()
        };

        // In a real implementation, we'd merge signatures from all parents.
        // For now, just use the first parent's signature.

        Theory {
            name: name.into(),
            parents,
            signature: sig,
            axioms: HashMap::new(),
            definitions: HashMap::new(),
            theorems: HashMap::new(),
        }
    }

    // =================================================================
    // Accessors
    // =================================================================

    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn signature(&self) -> &Signature {
        &self.signature
    }
    pub fn parents(&self) -> &[Arc<Theory>] {
        &self.parents
    }

    /// Look up a constant's type in this theory (including ancestor theories).
    pub fn const_type(&self, name: &str) -> Option<&Typ> {
        if let Some(typ) = self.signature.const_type(name) {
            return Some(typ);
        }
        for parent in &self.parents {
            if let Some(typ) = parent.const_type(name) {
                return Some(typ);
            }
        }
        None
    }

    /// Check if a constant is declared in this theory.
    pub fn is_declared(&self, name: &str) -> bool {
        self.signature.is_declared(name) || self.parents.iter().any(|p| p.is_declared(name))
    }

    // =================================================================
    // Extension (building theories incrementally)
    // =================================================================

    /// Add an axiom to the theory.
    ///
    /// An axiom is a proposition accepted as true without proof.
    /// In Isabelle, axioms are rare — most things are proved or defined.
    pub fn add_axiom(&mut self, name: impl Into<Symbol>, prop: Term) {
        self.axioms.insert(name.into(), Arc::new(prop));
    }

    /// Add a definition.
    ///
    /// A definition introduces a new constant as shorthand for an existing term.
    /// E.g., `definition "foo == bar"` declares `foo` and defines it as `bar`.
    pub fn add_definition(&mut self, def: Definition) {
        self.definitions.insert(Arc::clone(&def.name), def);
    }

    /// Add a proved theorem to the theory.
    ///
    /// The theorem must be unconditional (no hypotheses) and its propositions
    /// must be built from constants declared in this theory.
    pub fn add_theorem(&mut self, name: impl Into<Symbol>, thm: Thm) {
        assert!(thm.is_unconditional(), "stored theorems must be unconditional");
        self.theorems.insert(name.into(), Arc::new(thm));
    }

    /// Declare a new constant in the signature.
    pub fn declare_const(&mut self, name: impl Into<Symbol>, typ: Typ) {
        self.signature.declare(name, typ);
    }

    // =================================================================
    // Lookup
    // =================================================================

    pub fn lookup_theorem(&self, name: &str) -> Option<&Arc<Thm>> {
        if let Some(thm) = self.theorems.get(name) {
            return Some(thm);
        }
        for parent in &self.parents {
            if let Some(thm) = parent.lookup_theorem(name) {
                return Some(thm);
            }
        }
        None
    }

    /// Collect all axiom names (including from parents).
    pub fn all_axiom_names(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self.axioms.keys().map(|n| n.as_ref()).collect();
        for parent in &self.parents {
            names.extend(parent.all_axiom_names());
        }
        names
    }

    /// Collect all theorem names (including from parents).
    pub fn all_theorem_names(&self) -> Vec<&str> {
        let mut names: Vec<&str> = self.theorems.keys().map(|n| n.as_ref()).collect();
        for parent in &self.parents {
            names.extend(parent.all_theorem_names());
        }
        names
    }
}

// =========================================================================
// Proof Context — local proof state
// =========================================================================

/// A proof context: local fixed variables and assumptions.
///
/// Corresponds to `Proof.context` in `src/Pure/context.ML`.
///
/// Why this is separate from Theory:
/// - Theory: global, immutable, shared
/// - Context: local, grows with `fix` and `assume`, shrinks with `discharge`
#[derive(Clone, Debug)]
pub struct ProofContext {
    /// The theory this context belongs to.
    theory: Arc<Theory>,
    /// Locally fixed term variables: name → (typ, is_free).
    fixes: Vec<(Symbol, Typ)>,
    /// Local assumptions (hypotheses).
    assumptions: Vec<Term>,
}

impl ProofContext {
    /// Create a new proof context from a theory.
    pub fn init(theory: &Arc<Theory>) -> Self {
        ProofContext { theory: Arc::clone(theory), fixes: Vec::new(), assumptions: Vec::new() }
    }

    pub fn theory(&self) -> &Arc<Theory> {
        &self.theory
    }

    /// Fix a variable: add it to the local context.
    /// Corresponds to `fix x :: τ` in Isar.
    pub fn fix(&mut self, name: impl Into<Symbol>, typ: Typ) {
        self.fixes.push((name.into(), typ));
    }

    /// Assume a proposition.
    /// Corresponds to `assume "A"` in Isar.
    pub fn assume(&mut self, prop: Term) {
        self.assumptions.push(prop);
    }

    pub fn fixes(&self) -> &[(Symbol, Typ)] {
        &self.fixes
    }
    pub fn assumptions(&self) -> &[Term] {
        &self.assumptions
    }

    /// Restore context to a previous state (for backtracking).
    pub(crate) fn restore_to(&mut self, fixes_len: usize, assumptions_len: usize) {
        self.fixes.truncate(fixes_len);
        self.assumptions.truncate(assumptions_len);
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::{
        super::thm::{CTerm, ThmKernel},
        *,
    };

    #[test]
    fn test_pure_theory() {
        let pure = Theory::pure();
        assert_eq!(pure.name(), "Pure");
        assert!(pure.parents().is_empty());
        assert!(pure.is_declared("Pure.imp"));
        assert!(pure.is_declared("Pure.all"));
        assert!(pure.is_declared("Pure.eq"));
        assert!(!pure.is_declared("HOL.eq"));
    }

    #[test]
    fn test_theory_extension() {
        let pure = Theory::pure();
        let mut my_theory = Theory::begin("MyTheory", vec![Arc::clone(&pure)]);
        my_theory.declare_const("MyTheory.foo", Typ::base("prop"));

        assert!(my_theory.is_declared("Pure.imp")); // inherited
        assert!(my_theory.is_declared("MyTheory.foo")); // own
    }

    #[test]
    fn test_add_theorem() {
        let pure = Theory::pure();
        let mut my_theory = Theory::begin("MyTheory", vec![Arc::clone(&pure)]);

        // Prove A ==> A in this theory
        let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
        let thm = ThmKernel::trivial(a).unwrap();

        my_theory.add_theorem("trivial", thm);
        assert!(my_theory.lookup_theorem("trivial").is_some());
    }

    #[test]
    fn test_proof_context() {
        let pure = Theory::pure();
        let mut ctx = ProofContext::init(&pure);

        ctx.fix("x", Typ::base("nat"));
        assert_eq!(ctx.fixes().len(), 1);
        assert_eq!(ctx.fixes()[0].0.as_ref(), "x");

        ctx.assume(Term::const_("P", Typ::base("prop")));
        assert_eq!(ctx.assumptions().len(), 1);
    }
}
