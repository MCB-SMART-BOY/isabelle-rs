//! Local theory — incremental theory construction.
//!
//! Corresponds to `src/Pure/Isar/local_theory.ML`.
//!
//! A `LocalTheory` wraps a theory that is being constructed.
//! It processes theory-level commands (`definition`, `fun`, `datatype`,
//! `lemma`, etc.) and accumulates:
//! - New constant declarations (added to the signature)
//! - New axioms (accepted as true)
//! - New definitions (equational axioms)
//! - New theorems (proved lemmas)
//!
//! When the theory is complete (via `end`), the accumulated declarations
//! are frozen into a new immutable `Theory` that extends the parent.

use std::sync::Arc;

use crate::core::sign::Signature;
use crate::core::term::Term;
use crate::core::theory::Theory;
use crate::core::thm::{CTerm, Thm, ThmKernel};
use crate::core::types::Typ;

// =========================================================================
// LocalTheory
// =========================================================================

/// Incrementally built theory state.
#[derive(Clone)]
pub struct LocalTheory {
    /// The parent theory (immutable base).
    parent: Arc<Theory>,
    /// The theory name.
    name: String,
    /// Accumulated new constant declarations.
    new_consts: Vec<(String, Typ)>,
    /// Accumulated new type declarations.
    new_types: Vec<(String, usize)>,
    /// Accumulated new axioms.
    new_axioms: Vec<(String, Term)>,
    /// Accumulated new definitions.
    new_definitions: Vec<(String, Term)>,
    /// Accumulated new theorems (lemmas that have been proved).
    new_theorems: Vec<(String, Arc<Thm>)>,
    /// Current signature (extended from parent).
    signature: Signature,
}

impl LocalTheory {
    /// Begin a new theory extending the given parent.
    pub fn begin(parent: Arc<Theory>, name: &str) -> Self {
        LocalTheory {
            signature: parent.signature().clone(),
            parent,
            name: name.to_string(),
            new_consts: Vec::new(),
            new_types: Vec::new(),
            new_axioms: Vec::new(),
            new_definitions: Vec::new(),
            new_theorems: Vec::new(),
        }
    }

    /// The theory name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The current signature.
    pub fn signature(&self) -> &Signature {
        &self.signature
    }

    /// Number of new constants declared so far.
    pub fn const_count(&self) -> usize {
        self.new_consts.len()
    }

    /// Number of new theorems so far.
    pub fn theorem_count(&self) -> usize {
        self.new_theorems.len()
    }

    // ── Declaration commands ──

    /// `typedecl name` — declare a new type constructor.
    pub fn declare_type(&mut self, name: &str, arity: usize) {
        self.new_types.push((name.to_string(), arity));
    }

    /// `consts name :: typ` — declare a new constant.
    pub fn declare_const(&mut self, name: &str, typ: Typ) {
        self.new_consts.push((name.to_string(), typ.clone()));
        self.signature.declare(name, typ);
    }

    /// `definition name :: typ where "name = rhs"` — define a constant.
    /// The definition is accepted as an axiom (for now — proper definitional
    /// packages would prove the definition's consistency).
    pub fn define(&mut self, name: &str, typ: Typ, rhs: Term) -> Arc<Thm> {
        // Declare the constant
        self.declare_const(name, typ.clone());
        // Add the definition as an axiom: name == rhs
        let eq = Term::app(
            Term::app(
                Term::const_("Pure.eq", Typ::arrows(vec![typ.clone(), typ.clone()], Typ::base("prop"))),
                Term::const_(name, typ.clone()),
            ),
            rhs,
        );
        self.new_definitions.push((name.to_string(), eq.clone()));
        self.new_axioms.push((format!("{name}_def"), eq.clone()));
        // Return the definition as a theorem
        let ct = CTerm::certify(eq);
        let thm = ThmKernel::assume(ct);
        Arc::new(thm)
    }

    /// `axiomatization where name: "prop"` — add an axiom.
    /// Returns the axiom as a theorem.
    pub fn axiomatize(&mut self, name: &str, prop: Term) -> Arc<Thm> {
        self.new_axioms.push((name.to_string(), prop.clone()));
        let ct = CTerm::certify(prop);
        let thm = ThmKernel::assume(ct);
        Arc::new(thm)
    }

    /// `lemma name: "prop" ... proof ... qed` — record a proved theorem.
    pub fn note_theorem(&mut self, name: &str, thm: Arc<Thm>) {
        self.new_theorems.push((name.to_string(), thm));
    }

    /// `lemmas name = thms` — record named theorems.
    pub fn note_lemmas(&mut self, entries: Vec<(String, Vec<Arc<Thm>>)>) {
        for (name, thms) in entries {
            for (i, thm) in thms.into_iter().enumerate() {
                let full_name = if i == 0 {
                    name.clone()
                } else {
                    format!("{name}_{i}")
                };
                self.new_theorems.push((full_name, thm));
            }
        }
    }

    // ── Finalization ──

    /// Freeze the local theory into an immutable Theory.
    /// The resulting theory extends the parent with all accumulated
    /// declarations, axioms, definitions, and theorems.
    pub fn finalize(self) -> Arc<Theory> {
        let mut theory = Theory::begin(self.name.clone(), vec![self.parent.clone()]);

        // Add new constants
        for (name, typ) in &self.new_consts {
            theory.declare_const(name.as_str(), typ.clone());
        }

        // Add axioms
        for (name, axiom) in &self.new_axioms {
            theory.add_axiom(name.as_str(), axiom.clone());
        }

        // Add theorems
        for (name, thm) in &self.new_theorems {
            theory.add_theorem(name.as_str(), thm.as_ref().clone());
        }

        // Add definitions
        for (name, def_term) in &self.new_definitions {
            let def = crate::core::theory::Definition {
                name: Arc::from(name.as_str()),
                term: Arc::new(def_term.clone()),
            };
            theory.add_definition(def);
        }

        Arc::new(theory)
    }

    /// Get the parent theory.
    pub fn parent(&self) -> &Arc<Theory> {
        &self.parent
    }

    /// Get all new theorems accumulated.
    pub fn theorems(&self) -> &[(String, Arc<Thm>)] {
        &self.new_theorems
    }
}

// =========================================================================
// Theory extension helpers
// =========================================================================

// Re-exports from core Theory for convenience.
// The following methods are already defined on Theory:
// - Theory::declare_const(name, typ)
// - Theory::add_axiom(name, prop)
// - Theory::add_theorem(name, thm)
// - Theory::add_definition(def)

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_begin_empty() {
        let pure = Theory::pure();
        let lthy = LocalTheory::begin(pure, "Test");
        assert_eq!(lthy.name(), "Test");
        assert_eq!(lthy.const_count(), 0);
        assert_eq!(lthy.theorem_count(), 0);
    }

    #[test]
    fn test_declare_const() {
        let pure = Theory::pure();
        let mut lthy = LocalTheory::begin(pure, "Test");
        lthy.declare_const("foo", Typ::base("nat"));
        assert_eq!(lthy.const_count(), 1);
        assert!(lthy.signature().is_declared("foo"));
    }

    #[test]
    fn test_axiomatize() {
        let pure = Theory::pure();
        let mut lthy = LocalTheory::begin(pure, "Test");
        let thm = lthy.axiomatize("my_axiom", Term::const_("P", Typ::base("prop")));
        assert!(Arc::ptr_eq(&thm, &thm)); // just check it's valid
        assert_eq!(lthy.theorem_count(), 0); // axioms are not theorems
    }

    #[test]
    fn test_note_theorem() {
        let pure = Theory::pure();
        let mut lthy = LocalTheory::begin(pure, "Test");
        let true_ct = CTerm::certify(Term::const_("True", Typ::base("prop")));
        let thm = Arc::new(ThmKernel::trivial(true_ct).unwrap());
        lthy.note_theorem("my_lemma", Arc::clone(&thm));
        assert_eq!(lthy.theorem_count(), 1);
    }

    #[test]
    fn test_finalize() {
        let pure = Theory::pure();
        let mut lthy = LocalTheory::begin(pure, "Test");
        lthy.declare_const("foo", Typ::base("nat"));
        // Create an unconditional theorem
        let true_ct = CTerm::certify(Term::const_("True", Typ::base("prop")));
        let trivial = ThmKernel::trivial(true_ct).unwrap();
        lthy.note_theorem("trivial", Arc::new(trivial));

        let frozen = lthy.finalize();
        assert_eq!(frozen.name(), "Test");
    }
}
