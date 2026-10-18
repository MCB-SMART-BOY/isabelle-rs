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

use crate::core::{
    sign::{Signature, TypeDeclarationError},
    term::Term,
    theory::{Definition, Theory, TheoryMergeError},
    thm::{CTerm, Thm, ThmKernel},
    types::Typ,
};

// =========================================================================
// LocalTheory
// =========================================================================

/// Incrementally built theory state.
#[derive(Clone)]
pub struct LocalTheory {
    /// Private staged theory; no parent or registry is mutated before publication.
    theory: Theory,
    /// Number of declarations issued in this transaction.
    new_const_count: usize,
    /// Accumulated new theorems (lemmas that have been proved).
    new_theorems: Vec<(String, Arc<Thm>)>,
}

impl LocalTheory {
    /// Begin a private transaction over all validated, canonicalized parents.
    pub fn begin(parents: Vec<Arc<Theory>>, name: &str) -> Result<Self, TheoryMergeError> {
        Ok(LocalTheory {
            theory: Theory::begin(name, parents)?,
            new_const_count: 0,
            new_theorems: Vec::new(),
        })
    }

    /// The theory name.
    pub fn name(&self) -> &str {
        self.theory.name()
    }

    /// The current signature.
    pub fn signature(&self) -> &Signature {
        self.theory.signature()
    }

    /// Number of new constants declared so far.
    pub fn const_count(&self) -> usize {
        self.new_const_count
    }

    /// Number of new theorems so far.
    pub fn theorem_count(&self) -> usize {
        self.new_theorems.len()
    }

    // ── Declaration commands ──

    /// `typedecl name` — declare a new type constructor.
    pub fn declare_type(&mut self, name: &str, arity: usize) -> Result<(), TypeDeclarationError> {
        self.theory.declare_type(name, arity)
    }

    /// `consts name :: typ` — declare a new constant.
    pub fn declare_const(&mut self, name: &str, typ: Typ) {
        self.theory.declare_const(name, typ);
        self.new_const_count += 1;
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
                Term::const_(
                    "Pure.eq",
                    Typ::arrows(vec![typ.clone(), typ.clone()], Typ::base("prop")),
                ),
                Term::const_(name, typ.clone()),
            ),
            rhs,
        );
        self.theory
            .add_definition(Definition { name: Arc::from(name), term: Arc::new(eq.clone()) });
        self.theory.add_axiom(format!("{name}_def"), eq.clone());
        // Return the definition as a theorem
        let ct = CTerm::certify(eq);
        let thm = ThmKernel::assume_compat(ct);
        Arc::new(thm)
    }

    /// `axiomatization where name: "prop"` — add an axiom.
    /// Returns the axiom as a theorem.
    pub fn axiomatize(&mut self, name: &str, prop: Term) -> Arc<Thm> {
        self.theory.add_axiom(name, prop.clone());
        let ct = CTerm::certify(prop);
        let thm = ThmKernel::assume_compat(ct);
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
                let full_name = if i == 0 { name.clone() } else { format!("{name}_{i}") };
                self.new_theorems.push((full_name, thm));
            }
        }
    }

    // ── Finalization ──

    /// Publish the private transaction after all source commands have succeeded.
    /// Declarations were already checked in the staged signature, preserving their origins.
    pub fn finalize(mut self) -> Arc<Theory> {
        for (name, thm) in self.new_theorems {
            self.theory.add_theorem(name, thm.as_ref().clone());
        }
        Arc::new(self.theory)
    }

    /// Get the canonical imported theories in source order.
    pub fn parents(&self) -> &[Arc<Theory>] {
        self.theory.parents()
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
        let lthy = LocalTheory::begin(vec![pure], "Test").unwrap();
        assert_eq!(lthy.name(), "Test");
        assert_eq!(lthy.const_count(), 0);
        assert_eq!(lthy.theorem_count(), 0);
    }

    #[test]
    fn test_declare_const() {
        let pure = Theory::pure();
        let mut lthy = LocalTheory::begin(vec![pure], "Test").unwrap();
        lthy.declare_const("foo", Typ::base("nat"));
        assert_eq!(lthy.const_count(), 1);
        assert!(lthy.signature().is_declared("foo"));
    }

    #[test]
    fn test_axiomatize() {
        let pure = Theory::pure();
        let mut lthy = LocalTheory::begin(vec![pure], "Test").unwrap();
        let thm = lthy.axiomatize("my_axiom", Term::const_("P", Typ::base("prop")));
        assert!(!thm.is_strict_closed_proved());
        assert_eq!(lthy.theorem_count(), 0); // axioms are not theorems
    }

    #[test]
    fn test_note_theorem() {
        let pure = Theory::pure();
        let mut lthy = LocalTheory::begin(vec![pure], "Test").unwrap();
        let prop = Term::const_("P", Typ::base("prop"));
        let mut environment = crate::core::types::TypeEnv::new();
        environment.declare_const("P", Typ::base("prop"));
        let checked = CTerm::certify_checked(prop, &environment).unwrap();
        let thm = Arc::new(ThmKernel::trivial(checked).unwrap());
        lthy.note_theorem("my_lemma", Arc::clone(&thm));
        assert_eq!(lthy.theorem_count(), 1);
    }

    #[test]
    fn test_finalize() {
        let pure = Theory::pure();
        let mut lthy = LocalTheory::begin(vec![pure], "Test").unwrap();
        let nat = Typ::base("nat");
        lthy.declare_const("foo", nat.clone());
        let mut env = crate::core::types::TypeEnv::new();
        env.declare_const("foo", nat.clone());
        let foo = CTerm::certify_checked(Term::const_("foo", nat), &env).unwrap();
        let refl = ThmKernel::reflexive(foo).unwrap();
        lthy.note_theorem("foo_refl", Arc::new(refl));

        let frozen = lthy.finalize();
        assert_eq!(frozen.name(), "Test");
        assert!(frozen.lookup_theorem("foo_refl").is_some());
    }
}
