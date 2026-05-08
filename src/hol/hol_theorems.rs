//! HOL built-in theorems — foundational rules for proof search.
//!
//! These theorems are axiomatized (not proved from primitives) for now.
//! In a complete system, they would be proved from the HOL definitions.

use std::sync::Arc;
use crate::core::term::Term;
use crate::core::thm::{CTerm, Thm, ThmKernel};
use crate::core::logic::Pure;
use crate::core::types::Typ;

/// A named theorem in the HOL database.
#[derive(Clone)]
pub struct NamedThm {
    pub name: String,
    pub thm: Arc<Thm>,
    /// Kind: "intro", "elim", "simp", "dest"
    pub kind: String,
}

/// The HOL theorem database.
pub struct HolTheory {
    pub theorems: Vec<NamedThm>,
}

impl HolTheory {
    /// Build the standard HOL theory with basic rules.
    pub fn standard() -> Self {
        let mut thy = HolTheory { theorems: Vec::new() };

        // ── Propositional logic ──

        // TrueI: True
        thy.add("TrueI", &mk_prop("True"), "intro");

        // FalseE: False ==> P
        thy.add("FalseE", &Pure::mk_implies(mk_prop("False"), mk_prop("P")), "elim");

        // conjI: P ==> Q ==> P & Q
        thy.add("conjI", &Pure::mk_implies(mk_prop("P"),
            Pure::mk_implies(mk_prop("Q"), mk_conj("P", "Q"))), "intro");

        // conjE1: P & Q ==> P
        thy.add("conjE1", &Pure::mk_implies(mk_conj("P", "Q"), mk_prop("P")), "elim");

        // conjE2: P & Q ==> Q
        thy.add("conjE2", &Pure::mk_implies(mk_conj("P", "Q"), mk_prop("Q")), "elim");

        // disjI1: P ==> P | Q
        thy.add("disjI1", &Pure::mk_implies(mk_prop("P"), mk_disj("P", "Q")), "intro");

        // disjI2: Q ==> P | Q
        thy.add("disjI2", &Pure::mk_implies(mk_prop("Q"), mk_disj("P", "Q")), "intro");

        // mp: (P --> Q) ==> P ==> Q
        thy.add("mp", &Pure::mk_implies(mk_imp("P", "Q"),
            Pure::mk_implies(mk_prop("P"), mk_prop("Q"))), "elim");

        // impI: (P ==> Q) ==> P --> Q
        thy.add("impI", &Pure::mk_implies(
            Pure::mk_implies(mk_prop("P"), mk_prop("Q")),
            mk_imp("P", "Q")), "intro");

        // ── Quantifiers ──

        // allI: (!!x. P(x)) ==> ALL x. P(x)
        thy.add("allI", &Pure::mk_implies(
            Pure::mk_all("x", Typ::dummy(), mk_var_prop("P", 0)),
            mk_all("P")), "intro");

        // allE: ALL x. P(x) ==> P(t)
        thy.add("allE", &Pure::mk_implies(mk_all("P"), mk_prop("P")), "elim");

        // exI: P(t) ==> EX x. P(x)
        thy.add("exI", &Pure::mk_implies(mk_prop("P"), mk_ex("P")), "intro");

        // ── Equality ──

        // refl: t = t
        thy.add("refl", &Pure::mk_equals(Typ::dummy(),
            Term::free("t", Typ::dummy()), Term::free("t", Typ::dummy())), "intro");

        thy
    }

    fn add(&mut self, name: &str, prop: &Term, kind: &str) {
        let thm = ThmKernel::assume(CTerm::certify(prop.clone()));
        self.theorems.push(NamedThm {
            name: name.to_string(),
            thm: Arc::new(thm),
            kind: kind.to_string(),
        });
    }

    /// Look up theorems by kind.
    pub fn by_kind(&self, kind: &str) -> Vec<Arc<Thm>> {
        self.theorems.iter()
            .filter(|t| t.kind == kind)
            .map(|t| Arc::clone(&t.thm))
            .collect()
    }
}

// Helper: build a proposition constant
fn mk_prop(name: &str) -> Term {
    Term::const_(name, Typ::base("prop"))
}

fn mk_var_prop(name: &str, idx: usize) -> Term {
    Term::var(name, idx, Typ::base("prop"))
}

fn mk_conj(a: &str, b: &str) -> Term {
    let prop = Typ::base("prop");
    Term::app(
        Term::app(Term::const_("HOL.conj", Typ::arrow(prop.clone(), Typ::arrow(prop.clone(), prop.clone()))),
            mk_prop(a)),
        mk_prop(b),
    )
}

fn mk_disj(a: &str, b: &str) -> Term {
    let prop = Typ::base("prop");
    Term::app(
        Term::app(Term::const_("HOL.disj", Typ::arrow(prop.clone(), Typ::arrow(prop.clone(), prop.clone()))),
            mk_prop(a)),
        mk_prop(b),
    )
}

fn mk_imp(a: &str, b: &str) -> Term {
    let prop = Typ::base("prop");
    Term::app(
        Term::app(Term::const_("HOL.imp", Typ::arrow(prop.clone(), Typ::arrow(prop.clone(), prop.clone()))),
            mk_prop(a)),
        mk_prop(b),
    )
}

fn mk_all(p: &str) -> Term {
    let prop = Typ::base("prop");
    Term::app(
        Term::const_("HOL.All", Typ::arrow(Typ::arrow(Typ::dummy(), prop.clone()), prop)),
        Term::abs("x", Typ::dummy(), mk_prop(p)),
    )
}

fn mk_ex(p: &str) -> Term {
    let prop = Typ::base("prop");
    Term::app(
        Term::const_("HOL.Ex", Typ::arrow(Typ::arrow(Typ::dummy(), prop.clone()), prop)),
        Term::abs("x", Typ::dummy(), mk_prop(p)),
    )
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_standard_theory() {
        let thy = HolTheory::standard();
        assert!(thy.theorems.len() >= 10);
        let intros = thy.by_kind("intro");
        let elims = thy.by_kind("elim");
        assert!(!intros.is_empty());
        assert!(!elims.is_empty());
    }

    #[test]
    fn test_lookup_by_kind() {
        let thy = HolTheory::standard();
        let elims = thy.by_kind("elim");
        // Should have FalseE, conjE1, conjE2, mp, allE at minimum
        assert!(elims.len() >= 5);
    }
}
