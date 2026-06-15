//! HOL built-in theorems — foundational rules for proof search.
//!
//! These theorems are axiomatized (not proved from primitives) for now.
//! In a complete system, they would be proved from the HOL definitions.

use std::sync::Arc;

use crate::core::{
    logic::Pure,
    term::Term,
    thm::{CTerm, Thm, ThmKernel},
    types::Typ,
};
use crate::hol::hologic;

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
        thy.add(
            "conjI",
            &Pure::mk_implies(mk_prop("P"), Pure::mk_implies(mk_prop("Q"), mk_conj("P", "Q"))),
            "intro",
        );

        // conjE1: P & Q ==> P
        thy.add("conjE1", &Pure::mk_implies(mk_conj("P", "Q"), mk_prop("P")), "elim");

        // conjE2: P & Q ==> Q
        thy.add("conjE2", &Pure::mk_implies(mk_conj("P", "Q"), mk_prop("Q")), "elim");

        // disjI1: P ==> P | Q
        thy.add("disjI1", &Pure::mk_implies(mk_prop("P"), mk_disj("P", "Q")), "intro");

        // disjI2: Q ==> P | Q
        thy.add("disjI2", &Pure::mk_implies(mk_prop("Q"), mk_disj("P", "Q")), "intro");

        // mp: (P --> Q) ==> P ==> Q
        thy.add(
            "mp",
            &Pure::mk_implies(mk_imp("P", "Q"), Pure::mk_implies(mk_prop("P"), mk_prop("Q"))),
            "elim",
        );

        // impI: (P ==> Q) ==> P --> Q
        thy.add(
            "impI",
            &Pure::mk_implies(Pure::mk_implies(mk_prop("P"), mk_prop("Q")), mk_imp("P", "Q")),
            "intro",
        );

        // ── Quantifiers ──

        // allI: (!!x. P(x)) ==> ALL x. P(x)
        thy.add(
            "allI",
            &Pure::mk_implies(Pure::mk_all("x", Typ::dummy(), mk_var_prop("P", 0)), mk_all("P")),
            "intro",
        );

        // allE: ALL x. P(x) ==> P(t)
        thy.add("allE", &Pure::mk_implies(mk_all("P"), mk_prop("P")), "elim");

        // exI: P(t) ==> EX x. P(x)
        thy.add("exI", &Pure::mk_implies(mk_prop("P"), mk_ex("P")), "intro");

        // ── Equality ──

        // refl: t = t
        thy.add(
            "refl",
            &Pure::mk_equals(
                Typ::dummy(),
                Term::free("t", Typ::dummy()),
                Term::free("t", Typ::dummy()),
            ),
            "intro",
        );

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
        self.theorems.iter().filter(|t| t.kind == kind).map(|t| Arc::clone(&t.thm)).collect()
    }
}

// Helper: build a bool-typed constant
fn mk_bool(name: &str) -> Term {
    Term::const_(name, Typ::base("bool"))
}

// Helper: build a prop-typed constant via Trueprop embedding
fn mk_prop(name: &str) -> Term {
    hologic::mk_Trueprop(mk_bool(name))
}

fn mk_var_prop(name: &str, idx: usize) -> Term {
    Term::var(name, idx, Typ::base("prop"))
}

// All mk_* now delegate to hologic.rs (bool-level construction, Trueprop-lifted to prop)
fn mk_conj(a: &str, b: &str) -> Term {
    hologic::mk_Trueprop(hologic::mk_conj(mk_bool(a), mk_bool(b)))
}

fn mk_disj(a: &str, b: &str) -> Term {
    hologic::mk_Trueprop(hologic::mk_disj(mk_bool(a), mk_bool(b)))
}

fn mk_imp(a: &str, b: &str) -> Term {
    // BUGFIX: was using "HOL.imp" which is wrong; hologic::mk_imp uses the correct "HOL.implies"
    hologic::mk_Trueprop(hologic::mk_imp(mk_bool(a), mk_bool(b)))
}

fn mk_all(p: &str) -> Term {
    hologic::mk_Trueprop(hologic::mk_all("x", Typ::dummy(), mk_bool(p)))
}

fn mk_ex(p: &str) -> Term {
    hologic::mk_Trueprop(hologic::mk_exists("x", Typ::dummy(), mk_bool(p)))
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
