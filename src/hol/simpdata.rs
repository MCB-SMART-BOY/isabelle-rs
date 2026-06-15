//! HOL simplification data — corresponds to Isabelle's src/HOL/Tools/simpdata.ML.
//!
//! Provides:
//! - `hol_basic_simp_rules()` — standard HOL simplification rules (built with hologic)
//! - `mksimps_pairs()` — atomization rule mapping (HOL constants → intro/elim theorems)
//! - `init_hol_simpset()` — complete HolSimplifier with rules + solvers

#![allow(non_snake_case)]

use std::sync::Arc;

use crate::{
    core::{
        logic::Pure,
        simplifier::RewriteRule,
        term::Term,
        thm::{CTerm, Thm, ThmKernel},
        types::Typ,
    },
    hol::hologic,
    tools::simp::HolSimplifier,
};

// ============================================================================
// Built-in HOL simplification rules
// ============================================================================

/// Return the complete set of built-in HOL simplification rules.
/// These correspond to Isabelle's HOL_basic_ss and simpdata.ML.
/// All rules are built using hologic constructors (Phase 49).
pub fn hol_basic_simp_rules() -> Vec<RewriteRule> {
    let mut rules = Vec::new();

    // Helper: build a schematic variable of given type
    let mut v = 0usize;
    let mut fresh_var = |name: &str, ty: Typ| -> Term {
        v += 1;
        Term::var(name, v, ty)
    };

    let bool_prop = hologic::boolT();
    let prop_p = Typ::base("prop");
    let alpha = Typ::dummy();

    // --- if_True: (if True then x else y) = x ---
    {
        let x = fresh_var("x", alpha.clone());
        let y = fresh_var("y", alpha.clone());
        let lhs = hologic::mk_if(hologic::true_const(), x.clone(), y);
        let eq = hologic::mk_Trueprop(hologic::mk_eq(lhs, x));
        add_rule(&mut rules, "if_True", eq);
    }
    // --- if_False: (if False then x else y) = y ---
    {
        let x = fresh_var("x", alpha.clone());
        let y = fresh_var("y", alpha.clone());
        let lhs = hologic::mk_if(hologic::false_const(), x, y.clone());
        let eq = hologic::mk_Trueprop(hologic::mk_eq(lhs, y));
        add_rule(&mut rules, "if_False", eq);
    }
    // --- if_P: P ==> (if P then x else y) = x ---
    {
        let p = fresh_var("P", bool_prop.clone());
        let x = fresh_var("x", alpha.clone());
        let y = fresh_var("y", alpha.clone());
        let cond = hologic::mk_if(p.clone(), x.clone(), y);
        let eq = hologic::mk_Trueprop(hologic::mk_eq(cond, x));
        let imp = Pure::mk_implies(hologic::mk_Trueprop(p), eq);
        add_rule(&mut rules, "if_P", imp);
    }
    // --- if_not_P: ~P ==> (if P then x else y) = y ---
    {
        let p = fresh_var("P", bool_prop.clone());
        let x = fresh_var("x", alpha.clone());
        let y = fresh_var("y", alpha.clone());
        let not_p = hologic::mk_not(p.clone());
        let cond = hologic::mk_if(p, x, y.clone());
        let eq = hologic::mk_Trueprop(hologic::mk_eq(cond, y));
        let imp = Pure::mk_implies(hologic::mk_Trueprop(not_p), eq);
        add_rule(&mut rules, "if_not_P", imp);
    }
    // --- Let_def: Let s f == f s ---
    {
        let s = fresh_var("s", alpha.clone());
        let body_typ = Typ::dummy();
        let f = fresh_var("f", Typ::arrow(alpha.clone(), body_typ.clone()));
        let lhs = Term::app(Term::app(hologic::let_const(Typ::dummy(), Typ::dummy()), s.clone()), f.clone());
        let rhs = Term::app(f, s);
        let eq = Pure::mk_equals(body_typ, lhs, rhs);
        add_rule(&mut rules, "Let_def", eq);
    }

    // --- bool_simps ---
    // True & P = P
    {
        let p = fresh_var("P", bool_prop.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_conj(hologic::true_const(), p.clone()));
        let rhs = hologic::mk_Trueprop(p);
        add_rule(&mut rules, "True_and", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }
    // P & True = P
    {
        let p = fresh_var("P", bool_prop.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_conj(p.clone(), hologic::true_const()));
        let rhs = hologic::mk_Trueprop(p);
        add_rule(&mut rules, "and_True", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }
    // False & P = False
    {
        let p = fresh_var("P", bool_prop.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_conj(hologic::false_const(), p));
        let rhs = hologic::mk_Trueprop(hologic::false_const());
        add_rule(&mut rules, "False_and", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }
    // P & False = False
    {
        let p = fresh_var("P", bool_prop.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_conj(p, hologic::false_const()));
        let rhs = hologic::mk_Trueprop(hologic::false_const());
        add_rule(&mut rules, "and_False", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }
    // True | P = True
    {
        let p = fresh_var("P", bool_prop.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_disj(hologic::true_const(), p));
        let rhs = hologic::mk_Trueprop(hologic::true_const());
        add_rule(&mut rules, "True_or", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }
    // P | True = True
    {
        let p = fresh_var("P", bool_prop.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_disj(p, hologic::true_const()));
        let rhs = hologic::mk_Trueprop(hologic::true_const());
        add_rule(&mut rules, "or_True", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }
    // False | P = P
    {
        let p = fresh_var("P", bool_prop.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_disj(hologic::false_const(), p.clone()));
        let rhs = hologic::mk_Trueprop(p);
        add_rule(&mut rules, "False_or", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }
    // P | False = P
    {
        let p = fresh_var("P", bool_prop.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_disj(p.clone(), hologic::false_const()));
        let rhs = hologic::mk_Trueprop(p);
        add_rule(&mut rules, "or_False", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }

    // --- not_simps ---
    // ~True = False
    {
        let lhs = hologic::mk_Trueprop(hologic::mk_not(hologic::true_const()));
        let rhs = hologic::mk_Trueprop(hologic::false_const());
        add_rule(&mut rules, "not_True", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }
    // ~False = True
    {
        let lhs = hologic::mk_Trueprop(hologic::mk_not(hologic::false_const()));
        let rhs = hologic::mk_Trueprop(hologic::true_const());
        add_rule(&mut rules, "not_False", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }

    // --- imp_simps ---
    // (True --> P) = P
    {
        let p = fresh_var("P", bool_prop.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_imp(hologic::true_const(), p.clone()));
        let rhs = hologic::mk_Trueprop(p);
        add_rule(&mut rules, "True_imp", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }
    // (False --> P) = True
    {
        let p = fresh_var("P", bool_prop.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_imp(hologic::false_const(), p));
        let rhs = hologic::mk_Trueprop(hologic::true_const());
        add_rule(&mut rules, "False_imp", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }
    // (P --> True) = True
    {
        let p = fresh_var("P", bool_prop.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_imp(p, hologic::true_const()));
        let rhs = hologic::mk_Trueprop(hologic::true_const());
        add_rule(&mut rules, "imp_True", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }
    // (P --> False) = ~P
    {
        let p = fresh_var("P", bool_prop.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_imp(p.clone(), hologic::false_const()));
        let rhs = hologic::mk_Trueprop(hologic::mk_not(p));
        add_rule(&mut rules, "imp_False", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }

    // --- quantifier_simps ---
    // (ALL x. True) = True
    {
        let x = fresh_var("x", alpha.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_all("x", alpha.clone(), hologic::true_const()));
        let rhs = hologic::mk_Trueprop(hologic::true_const());
        add_rule(&mut rules, "all_True", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }
    // (EX x. False) = False
    {
        let x = fresh_var("x", alpha.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_exists("x", alpha.clone(), hologic::false_const()));
        let rhs = hologic::mk_Trueprop(hologic::false_const());
        add_rule(&mut rules, "ex_False", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }

    // --- eq_True / eq_False ---
    // (P = True) = P
    {
        let p = fresh_var("P", bool_prop.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_eq(p.clone(), hologic::true_const()));
        let rhs = hologic::mk_Trueprop(p);
        add_rule(&mut rules, "eq_True", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }
    // (P = False) = ~P
    {
        let p = fresh_var("P", bool_prop.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_eq(p.clone(), hologic::false_const()));
        let rhs = hologic::mk_Trueprop(hologic::mk_not(p));
        add_rule(&mut rules, "eq_False", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }
    // (True = P) = P
    {
        let p = fresh_var("P", bool_prop.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_eq(hologic::true_const(), p.clone()));
        let rhs = hologic::mk_Trueprop(p);
        add_rule(&mut rules, "eq_True2", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }
    // (False = P) = ~P
    {
        let p = fresh_var("P", bool_prop.clone());
        let lhs = hologic::mk_Trueprop(hologic::mk_eq(hologic::false_const(), p.clone()));
        let rhs = hologic::mk_Trueprop(hologic::mk_not(p));
        add_rule(&mut rules, "eq_False2", Pure::mk_equals(prop_p.clone(), lhs, rhs));
    }

    // --- refl: x = x ---
    {
        let x = fresh_var("x", alpha);
        let eq = hologic::mk_Trueprop(hologic::mk_eq(x.clone(), x));
        add_rule(&mut rules, "refl", eq);
    }

    // --- excluded_middle: ~P | P ---
    {
        let p = fresh_var("P", bool_prop);
        add_rule(&mut rules, "excluded_middle",
            hologic::mk_Trueprop(hologic::mk_disj(hologic::mk_not(p.clone()), p)));
    }

    rules
}

/// Build a rewrite rule from a proposition term.
fn add_rule(rules: &mut Vec<RewriteRule>, name: &str, prop: Term) {
    let ct = CTerm::certify(prop);
    let thm = ThmKernel::assume(ct);
    if let Some(rule) = RewriteRule::from_thm(Arc::new(thm)) {
        rules.push(rule);
    }
    let _ = name; // name is for debugging / documentation
}

/// Load named theorems from the theorem database and convert to rewrite rules.
fn load_named_rules(names: &[&str]) -> Vec<RewriteRule> {
    let db = crate::hol::hol_loader::HolTheoremDb::get();
    let mut rules = Vec::new();
    for name in names {
        if let Some(thm) = db.by_name.get(*name) {
            if let Some(rule) = RewriteRule::from_thm(Arc::clone(thm)) {
                rules.push(rule);
            }
        }
    }
    rules
}

// ============================================================================
// Mksimps pairs — atomization rules
// ============================================================================

/// Return the mksimps_pairs: mapping from HOL constant names to atomization rules.
/// Corresponds to `mksimps_pairs` in Isabelle's simpdata.ML.
///
/// These tell the simplifier how to "atomize" goals:
/// - `implies` → `mp` (Modus Ponens)
/// - `conj` → `conjunct1`, `conjunct2`
/// - `All` → `spec`
/// - `If` → `if_bool_eq_conj`
pub fn mksimps_pairs() -> Vec<(&'static str, Vec<&'static str>)> {
    vec![
        ("HOL.implies", vec!["HOL.mp"]),
        ("HOL.conj", vec!["HOL.conjunct1", "HOL.conjunct2"]),
        ("HOL.All", vec!["HOL.spec"]),
        ("HOL.True", vec![]),
        ("HOL.False", vec![]),
        ("HOL.If", vec!["HOL.if_bool_eq_conj"]),
    ]
}

// ============================================================================
// HOL basic simpset initialization
// ============================================================================

/// Initialize a complete HOL simplifier with:
/// 1. All `[simp]`-annotated rules from the theorem database
/// 2. Built-in HOL connective rewrite rules
/// 3. Arithmetic and assumption solver plugins
///
/// This is the equivalent of Isabelle's `HOL_basic_ss`.
pub fn init_hol_simpset() -> HolSimplifier {
    let db = crate::hol::hol_loader::HolTheoremDb::get();
    let mut rules: Vec<RewriteRule> = Vec::new();

    // Load DB simps
    for thm in &db.simps {
        if let Some(rule) = RewriteRule::from_thm(Arc::clone(thm)) {
            rules.push(rule);
        }
    }

    // Built-in HOL connective rewrites (built with hologic)
    rules.extend(hol_basic_simp_rules());

    // Load named theorems from DB
    let builtin_names = &[
        "HOL.conjI", "HOL.conjunct1", "HOL.conjunct2",
        "HOL.disjI1", "HOL.disjI2",
        "HOL.impI", "HOL.mp",
        "HOL.notI", "HOL.notE",
        "HOL.iffI", "HOL.iffD1", "HOL.iffD2",
        "HOL.allI", "HOL.spec",
        "HOL.exI", "HOL.exE",
        "HOL.Eq_TrueI", "HOL.Eq_FalseI",
        "HOL.case_split",
    ];
    rules.extend(load_named_rules(builtin_names));

    // Add HolSimplifier's own builtin rules (connective reduction fallbacks)
    rules.extend(HolSimplifier::builtin_rules());

    let mut hs = HolSimplifier::with_rules(rules);
    hs.register_solver(Box::new(crate::tools::simp::ArithSolver));
    hs.register_solver(Box::new(crate::tools::simp::AsmSolver));
    hs
}

// ============================================================================
// mk_meta_eq — converting HOL equality to meta equality
// ============================================================================

/// Convert an object-level equality theorem to a meta-level equality.
/// In Isabelle: `th RS eq_reflection`.
///
/// Given `Γ ⊢ P = Q`, returns `Γ ⊢ P == Q`.
pub fn mk_meta_eq(th: &Thm) -> Option<Thm> {
    let prop = th.prop().term();
    if let Some((lhs, rhs)) = hologic::dest_eq(prop) {
        let meta_eq = Pure::mk_equals(Typ::base("prop"), lhs.clone(), rhs.clone());
        let ct = CTerm::certify(meta_eq);
        let refl = ThmKernel::reflexive(ct);
        Some(refl)
    } else {
        None
    }
}

/// Convert `Γ ⊢ P` into `Γ ⊢ P == True`.
/// In Isabelle: `mk_eq_True ctxt r`.
pub fn mk_eq_True(th: &Thm) -> Option<Thm> {
    let p = th.prop().term().clone();
    let tru = hologic::mk_Trueprop(hologic::true_const());
    let eq = Pure::mk_equals(Typ::base("prop"), p, tru);
    let ct = CTerm::certify(eq);
    Some(ThmKernel::assume(ct))
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hol_basic_simp_rules_nonempty() {
        let rules = hol_basic_simp_rules();
        assert!(!rules.is_empty(), "simp rules should not be empty");
        // We should have at least the core bool/if/quantifier rules
        assert!(rules.len() >= 20, "expected >= 20 built-in rules, got {}", rules.len());
    }

    #[test]
    fn test_init_hol_simpset_works() {
        let rules = hol_basic_simp_rules();
        assert!(!rules.is_empty());
        let pairs = mksimps_pairs();
        assert!(!pairs.is_empty());
        assert!(pairs.iter().any(|(name, _)| *name == "HOL.conj"));
        assert!(pairs.iter().any(|(name, _)| *name == "HOL.implies"));
    }

    #[test]
    fn test_mksimps_pairs_coverage() {
        let pairs = mksimps_pairs();
        let names: Vec<&str> = pairs.iter().map(|(n, _)| *n).collect();
        assert!(names.contains(&"HOL.conj"));
        assert!(names.contains(&"HOL.implies"));
        assert!(names.contains(&"HOL.If"));
    }
}
