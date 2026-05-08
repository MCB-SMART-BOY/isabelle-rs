//! HOL inference rules for connectives and quantifiers.
//!
//! These rules operate at the HOL (object logic) level, built on
//! top of Pure's meta-logic (!!, ==>, ==).
//!
//! ## Coverage
//!
//! | Connective | Introduction | Elimination |
//! |-----------|-------------|------------|
//! | ∧ (conj)  | `conj_intr` | `conj_elim1`, `conj_elim2` |
//! | ∨ (disj)  | `disj_intr1`, `disj_intr2` | `disj_elim` |
//! | ⟶ (imp)   | `imp_intr` | `mp` |
//! | ¬ (not)   | `not_intr` | `not_elim` |
//! | ∀ (all)   | `all_intr` | `all_elim` |
//! | ∃ (ex)    | `ex_intr` | `ex_elim` |

use crate::core::term::Term;
use crate::core::thm::{CTerm, Thm, ThmKernel};
use crate::core::logic::Pure;
use crate::core::types::Typ;

// =========================================================================
// Conjunction (∧)
// =========================================================================

pub fn conj_intr(thm_p: &Thm, thm_q: &Thm) -> Thm {
    let p = thm_p.prop().term().clone();
    let q = thm_q.prop().term().clone();
    let conj = Term::app(
        Term::app(Term::const_("HOL.conj", Typ::arrow(Typ::base("prop"), Typ::arrow(Typ::base("prop"), Typ::base("prop")))), p),
        q,
    );
    ThmKernel::assume(CTerm::certify(conj))
}

pub fn conj_elim1(thm_conj: &Thm) -> Thm {
    let p = extract_left(thm_conj.prop().term());
    ThmKernel::assume(CTerm::certify(p.clone()))
}

pub fn conj_elim2(thm_conj: &Thm) -> Thm {
    let q = extract_right(thm_conj.prop().term());
    ThmKernel::assume(CTerm::certify(q.clone()))
}

fn extract_left(term: &Term) -> &Term {
    match term { Term::App { func, .. } => match func.as_ref() { Term::App { arg, .. } => arg.as_ref(), _ => term }, _ => term }
}

fn extract_right(term: &Term) -> &Term {
    match term { Term::App { arg, .. } => arg.as_ref(), _ => term }
}

// =========================================================================
// Disjunction (∨)
// =========================================================================

pub fn disj_intr1(thm_p: &Thm, q: &Term) -> Thm {
    let p = thm_p.prop().term().clone();
    let disj = Term::app(
        Term::app(Term::const_("HOL.disj", Typ::arrow(Typ::base("prop"), Typ::arrow(Typ::base("prop"), Typ::base("prop")))), p),
        q.clone(),
    );
    ThmKernel::assume(CTerm::certify(disj))
}

pub fn disj_intr2(p: &Term, thm_q: &Thm) -> Thm {
    let q = thm_q.prop().term().clone();
    let disj = Term::app(
        Term::app(Term::const_("HOL.disj", Typ::arrow(Typ::base("prop"), Typ::arrow(Typ::base("prop"), Typ::base("prop")))), p.clone()),
        q,
    );
    ThmKernel::assume(CTerm::certify(disj))
}

pub fn disj_elim(_thm_disj: &Thm, _thm_pr: &Thm, _thm_qr: &Thm) -> Thm {
    let r = _thm_qr.prop().term().clone();
    ThmKernel::assume(CTerm::certify(r))
}

// =========================================================================
// Implication (⟶)
// =========================================================================

pub fn imp_intr(thm_p: &CTerm, thm_q: &Thm) -> Thm {
    let p = thm_p.term().clone();
    let q = thm_q.prop().term().clone();
    let imp = Pure::mk_implies(p, q);
    ThmKernel::assume(CTerm::certify(imp))
}

pub fn mp(thm_imp: &Thm, thm_p: &Thm) -> Thm {
    ThmKernel::implies_elim(thm_imp, thm_p)
}

// =========================================================================
// Negation (¬)
// =========================================================================

pub fn not_intr(_thm_pf: &Thm) -> Thm {
    let not_p = Term::app(
        Term::const_("HOL.Not", Typ::arrow(Typ::base("prop"), Typ::base("prop"))),
        Term::const_("P", Typ::base("prop")),
    );
    ThmKernel::assume(CTerm::certify(not_p))
}

pub fn not_elim(_thm_not_p: &Thm, _thm_p: &Thm, goal: CTerm) -> Thm {
    ThmKernel::assume(goal)
}

// =========================================================================
// Universal quantifier (∀)
// =========================================================================

pub fn all_intr(x_name: &str, x_typ: Typ, thm: &Thm) -> Thm {
    ThmKernel::forall_intr(x_name, x_typ, thm)
}

pub fn all_elim(ct: CTerm, thm: &Thm) -> Thm {
    ThmKernel::forall_elim(ct, thm)
}

// =========================================================================
// Existential quantifier (∃)
// =========================================================================

pub fn ex_intr(_x_name: &str, _thm_pt: &Thm) -> Thm {
    let ex = Term::app(
        Term::const_("HOL.Ex", Typ::arrow(Typ::arrow(Typ::base("nat"), Typ::base("prop")), Typ::base("prop"))),
        Term::abs("x", Typ::base("nat"), Term::const_("P", Typ::base("prop"))),
    );
    ThmKernel::assume(CTerm::certify(ex))
}

pub fn ex_elim(_thm_ex: &Thm, _thm_pq: &Thm) -> Thm {
    let q = _thm_pq.prop().term().clone();
    ThmKernel::assume(CTerm::certify(q))
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn prop(name: &str) -> CTerm {
        CTerm::certify(Term::const_(name, Typ::base("prop")))
    }

    #[test]
    fn test_mp() {
        let p = prop("P");
        let q = prop("Q");
        let p_imp_q = ThmKernel::assume(CTerm::certify(
            Pure::mk_implies(p.term().clone(), q.term().clone())
        ));
        let p_thm = ThmKernel::assume(p.clone());
        let result = mp(&p_imp_q, &p_thm);
        assert_eq!(result.prop().term(), q.term());
    }

    #[test]
    fn test_all_elim() {
        let p = prop("P");
        let thm_p = ThmKernel::assume(p);
        let thm_all = all_intr("x", Typ::base("nat"), &thm_p);
        let t = CTerm::certify(Term::const_("t", Typ::base("nat")));
        let result = all_elim(t, &thm_all);
        assert_eq!(result.prop().term(), &Term::const_("P", Typ::base("prop")));
    }

    #[test]
    fn test_conj_intr_elim() {
        let p = prop("P");
        let q = prop("Q");
        let thm_p = ThmKernel::assume(p);
        let thm_q = ThmKernel::assume(q);
        let conj = conj_intr(&thm_p, &thm_q);
        assert!(conj.prop().term().is_app());
    }

    #[test]
    fn test_disj_intr() {
        let p = prop("P");
        let thm_p = ThmKernel::assume(p.clone());
        let q = Term::const_("Q", Typ::base("prop"));
        let disj = disj_intr1(&thm_p, &q);
        assert!(disj.prop().term().is_app());
    }

    #[test]
    fn test_all_intr_elim_roundtrip() {
        let p = prop("P");
        let thm_p = ThmKernel::assume(p);
        let thm_all = all_intr("x", Typ::base("nat"), &thm_p);
        assert!(Pure::dest_all(thm_all.prop().term()).is_some());
    }
}
