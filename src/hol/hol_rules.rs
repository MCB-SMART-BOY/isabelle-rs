//! HOL inference rules for connectives and quantifiers.
//!
//! These rules operate at the HOL (object logic) level, built on
//! top of Pure's meta-logic (!!, ==>, ==).
//!
//! ## Trust status (T1)
//!
//! `mp`, `all_intr`, `all_elim` are **genuine** — they delegate to the LCF
//! kernel (`ThmKernel`). Every other rule here is an **unsound stub**: it
//! constructs the *shape* of the conclusion but does not actually derive it
//! from its premises. To keep the kernel honest (it must be impossible to
//! forge a "proved" theorem), these stubs route through `ThmKernel::admit`
//! with the oracle tag `"hol_rules:STUB"`. Any theorem produced by them is
//! therefore **not** `is_fully_proved()`, and that taint propagates. They are
//! `pub(crate)` so they cannot leak outside this crate, and exist only as
//! placeholders pending real HOL-level derivations.
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

use crate::core::{
    error::KernelError,
    logic::Pure,
    term::Term,
    thm::{CTerm, Thm, ThmKernel},
    types::Typ,
};
use crate::hol::hologic;

/// Oracle tag for the unsound connective stubs below. A theorem carrying this
/// tag was NOT derived from its premises — it was admitted (see module docs).
const STUB_ORACLE: &str = "hol_rules:STUB";

// =========================================================================
// Conjunction (∧)
// =========================================================================

pub(crate) fn conj_intr(thm_p: &Thm, thm_q: &Thm) -> Thm {
    let p = thm_p.prop().term().clone();
    let q = thm_q.prop().term().clone();
    let conj = hologic::mk_Trueprop(hologic::mk_conj(p, q));
    ThmKernel::admit(CTerm::certify(conj), STUB_ORACLE)
}

pub(crate) fn conj_elim1(thm_conj: &Thm) -> Thm {
    let p = extract_left(thm_conj.prop().term());
    ThmKernel::admit(CTerm::certify(p.clone()), STUB_ORACLE)
}

pub(crate) fn conj_elim2(thm_conj: &Thm) -> Thm {
    let q = extract_right(thm_conj.prop().term());
    ThmKernel::admit(CTerm::certify(q.clone()), STUB_ORACLE)
}

fn extract_left(term: &Term) -> &Term {
    match term {
        Term::App { func, .. } => match func.as_ref() {
            Term::App { arg, .. } => arg.as_ref(),
            _ => term,
        },
        _ => term,
    }
}

fn extract_right(term: &Term) -> &Term {
    match term {
        Term::App { arg, .. } => arg.as_ref(),
        _ => term,
    }
}

// =========================================================================
// Disjunction (∨)
// =========================================================================

pub(crate) fn disj_intr1(thm_p: &Thm, q: &Term) -> Thm {
    let p = thm_p.prop().term().clone();
    let disj = hologic::mk_Trueprop(hologic::mk_disj(p, q.clone()));
    ThmKernel::admit(CTerm::certify(disj), STUB_ORACLE)
}

pub(crate) fn disj_intr2(p: &Term, thm_q: &Thm) -> Thm {
    let q = thm_q.prop().term().clone();
    let disj = hologic::mk_Trueprop(hologic::mk_disj(p.clone(), q));
    ThmKernel::admit(CTerm::certify(disj), STUB_ORACLE)
}

pub(crate) fn disj_elim(_thm_disj: &Thm, _thm_pr: &Thm, _thm_qr: &Thm) -> Thm {
    let r = _thm_qr.prop().term().clone();
    ThmKernel::admit(CTerm::certify(r), STUB_ORACLE)
}

// =========================================================================
// Implication (⟶)
// =========================================================================

pub(crate) fn imp_intr(thm_p: &CTerm, thm_q: &Thm) -> Thm {
    let p = thm_p.term().clone();
    let q = thm_q.prop().term().clone();
    let imp = Pure::mk_implies(p, q);
    ThmKernel::admit(CTerm::certify(imp), STUB_ORACLE)
}

/// **Genuine**: delegates to the kernel's `implies_elim` (modus ponens).
pub fn mp(thm_imp: &Thm, thm_p: &Thm) -> Result<Thm, KernelError> {
    ThmKernel::implies_elim(thm_imp, thm_p)
}

// =========================================================================
// Negation (¬)
// =========================================================================

pub(crate) fn not_intr(_thm_pf: &Thm) -> Thm {
    let not_p = hologic::mk_Trueprop(hologic::mk_not(Term::const_("P", Typ::base("bool"))));
    ThmKernel::admit(CTerm::certify(not_p), STUB_ORACLE)
}

pub(crate) fn not_elim(_thm_not_p: &Thm, _thm_p: &Thm, goal: CTerm) -> Thm {
    ThmKernel::admit(goal, STUB_ORACLE)
}

// =========================================================================
// Universal quantifier (∀)
// =========================================================================

/// **Genuine**: delegates to the kernel's `forall_intr`.
pub fn all_intr(x_name: &str, x_typ: Typ, thm: &Thm) -> Result<Thm, KernelError> {
    ThmKernel::forall_intr(x_name, x_typ, thm)
}

/// **Genuine**: delegates to the kernel's `forall_elim`.
pub fn all_elim(ct: CTerm, thm: &Thm) -> Result<Thm, KernelError> {
    ThmKernel::forall_elim(ct, thm)
}

// =========================================================================
// Existential quantifier (∃)
// =========================================================================

pub(crate) fn ex_intr(_x_name: &str, _thm_pt: &Thm) -> Thm {
    let ex = hologic::mk_Trueprop(hologic::mk_exists(
        "x",
        Typ::base("nat"),
        Term::const_("P", Typ::base("bool")),
    ));
    ThmKernel::admit(CTerm::certify(ex), STUB_ORACLE)
}

pub(crate) fn ex_elim(_thm_ex: &Thm, _thm_pq: &Thm) -> Thm {
    let q = _thm_pq.prop().term().clone();
    ThmKernel::admit(CTerm::certify(q), STUB_ORACLE)
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
        let p_imp_q = ThmKernel::assume_compat(CTerm::certify(Pure::mk_implies(
            p.term().clone(),
            q.term().clone(),
        )));
        let p_thm = ThmKernel::assume_compat(p.clone());
        let result = mp(&p_imp_q, &p_thm).unwrap();
        assert_eq!(result.prop().term(), q.term());
    }

    #[test]
    fn test_all_elim() {
        let p = prop("P");
        let thm_p = ThmKernel::assume_compat(p);
        let thm_all = all_intr("x", Typ::base("nat"), &thm_p).expect("forall_intr should succeed");
        let t = CTerm::certify(Term::const_("t", Typ::base("nat")));
        let result = all_elim(t, &thm_all).unwrap();
        assert_eq!(result.prop().term(), &Term::const_("P", Typ::base("prop")));
    }

    #[test]
    fn test_conj_intr_elim() {
        let p = prop("P");
        let q = prop("Q");
        let thm_p = ThmKernel::assume_compat(p);
        let thm_q = ThmKernel::assume_compat(q);
        let conj = conj_intr(&thm_p, &thm_q);
        assert!(conj.prop().term().is_app());
        // T1: connective stubs are admitted, NOT genuine proofs — they must
        // carry the oracle tag so their use is exposed in the trust footprint.
        assert!(!conj.is_fully_proved(), "conj_intr stub must be admitted, not proved");
        assert_eq!(&*conj.oracles()[0], STUB_ORACLE);
    }

    #[test]
    fn test_disj_intr() {
        let p = prop("P");
        let thm_p = ThmKernel::assume_compat(p.clone());
        let q = Term::const_("Q", Typ::base("prop"));
        let disj = disj_intr1(&thm_p, &q);
        assert!(disj.prop().term().is_app());
    }

    #[test]
    fn test_all_intr_elim_roundtrip() {
        let p = prop("P");
        let thm_p = ThmKernel::assume_compat(p);
        let thm_all = all_intr("x", Typ::base("nat"), &thm_p).expect("forall_intr should succeed");
        assert!(Pure::dest_all(thm_all.prop().term()).is_some());
    }
}
