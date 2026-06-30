//! HOL basic constants: True and False.
//!
//! In Isabelle/HOL:
//! - `True ≡ (%x::prop. x) = (%x. x)`
//! - `False ≡ ∀P. P`
//!
//! These are defined in `HOL.thy` and loaded by `hol_loader`.
//!
//! ## Trust status (T1)
//!
//! `true_intr` is **genuine** (proved by `ThmKernel::reflexive`). `eq_true_elim`,
//! `eq_true_intr`, and `false_elim` are **unsound stubs** that construct the
//! conclusion's shape without deriving it; they route through
//! `ThmKernel::admit` (oracle tag `"hol_consts:STUB"`) so the result is not
//! `is_fully_proved()`, and are `pub(crate)` so they cannot leak.

use crate::core::{
    term::Term,
    thm::{CTerm, Thm, ThmKernel},
    types::Typ,
};

/// Oracle tag for the unsound stubs below (see module docs).
const STUB_ORACLE: &str = "hol_consts:STUB";

/// Truth introduction: `⊢ True`
///
/// From the definition of True, this is equivalent to proving
/// `(%x. x) = (%x. x)` which holds by reflexivity. **Genuine.**
pub fn true_intr() -> Thm {
    // True ≡ (%x::prop. x) = (%x. x)
    // By reflexive: (%x. x) = (%x. x)
    let id_lam = Term::abs("x", Typ::base("prop"), Term::bound(0));
    let ct = CTerm::certify(id_lam);
    ThmKernel::reflexive_compat(ct)
}

/// Truth elimination: `P == True ⟹ P`
///
/// Stub: admitted, not derived (see module docs).
pub(crate) fn eq_true_elim(thm: &Thm) -> Option<Thm> {
    use crate::core::logic::Pure;
    let (p, tru) = Pure::dest_equals(thm.prop().term())?;
    // Check that the RHS is True
    // This is simplified — full impl would check the definition
    let _ = tru;
    let p_ct = CTerm::certify(p.clone());
    Some(ThmKernel::admit(p_ct, STUB_ORACLE))
}

/// Convert P to `P == True`. Stub: admitted, not derived (see module docs).
pub(crate) fn eq_true_intr(thm: &Thm) -> Thm {
    use crate::core::logic::Pure;
    let p = thm.prop().term().clone();
    let tru = Term::const_("True", Typ::base("prop"));
    let eq = Pure::mk_equals(Typ::base("prop"), p, tru);
    let ct = CTerm::certify(eq);
    ThmKernel::admit(ct, STUB_ORACLE) // full impl uses trivial + combination
}

/// False elimination: `False ⟹ P` (ex falso quodlibet).
///
/// Stub: admitted, not derived (see module docs).
pub(crate) fn false_elim(_thm_false: &Thm, goal: CTerm) -> Thm {
    // False ≡ ∀P. P; full impl instantiates ∀P.P with the goal.
    ThmKernel::admit(goal, STUB_ORACLE)
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_true_intr() {
        let thm = true_intr();
        assert!(thm.is_unconditional());
    }

    #[test]
    fn test_false_elim() {
        let p = CTerm::certify(Term::const_("P", Typ::base("prop")));
        let false_thm =
            ThmKernel::assume_compat(CTerm::certify(Term::const_("False", Typ::base("prop"))));
        let result = false_elim(&false_thm, p);
        assert_eq!(result.prop().term(), &Term::const_("P", Typ::base("prop")));
    }

    #[test]
    fn test_stubs_are_admitted_not_proved() {
        // T1 invariant: the unsound stubs must never produce a fully-proved
        // theorem — their output must carry the "hol_consts:STUB" oracle so
        // any reliance on them is visible in the trust footprint.
        let p = CTerm::certify(Term::const_("P", Typ::base("prop")));
        let goal = false_elim(&true_intr(), p.clone());
        assert!(!goal.is_fully_proved(), "false_elim must be admitted, not proved");
        assert_eq!(&*goal.oracles()[0], STUB_ORACLE);

        let p_thm = ThmKernel::assume_compat(p);
        let eqt = eq_true_intr(&p_thm);
        assert!(!eqt.is_fully_proved(), "eq_true_intr must be admitted, not proved");

        // true_intr, by contrast, IS a genuine proof (reflexivity).
        assert!(true_intr().is_fully_proved(), "true_intr must be a genuine proof");
    }
}
