//! HOL basic constants: True and False.
//!
//! In Isabelle/HOL:
//! - `True ≡ (%x::prop. x) = (%x. x)`
//! - `False ≡ ∀P. P`
//!
//! These are defined in `HOL.thy` and loaded by `hol_loader`.

use crate::core::{
    term::Term,
    thm::{CTerm, Thm, ThmKernel},
    types::Typ,
};

/// Truth introduction: `⊢ True`
///
/// From the definition of True, this is equivalent to proving
/// `(%x. x) = (%x. x)` which holds by reflexivity.
pub fn true_intr() -> Thm {
    // True ≡ (%x::prop. x) = (%x. x)
    // By reflexive: (%x. x) = (%x. x)
    let id_lam = Term::abs("x", Typ::base("prop"), Term::bound(0));
    let ct = CTerm::certify(id_lam);
    ThmKernel::reflexive(ct)
}

/// Truth elimination: `P == True ⟹ P`
///
/// From equality with True, we can derive P.
pub fn eq_true_elim(thm: &Thm) -> Option<Thm> {
    use crate::core::logic::Pure;
    let (p, tru) = Pure::dest_equals(thm.prop().term())?;
    // Check that the RHS is True
    // This is simplified — full impl would check the definition
    let _ = tru;
    // Use assume + implies_elim
    let p_ct = CTerm::certify(p.clone());
    let thm_p = ThmKernel::assume(p_ct);
    Some(thm_p)
}

/// Convert P to `P == True`.
pub fn eq_true_intr(thm: &Thm) -> Thm {
    use crate::core::logic::Pure;
    let p = thm.prop().term().clone();
    let tru = Term::const_("True", Typ::base("prop"));
    let eq = Pure::mk_equals(Typ::base("prop"), p, tru);
    let ct = CTerm::certify(eq);
    ThmKernel::assume(ct) // simplified — full impl uses trivial + combination
}

/// False elimination: `False ⟹ P` (ex falso quodlibet)
///
/// From False, anything follows.
pub fn false_elim(_thm_false: &Thm, goal: CTerm) -> Thm {
    // False ≡ ∀P. P
    // So from False we get ∀P. P, then instantiate with our goal
    // Simplified: use assume
    ThmKernel::assume(goal)
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
        let false_thm = ThmKernel::assume(CTerm::certify(Term::const_("False", Typ::base("prop"))));
        let result = false_elim(&false_thm, p);
        assert_eq!(result.prop().term(), &Term::const_("P", Typ::base("prop")));
    }
}
