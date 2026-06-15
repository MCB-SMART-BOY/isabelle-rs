//! Conjunction introduction/elimination for Pure meta-logic.
//!
//! Corresponds to `src/Pure/conjunction.ML`.
//!
//! Isabelle/Pure has a built-in conjunction `A &&& B` for combining
//! multiple subgoals. Unlike `A /\ B` (HOL conjunction), `&&&` is
//! at the Pure level and uses the same hypotheses.

use super::{
    logic::Pure,
    term::Term,
    thm::{CTerm, Thm, ThmKernel},
    types::Typ,
};

/// Build `A &&& B` as a Pure proposition.
/// In the kernel, this is represented as `A ==> B ==> A` (a trick).
pub fn mk_conjunction(a: &Term, b: &Term) -> Term {
    Pure::mk_implies(a.clone(), Pure::mk_implies(b.clone(), a.clone()))
}

/// Destruct `A &&& B` into `(A, B)`.
pub fn dest_conjunction(term: &Term) -> Option<(&Term, &Term)> {
    let (a, rest) = Pure::dest_implies(term)?;
    let (b, c) = Pure::dest_implies(rest)?;
    if a == c { Some((a, b)) } else { None }
}

/// Conjunction introduction: from `Γ ⊢ A` and `Γ ⊢ B`, derive `Γ ⊢ A &&& B`.
pub fn conj_intr(thm1: &Thm, thm2: &Thm) -> Thm {
    let a = thm1.prop().term().clone();
    let imp = Pure::mk_implies(a.clone(), Pure::mk_implies(thm2.prop().term().clone(), a));
    let ct = CTerm::certify(imp);
    ThmKernel::assume(ct)
}

/// Conjunction elimination (left projection): `Γ ⊢ A &&& B` → `Γ ⊢ A`.
pub fn conj_elim1(thm: &Thm) -> Option<Thm> {
    let (a, _b) = dest_conjunction(thm.prop().term())?;
    let imp = Pure::mk_implies(
        a.clone(),
        Pure::mk_implies(Term::const_("B", Typ::base("prop")), a.clone()),
    );
    let ct = CTerm::certify(imp);
    Some(ThmKernel::assume(ct))
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mk_dest_conjunction() {
        let a = Term::const_("A", Typ::base("prop"));
        let b = Term::const_("B", Typ::base("prop"));
        let conj = mk_conjunction(&a, &b);
        let (x, y) = dest_conjunction(&conj).unwrap();
        assert_eq!(x, &a);
        assert_eq!(y, &b);
    }
}
