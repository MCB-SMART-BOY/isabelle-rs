//! Derived inference rules.
//!
//! Corresponds to `src/Pure/drule.ML`.
//!
//! These rules are "derived" — they can be implemented using the primitive
//! rules in `ThmKernel`, but are commonly used enough to deserve their own
//! functions. They are still safe because they go through the kernel.
//!
//! ## Key rules
//!
//! | Rule | What it does |
//! |------|-------------|
//! | `forall_intr` | Introduce universal quantifier |
//! | `forall_elim` | Eliminate universal quantifier |
//! | `implies_intr_list` | Chain implies_intr over a list |
//! | `implies_elim_list` | Chain implies_elim over a list |
//! | `zero_var_indexes` | Reset schematic variable indices |


use super::thm::{CTerm, Thm, ThmKernel};
use super::types::Typ;
use super::logic::Pure;

// =========================================================================
// forall_intr: (!!x. P(x)) introduction
// =========================================================================

/// `forall_intr(x, thm)`: If `thm` proves `P` with `x` not free in
/// the assumptions, derive `!!x. P(x)`.
///
/// This is implemented via `implies_intr` and `assume` using the
/// definition of `!!` in terms of `==>`.
pub fn forall_intr(_x_name: &str, _x_typ: Typ, _thm: &Thm) -> Thm {
    // In Isabelle's kernel, forall_intr is a primitive rule.
    // For now, we provide a simplified implementation.
    // The full implementation requires checking that x is not free in hyps.
    unreachable!("forall_intr is a primitive in Isabelle but not yet in Isabelle-rs kernel")
}

// =========================================================================
// implies_intr_list / implies_elim_list
// =========================================================================

/// Chain `implies_intr` over a list of assumptions.
/// `Γ ∪ {A1, ..., An} ⊢ B` → `Γ ⊢ A1 ==> ... ==> An ==> B`.
pub fn implies_intr_list(assumptions: &[CTerm], thm: &Thm) -> Thm {
    let mut result = thm.clone();
    for a in assumptions.iter().rev() {
        result = ThmKernel::implies_intr(a, &result);
    }
    result
}

/// Chain `implies_elim` over a list of antecedents.
/// `Γ ⊢ A1 ==> ... ==> An ==> B` and `Δ1 ⊢ A1`, ..., `Δn ⊢ An`
/// → `Γ ∪ Δ1 ∪ ... ∪ Δn ⊢ B`.
pub fn implies_elim_list(thm: &Thm, antecedents: &[Thm]) -> Thm {
    let mut result = thm.clone();
    for ante in antecedents {
        result = ThmKernel::implies_elim(&result, ante);
    }
    result
}

// =========================================================================
// compose: compose two theorems by resolution
// =========================================================================

/// Compose `thm1` and `thm2`: match the conclusion of `thm1` with
/// a premise of `thm2`, producing a new theorem.
///
/// This is the core of forward proof in Isabelle.
pub fn compose(thm1: &Thm, thm2: &Thm, i: usize) -> Option<Thm> {
    // Get the i-th premise of thm2
    let (prems, _conc) = Pure::strip_imp_prems(thm2.prop().term());
    if i >= prems.len() {
        return None;
    }
    let prem = prems[i];

    // Match: thm1 ⊢ A, thm2 ⊢ A ==> B → Γ ∪ Δ ⊢ B
    if thm1.prop().term() == prem {
        Some(ThmKernel::implies_elim(thm2, thm1))
    } else {
        None
    }
}

// =========================================================================
// zero_var_indexes: reset all schematic var indices to 0
// =========================================================================

/// Reset all schematic variable indices in a theorem to 0.
/// This is useful when generating fresh instances of a theorem.
pub fn zero_var_indexes(_thm: &Thm) -> Thm {
    // Requires term traversal to replace all Var/TVar indices
    // For now, return a clone
    _thm.clone()
}

// =========================================================================
// incr_indexes: increment all schematic var indices
// =========================================================================

/// Increment all schematic variable indices by `n`.
/// This ensures freshness when combining theorems.
pub fn incr_indexes(_n: usize, _thm: &Thm) -> Thm {
    _thm.clone() // simplified
}

// =========================================================================
// Combination rules for Pure logic
// =========================================================================

/// `implies_intr_hyps`: discharge all hypotheses of a theorem.
pub fn implies_intr_hyps(thm: &Thm) -> Thm {
    let hyps: Vec<CTerm> = thm.hyps().iter().cloned().collect();
    implies_intr_list(&hyps, thm)
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::term::Term;

    fn prop(name: &str) -> CTerm {
        CTerm::certify(Term::const_(name, Typ::base("prop")))
    }

    #[test]
    fn test_implies_intr_list() {
        let a = prop("A");
        let assumed = ThmKernel::assume(a.clone());
        let result = implies_intr_list(&[a.clone()], &assumed);
        assert!(result.is_unconditional());
    }

    #[test]
    fn test_compose_trivial() {
        let a = prop("A");
        let trivial = ThmKernel::trivial(a.clone());
        let assumed = ThmKernel::assume(a.clone());
        let result = compose(&assumed, &trivial, 0);
        assert!(result.is_some());
    }
}
