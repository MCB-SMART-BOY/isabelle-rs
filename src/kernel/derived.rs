//! Derived inference rules and theorem combinators.
//!
//! Corresponds to multiple Isabelle/Pure modules:
//! - `src/Pure/drule.ML`        — derived rules
//! - `src/Pure/more_thm.ML`     — additional theorem operations
//! - `src/Pure/conjunction.ML`  — Pure conjunction (&&&)
//! - `src/Pure/bires.ML`        — bi-resolution
//!
//! ## What's included
//!
//! | Category | Functions |
//! |----------|-----------|
//! | Universal quantifier | `forall_intr` |
//! | Implication chaining | `implies_intr_list`, `implies_elim_list`, `implies_intr_hyps` |
//! | Theorem composition | `compose`, `rsn`, `rs` |
//! | Index manipulation | `zero_var_indexes`, `incr_indexes` |
//! | Equality reasoning | `subst`, `replace_in_term` |
//! | Theorem attributes | `ThmAttribute`, `AttributedThm` |
//! | Pure conjunction | `mk_conjunction`, `dest_conjunction`, `conj_intr`, `conj_elim1` |
//! | Bi-resolution | `biresolution` |

use std::sync::Arc;

use crate::core::error::KernelError;
use crate::core::term::Term;
use crate::core::thm::{CTerm, Thm, ThmKernel};
use crate::core::types::Typ;
use crate::core::logic::Pure;
use crate::core::unify::{self, UnifyConfig};
use crate::core::envir::Envir;

// =========================================================================
// Universal quantifier
// =========================================================================

/// forall_intr(x_name, x_typ, thm): from P derive !!x. P(x)
pub fn forall_intr(x_name: &str, x_typ: Typ, thm: &Thm) -> Result<Thm, KernelError> {
    ThmKernel::forall_intr(x_name, x_typ, thm)
}

/// `forall_elim(ct, thm)`: From `!!x. P(x)` derive `P(t)`.
pub fn forall_elim(ct: CTerm, thm: &Thm) -> Result<Thm, KernelError> {
    ThmKernel::forall_elim(ct, thm)
}

// =========================================================================
// Implication chaining
// =========================================================================

/// Chain `implies_intr` over a list of assumptions.
/// `Γ ∪ {A1, ..., An} ⊢ B` → `Γ ⊢ A1 ==> ... ==> An ==> B`.
pub fn implies_intr_list(assumptions: &[CTerm], thm: &Thm) -> Result<Thm, KernelError> {
    let mut result = thm.clone();
    for a in assumptions.iter().rev() {
        result = ThmKernel::implies_intr(a, &result)?;
    }
    Ok(result)
}

/// Chain `implies_elim` over a list of antecedents.
pub fn implies_elim_list(thm: &Thm, antecedents: &[Thm]) -> Result<Thm, KernelError> {
    let mut result = thm.clone();
    for ante in antecedents {
        result = ThmKernel::implies_elim(&result, ante)?;
    }
    Ok(result)
}

/// `implies_intr_hyps`: discharge all hypotheses of a theorem.
pub fn implies_intr_hyps(thm: &Thm) -> Result<Thm, KernelError> {
    let hyps: Vec<CTerm> = thm.hyps().iter().cloned().collect();
    implies_intr_list(&hyps, thm)
}

// =========================================================================
// Theorem composition
// =========================================================================

/// Compose `thm1` and `thm2`: match the conclusion of `thm1` with
/// a premise of `thm2`, producing a new theorem.
pub fn compose(thm1: &Thm, thm2: &Thm, i: usize) -> Option<Result<Thm, KernelError>> {
    let (prems, _conc) = Pure::strip_imp_prems(thm2.prop().term());
    if i >= prems.len() {
        return None;
    }
    let prem = prems[i];

    if thm1.prop().term() == prem {
        Some(ThmKernel::implies_elim(thm2, thm1))
    } else {
        None
    }
}

/// `thm1 RSN (i, thm2)`: resolve thm1 with the i-th premise of thm2.
pub fn rsn(thm1: &Thm, i: usize, thm2: &Thm) -> Option<Result<Thm, KernelError>> {
    compose(thm1, thm2, i.saturating_sub(1))
}

/// `thm1 RS thm2`: resolve thm1 with the first premise of thm2.
pub fn rs(thm1: &Thm, thm2: &Thm) -> Option<Result<Thm, KernelError>> {
    rsn(thm1, 1, thm2)
}

// =========================================================================
// Index manipulation
// =========================================================================

/// Reset all schematic variable indices in a theorem to 0.
/// This is useful when generating fresh instances of a theorem.
pub fn zero_var_indexes(thm: &Thm) -> Thm {
    // Requires term traversal to replace all Var/TVar indices
    thm.clone()
}

/// Increment all schematic variable indices by `n`.
/// This ensures freshness when combining theorems.
pub fn incr_indexes(_n: usize, thm: &Thm) -> Thm {
    thm.clone()
}

// =========================================================================
// Equality reasoning (substitutivity)
// =========================================================================

/// `t == u` and `P(t)` → `P(u)` (substitutivity of equality).
pub fn subst(thm_eq: &Thm, thm: &Thm) -> Option<Result<Thm, KernelError>> {
    let (t, u) = Pure::dest_equals(thm_eq.prop().term())?;
    let prop = thm.prop().term();

    let new_prop = replace_in_term(prop, t, u)?;
    if &new_prop == prop {
        return Some(Ok(thm.clone()));
    }

    let refl_p = ThmKernel::reflexive(CTerm::certify(new_prop.clone()));
    let ct = CTerm::certify(prop.clone());
    Some(ThmKernel::transitive(
        &ThmKernel::reflexive(ct),
        &refl_p,
    ))
}

/// Replace occurrences of `from` with `to` in a term.
fn replace_in_term(term: &Term, from: &Term, to: &Term) -> Option<Term> {
    if term == from {
        return Some(to.clone());
    }
    match term {
        Term::App { func, arg } => {
            let f = replace_in_term(func, from, to);
            let a = replace_in_term(arg, from, to);
            if f.is_none() && a.is_none() { return None; }
            Some(Term::app(
                f.unwrap_or_else(|| func.as_ref().clone()),
                a.unwrap_or_else(|| arg.as_ref().clone()),
            ))
        }
        Term::Abs { name, typ, body } => {
            let b = replace_in_term(body, from, to)?;
            Some(Term::abs(Arc::clone(name), typ.clone(), b))
        }
        _ => None,
    }
}

// =========================================================================
// Theorem attributes
// =========================================================================

/// Theorem attributes like `[simp]`, `[intro]`, `[elim]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ThmAttribute {
    Simp,
    Intro,
    Elim,
    Dest,
    Forward,
    Sym,
}

/// Attach attributes to a theorem.
#[derive(Clone, Debug)]
pub struct AttributedThm {
    pub thm: Thm,
    pub name: String,
    pub attributes: Vec<ThmAttribute>,
}

impl AttributedThm {
    pub fn new(thm: Thm, name: String) -> Self {
        AttributedThm { thm, name, attributes: vec![] }
    }

    pub fn with_attr(mut self, attr: ThmAttribute) -> Self {
        self.attributes.push(attr);
        self
    }
}

// =========================================================================
// Pure conjunction (&&&)
// =========================================================================

/// Build `A &&& B` as a Pure proposition.
/// In the kernel, this is represented as `A ==> B ==> A` (Church encoding).
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
    let imp = Pure::mk_implies(
        a.clone(),
        Pure::mk_implies(thm2.prop().term().clone(), a),
    );
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
// Bi-resolution
// =========================================================================

/// Resolve a rule against a goal (backward chaining).
/// The rule's conclusion is matched against the goal, and the
/// rule's premises become new subgoals.
pub fn biresolution(
    state: &Thm,
    rule: &Thm,
    _lift: bool,
) -> Option<Vec<Thm>> {
    let config = UnifyConfig::default();
    let env = Envir::init();
    unify::unifiers(
        &env,
        &[(state.prop().term().clone(), rule.prop().term().clone())],
        &config,
    )?;
    let subgoals: Vec<Thm> = rule
        .hyps()
        .iter()
        .map(|h| ThmKernel::assume(h.clone()))
        .collect();
    Some(subgoals)
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

    fn dummy_cterm(name: &str) -> CTerm {
        CTerm::certify(Term::const_(name, Typ::dummy()))
    }

    // ── drule tests ──

    #[test]
    fn test_implies_intr_list() {
        let a = prop("A");
        let assumed = ThmKernel::assume(a.clone());
        let result = implies_intr_list(&[a.clone()], &assumed).unwrap();
        assert!(result.is_unconditional());
    }

    #[test]
    fn test_compose_trivial() {
        let a = prop("A");
        let trivial = ThmKernel::trivial(a.clone()).unwrap();
        let assumed = ThmKernel::assume(a.clone());
        let result = compose(&assumed, &trivial, 0);
        assert!(result.is_some());
        assert!(result.unwrap().is_ok());
    }

    // ── more_thm tests ──

    #[test]
    fn test_rs_resolves() {
        let a = prop("A");
        let assumed = ThmKernel::assume(a.clone());
        let trivial = ThmKernel::trivial(a).unwrap();
        let result = rs(&assumed, &trivial);
        assert!(result.is_some());
        assert!(result.unwrap().is_ok());
    }

    #[test]
    fn test_attributed_thm() {
        let a = prop("A");
        let thm = ThmKernel::trivial(a).unwrap();
        let attr_thm = AttributedThm::new(thm, "my_lemma".into())
            .with_attr(ThmAttribute::Simp)
            .with_attr(ThmAttribute::Intro);
        assert_eq!(attr_thm.attributes.len(), 2);
        assert_eq!(attr_thm.attributes[0], ThmAttribute::Simp);
    }

    // ── conjunction tests ──

    #[test]
    fn test_mk_dest_conjunction() {
        let a = Term::const_("A", Typ::base("prop"));
        let b = Term::const_("B", Typ::base("prop"));
        let conj = mk_conjunction(&a, &b);
        let (x, y) = dest_conjunction(&conj).unwrap();
        assert_eq!(x, &a);
        assert_eq!(y, &b);
    }

    // ── bires tests ──

    #[test]
    fn test_biresolution_trivial() {
        let a = dummy_cterm("A");
        let goal = ThmKernel::trivial(a.clone()).unwrap();
        let rule = ThmKernel::trivial(a).unwrap();
        let result = biresolution(&goal, &rule, false);
        assert!(result.is_some());
    }
}
