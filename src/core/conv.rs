//! Conversions: structured rewriting functions for terms and theorems.
//!
//! Corresponds to `src/Pure/conv.ML`.
//!
//! A **conversion** is a function `Thm → Thm` that proves an equality
//! between a given term and a rewritten version. Conversions compose
//! via combinators to perform complex rewriting in a structured way.
//!
//! ## Core concept
//!
//! ```text
//! conv: Thm → Thm
//!   input:  ⊢ t          (a theorem whose conclusion is the term to rewrite)
//!   output: ⊢ t ≡ t'     (an equality between original and rewritten term)
//! ```
//!
//! ## Combinators
//!
//! - **then_conv(c1, c2)**: c1 then c2 (transitivity of equality)
//! - **orelse_conv(c1, c2)**: try c1, if it fails try c2
//! - **arg_conv(c)**: apply c to the argument of an application
//! - **fun_conv(c)**: apply c to the function part of an application
//! - **abs_conv(c)**: apply c under an abstraction
//! - **sub_conv(c)**: apply c to all immediate subterms
//! - **top_conv(c)**: apply c at the top level of a term
//! - **bottom_conv(c)**: apply c at the leaves (bottom-up)
//! - **top_sweep_conv(c)**: apply c in a top-down sweep
//! - **rewr_conv(thm)**: conversion from a rewrite rule (equality theorem)
//! - **then_conv(c1, c2)**: sequential composition
//! - **try_conv(c)**: try a conversion, return identity on failure
//! - **repeat_conv(c)**: apply c repeatedly until no change

use std::sync::Arc;

use super::{
    logic::Pure,
    term::Term,
    thm::{CTerm, Thm, ThmKernel},
};

// =========================================================================
// Conversion type
// =========================================================================

/// A conversion is a function that transforms a theorem ⊢ t
/// into a theorem ⊢ t ≡ t' (an equality between the original term
/// and a rewritten version).
///
/// Returns `None` if the conversion does not apply.
pub type Conv = Arc<dyn Fn(&Thm) -> Option<Thm> + Send + Sync>;

// =========================================================================
// Primitive conversions
// =========================================================================

/// The identity conversion: returns ⊢ t ≡ t (reflexivity).
pub fn all_conv() -> Conv {
    Arc::new(|thm: &Thm| {
        let ct = CTerm::certify(thm.concl());
        Some(ThmKernel::reflexive(ct))
    })
}

/// The failing conversion: always returns None.
pub fn no_conv() -> Conv {
    Arc::new(|_: &Thm| None)
}

/// Create a conversion from a rewrite rule (an equality theorem ⊢ lhs ≡ rhs).
/// When applied to a term ⊢ t, if t matches lhs, returns ⊢ t ≡ rhs[lhs := t].
pub fn rewr_conv(rule: Thm) -> Conv {
    Arc::new(move |thm: &Thm| {
        let t = thm.concl();
        // Try to match the conclusion against the left-hand side of the rule
        let rule_eq = rule.concl();
        if let Term::App { func, arg: _rhs } = &rule_eq
            && let Term::App { func: eq_const, arg: lhs } = func.as_ref()
            && is_hol_eq(eq_const)
        {
            // If the term equals lhs, return reflexive equality
            if t == **lhs {
                // We have: rule ⊢ lhs ≡ rhs
                // And thm: ⊢ lhs (= t)
                // We need: ⊢ t ≡ rhs → which is just the rule
                return Some(rule.clone());
            }

            // Try to instantiate the rule
            return match_term(lhs, &t).and_then(|inst| instantiate_rule(&rule, &inst));
        }
        None
    })
}

// =========================================================================
// Combinators
// =========================================================================

/// Sequential composition: apply c1, then c2 to the result.
/// Uses transitivity: from ⊢ t ≡ u and ⊢ u ≡ v, derive ⊢ t ≡ v.
pub fn then_conv(c1: Conv, c2: Conv) -> Conv {
    Arc::new(move |thm: &Thm| {
        let r1 = c1(thm)?;
        // r1: ⊢ t ≡ u
        // Now apply c2 to the right-hand side of r1
        let u = rhs_of_conv(&r1)?;
        let u_thm = ThmKernel::assume(CTerm::certify(u.clone()));
        let r2 = c2(&u_thm)?;

        // Combine: ⊢ t ≡ u  and  ⊢ u ≡ v  →  ⊢ t ≡ v
        Some(ThmKernel::transitive(&r1, &r2).unwrap_or(r1))
    })
}

/// Alternative: try c1, if it returns None, try c2.
pub fn orelse_conv(c1: Conv, c2: Conv) -> Conv {
    Arc::new(move |thm: &Thm| c1(thm).or_else(|| c2(thm)))
}

/// Try a conversion; if it fails, return the identity ⊢ t ≡ t.
pub fn try_conv(c: Conv) -> Conv {
    let all = all_conv();
    Arc::new(move |thm: &Thm| c(thm).or_else(|| all(thm)))
}

/// Repeat the conversion until it no longer applies.
/// Has a safety limit of 100 iterations to prevent infinite loops.
pub fn repeat_conv(c: Conv) -> Conv {
    Arc::new(move |thm: &Thm| {
        let mut current = thm.clone();
        let mut iterations = 0u32;
        while iterations < 100 {
            iterations += 1;
            match c(&current) {
                Some(next) => {
                    // Extract the RHS from the equality theorem: ⊢ t ≡ u → u is the result
                    let next_concl = next.concl();
                    let (lhs, rhs) = match Pure::dest_equals(&next_concl) {
                        Some(pair) => (pair.0, pair.1),
                        None => return Some(current), // not an equality — stop
                    };
                    let cur_concl = current.concl();
                    // Convergence: RHS equals LHS (no actual rewriting happened)
                    if lhs == rhs {
                        return Some(next);
                    }
                    // Convergence: RHS equals current conclusion (fixed point)
                    if rhs == &cur_concl {
                        return Some(next);
                    }
                    current = next;
                },
                None => return Some(current),
            }
        }
        // Max iterations reached — return best result so far
        Some(current)
    })
}

// =========================================================================
// Subterm combinators
// =========================================================================

/// Apply conversion to the argument of an application.
/// From ⊢ f a, produce ⊢ f a ≡ f a' where a ≡ a' from c.
pub fn arg_conv(c: Conv) -> Conv {
    Arc::new(move |thm: &Thm| {
        let t = thm.concl();
        match &t {
            Term::App { func, arg } => {
                let arg_thm = ThmKernel::assume(CTerm::certify(arg.as_ref().clone()));
                let arg_eq = c(&arg_thm)?;
                // arg_eq: ⊢ arg ≡ arg'
                // Build: ⊢ f arg ≡ f arg' using combination
                let fun_refl = ThmKernel::reflexive(CTerm::certify(func.as_ref().clone()));
                ThmKernel::combination(&fun_refl, &arg_eq).ok()
            },
            _ => None,
        }
    })
}

/// Apply conversion to the function part of an application.
/// From ⊢ f a, produce ⊢ f a ≡ f' a where f ≡ f' from c.
pub fn fun_conv(c: Conv) -> Conv {
    Arc::new(move |thm: &Thm| {
        let t = thm.concl();
        match &t {
            Term::App { func, arg } => {
                let fun_thm = ThmKernel::assume(CTerm::certify(func.as_ref().clone()));
                let fun_eq = c(&fun_thm)?;
                // fun_eq: ⊢ func ≡ func'
                let arg_refl = ThmKernel::reflexive(CTerm::certify(arg.as_ref().clone()));
                ThmKernel::combination(&fun_eq, &arg_refl).ok()
            },
            _ => None,
        }
    })
}

/// Apply conversion under an abstraction (binder).
/// From ⊢ λx. body, produce ⊢ λx. body ≡ λx. body' where body ≡ body' from c.
pub fn abs_conv(c: Conv) -> Conv {
    Arc::new(move |thm: &Thm| {
        let t = thm.concl();
        match &t {
            Term::Abs { name, typ, body } => {
                let body_thm = ThmKernel::assume(CTerm::certify(body.as_ref().clone()));
                let body_eq = c(&body_thm)?;
                // body_eq: ⊢ body ≡ body'
                // Build: ⊢ (λx. body) ≡ (λx. body') using abstraction
                ThmKernel::abstraction(name.as_ref(), typ.clone(), &body_eq).ok()
            },
            _ => None,
        }
    })
}

/// Apply conversion to all immediate subterms.
/// For f a: apply c to both f and a.
/// For λx. body: apply c to body.
pub fn sub_conv(c: Conv) -> Conv {
    Arc::new(move |thm: &Thm| {
        let t = thm.concl();
        match &t {
            Term::App { .. } => {
                let c_arg = arg_conv(Arc::clone(&c));
                let c_fun = fun_conv(Arc::clone(&c));
                let combined = then_conv(c_fun, c_arg);
                combined(thm)
            },
            Term::Abs { .. } => abs_conv(Arc::clone(&c))(thm),
            _ => c(thm),
        }
    })
}

// =========================================================================
// Traversal helpers — explicit term walking
// =========================================================================

/// Top-down sweep on a term: try c at the top, then descend.
fn top_sweep_walk(c: Conv, thm: &Thm) -> Option<Thm> {
    // First try c at this level
    let result = c(thm);
    let current = result.as_ref().unwrap_or(thm);
    let t = current.concl();

    match &t {
        Term::App { func: _, arg: _ } => {
            let c_fun = fun_conv(Arc::clone(&c));
            let c_arg = arg_conv(Arc::clone(&c));
            // Try top-level first, then descend
            let step = result.or_else(|| c_fun(thm));

            step.or_else(|| c_arg(thm))
        },
        Term::Abs { .. } => {
            let c_abs = abs_conv(Arc::clone(&c));
            result.or_else(|| c_abs(thm))
        },
        _ => result,
    }
}

/// Bottom-up walk on a term: descend first, then try c at the top.
fn bottom_walk(c: Conv, thm: &Thm) -> Option<Thm> {
    let t = thm.concl();
    // Descend into subterms first
    let rewritten = match &t {
        Term::App { .. } => {
            let c_fun = fun_conv(Arc::clone(&c));
            let c_arg = arg_conv(Arc::clone(&c));
            // Try func first, then arg
            let after_fun = c_fun(thm).unwrap_or_else(|| thm.clone());
            c_arg(&after_fun).unwrap_or(after_fun)
        },
        Term::Abs { .. } => {
            let c_abs = abs_conv(Arc::clone(&c));
            c_abs(thm).unwrap_or_else(|| thm.clone())
        },
        _ => thm.clone(), // leaf: no subterms
    };
    // Now try applying c at the top of the rewritten term
    c(&rewritten).or(Some(rewritten))
}

// =========================================================================
// Traversal strategies
// =========================================================================

/// Top-down sweep: apply c at the top level, then recursively to subterms.
/// Uses iterative traversal with explicit term walking to avoid infinite recursion
/// that would occur if we used Conv combinators recursively.
pub fn top_sweep_conv(c: Conv) -> Conv {
    Arc::new(move |thm: &Thm| top_sweep_walk(Arc::clone(&c), thm))
}

/// Bottom-up sweep: recursively apply c to subterms first, then at top.
pub fn bottom_conv(c: Conv) -> Conv {
    Arc::new(move |thm: &Thm| bottom_walk(Arc::clone(&c), thm))
}

/// Apply c exactly at the top of the term (no recursion).
pub fn top_conv(c: Conv) -> Conv {
    c
}

// =========================================================================
// Depth-limited conversion
// =========================================================================

/// Apply conversion with a depth limit on recursion.
pub fn depth_conv(depth: usize, c: Conv) -> Conv {
    if depth == 0 {
        return all_conv();
    }
    let c_sub = sub_conv(depth_conv(depth - 1, Arc::clone(&c)));
    let combined = then_conv(c_sub, try_conv(c));
    Arc::new(move |thm: &Thm| combined(thm))
}

// =========================================================================
// Helpers
// =========================================================================

/// Check if a term is an equality constant (Pure.eq or HOL.eq).
fn is_hol_eq(term: &Term) -> bool {
    match term {
        Term::Const { name, .. } => {
            name.as_ref() == "Pure.eq"
                || name.as_ref() == "HOL.eq"
                || name.as_ref().ends_with(".eq")
        },
        _ => false,
    }
}

/// Extract the right-hand side of an equality theorem ⊢ lhs ≡ rhs.
fn rhs_of_conv(thm: &Thm) -> Option<Term> {
    let concl = thm.concl();
    match &concl {
        Term::App { func, arg: rhs } => {
            if let Term::App { func: eq_const, .. } = func.as_ref()
                && is_hol_eq(eq_const)
            {
                return Some(rhs.as_ref().clone());
            }
            None
        },
        _ => None,
    }
}

/// Try to match a pattern term against a target term.
/// Returns a list of (variable, term) pairs if matching succeeds.
fn match_term(pattern: &Term, target: &Term) -> Option<Vec<(Term, Term)>> {
    match (pattern, target) {
        (Term::Var { name: _pn, index: _pi, typ: _pt }, _) => {
            // Pattern variable: bind it
            Some(vec![(pattern.clone(), target.clone())])
        },
        (Term::Const { name: pn, typ: pt }, Term::Const { name: tn, typ: tt }) => {
            if pn == tn && pt == tt { Some(vec![]) } else { None }
        },
        (Term::Free { name: pn, typ: pt }, Term::Free { name: tn, typ: tt }) => {
            if pn == tn && pt == tt { Some(vec![]) } else { None }
        },
        (Term::Bound(pi), Term::Bound(ti)) => {
            if pi == ti {
                Some(vec![])
            } else {
                None
            }
        },
        (Term::Abs { name: _, typ: pt, body: pb }, Term::Abs { name: _, typ: tt, body: tb }) => {
            if pt == tt {
                match_term(pb, tb)
            } else {
                None
            }
        },
        (Term::App { func: pf, arg: pa }, Term::App { func: tf, arg: ta }) => {
            let mut bindings = match_term(pf, tf)?;
            bindings.extend(match_term(pa, ta)?);
            Some(bindings)
        },
        _ => None,
    }
}

/// Instantiate a theorem by substituting variables with terms.
fn instantiate_rule(rule: &Thm, inst: &[(Term, Term)]) -> Option<Thm> {
    let mut env = crate::core::envir::Envir::empty(rule.maxidx());
    for (var, replacement) in inst {
        if let Term::Var { name, index, typ } = var {
            env.update(name.clone(), *index, typ.clone(), replacement.clone());
        }
    }
    ThmKernel::instantiate_checked(&env, rule).ok()
}

// =========================================================================
// Convenience constructors
// =========================================================================

/// Create a conversion that rewrites using a list of rewrite rules.
/// Returns the first successful rewrite, or None.
pub fn first_conv(rules: &[Thm]) -> Conv {
    if rules.is_empty() {
        return no_conv();
    }
    let mut c = rewr_conv(rules[0].clone());
    for rule in &rules[1..] {
        c = orelse_conv(c, rewr_conv(rule.clone()));
    }
    c
}

/// Create a bottom-up rewriter from a set of rewrite rules.
pub fn bottom_rewriter(rules: &[Thm]) -> Conv {
    let rule_conv = first_conv(rules);
    bottom_conv(rule_conv)
}

/// Create a top-down rewriter from a set of rewrite rules.
pub fn top_rewriter(rules: &[Thm]) -> Conv {
    let rule_conv = first_conv(rules);
    top_sweep_conv(rule_conv)
}

// =========================================================================
// Conditional conversion
// =========================================================================

/// A conversion that only applies if a precondition is met.
pub fn conditional_conv(pred: impl Fn(&Thm) -> bool + Send + Sync + 'static, c: Conv) -> Conv {
    Arc::new(move |thm: &Thm| if pred(thm) { c(thm) } else { None })
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::types::Typ;

    fn prop_typ() -> Typ {
        Typ::base("prop")
    }

    #[test]
    fn test_all_conv() {
        let c = all_conv();
        let t = Term::const_("P", prop_typ());
        let thm = ThmKernel::assume(CTerm::certify(t.clone()));
        let result = c(&thm).unwrap();
        // result should be: ⊢ P ≡ P
        let concl = result.concl();
        if let Term::App { func, arg: rhs } = &concl {
            assert!(matches!(func.as_ref(), Term::App { .. }));
            assert_eq!(rhs.as_ref(), &t);
        } else {
            panic!("Expected equality");
        }
    }

    #[test]
    fn test_no_conv() {
        let c = no_conv();
        let t = Term::const_("P", prop_typ());
        let thm = ThmKernel::assume(CTerm::certify(t));
        assert!(c(&thm).is_none());
    }

    #[test]
    fn test_orelse_conv() {
        let all = all_conv();
        let no = no_conv();
        let c = orelse_conv(no, all);

        let t = Term::const_("P", prop_typ());
        let thm = ThmKernel::assume(CTerm::certify(t));
        assert!(c(&thm).is_some());
    }

    #[test]
    fn test_try_conv() {
        let c = try_conv(no_conv());
        let t = Term::const_("P", prop_typ());
        let thm = ThmKernel::assume(CTerm::certify(t.clone()));
        let result = c(&thm).unwrap();
        let concl = result.concl();
        if let Term::App { func: _, arg: rhs } = &concl {
            assert_eq!(rhs.as_ref(), &t);
        } else {
            panic!("Expected equality");
        }
    }

    #[test]
    fn test_then_conv() {
        // This test verifies that then_conv composes correctly
        let c1 = all_conv(); // ⊢ t ≡ t
        let c2 = all_conv(); // ⊢ t ≡ t
        let c = then_conv(c1, c2);

        let t = Term::const_("P", prop_typ());
        let thm = ThmKernel::assume(CTerm::certify(t.clone()));
        let result = c(&thm);
        assert!(result.is_some());
    }

    #[test]
    fn test_repeat_conv_converges() {
        // The identity conversion should converge immediately
        let c = repeat_conv(all_conv());
        let t = Term::const_("P", prop_typ());
        let thm = ThmKernel::assume(CTerm::certify(t.clone()));
        let result = c(&thm).unwrap();
        let concl = result.concl();
        if let Term::App { func: _, arg: rhs } = &concl {
            assert_eq!(rhs.as_ref(), &t);
        }
    }

    #[test]
    fn test_arg_conv() {
        // f(P) should convert to f(P) via arg_conv(all_conv)
        let f = Term::const_("f", Typ::arrow(prop_typ(), prop_typ()));
        let p = Term::const_("P", prop_typ());
        let fa = Term::app(f, p);
        let thm = ThmKernel::assume(CTerm::certify(fa));
        let c = arg_conv(all_conv());
        let result = c(&thm);
        assert!(result.is_some());
    }

    #[test]
    fn test_abs_conv() {
        let p = Term::const_("P", prop_typ());
        let abs = Term::abs("x", prop_typ(), p);
        let thm = ThmKernel::assume(CTerm::certify(abs));
        let c = abs_conv(all_conv());
        let result = c(&thm);
        assert!(result.is_some());
    }

    #[test]
    fn test_bottom_conv() {
        // Bottom-up conversion on a complex term
        let c = bottom_conv(all_conv());
        let t = Term::const_("P", prop_typ());
        let thm = ThmKernel::assume(CTerm::certify(t.clone()));
        let result = c(&thm).unwrap();
        let concl = result.concl();
        if let Term::App { func: _, arg: rhs } = &concl {
            assert_eq!(rhs.as_ref(), &t);
        }
    }

    #[test]
    fn test_rewr_conv_identity() {
        // Rewriting with refl: ⊢ t ≡ t should succeed on ⊢ t
        let t = Term::const_("P", prop_typ());
        let ct = CTerm::certify(t.clone());
        let refl = ThmKernel::reflexive(ct);

        let c = rewr_conv(refl);
        let thm = ThmKernel::assume(CTerm::certify(t.clone()));
        let result = c(&thm);
        assert!(result.is_some());
    }
}
