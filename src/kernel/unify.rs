//! Strict matcher for the kernel nucleus.
//!
//! This module provides a conservative first-order structural matcher.
//! It does NOT implement full unification, flex-flex pairs, or
//! higher-order pattern matching.
//!
//! # Design
//!
//! The matcher (`match_terms`) is a pure structural operation on `Term`
//! values. It produces raw `MatchBinding` values with bare `Term`
//! replacements — it does NOT construct `CTerm` or `InstEntry` directly.
//!
//! Callers in `KernelRules` wrap the bindings into `InstEntry` using
//! `ProofContext`, enforcing the certified-by-origin contract: only
//! subterms originating from certified `CProp` propositions enter the
//! substitution.
//!
//! # Constraints (first version)
//!
//! - Only pattern-side `Var` nodes are matched (no target-side instantiation).
//! - Exact type match required for every `Var` binding.
//! - Repeated assignments must be consistent (same `Var` → same replacement).
//! - Replacements must not contain `Bound` variables.
//! - No flex-flex pairs.
//! - No higher-order pattern unification.

use std::collections::HashMap;

use super::{KernelError, Name, Term, Ty};

/// Raw match binding produced by the strict matcher.
///
/// Maps a pattern-side schematic variable `Var(name, index, var_ty)` to
/// a replacement `Term` from the target. The replacement is a bare `Term`
/// — the caller must certify it through `ProofContext` before constructing
/// `InstEntry`.
///
/// This type is `pub(in crate::kernel)` — only `src/kernel/` modules may
/// access raw match bindings; they always flow through `InstEntry`
/// certification before reaching upper layers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(in crate::kernel) struct MatchBinding {
    /// Name of the schematic variable to replace.
    pub name: Name,
    /// De Bruijn-style index of the schematic variable.
    pub index: usize,
    /// Type of the schematic variable.
    pub var_ty: Ty,
    /// The replacement term from the target (NOT yet wrapped in CTerm).
    pub replacement: Term,
}

/// Strict one-way structural matcher.
///
/// Matches a `pattern` (containing schematic `Var` nodes) against a concrete
/// `target` term. Only pattern-side `Var` nodes are matched — target-side
/// `Var` nodes are treated as concrete constants and must match exactly.
///
/// # Returns
///
/// - `Ok(Vec<MatchBinding>)` — one binding per distinct pattern `Var`.
/// - `Err(KernelError)` — match failure, type mismatch, inconsistent binding,
///   or `Bound` in replacement.
///
/// # Examples
///
/// ```ignore
/// // Pattern: ?P ==> ?Q  (with Vars)
/// // Target:  A ==> B    (concrete)
/// // → binds ?P → A, ?Q → B
/// ```
pub(in crate::kernel) fn match_terms(
    pattern: &Term,
    target: &Term,
) -> Result<Vec<MatchBinding>, KernelError> {
    let mut bindings: HashMap<(Name, usize), MatchBinding> = HashMap::new();
    let mut stack: Vec<(Term, Term)> = vec![(pattern.clone(), target.clone())];

    while let Some((pat, tgt)) = stack.pop() {
        match (&pat, &tgt) {
            // ── Var (pattern-side): bind or check consistency ──
            (Term::Var { name, index, ty: var_ty }, _) => {
                let key = (name.clone(), *index);
                if let Some(existing) = bindings.get(&key) {
                    // Repeated Var — must be consistent.
                    if existing.var_ty != *var_ty {
                        return Err(KernelError::TypeMismatch {
                            expected: existing.var_ty.clone(),
                            actual: var_ty.clone(),
                        });
                    }
                    if !alpha_eq_terms(&existing.replacement, &tgt) {
                        return Err(KernelError::Invariant(format!(
                            "inconsistent match for Var {name}[{index}]: \
                             previously matched to {:?}, now to {:?}",
                            existing.replacement, tgt,
                        )));
                    }
                } else {
                    // First occurrence — bind.
                    if *var_ty != tgt.ty() {
                        return Err(KernelError::TypeMismatch {
                            expected: (*var_ty).clone(),
                            actual: tgt.ty(),
                        });
                    }
                    if contains_bound(&tgt) {
                        return Err(KernelError::BoundInSubstitution);
                    }
                    bindings.insert(
                        key,
                        MatchBinding {
                            name: name.clone(),
                            index: *index,
                            var_ty: var_ty.clone(),
                            replacement: tgt.clone(),
                        },
                    );
                }
            },

            // ── Const: exact match ──
            (Term::Const { name: n1, ty: t1 }, Term::Const { name: n2, ty: t2 }) => {
                if n1 != n2 || t1 != t2 {
                    return Err(KernelError::Invariant(format!(
                        "Const mismatch: {:?} vs {:?}",
                        pat, tgt,
                    )));
                }
            },

            // ── Free: exact match ──
            (Term::Free { name: n1, ty: t1 }, Term::Free { name: n2, ty: t2 }) => {
                if n1 != n2 || t1 != t2 {
                    return Err(KernelError::Invariant(format!(
                        "Free mismatch: {:?} vs {:?}",
                        pat, tgt,
                    )));
                }
            },

            // ── Bound: exact match (both index and type) ──
            (Term::Bound { index: i1, ty: t1 }, Term::Bound { index: i2, ty: t2 }) => {
                if i1 != i2 || t1 != t2 {
                    return Err(KernelError::Invariant(format!(
                        "Bound mismatch: {:?} vs {:?}",
                        pat, tgt,
                    )));
                }
            },

            // ── Abs: same binder type, recurse into bodies ──
            (
                Term::Abs { name: _, param_ty: pt1, body: b1, ty: _ },
                Term::Abs { name: _, param_ty: pt2, body: b2, ty: _ },
            ) => {
                if pt1 != pt2 {
                    return Err(KernelError::TypeMismatch {
                        expected: pt1.clone(),
                        actual: pt2.clone(),
                    });
                }
                stack.push(((**b1).clone(), (**b2).clone()));
            },

            // ── Forall: same binder type, recurse into bodies ──
            (
                Term::Forall { name: _, param_ty: pt1, body: b1 },
                Term::Forall { name: _, param_ty: pt2, body: b2 },
            ) => {
                if pt1 != pt2 {
                    return Err(KernelError::TypeMismatch {
                        expected: pt1.clone(),
                        actual: pt2.clone(),
                    });
                }
                stack.push(((**b1).clone(), (**b2).clone()));
            },

            // ── App: recurse into func and arg ──
            (Term::App { func: f1, arg: a1, ty: _ }, Term::App { func: f2, arg: a2, ty: _ }) => {
                stack.push(((**a1).clone(), (**a2).clone()));
                stack.push(((**f1).clone(), (**f2).clone()));
            },

            // ── Eq: same object type, recurse into lhs and rhs ──
            (
                Term::Eq { object_ty: ot1, lhs: l1, rhs: r1 },
                Term::Eq { object_ty: ot2, lhs: l2, rhs: r2 },
            ) => {
                if ot1 != ot2 {
                    return Err(KernelError::TypeMismatch {
                        expected: ot1.clone(),
                        actual: ot2.clone(),
                    });
                }
                stack.push(((**r1).clone(), (**r2).clone()));
                stack.push(((**l1).clone(), (**l2).clone()));
            },

            // ── Imp: recurse into premise and conclusion ──
            (
                Term::Imp { premise: p1, conclusion: c1 },
                Term::Imp { premise: p2, conclusion: c2 },
            ) => {
                stack.push(((**c1).clone(), (**c2).clone()));
                stack.push(((**p1).clone(), (**p2).clone()));
            },

            // ── Any other combination: structural mismatch ──
            _ => {
                return Err(KernelError::Invariant(format!(
                    "structural mismatch in match_terms: pattern={:?}, target={:?}",
                    pat, tgt,
                )));
            },
        }
    }

    let mut result: Vec<_> = bindings.into_values().collect();
    result.sort_by(|a, b| {
        a.name
            .cmp(&b.name)
            .then_with(|| a.index.cmp(&b.index))
            .then_with(|| a.var_ty.cmp(&b.var_ty))
    });
    Ok(result)
}

/// Check whether two `Term` values are syntactically equal (structural
/// equality, not up to alpha). The strict kernel `Term` does not use
/// de Bruijn indices for named binders, so structural equality is
/// adequate for matching consistency checks.
fn alpha_eq_terms(a: &Term, b: &Term) -> bool {
    a == b
}

/// Check whether a `Term` contains any `Bound` node.
fn contains_bound(term: &Term) -> bool {
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        match t {
            Term::Bound { .. } => return true,
            Term::Abs { body, .. } | Term::Forall { body, .. } => stack.push(body),
            Term::App { func, arg, .. } => {
                stack.push(arg);
                stack.push(func);
            },
            Term::Eq { lhs, rhs, .. } => {
                stack.push(rhs);
                stack.push(lhs);
            },
            Term::Imp { premise, conclusion } => {
                stack.push(conclusion);
                stack.push(premise);
            },
            Term::Const { .. } | Term::Free { .. } | Term::Var { .. } => {},
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var_term(name: &str, index: usize, ty: Ty) -> Term {
        Term::Var { name: Name::from(name), index, ty }
    }

    fn const_term(name: &str, ty: Ty) -> Term {
        Term::Const { name: Name::from(name), ty }
    }

    fn free_term(name: &str, ty: Ty) -> Term {
        Term::Free { name: Name::from(name), ty }
    }

    fn app_term(func: Term, arg: Term) -> Term {
        let ty = func.ty();
        let result_ty = if ty.is_prop() {
            Ty::prop() // degenerate
        } else {
            ty.dest_arrow().map(|(_, to)| to.clone()).unwrap_or_else(|| ty.clone())
        };
        Term::App { func: Box::new(func), arg: Box::new(arg), ty: result_ty }
    }

    fn prop_ty() -> Ty {
        Ty::prop()
    }

    fn alpha_ty() -> Ty {
        Ty::base("alpha").unwrap()
    }

    // ── Tests ──

    #[test]
    fn match_terms_basic_var() {
        // Pattern: ?P (Var "P", index 0, prop)
        // Target:  A (Const "A", prop)
        let pattern = var_term("P", 0, prop_ty());
        let target = const_term("A", prop_ty());
        let bindings = match_terms(&pattern, &target).unwrap();
        assert_eq!(bindings.len(), 1);
        assert_eq!(bindings[0].name.as_str(), "P");
        assert_eq!(bindings[0].index, 0);
        assert_eq!(bindings[0].var_ty, prop_ty());
        assert_eq!(bindings[0].replacement, const_term("A", prop_ty()));
    }

    #[test]
    fn match_terms_repeated_var_consistent() {
        // Pattern: ?P ==> ?P  (same Var twice)
        // Target:  A ==> A    (consistent)
        let var_p = var_term("P", 0, prop_ty());
        let a = const_term("A", prop_ty());
        let pattern = Term::Imp { premise: Box::new(var_p.clone()), conclusion: Box::new(var_p) };
        let target = Term::Imp { premise: Box::new(a.clone()), conclusion: Box::new(a) };
        let bindings = match_terms(&pattern, &target).unwrap();
        assert_eq!(bindings.len(), 1);
        assert_eq!(bindings[0].replacement, const_term("A", prop_ty()));
    }

    #[test]
    fn match_terms_repeated_var_inconsistent_rejected() {
        // Pattern: ?P ==> ?P  (same Var twice)
        // Target:  A ==> B    (inconsistent — different replacements)
        let var_p = var_term("P", 0, prop_ty());
        let a = const_term("A", prop_ty());
        let b = const_term("B", prop_ty());
        let pattern = Term::Imp { premise: Box::new(var_p.clone()), conclusion: Box::new(var_p) };
        let target = Term::Imp { premise: Box::new(a), conclusion: Box::new(b) };
        let result = match_terms(&pattern, &target);
        assert!(result.is_err());
        let err = format!("{}", result.unwrap_err());
        assert!(err.contains("inconsistent"), "expected inconsistent match error, got: {err}");
    }

    #[test]
    fn match_terms_type_mismatch_rejected() {
        // Pattern: ?P (Var "P", index 0, prop)
        // Target:  x (Free "x", alpha) — wrong type
        let pattern = var_term("P", 0, prop_ty());
        let target = free_term("x", alpha_ty());
        let result = match_terms(&pattern, &target);
        assert!(result.is_err());
        let err = format!("{}", result.unwrap_err());
        assert!(err.contains("type mismatch"), "expected type mismatch error, got: {err}");
    }

    #[test]
    fn match_terms_const_mismatch_rejected() {
        // Pattern: A (Const "A", prop)
        // Target:  B (Const "B", prop) — different constant
        let pattern = const_term("A", prop_ty());
        let target = const_term("B", prop_ty());
        let result = match_terms(&pattern, &target);
        assert!(result.is_err());
        let err = format!("{}", result.unwrap_err());
        assert!(err.contains("Const mismatch"), "expected Const mismatch error, got: {err}");
    }

    #[test]
    fn match_terms_nested_app() {
        // Pattern: ?P(?x) — Var applied to Var
        // Target:  P(a)   — Const applied to Const
        let p_var = var_term("P", 0, Ty::arrow(alpha_ty(), prop_ty()));
        let x_var = var_term("x", 0, alpha_ty());
        let pattern = app_term(p_var, x_var);

        let p_const = const_term("P", Ty::arrow(alpha_ty(), prop_ty()));
        let a_const = const_term("a", alpha_ty());
        let target = app_term(p_const, a_const);

        let bindings = match_terms(&pattern, &target).unwrap();
        assert_eq!(bindings.len(), 2);
        // Check that both Vars got bound
        let p_binding = bindings.iter().find(|b| b.name.as_str() == "P").unwrap();
        assert_eq!(p_binding.replacement, const_term("P", Ty::arrow(alpha_ty(), prop_ty())));
        let x_binding = bindings.iter().find(|b| b.name.as_str() == "x").unwrap();
        assert_eq!(x_binding.replacement, const_term("a", alpha_ty()));
    }

    #[test]
    fn match_terms_rejects_bound_replacement() {
        // Pattern: ?P (prop)
        // Target:  Bound(0) — a Bound variable cannot be a replacement
        // To construct this, we need an Abs with a Var body... but
        // the simple case: can't match Var against a top-level Bound.
        let pattern = var_term("P", 0, prop_ty());
        let target = Term::Bound { index: 0, ty: prop_ty() };
        let result = match_terms(&pattern, &target);
        assert!(result.is_err());
        let err = format!("{}", result.unwrap_err());
        assert!(err.contains("Bound"), "expected Bound-in-substitution error, got: {err}");
    }

    #[test]
    fn match_terms_no_vars_identical_const() {
        // Pattern with no Vars: exact match should succeed with empty bindings.
        let pattern = const_term("A", prop_ty());
        let target = const_term("A", prop_ty());
        let bindings = match_terms(&pattern, &target).unwrap();
        assert!(bindings.is_empty());
    }

    #[test]
    fn match_terms_no_vars_mismatch_rejected() {
        // Pattern with no Vars: mismatch should fail.
        let pattern = const_term("A", prop_ty());
        let target = const_term("B", prop_ty());
        let result = match_terms(&pattern, &target);
        assert!(result.is_err());
    }

    #[test]
    fn match_terms_eq_structure() {
        // Pattern: ?x == ?y
        // Target:  a == b
        let x_var = var_term("x", 0, alpha_ty());
        let y_var = var_term("y", 1, alpha_ty());
        let pattern =
            Term::Eq { object_ty: alpha_ty(), lhs: Box::new(x_var), rhs: Box::new(y_var) };
        let a = const_term("a", alpha_ty());
        let b = const_term("b", alpha_ty());
        let target =
            Term::Eq { object_ty: alpha_ty(), lhs: Box::new(a.clone()), rhs: Box::new(b.clone()) };
        let bindings = match_terms(&pattern, &target).unwrap();
        assert_eq!(bindings.len(), 2);
        let xb = bindings.iter().find(|b| b.name.as_str() == "x").unwrap();
        assert_eq!(xb.replacement, a);
        let yb = bindings.iter().find(|b| b.name.as_str() == "y").unwrap();
        assert_eq!(yb.replacement, b);
    }

    #[test]
    fn match_terms_target_var_treated_as_concrete() {
        // Pattern: ?P
        // Target:  ?Q (Var in target — NOT instantiated, treated as concrete)
        let pattern = var_term("P", 0, prop_ty());
        let target = var_term("Q", 1, prop_ty());
        // Target-side Var "Q"[1] is treated as a concrete term.
        // Pattern Var "P"[0] binds to the Var term "Q"[1].
        let bindings = match_terms(&pattern, &target).unwrap();
        assert_eq!(bindings.len(), 1);
        assert_eq!(bindings[0].replacement, var_term("Q", 1, prop_ty()));
    }

    #[test]
    fn match_terms_multiple_distinct_vars() {
        // Pattern: ?P ==> ?Q
        // Target:  A ==> B
        let p_var = var_term("P", 0, prop_ty());
        let q_var = var_term("Q", 1, prop_ty());
        let pattern = Term::Imp { premise: Box::new(p_var), conclusion: Box::new(q_var) };
        let a = const_term("A", prop_ty());
        let b = const_term("B", prop_ty());
        let target = Term::Imp { premise: Box::new(a.clone()), conclusion: Box::new(b.clone()) };
        let bindings = match_terms(&pattern, &target).unwrap();
        assert_eq!(bindings.len(), 2);
        let pb = bindings.iter().find(|b| b.name.as_str() == "P").unwrap();
        assert_eq!(pb.replacement, a);
        let qb = bindings.iter().find(|b| b.name.as_str() == "Q").unwrap();
        assert_eq!(qb.replacement, b);
    }

    #[test]
    fn match_terms_multiple_distinct_vars_are_sorted() {
        // The matcher stores bindings internally in a HashMap. The public
        // kernel-internal result must still be deterministic because
        // derivation replay compares recorded substitutions.
        let q_var = var_term("Q", 1, prop_ty());
        let p_var = var_term("P", 0, prop_ty());
        let pattern = Term::Imp { premise: Box::new(q_var), conclusion: Box::new(p_var) };
        let target = Term::Imp {
            premise: Box::new(const_term("B", prop_ty())),
            conclusion: Box::new(const_term("A", prop_ty())),
        };

        let bindings = match_terms(&pattern, &target).unwrap();
        assert_eq!(bindings.len(), 2);
        assert_eq!(bindings[0].name.as_str(), "P");
        assert_eq!(bindings[0].index, 0);
        assert_eq!(bindings[1].name.as_str(), "Q");
        assert_eq!(bindings[1].index, 1);
    }

    #[test]
    fn match_terms_abs_structure() {
        // Pattern: λx:alpha. ?P(x)
        // Target:  λx:alpha. f(x)
        let bound0 = Term::Bound { index: 0, ty: alpha_ty() };
        let p_var = var_term("P", 0, Ty::arrow(alpha_ty(), prop_ty()));
        let pattern_body = app_term(p_var, bound0);
        let pattern = Term::Abs {
            name: Name::from("x"),
            param_ty: alpha_ty(),
            body: Box::new(pattern_body),
            ty: Ty::arrow(alpha_ty(), prop_ty()),
        };

        let f_const = const_term("f", Ty::arrow(alpha_ty(), prop_ty()));
        let target_body = app_term(f_const.clone(), Term::Bound { index: 0, ty: alpha_ty() });
        let target = Term::Abs {
            name: Name::from("x"),
            param_ty: alpha_ty(),
            body: Box::new(target_body),
            ty: Ty::arrow(alpha_ty(), prop_ty()),
        };

        let bindings = match_terms(&pattern, &target).unwrap();
        assert_eq!(bindings.len(), 1);
        assert_eq!(bindings[0].name.as_str(), "P");
        assert_eq!(bindings[0].replacement, f_const);
    }
}
