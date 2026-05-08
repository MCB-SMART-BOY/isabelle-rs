//! Efficient type/term substitution.
//!
//! Corresponds to `src/Pure/term_subst.ML`.
//!
//! Substitution is the fundamental operation for:
//! - **β-reduction**: `(λx. t) u` → `t[x := u]`
//! - **Instantiation**: replace schematic variables with concrete terms
//! - **Generalization**: replace free variables with schematic variables
//!
//! ## Operations
//!
//! | Function | What it does |
//! |----------|-------------|
//! | `subst_bounds(args, body)` | Substitute `Bound(i)` with `args[i]` |
//! | `instantiate(tyinst, tminst, term)` | Replace TVars and Vars |
//! | `generalize(frees, idx, term)` | Replace Frees with Vars (for export) |
//! | `beta_norm(term)` | Fully β-normalize a term |

use std::collections::HashMap;
use std::sync::Arc;

use super::term::Term;
use super::types::Symbol;
use super::types::{Sort, Typ};

use super::envir::VarKey;

// =========================================================================
// Bound variable substitution
// =========================================================================

/// Substitute bound variables: `Body[Bound(0) := args[0], Bound(1) := args[1], ...]`.
///
/// This is the core of β-reduction: `(λx y. body) a b` → `subst_bounds([a, b], body)`.
pub fn subst_bounds(args: &[Term], body: &Term) -> Term {
    match body {
        Term::Bound(i) => {
            if *i < args.len() {
                args[*i].clone()
            } else {
                Term::bound(*i - args.len()) // shift remaining Bound indices
            }
        }
        Term::Abs { name, typ, body: inner } => {
            // Under a binder: Bound(0) is the new binder, args start at Bound(1)
            let dummy = Term::bound(0);
            let mut new_args: Vec<Term> = vec![dummy];
            new_args.extend(args.iter().map(|a| lift_bound(a, 0, 1)));
            let substituted = subst_bounds(&new_args, inner);
            Term::abs(Arc::clone(name), typ.clone(), substituted)
        }
        Term::App { func, arg } => {
            Term::app(
                subst_bounds(args, func),
                subst_bounds(args, arg),
            )
        }
        // Const, Free, Var: no Bound vars to substitute
        other => other.clone(),
    }
}

/// Lift all `Bound(i)` where `i >= cutoff` by `n` levels.
/// This is needed when substituting under binders.
fn lift_bound(term: &Term, cutoff: usize, n: usize) -> Term {
    match term {
        Term::Bound(i) => {
            if *i >= cutoff {
                Term::bound(*i + n)
            } else {
                Term::bound(*i)
            }
        }
        Term::Abs { name, typ, body } => {
            Term::abs(
                Arc::clone(name),
                typ.clone(),
                lift_bound(body, cutoff + 1, n),
            )
        }
        Term::App { func, arg } => {
            Term::app(
                lift_bound(func, cutoff, n),
                lift_bound(arg, cutoff, n),
            )
        }
        other => other.clone(),
    }
}

// =========================================================================
// Instantiation
// =========================================================================

/// Type instantiation table: TVar → Typ.
pub type TypeInst = HashMap<VarKey, Typ>;

/// Term instantiation table: Var → Term.
pub type TermInst = HashMap<VarKey, Term>;

/// Instantiate type variables in a type.
pub fn instantiate_type(tyinst: &TypeInst, typ: &Typ) -> Typ {
    match typ {
        Typ::TVar { name, index, .. } => {
            if let Some(assigned) = tyinst.get(&(Arc::clone(name), *index)) {
                assigned.clone()
            } else {
                typ.clone()
            }
        }
        Typ::Type { name, args } => {
            Typ::apply(
                Arc::clone(name),
                args.iter().map(|a| instantiate_type(tyinst, a)).collect(),
            )
        }
        Typ::TFree { .. } => typ.clone(),
    }
}

/// Instantiate a term: replace all Vars and TVars with their assignments.
///
/// ```
/// instantiate({?'a := nat}, {?P := λx. x}, ?P(0))
/// → (λx. x)(0)
/// ```
pub fn instantiate(tyinst: &TypeInst, tminst: &TermInst, term: &Term) -> Term {
    match term {
        Term::Var { name, index, .. } => {
            if let Some(assigned) = tminst.get(&(Arc::clone(name), *index)) {
                // Also apply type instantiation to the assigned term
                instantiate(tyinst, tminst, assigned)
            } else {
                // Instantiate the type part
                let new_typ = match term {
                    Term::Var { typ, .. } => instantiate_type(tyinst, typ),
                    _ => unreachable!(),
                };
                Term::var(Arc::clone(name), *index, new_typ)
            }
        }
        Term::Const { name, typ } => {
            Term::const_(Arc::clone(name), instantiate_type(tyinst, typ))
        }
        Term::Free { name, typ } => {
            Term::free(Arc::clone(name), instantiate_type(tyinst, typ))
        }
        Term::Bound(i) => Term::bound(*i),
        Term::Abs { name, typ, body } => {
            Term::abs(
                Arc::clone(name),
                instantiate_type(tyinst, typ),
                instantiate(tyinst, tminst, body),
            )
        }
        Term::App { func, arg } => {
            Term::app(
                instantiate(tyinst, tminst, func),
                instantiate(tyinst, tminst, arg),
            )
        }
    }
}

// =========================================================================
// Generalization: Free → Var
// =========================================================================

/// Generalize free variables to schematic variables.
/// Used when exporting a proved subgoal back to the outer context.
///
/// `generalize({x}, 0, x+y)` → `?x.0 + ?y.0`
pub fn generalize(frees: &[&str], maxidx: usize, term: &Term) -> Term {
    let free_set: std::collections::BTreeSet<&str> = frees.iter().copied().collect();
    generalize_inner(&free_set, maxidx, term)
}

fn generalize_inner(
    frees: &std::collections::BTreeSet<&str>,
    idx: usize,
    term: &Term,
) -> Term {
    match term {
        Term::Free { name, typ } => {
            if frees.contains(name.as_ref()) {
                Term::var(Arc::clone(name), idx, typ.clone())
            } else {
                term.clone()
            }
        }
        Term::Const { .. } | Term::Bound(_) | Term::Var { .. } => term.clone(),
        Term::Abs { name, typ, body } => {
            Term::abs(
                Arc::clone(name),
                typ.clone(),
                generalize_inner(frees, idx, body),
            )
        }
        Term::App { func, arg } => {
            Term::app(
                generalize_inner(frees, idx, func),
                generalize_inner(frees, idx, arg),
            )
        }
    }
}

// =========================================================================
// β-normalization
// =========================================================================

/// Fully β-normalize a term: reduce all β-redexes.
///
/// ```
/// beta_norm( (λx. (λy. y) x) a )
/// → a
/// ```
pub fn beta_norm(term: &Term) -> Term {
    match term {
        Term::App { func, arg } => {
            let func_norm = beta_norm(func);
            match &func_norm {
                Term::Abs { body, .. } => {
                    // (λx. t) u → t[x:=u]
                    let reduced = subst_bounds(&[beta_norm(arg)], body);
                    beta_norm(&reduced) // continue normalizing
                }
                _ => Term::app(func_norm, beta_norm(arg)),
            }
        }
        Term::Abs { name, typ, body } => {
            Term::abs(Arc::clone(name), typ.clone(), beta_norm(body))
        }
        other => other.clone(),
    }
}

// =========================================================================
// η-expansion / η-contraction
// =========================================================================

/// η-contract: `λx. f x` → `f` (if x not free in f).
pub fn eta_contract(term: &Term) -> Term {
    match term {
        Term::Abs { body, .. } => {
            match name.as_ref() {
                Term::App { func, arg } => {
                    match name.as_ref() {
                        Term::Bound(0) => {
                            // λx. f x  where x = Bound(0) and x ∉ FV(f)
                            if !occurs_bound(0, func) {
                                // Shift remaining Bound indices down by 1
                                eta_contract(&lower_bound(func, 1))
                            } else {
                                term.clone()
                            }
                        }
                        _ => term.clone(),
                    }
                }
                _ => term.clone(),
            }
        }
        _ => term.clone(),
    }
}

/// Check if Bound(i) occurs in term.
fn occurs_bound(i: usize, term: &Term) -> bool {
    match term {
        Term::Bound(j) => *j == i,
        Term::Abs { body, .. } => occurs_bound(i + 1, body),
        Term::App { func, arg } => occurs_bound(i, func) || occurs_bound(i, arg),
        _ => false,
    }
}

/// Lower all Bound indices >= cutoff by 1.
fn lower_bound(term: &Term, cutoff: usize) -> Term {
    match term {
        Term::Bound(i) => {
            if *i >= cutoff {
                Term::bound(*i - 1)
            } else {
                Term::bound(*i)
            }
        }
        Term::Abs { name, typ, body } => {
            Term::abs(Arc::clone(name), typ.clone(), lower_bound(body, cutoff + 1))
        }
        Term::App { func, arg } => {
            Term::app(lower_bound(func, cutoff), lower_bound(arg, cutoff))
        }
        other => other.clone(),
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_subst_bounds() {
        let a = Term::free("a", Typ::dummy());
        let b = Term::free("b", Typ::dummy());
        // subst_bounds([v0,v1,...], Bound(i)) = v_i
        assert_eq!(subst_bounds(&[a.clone()], &Term::bound(0)), a.clone());
        assert_eq!(subst_bounds(&[a.clone(), b.clone()], &Term::bound(0)), a.clone());
        assert_eq!(subst_bounds(&[a.clone(), b.clone()], &Term::bound(1)), b);
    }

    #[test]
    fn test_beta_norm_simple() {
        // (λx. x) a → a
        let lam = Term::abs("x", Typ::dummy(), Term::bound(0));
        let a = Term::free("a", Typ::dummy());
        let app = Term::app(lam, a.clone());
        let result = beta_norm(&app);
        assert_eq!(result, a);
    }

    #[test]
    fn test_beta_norm_nested() {
        // (λx. (λy. y) x) a → a
        let inner = Term::abs("y", Typ::dummy(), Term::bound(0));
        let outer = Term::abs("x", Typ::dummy(), Term::app(inner, Term::bound(0)));
        let a = Term::free("a", Typ::dummy());
        let app = Term::app(outer, a.clone());
        let result = beta_norm(&app);
        assert_eq!(result, a);
    }

    #[test]
    fn test_instantiate() {
        let mut tyinst = TypeInst::new();
        let a_name: Symbol = Arc::from("'a");
        tyinst.insert((a_name, 0), Typ::base("nat"));

        let mut tminst = TermInst::new();
        let p_name: Symbol = Arc::from("P");
        // ?P.0 := λx. x
        let lam = Term::abs("x", Typ::dummy(), Term::bound(0));
        tminst.insert((p_name, 0), lam);

        // ?P.0 :: 'a
        let var = Term::var("P", 0, Typ::var("'a", 0, Sort::singleton("type")));
        let result = instantiate(&tyinst, &tminst, &var);
        // Should be λx. x (the type part is also instantiated)
        match &result {
            Term::Abs { .. } => { /* ok */ }
            _ => panic!("expected Abs, got {result:?}"),
        }
    }

    #[test]
    fn test_generalize() {
        // generalize({x}, 0, x(some_free)) → ?x.0(some_free)
        let x = Term::free("x", Typ::dummy());
        let result = generalize(&["x"], 10, &x);
        match &result {
            Term::Var { name, index, .. } => {
                assert_eq!(name.as_ref(), "x");
                assert_eq!(*index, 10);
            }
            _ => panic!("expected Var, got {result:?}"),
        }
    }

    #[test]
    fn test_eta_contract() {
        // λx. f x → f (x not free in f)
        let f = Term::free("f", Typ::arrow(Typ::dummy(), Typ::dummy()));
        let app = Term::app(f.clone(), Term::bound(0));
        let lam = Term::abs("x", Typ::dummy(), app);
        let result = eta_contract(&lam);
        assert_eq!(result, f);
    }
}
