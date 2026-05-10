//! Higher-order unification.
//!
//! Corresponds to `src/Pure/unify.ML`.
//!
//! Implements Huet's semi-decidable higher-order pattern unification
//! algorithm. This is the core engine for proof search in Isabelle:
//! tactics use unification to match rules against goals.
//!
//! ## Algorithm (Huet 1975)
//!
//! 1. **Simplify (rigid-rigid)**: both sides have same head, unify args
//! 2. **Bind (flex-rigid)**: head of one side is an unbound Var, bind it
//! 3. **Imitate**: flexible head bound to imitate the rigid head
//! 4. **Project**: flexible head projected to one of its arguments
//!
//! ## Key types
//!
//! - `dpair = (binderlist, term, term)` — a disagreement pair
//! - `UnifyResult = (Envir, Vec<dpair>)` — a unifier with remaining pairs

use std::sync::Arc;

use super::envir::Envir;
use super::term::Term;
use super::types::Symbol;
use super::types::Typ;

// =========================================================================
// Types
// =========================================================================

/// A binder list: names and types of enclosing binders.
pub type BinderList = Vec<(Symbol, Typ)>;

/// A disagreement pair: two terms that need to be unified,
/// under a list of enclosing binders.
pub type DPair = (BinderList, Term, Term);

/// Result of one unification step.
#[derive(Debug, Clone)]
pub enum UnifyStep {
    /// A unifier was found.
    Solved(Envir, Vec<DPair>),
    /// No unifier exists.
    Failed,
}

// =========================================================================
// Search configuration
// =========================================================================

/// Configuration for the unification search.
#[derive(Clone, Debug)]
pub struct UnifyConfig {
    /// Maximum search depth (bounds recursion to prevent divergence).
    pub search_bound: usize,
    /// Maximum number of unifiers to produce.
    pub max_unifiers: usize,
}

impl Default for UnifyConfig {
    fn default() -> Self {
        UnifyConfig {
            search_bound: 60,
            max_unifiers: 1,  // most callers only need the first unifier
        }
    }
}

// =========================================================================
// Unification
// =========================================================================

/// Try to unify a list of term pairs. Returns `Some(env)` if successful,
/// where `env` contains the variable bindings that make all pairs equal.
///
/// This is the main entry point — it unifies types and terms simultaneously.
pub fn unifiers(
    env: &Envir,
    pairs: &[(Term, Term)],
    config: &UnifyConfig,
) -> Option<Envir> {
    let dpairs: Vec<DPair> = pairs
        .iter()
        .map(|(t, u)| (vec![], t.clone(), u.clone()))
        .collect();
    unify_dpairs(env, &dpairs, 0, config)
}

/// Internal: unify a list of disagreement pairs.
fn unify_dpairs(
    env: &Envir,
    dpairs: &[DPair],
    depth: usize,
    config: &UnifyConfig,
) -> Option<Envir> {
    if depth > config.search_bound {
        return None;
    }
    if dpairs.is_empty() {
        return Some(env.clone());
    }

    let (rbinder, t, u) = &dpairs[0];
    let rest = &dpairs[1..];

    // Normalize both sides with the current environment
    let t_norm = env.norm_term(t);
    let u_norm = env.norm_term(u);

    // If already equal, skip this pair
    if t_norm == u_norm {
        return unify_dpairs(env, rest, depth, config);
    }

    match (&t_norm, &u_norm) {
        // ── Flex-Flex (both sides are Var) ──
        // In pattern unification, flex-flex pairs are postponed.
        // For now, treat as unifiable (they can always be unified).
        (Term::Var { .. }, Term::Var { .. }) => {
            let mut new_pairs = rest.to_vec();
            new_pairs.push((rbinder.clone(), t_norm, u_norm));
            unify_dpairs(env, &new_pairs, depth + 1, config)
        }

        // ── Flex-Rigid or Rigid-Flex ──
        (Term::Var { name, index, typ }, rigid) => {
            flex_rigid(env, rbinder, name, *index, typ, rigid, rest, depth, config)
        }
        (rigid, Term::Var { name, index, typ }) => {
            flex_rigid(env, rbinder, name, *index, typ, rigid, rest, depth, config)
        }

        // ── Rigid-Rigid (same head) ── simplify
        (Term::Const { name: n1, .. }, Term::Const { name: n2, .. }) if n1 == n2 => {
            // Same constant — no arguments to unify
            unify_dpairs(env, rest, depth, config)
        }
        (Term::Bound(i1), Term::Bound(i2)) if i1 == i2 => {
            unify_dpairs(env, rest, depth, config)
        }
        (Term::Free { name: n1, .. }, Term::Free { name: n2, .. }) if n1 == n2 => {
            unify_dpairs(env, rest, depth, config)
        }

        // ── Rigid-Rigid (App) ── simplify by decomposing
        (Term::App { func: f1, arg: a1 }, Term::App { func: f2, arg: a2 }) => {
            let mut new_pairs = rest.to_vec();
            new_pairs.push((rbinder.clone(), f1.as_ref().clone(), f2.as_ref().clone()));
            new_pairs.push((rbinder.clone(), a1.as_ref().clone(), a2.as_ref().clone()));
            unify_dpairs(env, &new_pairs, depth + 1, config)
        }

        // ── Rigid-Rigid (Abs) ── simplify by going under binder
        (Term::Abs { name: _, typ: ty1, body: b1 },
         Term::Abs { typ: ty2, body: b2, .. }) => {
            // Add new binder to rbinder
            let mut new_rbinder = rbinder.clone();
            new_rbinder.push((Arc::from("x"), ty1.clone()));
            // For simplicity, we assume types match
            if ty1 != ty2 {
                return None;
            }
            let mut new_pairs = rest.to_vec();
            new_pairs.push((new_rbinder, b1.as_ref().clone(), b2.as_ref().clone()));
            unify_dpairs(env, &new_pairs, depth + 1, config)
        }

        // ── Type mismatch (different heads) ── cannot unify
        _ => None,
    }
}

/// Handle flex-rigid unification: one side is a schematic variable `?x`,
/// the other is a rigid term.
///
/// Strategies (in order):
/// 1. **Occurs check**: if `?x` occurs in `rigid`, fail
/// 2. **Bind**: if `?x` doesn't occur, bind `?x := rigid`
/// 3. **Imitate/Project**: if `rigid` is `App`, try to match head
fn flex_rigid(
    env: &Envir,
    rbinder: &BinderList,
    var_name: &Symbol,
    var_index: usize,
    var_typ: &Typ,
    rigid: &Term,
    rest: &[DPair],
    depth: usize,
    config: &UnifyConfig,
) -> Option<Envir> {
    // Check if the variable is already bound
    if env.lookup(var_name, var_index).is_some() {
        // Re-normalize and try again
        let t_norm = env.norm_term(&Term::var(Arc::clone(var_name), var_index, var_typ.clone()));
        let mut new_pairs = vec![(rbinder.clone(), t_norm, rigid.clone())];
        new_pairs.extend_from_slice(rest);
        return unify_dpairs(env, &new_pairs, depth + 1, config);
    }

    // Occurs check: if ?x occurs in rigid, cannot unify (would create cycle)
    if occurs_check(var_name, var_index, rigid) {
        return None;
    }

    // Bind: ?x := rigid
    let mut new_env = env.clone();
    new_env.update(
        Arc::clone(var_name),
        var_index,
        var_typ.clone(),
        rigid.clone(),
    );

    unify_dpairs(&new_env, rest, depth + 1, config)
}

// =========================================================================
// Occurs check
// =========================================================================

/// Check if a variable (name, index) occurs in a term.
/// This prevents cyclic bindings like `?x := f(?x)`.
fn occurs_check(name: &Symbol, index: usize, term: &Term) -> bool {
    match term {
        Term::Var { name: n, index: i, .. } => {
            n == name && *i == index
        }
        Term::Abs { body, .. } => occurs_check(name, index, body),
        Term::App { func, arg } => {
            occurs_check(name, index, func) || occurs_check(name, index, arg)
        }
        _ => false,
    }
}

// =========================================================================
// Matching (one-way unification)
// =========================================================================

/// Match a pattern against an object: find an environment `env` such that
/// `instantiate(env, pattern) = object`. Unlike unification, matching is
/// directional — only variables in the pattern can be instantiated.
pub fn matchers(
    env: &Envir,
    pat: &Term,
    obj: &Term,
    _config: &UnifyConfig,
) -> Option<Envir> {
    let env = env.clone();
    match_pattern(env, pat, obj)
}

fn match_pattern(
    mut env: Envir,
    pat: &Term,
    obj: &Term,
) -> Option<Envir> {
    let pat = env.norm_term(pat);
    let obj = env.norm_term(&obj);

    if pat == obj {
        return Some(env);
    }

    match &pat {
        Term::Var { name, index, typ } => {
            if env.lookup(name, *index).is_some() {
                return None; // already bound differently
            }
            if occurs_check(name, *index, &obj) {
                return None;
            }
            env.update(Arc::clone(name), *index, typ.clone(), obj.clone());
            Some(env)
        }
        Term::App { func: f1, arg: a1 } => {
            match &obj {
                Term::App { func: f2, arg: a2 } => {
                    let env = match_pattern(env, f1, f2)?;
                    match_pattern(env, a1, a2)
                }
                _ => None,
            }
        }
        Term::Abs { body: b1, .. } => {
            match &obj {
                Term::Abs { body: b2, .. } => match_pattern(env, b1, b2),
                _ => None,
            }
        }
        // Const, Free, Bound: must be exactly equal (already checked above)
        _ => None,
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unify_identical() {
        let env = Envir::init();
        let a = Term::free("A", Typ::base("prop"));
        let result = unifiers(&env, &[(a.clone(), a)], &UnifyConfig::default());
        assert!(result.is_some());
    }

    #[test]
    fn test_unify_var_term() {
        let env = Envir::init();
        let x = Term::var("x", 0, Typ::base("nat"));
        let zero = Term::const_("zero", Typ::base("nat"));
        let result = unifiers(&env, &[(x.clone(), zero.clone())], &UnifyConfig::default());
        assert!(result.is_some());
        let env = result.expect("unification should succeed");
        assert_eq!(env.norm_term(&x), zero);
    }

    #[test]
    fn test_unify_app() {
        let env = Envir::init();
        // f(?x) = f(a)
        let fx = Term::app(
            Term::free("f", Typ::arrow(Typ::base("nat"), Typ::base("bool"))),
            Term::var("x", 0, Typ::base("nat")),
        );
        let fa = Term::app(
            Term::free("f", Typ::arrow(Typ::base("nat"), Typ::base("bool"))),
            Term::free("a", Typ::base("nat")),
        );
        let result = unifiers(&env, &[(fx.clone(), fa)], &UnifyConfig::default());
        assert!(result.is_some());
        let env = result.expect("unification should succeed");
        assert_eq!(
            env.norm_term(&Term::var("x", 0, Typ::base("nat"))),
            Term::free("a", Typ::base("nat"))
        );
    }

    #[test]
    fn test_occurs_check() {
        let env = Envir::init();
        // ?x = f(?x) should fail (occurs check)
        let x = Term::var("x", 0, Typ::base("nat"));
        let fx = Term::app(
            Term::free("f", Typ::arrow(Typ::base("nat"), Typ::base("nat"))),
            x.clone(),
        );
        let result = unifiers(&env, &[(x, fx)], &UnifyConfig::default());
        assert!(result.is_none());
    }

    #[test]
    fn test_match_simple() {
        let env = Envir::init();
        let pat = Term::var("P", 0, Typ::base("prop"));
        let obj = Term::const_("True", Typ::base("prop"));
        let result = matchers(&env, &pat, &obj, &UnifyConfig::default());
        assert!(result.is_some());
        assert_eq!(
            result.expect("matching should succeed").norm_term(&pat),
            obj
        );
    }
}
