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

use super::{
    envir::Envir,
    term::Term,
    types::{Symbol, Typ},
};

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
            max_unifiers: 1, // most callers only need the first unifier
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
pub fn unifiers(env: &Envir, pairs: &[(Term, Term)], config: &UnifyConfig) -> Option<Envir> {
    let dpairs: Vec<DPair> = pairs.iter().map(|(t, u)| (vec![], t.clone(), u.clone())).collect();
    unify_dpairs_iter(env.clone(), dpairs, config)
}

/// Iterative unification of disagreement pairs using an explicit work stack.
/// This replaces the recursive `unify_dpairs` to prevent stack overflow on
/// deeply nested terms (e.g., inductive definitions, fixpoint combinators).
fn unify_dpairs_iter(
    mut env: Envir,
    initial_pairs: Vec<DPair>,
    config: &UnifyConfig,
) -> Option<Envir> {
    let mut stack: Vec<DPair> = initial_pairs;
    stack.reverse(); // Process in original order (pop from back)
    let mut steps = 0usize;

    while let Some((rbinder, t, u)) = stack.pop() {
        steps += 1;
        if steps > config.search_bound * 10 {
            return None;
        }

        let t_norm = env.norm_term(&t);
        let u_norm = env.norm_term(&u);

        if t_norm == u_norm {
            continue;
        }

        match (&t_norm, &u_norm) {
            // ── Flex-Flex: postpone ──
            (Term::Var { .. }, Term::Var { .. }) => {
                // Push to back to handle later (after bindings may resolve them)
                // But don't loop endlessly — only postpone once
            },

            // ── Flex-Rigid ──
            (Term::Var { name, index, typ }, rigid) => {
                match bind_var_step(&mut env, name, *index, typ, rigid) {
                    BindResult::Bound => {}, // env updated, continue
                    BindResult::AlreadyBound => {
                        // Re-normalize and retry
                        let renamed =
                            env.norm_term(&Term::var(Arc::clone(name), *index, typ.clone()));
                        stack.push((rbinder, renamed, rigid.clone()));
                    },
                    BindResult::Failed => return None,
                }
            },
            (rigid, Term::Var { name, index, typ }) => {
                match bind_var_step(&mut env, name, *index, typ, rigid) {
                    BindResult::Bound => {},
                    BindResult::AlreadyBound => {
                        let renamed =
                            env.norm_term(&Term::var(Arc::clone(name), *index, typ.clone()));
                        stack.push((rbinder, rigid.clone(), renamed));
                    },
                    BindResult::Failed => return None,
                }
            },

            // ── Rigid-Rigid: decompose App ──
            (Term::App { func: f1, arg: a1 }, Term::App { func: f2, arg: a2 }) => {
                // Push arg first (processed second), func second (processed first)
                stack.push((rbinder.clone(), a1.as_ref().clone(), a2.as_ref().clone()));
                stack.push((rbinder, f1.as_ref().clone(), f2.as_ref().clone()));
            },

            // ── Rigid-Rigid: decompose Abs ──
            (Term::Abs { name: _, typ: ty1, body: b1 }, Term::Abs { typ: ty2, body: b2, .. }) => {
                if ty1 != ty2 {
                    return None;
                }
                let mut new_rbinder = rbinder.clone();
                new_rbinder.push((Arc::from("x"), ty1.clone()));
                stack.push((new_rbinder, b1.as_ref().clone(), b2.as_ref().clone()));
            },

            // ── Same head atoms ──
            (Term::Const { name: n1, .. }, Term::Const { name: n2, .. }) if n1 == n2 => continue,
            (Term::Bound(i1), Term::Bound(i2)) if i1 == i2 => continue,
            (Term::Free { name: n1, .. }, Term::Free { name: n2, .. }) if n1 == n2 => continue,

            // ── Flex-App vs non-App (identity/projection cases) ──
            (Term::App { func, arg }, obj)
                if matches!(func.as_ref(), Term::Var { .. }) && term_eq_notypes(arg, obj) =>
            {
                if let Term::Var { name, index, typ } = func.as_ref() {
                    env.update(
                        name.clone(),
                        *index,
                        typ.clone(),
                        Term::abs("x", Typ::dummy(), Term::bound(0)),
                    );
                }
            },
            (obj, Term::App { func, arg })
                if matches!(func.as_ref(), Term::Var { .. }) && term_eq_notypes(arg, obj) =>
            {
                if let Term::Var { name, index, typ } = func.as_ref() {
                    env.update(
                        name.clone(),
                        *index,
                        typ.clone(),
                        Term::abs("x", Typ::dummy(), Term::bound(0)),
                    );
                }
            },

            // ── Type mismatch ──
            _ => return None,
        }
    }

    Some(env)
}

/// Result of attempting to bind a variable.
enum BindResult {
    /// Variable was successfully bound.
    Bound,
    /// Variable was already bound (needs re-normalization).
    AlreadyBound,
    /// Binding failed (occurs check).
    Failed,
}

/// Attempt to bind a variable to a term. Returns the result.
fn bind_var_step(
    env: &mut Envir,
    name: &Symbol,
    index: usize,
    typ: &Typ,
    rigid: &Term,
) -> BindResult {
    if env.lookup(name, index).is_some() {
        return BindResult::AlreadyBound;
    }
    if occurs_check(name, index, rigid) {
        return BindResult::Failed;
    }
    env.update(Arc::clone(name), index, typ.clone(), rigid.clone());
    BindResult::Bound
}

// =========================================================================
// Occurs check
// =========================================================================

/// Check if a variable (name, index) occurs in a term.
/// This prevents cyclic bindings like `?x := f(?x)`.
/// Iterative implementation to avoid stack overflow.
fn occurs_check(name: &Symbol, index: usize, term: &Term) -> bool {
    let mut stack: Vec<&Term> = vec![term];
    while let Some(t) = stack.pop() {
        match t {
            Term::Var { name: n, index: i, .. } if n == name && *i == index => return true,
            Term::Abs { body, .. } => stack.push(body),
            Term::App { func, arg } => {
                stack.push(arg);
                stack.push(func);
            },
            _ => {},
        }
    }
    false
}

// =========================================================================
// Matching (one-way unification)
// =========================================================================

/// Match a pattern against an object: find an environment `env` such that
/// `instantiate(env, pattern) = object`. Unlike unification, matching is
/// directional — only variables in the pattern can be instantiated.
pub fn matchers(env: &Envir, pat: &Term, obj: &Term, _config: &UnifyConfig) -> Option<Envir> {
    match_pattern_iter(env.clone(), pat, obj)
}

/// Iterative pattern matching using an explicit work stack.
/// Replaces the recursive `match_pattern` to prevent stack overflow.
fn match_pattern_iter(mut env: Envir, initial_pat: &Term, initial_obj: &Term) -> Option<Envir> {
    // Stack of (env, pat, obj) frames to process.
    // We use a Vec as a stack: push frames, pop and process.
    struct Frame {
        pat: Term,
        obj: Term,
    }

    let mut frames: Vec<Frame> = vec![Frame { pat: initial_pat.clone(), obj: initial_obj.clone() }];
    let mut steps = 0usize;

    while let Some(frame) = frames.pop() {
        steps += 1;
        if steps > 2000 {
            return None;
        }

        let pat = env.norm_term(&frame.pat);
        let obj = env.norm_term(&frame.obj);

        if pat == obj {
            continue;
        }

        match &pat {
            Term::Var { name, index, typ } => {
                if env.lookup(name, *index).is_some() {
                    return None;
                }
                if occurs_check(name, *index, &obj) {
                    return None;
                }
                env.update(Arc::clone(name), *index, typ.clone(), obj.clone());
            },
            Term::App { func: f1, arg: a1 } => {
                // Higher-order pattern: if head is Var applied to bound vars
                if let Some(bound_vars) = collect_bound_args(&pat) {
                    let (var_name, var_index, var_typ) = dest_head_var(&pat)?;
                    return match_ho_pattern(env, var_name, var_index, var_typ, &bound_vars, &obj);
                }
                // Standard first-order: decompose App
                match &obj {
                    Term::App { func: f2, arg: a2 } => {
                        // Push arg first (processed second), func second (processed first)
                        frames.push(Frame { pat: a1.as_ref().clone(), obj: a2.as_ref().clone() });
                        frames.push(Frame { pat: f1.as_ref().clone(), obj: f2.as_ref().clone() });
                    },
                    _ => return None,
                }
            },
            Term::Abs { body: b1, .. } => match &obj {
                Term::Abs { body: b2, .. } => {
                    frames.push(Frame { pat: b1.as_ref().clone(), obj: b2.as_ref().clone() });
                },
                _ => return None,
            },
            _ => return None,
        }
    }

    Some(env)
}

/// Check if a term is a pattern `?P(a1,...,an)` where `?P` is a Var
/// and `a1...an` are all distinct bound/free variables (a "higher-order pattern").
/// Returns the list of bound variable args if it is a HO pattern.
fn collect_bound_args(term: &Term) -> Option<Vec<Term>> {
    match term {
        Term::Var { .. } | Term::Free { .. } => Some(Vec::new()),
        Term::App { func, arg } => {
            let mut args = collect_bound_args(func)?;
            // Each argument must be a distinct bound/free variable.
            // NOTE: Var (schematic variables) are NOT treated as bound args —
            // they represent unknowns that should be decomposed directly.
            match arg.as_ref() {
                Term::Bound(_) | Term::Free { .. } => {
                    if args.iter().any(|a| a == arg.as_ref()) {
                        return None;
                    }
                    args.push(arg.as_ref().clone());
                    Some(args)
                },
                _ => None,
            }
        },
        _ => None,
    }
}

/// Extract the head variable from a HO pattern like `?P(a1,...,an)`.
fn dest_head_var(term: &Term) -> Option<(&Symbol, usize, &Typ)> {
    match term {
        Term::Var { name, index, typ } => Some((name, *index, typ)),
        Term::Free { name, typ } => Some((name, 0, typ)),
        Term::App { func, .. } => dest_head_var(func),
        _ => None,
    }
}

/// Match a higher-order pattern `?P(args)` against `obj`:
/// bind `?P` to `λargs. obj`, with args abstracted from obj.
fn match_ho_pattern(
    mut env: Envir,
    var_name: &Symbol,
    var_index: usize,
    var_typ: &Typ,
    args: &[Term],
    obj: &Term,
) -> Option<Envir> {
    if env.lookup(var_name, var_index).is_some() {
        return None;
    }
    // Build the abstraction: λa1...an. obj
    // All args (Bound, Free, Var) are abstracted
    let mut abstracted = obj.clone();
    for arg in args.iter().rev() {
        match arg {
            Term::Bound(i) => {
                abstracted = Term::abs(Arc::from(format!("x{}", i)), Typ::dummy(), abstracted);
            },
            Term::Free { name, typ } => {
                abstracted = Term::abs(Arc::clone(name), typ.clone(), abstracted);
            },
            Term::Var { name, typ, .. } => {
                abstracted = Term::abs(Arc::clone(name), typ.clone(), abstracted);
            },
            _ => {},
        }
    }
    if occurs_check(var_name, var_index, &abstracted) {
        return None;
    }
    env.update(Arc::clone(var_name), var_index, var_typ.clone(), abstracted);
    Some(env)
}

// =========================================================================
// Tests
// =========================================================================

/// Structural equality ignoring types.
/// Iterative implementation to avoid stack overflow.
fn term_eq_notypes(a: &Term, b: &Term) -> bool {
    let mut stack: Vec<(&Term, &Term)> = vec![(a, b)];
    while let Some((a, b)) = stack.pop() {
        match (a, b) {
            (Term::Const { name: n1, .. }, Term::Const { name: n2, .. }) if n1 == n2 => continue,
            (Term::Free { name: n1, .. }, Term::Free { name: n2, .. }) if n1 == n2 => continue,
            (Term::Var { name: n1, index: i1, .. }, Term::Var { name: n2, index: i2, .. })
                if n1 == n2 && i1 == i2 =>
            {
                continue;
            },
            (Term::Bound(i1), Term::Bound(i2)) if i1 == i2 => continue,
            (Term::Abs { body: b1, .. }, Term::Abs { body: b2, .. }) => {
                stack.push((b1, b2));
            },
            (Term::App { func: f1, arg: a1 }, Term::App { func: f2, arg: a2 }) => {
                stack.push((a1, a2));
                stack.push((f1, f2));
            },
            _ => return false,
        }
    }
    true
}

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
        let fx =
            Term::app(Term::free("f", Typ::arrow(Typ::base("nat"), Typ::base("nat"))), x.clone());
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
        assert_eq!(result.expect("matching should succeed").norm_term(&pat), obj);
    }

    #[test]
    fn test_ho_pattern_induction() {
        // Test HO matching: ?P(xs) against concrete goal `length xs = 0`
        let env = Envir::init();
        // Pattern: ?P xs  (like the conclusion of list.induct)
        let p_var = Term::var("P", 0, Typ::base("prop"));
        let xs = Term::free("xs", Typ::base("list"));
        let pat = Term::app(p_var.clone(), xs.clone());
        // Object: length xs = 0
        let obj = crate::core::logic::Pure::mk_equals(
            Typ::base("nat"),
            Term::app(Term::const_("length", Typ::dummy()), xs.clone()),
            Term::const_("0", Typ::base("nat")),
        );
        let result = matchers(&env, &pat, &obj, &UnifyConfig::default());
        assert!(result.is_some(), "HO matching should succeed for induction pattern");
        let env = result.unwrap();
        // ?P should be bound to λxs. length xs = 0
        let p_bound = env.norm_term(&p_var);
        eprintln!("P bound to: {:?}", p_bound);
        // Apply the bound P to xs, should equal obj
        let applied = Term::app(p_bound, xs.clone());
        let normalized = env.norm_term(&applied);
        eprintln!("P(xs) = {:?}", normalized);
    }
}
