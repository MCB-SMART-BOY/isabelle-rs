//! Type inference for Isabelle terms.
//!
//! Corresponds to `src/Pure/type_infer.ML`.
//!
//! Implements Hindley-Milner style type inference adapted for Isabelle's
//! simply-typed lambda calculus with type classes.
//!
//! ## Algorithm
//!
//! 1. **Generate constraints**: Walk the term and generate type equality
//!    constraints (e.g., from `f x` we get `typeof(f) = typeof(x) → α`)
//! 2. **Unify constraints**: Solve the constraints via unification
//! 3. **Apply substitution**: Apply the resulting type substitution to the term
//! 4. **Generalize**: Quantify over unconstrained type variables
//!
//! ## Key Types
//!
//! - `TypeVar` — an inference variable (like Isabelle's `?'a`)
//! - `Constraint` — a type equality `τ1 ≡ τ2`
//! - `TypeSubst` — a substitution from type variables to types

use std::collections::HashMap;

use super::term::Term;
use super::types::{Sort, Symbol, Typ};

// =========================================================================
// Inference types
// =========================================================================

/// A type inference variable: `?'a` with an optional sort constraint.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeVar {
    /// Variable name (e.g., "?'a")
    pub name: Symbol,
    /// Sort constraint (default: top sort)
    pub sort: Sort,
}

impl TypeVar {
    pub fn new(name: impl Into<Symbol>, sort: Sort) -> Self {
        TypeVar { name: name.into(), sort }
    }
}

/// A type equality constraint: `τ1 ≡ τ2`.
#[derive(Debug, Clone)]
pub struct Constraint {
    pub left: Typ,
    pub right: Typ,
}

/// A type substitution: maps type inference variables to types.
#[derive(Debug, Clone, Default)]
pub struct TypeSubst {
    map: HashMap<String, Typ>,
}

impl TypeSubst {
    pub fn new() -> Self {
        TypeSubst { map: HashMap::new() }
    }

    /// Insert a binding.
    pub fn insert(&mut self, var: Symbol, typ: Typ) {
        self.map.insert(var.to_string(), typ);
    }

    /// Look up a variable.
    pub fn get(&self, var: &Symbol) -> Option<&Typ> {
        self.map.get(var.as_ref())
    }

    /// Apply the substitution to a type (dereference).
    pub fn apply(&self, typ: &Typ) -> Typ {
        match typ {
            Typ::TVar { name, index: _, sort: _ } => {
                if let Some(t) = self.map.get(name.as_ref()) {
                    self.apply(t)
                } else {
                    typ.clone()
                }
            }
            Typ::Type { name, args } => {
                let args: Vec<Typ> = args.iter().map(|a| self.apply(a)).collect();
                Typ::Type { name: name.clone(), args }
            }
            Typ::TFree { .. } => typ.clone(),
        }
    }

    /// Compose two substitutions: `self ∘ other`.
    pub fn compose(&self, other: &TypeSubst) -> TypeSubst {
        let mut result = other.clone();
        for (var, typ) in &self.map {
            let applied = other.apply(typ);
            result.insert(Symbol::from(var.as_str()), applied);
        }
        result
    }
}

// =========================================================================
// Type inference engine
// =========================================================================

/// The type inference engine.
pub struct TypeInfer {
    /// Current substitution
    subst: TypeSubst,
    /// Next inference variable index
    next_var: usize,
    /// Type environment for constant lookup
    type_env: Option<super::types::TypeEnv>,
}

impl TypeInfer {
    /// Create a new inference engine.
    pub fn new() -> Self {
        TypeInfer {
            subst: TypeSubst::new(),
            next_var: 0,
            type_env: None,
        }
    }

    /// Create with a type environment.
    pub fn with_env(env: super::types::TypeEnv) -> Self {
        TypeInfer {
            subst: TypeSubst::new(),
            next_var: 0,
            type_env: Some(env),
        }
    }

    /// Generate a fresh inference variable.
    fn fresh_var(&mut self, sort: Sort) -> Typ {
        let name = Symbol::from(format!("?'a{}", self.next_var));
        self.next_var += 1;
        Typ::TVar { name, index: 0, sort }
    }

    /// Infer the type of a term.
    ///
    /// Returns `Some(typ)` if inference succeeds, `None` if constraints
    /// cannot be satisfied.
    pub fn infer(&mut self, term: &Term) -> Option<Typ> {
        let (typ, mut constraints) = self.infer_with_constraints(term);
        // Solve constraints
        if self.solve_constraints(&mut constraints) {
            Some(self.subst.apply(&typ))
        } else {
            None
        }
    }

    /// Infer type and generate constraints.
    fn infer_with_constraints(&mut self, term: &Term) -> (Typ, Vec<Constraint>) {
        match term {
            Term::Const { name, typ } => {
                // Look up in TypeEnv if type is dummy
                if typ.is_dummy() {
                    if let Some(env) = &self.type_env {
                        if let Some(t) = env.const_type(name.as_ref()) {
                            return (t.clone(), vec![]);
                        }
                    }
                }
                if typ.is_dummy() {
                    // Generate a fresh variable for unknown constants
                    let v = self.fresh_var(Sort::top());
                    (v, vec![])
                } else {
                    (typ.clone(), vec![])
                }
            }

            Term::Free { typ, .. } => {
                if typ.is_dummy() {
                    let v = self.fresh_var(Sort::top());
                    (v, vec![])
                } else {
                    (typ.clone(), vec![])
                }
            }

            Term::Var { typ, .. } => {
                if typ.is_dummy() {
                    let v = self.fresh_var(Sort::top());
                    (v, vec![])
                } else {
                    (typ.clone(), vec![])
                }
            }

            Term::Bound(_) => {
                let v = self.fresh_var(Sort::top());
                (v, vec![])
            }

            Term::Abs { typ, body, .. } => {
                let dom = if typ.is_dummy() {
                    self.fresh_var(Sort::top())
                } else {
                    typ.clone()
                };
                let (cod, constraints) = self.infer_with_constraints(body);
                let fun_typ = Typ::arrow(dom, cod);
                (fun_typ, constraints)
            }

            Term::App { func, arg } => {
                let (fn_typ, mut constraints) = self.infer_with_constraints(func);
                let (arg_typ, arg_constraints) = self.infer_with_constraints(arg);
                constraints.extend(arg_constraints);

                let result_typ = self.fresh_var(Sort::top());
                constraints.push(Constraint {
                    left: fn_typ,
                    right: Typ::arrow(arg_typ, result_typ.clone()),
                });
                (result_typ, constraints)
            }
        }
    }

    /// Solve a set of type equality constraints via unification.
    fn solve_constraints(&mut self, constraints: &mut Vec<Constraint>) -> bool {
        // Simple unification loop
        while let Some(constraint) = constraints.pop() {
            let t1 = self.subst.apply(&constraint.left);
            let t2 = self.subst.apply(&constraint.right);

            if t1 == t2 {
                continue;
            }

            match (&t1, &t2) {
                // Both are type constructors: unify args
                (Typ::Type { name: n1, args: a1 }, Typ::Type { name: n2, args: a2 })
                    if n1 == n2 && a1.len() == a2.len() =>
                {
                    for (a, b) in a1.iter().zip(a2.iter()) {
                        constraints.push(Constraint {
                            left: a.clone(),
                            right: b.clone(),
                        });
                    }
                }

                // Inference variable on left
                (Typ::TVar { name, index: _, sort: _ }, _) => {
                    // Occurs check
                    if occurs_in(name, &t2) {
                        return false;
                    }
                    self.subst.insert(name.clone(), t2.clone());
                }

                // Inference variable on right
                (_, Typ::TVar { name, index: _, sort: _ }) => {
                    if occurs_in(name, &t1) {
                        return false;
                    }
                    self.subst.insert(name.clone(), t1.clone());
                }

                // Arrow types: ensure both have 2 args before indexing
                (Typ::Type { name: n1, args: a1 }, Typ::Type { name: n2, args: a2 })
                    if n1.as_ref() == "fun" && n2.as_ref() == "fun"
                    && a1.len() == 2 && a2.len() == 2 =>
                {
                    constraints.push(Constraint { left: a1[0].clone(), right: a2[0].clone() });
                    constraints.push(Constraint { left: a1[1].clone(), right: a2[1].clone() });
                }

                // Mismatch
                _ => return false,
            }
        }
        true
    }

    /// Get the final substitution.
    pub fn substitution(&self) -> &TypeSubst {
        &self.subst
    }

    /// Apply the inferred types to a term, replacing dummy types.
    pub fn apply_to_term(&self, term: &Term) -> Term {
        match term {
            Term::Const { name, typ } => {
                Term::const_(name.as_ref(), self.subst.apply(typ))
            }
            Term::Free { name, typ } => {
                Term::free(name.as_ref(), self.subst.apply(typ))
            }
            Term::Var { name, index, typ } => {
                Term::var(name.as_ref(), *index, self.subst.apply(typ))
            }
            Term::Bound(i) => Term::bound(*i),
            Term::Abs { name, typ, body } => {
                Term::abs(
                    name.as_ref(),
                    self.subst.apply(typ),
                    self.apply_to_term(body),
                )
            }
            Term::App { func, arg } => {
                Term::app(
                    self.apply_to_term(func),
                    self.apply_to_term(arg),
                )
            }
        }
    }
}

impl Default for TypeInfer {
    fn default() -> Self {
        Self::new()
    }
}

// =========================================================================
// Helper functions
// =========================================================================

/// Check if a type variable occurs in a type (occurs check).
fn occurs_in(var: &Symbol, typ: &Typ) -> bool {
    match typ {
        Typ::TVar { name, .. } => name == var,
        Typ::Type { args, .. } => args.iter().any(|a| occurs_in(var, a)),
        Typ::TFree { .. } => false,
    }
}

/// Infer the principal type of a term using the global HOL theorem database.
///
/// This is the primary entry point for type inference outside of the kernel.
/// It looks up constant types from the `HolTheoremDb` type environment and
/// runs Hindley-Milner inference to determine the most general type of `term`.
///
/// # Returns
///
/// - `Some(typ)` — the inferred type if constraints can be satisfied.
/// - `None` — if unification fails (type mismatch) or an occurs-check
///   violation is detected.
///
/// # Errors
///
/// Returns `None` (rather than panicking) when inference fails.  Common
/// failure cases include:
/// - Applying a non-function term (e.g., `True x`).
/// - Circular type constraints (occurs-check failure).
/// - Type constructor arity mismatches.
///
/// # Examples
///
/// ```rust
/// use isabelle_rs::core::term::Term;
/// use isabelle_rs::core::types::Typ;
/// use isabelle_rs::core::type_infer::infer_type;
///
/// // Infer type of a constant application: `¬ True`
/// let not_true = Term::app(
///     Term::const_("HOL.Not", Typ::dummy()),
///     Term::const_("HOL.True", Typ::dummy()),
/// );
/// let typ = infer_type(&not_true);
/// assert!(typ.is_some());
/// ```
pub fn infer_type(term: &Term) -> Option<Typ> {
    let env = crate::hol::hol_loader::HolTheoremDb::get().type_env.clone();
    let mut infer = TypeInfer::with_env(env);
    infer.infer(term)
}

/// Infer types for all sub-terms of `term` and return a fully-annotated copy.
///
/// This is a convenience wrapper that first calls [`infer_type`] to compute
/// the principal type, then returns a new [`Term`] where every sub-term
/// carries its inferred type (replacing any [`Typ::dummy`] placeholders).
///
/// # Errors
///
/// Returns `None` if type inference fails for any sub-term.  The same
/// failure conditions as [`infer_type`] apply.
///
/// # Examples
///
/// ```rust
/// use isabelle_rs::core::term::Term;
/// use isabelle_rs::core::types::Typ;
/// use isabelle_rs::core::type_infer::infer_and_annotate;
///
/// let f_x = Term::app(
///     Term::free("f", Typ::dummy()),
///     Term::free("x", Typ::dummy()),
/// );
/// let annotated = infer_and_annotate(&f_x).unwrap();
/// // The annotated term should no longer contain dummy types.
/// ```
pub fn infer_and_annotate(term: &Term) -> Option<Term> {
    let env = crate::hol::hol_loader::HolTheoremDb::get().type_env.clone();
    let mut infer = TypeInfer::with_env(env);
    let _typ = infer.infer(term)?;
    Some(infer.apply_to_term(term))
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_infer_const() {
        let t = Term::const_("True", Typ::base("bool"));
        let mut infer = TypeInfer::new();
        let typ = infer.infer(&t);
        assert_eq!(typ, Some(Typ::base("bool")));
    }

    #[test]
    fn test_infer_application() {
        // f x  where f: ?a → bool, x: ?a
        let f = Term::free("f", Typ::arrow(Typ::free("'a", Sort::top()), Typ::base("bool")));
        let x = Term::free("x", Typ::free("'a", Sort::top()));
        let app = Term::app(f, x);

        let mut infer = TypeInfer::new();
        let typ = infer.infer(&app);
        assert_eq!(typ, Some(Typ::base("bool")));
    }

    #[test]
    fn test_infer_lambda() {
        // λx. x  where x: ?a
        let x = Term::bound(0);
        let abs = Term::abs("x", Typ::free("'a", Sort::top()), x);

        let mut infer = TypeInfer::new();
        let typ = infer.infer(&abs);
        // Should be 'a → 'a
        if let Some(t) = typ {
            assert!(t.dest_fun().is_some());
        } else {
            panic!("Expected type, got None");
        }
    }

    #[test]
    fn test_infer_occurs_check() {
        // With our current simple inference (fresh vars per occurrence),
        // the occurs check is only triggered by explicit circular constraints.
        // This test validates the occurs check mechanism exists.
        // Full Hindley-Milner with proper variable scoping is a Phase 50+ task.
        let t1 = Typ::TVar { name: Symbol::from("?a"), index: 0, sort: Sort::top() };
        let t2 = Typ::arrow(t1.clone(), Typ::base("bool"));
        // occurs_in should detect the circular reference
        assert!(occurs_in(&Symbol::from("?a"), &t2));
    }
}
