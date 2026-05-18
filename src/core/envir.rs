//! Variable environments for unification and proof search.
//!
//! Corresponds to `src/Pure/envir.ML`.
//!
//! An environment tracks the bindings of schematic variables during
//! unification and proof search:
//! - **Term environment (tenv)**: `?x` → `t` (maps Var to its term)
//! - **Type environment (tyenv)**: `?'a` → `τ` (maps TVar to its type)
//! - **maxidx**: upper bound for generating fresh variable indices
//!
//! ## Why environments are needed
//!
//! When Isabelle unifies `?P(x)` with `f(y)`, it produces an environment:
//!   `{?P := λz. f(y), ?x := y}`
//! This environment is then applied to normalize both terms.

use std::collections::HashMap;
use std::sync::Arc;

use super::term::Term;
use super::types::Symbol;
use super::types::{Sort, Typ};

// =========================================================================
// Type alias for variable indices
// =========================================================================

/// An (name, index) pair identifying a schematic variable.
pub type VarKey = (Symbol, usize);

// =========================================================================
// Envir — the variable environment
// =========================================================================

/// An environment maps schematic variables to their bindings.
///
/// Updates must keep `maxidx` as the upper bound of all variable indices
/// in the environment. The lookup function applies type substitutions
/// because they may change a variable's type identity.
#[derive(Clone, Debug)]
pub struct Envir {
    /// Upper bound of maximum variable index (for generating fresh variables).
    maxidx: usize,
    /// Term variable assignments: Var(name, index) → (original_type, assigned_term).
    tenv: HashMap<VarKey, (Typ, Term)>,
    /// Type variable assignments: TVar(name, index) → (original_sort, assigned_type).
    tyenv: HashMap<VarKey, (Sort, Typ)>,
}

impl Envir {
    // =================================================================
    // Construction
    // =================================================================

    /// Create an empty environment with the given maxidx.
    pub fn empty(maxidx: usize) -> Self {
        Envir {
            maxidx,
            tenv: HashMap::new(),
            tyenv: HashMap::new(),
        }
    }

    /// The initial environment (maxidx = 0, empty).
    pub fn init() -> Self {
        Envir::empty(0)
    }

    // =================================================================
    // Accessors
    // =================================================================

    pub fn maxidx(&self) -> usize { self.maxidx }

    pub fn is_empty(&self) -> bool {
        self.tenv.is_empty() && self.tyenv.is_empty()
    }

    /// Get the type environment (for type instantiation).
    pub fn type_env(&self) -> &HashMap<VarKey, (Sort, Typ)> {
        &self.tyenv
    }

    /// Get the term environment (for term instantiation).
    pub fn term_env(&self) -> &HashMap<VarKey, (Typ, Term)> {
        &self.tenv
    }

    // =================================================================
    // Variable generation
    // =================================================================

    /// Generate a fresh schematic variable: increments maxidx, creates Var(name, maxidx, typ).
    pub fn genvar(&mut self, name: &str, typ: Typ) -> Term {
        self.maxidx += 1;
        Term::var(name, self.maxidx, typ)
    }

    /// Generate multiple fresh variables from a list of types.
    pub fn genvars(&mut self, name: &str, types: &[Typ]) -> Vec<Term> {
        types.iter().map(|typ| self.genvar(name, typ.clone())).collect()
    }

    // =================================================================
    // Lookup
    // =================================================================

    /// Look up a term variable's binding in the environment.
    /// Returns the assigned term if the variable is bound.
    pub fn lookup(&self, name: &Symbol, index: usize) -> Option<&Term> {
        self.tenv.get(&(Arc::clone(name), index)).map(|(_, t)| t)
    }

    /// Look up a type variable's binding.
    pub fn lookup_type(&self, name: &Symbol, index: usize) -> Option<&Typ> {
        self.tyenv.get(&(Arc::clone(name), index)).map(|(_, t)| t)
    }

    // =================================================================
    // Update
    // =================================================================

    /// Bind a term variable. Panics if the index exceeds maxidx.
    pub fn update(&mut self, name: Symbol, index: usize, typ: Typ, term: Term) {
        assert!(index <= self.maxidx, "Envir.update: index {index} > maxidx {}", self.maxidx);
        self.tenv.insert((name, index), (typ, term));
    }

    /// Bind a type variable.
    pub fn update_type(&mut self, name: Symbol, index: usize, sort: Sort, typ: Typ) {
        assert!(index <= self.maxidx, "Envir.update_type: index {index} > maxidx {}", self.maxidx);
        self.tyenv.insert((name, index), (sort, typ));
    }

    // =================================================================
    // Normalization
    // =================================================================

    /// Normalize a type: replace all bound TVars with their assignments.
    pub fn norm_type(&self, typ: &Typ) -> Typ {
        match typ {
            Typ::TVar { name, index, sort: _ } => {
                if let Some((_, assigned)) = self.tyenv.get(&(Arc::clone(name), *index)) {
                    self.norm_type(assigned) // recursive — assigned type may contain TVars
                } else {
                    typ.clone()
                }
            }
            Typ::Type { name, args } => {
                Typ::apply(Arc::clone(name), args.iter().map(|a| self.norm_type(a)).collect())
            }
            Typ::TFree { .. } => typ.clone(),
        }
    }

    /// Normalize a term: replace all bound Vars with their assignments,
    /// and apply type normalization to all embedded types.
    pub fn norm_term(&self, term: &Term) -> Term {
        match term {
            Term::Var { name, index, typ } => {
                let norm_typ = self.norm_type(typ);
                if let Some((_, assigned)) = self.tenv.get(&(Arc::clone(name), *index)) {
                    self.norm_term(assigned)
                } else {
                    Term::var(Arc::clone(name), *index, norm_typ)
                }
            }
            Term::Const { name, typ } => {
                Term::const_(Arc::clone(name), self.norm_type(typ))
            }
            Term::Free { name, typ } => {
                Term::free(Arc::clone(name), self.norm_type(typ))
            }
            Term::Bound(i) => Term::bound(*i),
            Term::Abs { name, typ, body } => {
                Term::abs(
                    Arc::clone(name),
                    self.norm_type(typ),
                    self.norm_term(body),
                )
            }
            Term::App { func, arg } => {
                let nf = self.norm_term(func);
                let na = self.norm_term(arg);
                // Beta-reduce: (λx. body) arg → body[x := arg]
                if let Term::Abs { body, .. } = &nf {
                    let reduced = crate::core::term_subst::subst_bounds(&[na], body);
                    return self.norm_term(&reduced);
                }
                Term::app(nf, na)
            }
        }
    }

    // =================================================================
    // Merge
    // =================================================================

    /// Merge two environments. The second environment's bindings
    /// take precedence on conflict.
    pub fn merge(&self, other: &Envir) -> Envir {
        let mut result = Envir::empty(usize::max(self.maxidx, other.maxidx));
        for (k, v) in &self.tenv {
            result.tenv.insert(k.clone(), v.clone());
        }
        for (k, v) in &self.tyenv {
            result.tyenv.insert(k.clone(), v.clone());
        }
        for (k, v) in &other.tenv {
            result.tenv.insert(k.clone(), v.clone());
        }
        for (k, v) in &other.tyenv {
            result.tyenv.insert(k.clone(), v.clone());
        }
        result
    }

    /// Check if the environment's maxidx is strictly above the given index
    /// (i.e., the index is within valid range).
    pub fn above(&self, index: usize) -> bool {
        index < self.maxidx
    }
}

impl Default for Envir {
    fn default() -> Self {
        Envir::init()
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_env() {
        let env = Envir::empty(10);
        assert_eq!(env.maxidx(), 10);
        assert!(env.is_empty());
    }

    #[test]
    fn test_genvar() {
        let mut env = Envir::init();
        let v1 = env.genvar("x", Typ::base("nat"));
        assert!(matches!(v1, Term::Var { .. }));
        if let Term::Var { name, index, .. } = &v1 {
            assert_eq!(name.as_ref(), "x");
            assert_eq!(*index, 1);
        }
    }

    #[test]
    fn test_update_and_lookup() {
        let mut env = Envir::empty(10);
        let name = Arc::<str>::from("x");
        let typ = Typ::base("nat");
        let term = Term::const_("zero", Typ::base("nat"));

        env.update(Arc::clone(&name), 0, typ.clone(), term.clone());
        let found = env.lookup(&name, 0);
        assert!(found.is_some());
        assert_eq!(found.unwrap(), &term);
    }

    #[test]
    fn test_norm_term() {
        let mut env = Envir::empty(10);
        let name = Arc::<str>::from("x");
        let nat = Typ::base("nat");
        let zero = Term::const_("zero", nat.clone());
        env.update(Arc::clone(&name), 0, nat.clone(), zero.clone());

        let var = Term::var("x", 0, nat);
        let normed = env.norm_term(&var);
        assert_eq!(normed, zero);
    }

    #[test]
    fn test_norm_type() {
        let mut env = Envir::empty(10);
        let name = Arc::<str>::from("'a");
        let sort = Sort::singleton("type");
        let nat = Typ::base("nat");
        env.update_type(Arc::clone(&name), 0, sort, nat.clone());

        let tvar = Typ::var("'a", 0, Sort::singleton("type"));
        let normed = env.norm_type(&tvar);
        assert_eq!(normed, nat);
    }

    #[test]
    fn test_merge() {
        let mut env1 = Envir::empty(10);
        let mut env2 = Envir::empty(20);

        let name = Arc::<str>::from("x");
        env1.update(Arc::clone(&name), 0, Typ::base("nat"), Term::bound(0));

        let name2 = Arc::<str>::from("y");
        env2.update(Arc::clone(&name2), 0, Typ::base("bool"), Term::bound(1));

        let merged = env1.merge(&env2);
        assert_eq!(merged.maxidx(), 20);
        assert!(merged.lookup(&name, 0).is_some());
        assert!(merged.lookup(&name2, 0).is_some());
    }
}
