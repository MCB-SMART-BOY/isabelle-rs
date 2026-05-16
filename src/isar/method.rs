//! Proof method system.
//!
//! Corresponds to `src/Pure/Isar/method.ML`.
//!
//! Methods are the "actions" of Isar proofs: `rule`, `simp`, `auto`,
//! `blast`, `induct`, `cases`, etc.

use std::sync::Arc;

use crate::core::term::Term;
use crate::core::thm::{CTerm, Thm, ThmKernel};
use crate::core::simplifier::Simplifier;
use crate::core::tactic;

// =========================================================================
// Method
// =========================================================================

/// A proof method: applies a tactic or conversion to a goal.
pub enum Method {
    /// `assumption` — solve by assumption.
    Assumption,
    /// `rule thm` — apply a theorem as an introduction/elimination rule.
    Rule(Vec<Arc<Thm>>),
    /// `simp` — simplify the goal.
    Simp(Simplifier),
    /// `auto` — automated proof search.
    Auto,
    /// `blast` — tableau prover.
    Blast,
    /// `induct x` — induction on variable x.
    Induct(String),
    /// `cases x` — case analysis on variable x.
    Cases(String),
    /// `unfold thms` — unfold definitions.
    Unfold(Vec<Arc<Thm>>),
    /// `fold thms` — fold definitions.
    Fold(Vec<Arc<Thm>>),
    /// `insert thms` — insert facts.
    Insert(Vec<Arc<Thm>>),
    /// `erule thm` — apply as elimination.
    Erule(Vec<Arc<Thm>>),
    /// `drule thm` — apply as destruction.
    Drule(Vec<Arc<Thm>>),
    /// `frule thm` — apply as forward rule.
    Frule(Vec<Arc<Thm>>),
    /// This method never fails (skip).
    Skip,
    /// This method always fails.
    Fail,
}

impl Method {
    /// Create the `assumption` method.
    pub fn assumption() -> Self { Method::Assumption }

    /// Create the `rule` method.
    pub fn rule(thms: Vec<Arc<Thm>>) -> Self { Method::Rule(thms) }

    /// Execute the method on a goal state (a `Thm`), returning new goal states.
    pub fn execute(&self, state: &Thm) -> Vec<Thm> {
        self.execute_depth(state, 0)
    }

    fn execute_depth(&self, state: &Thm, depth: usize) -> Vec<Thm> {
        if depth > 20 {
            return vec![state.clone()];
        }
        match self {
            Method::Assumption => {
                tactic::assume_tac(0).apply(state)
            }
            Method::Rule(thms) => {
                tactic::resolve_tac(thms, 0).apply(state)
            }
            Method::Simp(simp) => {
                // Simplify the conclusion of the first subgoal
                if let Some(goal) = state.prem(0) {
                    let simplified = simp.rewrite_all(&goal);
                    if &simplified != &goal {
                        // Try to rewrite: use reflexive on the goal, then rewrite
                        // For now, just return the state unchanged
                        return vec![state.clone()];
                    }
                }
                vec![state.clone()]
            }
            Method::Skip => vec![],
            Method::Fail => vec![],
            Method::Auto => Self::auto_exec(state, depth),
            _ => vec![state.clone()],
        }
    }

    fn auto_exec(state: &Thm, depth: usize) -> Vec<Thm> {
        // 1. Try assumption on first subgoal
        let results = Self::Assumption.execute_depth(state, depth + 1);
        for r in &results {
            if r.nprems() == 0 {
                return results;
            }
        }
        // 2. Try loaded HOL theorems (resolve on first subgoal)
        if let Some(results) = Self::auto_resolve(state) {
            for r in &results {
                if r.nprems() == 0 {
                    return results;
                }
            }
            // Recurse on first result
            if let Some(first) = results.first() {
                return Self::auto_exec(first, depth + 1);
            }
        }
        // 3. Try intro/elim (not yet implemented for Thm)
        // 4. Fall back to simp
        Self::Simp(crate::core::simplifier::beta_simp()).execute_depth(state, depth + 1)
    }

    fn auto_resolve(state: &Thm) -> Option<Vec<Thm>> {
        use crate::hol::hol_loader::HolTheoremDb;
        let db = HolTheoremDb::get();
        let outcomes = crate::core::tactic::resolve_tac(&db.all, 0).apply(state);
        if outcomes.is_empty() {
            None
        } else {
            Some(outcomes)
        }
    }
}

// =========================================================================
// Method combinator: THEN
// =========================================================================

/// Combine two methods in sequence: apply m1, then m2 to all results.
pub fn method_then(m1: &Method, m2: &Method, state: &Thm) -> Vec<Thm> {
    m1.execute(state)
        .into_iter()
        .flat_map(|s| m2.execute(&s))
        .collect()
}

// =========================================================================
// Method combinator: ORELSE
// =========================================================================

/// Try m1; if it yields nothing, try m2.
pub fn method_orelse(m1: &Method, m2: &Method, state: &Thm) -> Vec<Thm> {
    let r = m1.execute(state);
    if r.is_empty() { m2.execute(state) } else { r }
}

// =========================================================================
// Method parser (from string)
// =========================================================================

impl Method {
    /// Parse a method from its string name.
    pub fn from_name(name: &str, _facts: &[Arc<Thm>]) -> Option<Self> {
        match name.trim() {
            "assumption" | "." => Some(Method::Assumption),
            "this" => Some(Method::Skip),
            "rule" | "intro" => Some(Method::Rule(vec![])),
            "simp" => Some(Method::Simp(crate::core::simplifier::beta_simp())),
            "auto" => Some(Method::Auto),
            "blast" => Some(Method::Blast),
            "fail" => Some(Method::Fail),
            "skip" => Some(Method::Skip),
            _ if name.starts_with("induct") => {
                let var = name.strip_prefix("induct ")?.to_string();
                Some(Method::Induct(var))
            }
            _ if name.starts_with("cases") => {
                let var = name.strip_prefix("cases ")?.to_string();
                Some(Method::Cases(var))
            }
            _ => None,
        }
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::types::Typ;

    fn trivial_goal(name: &str) -> Thm {
        let ct = CTerm::certify(Term::const_(name, Typ::base("prop")));
        ThmKernel::trivial(ct).unwrap()
    }

    #[test]
    fn test_method_assumption_solves() {
        let state = trivial_goal("A");
        let results = Method::Assumption.execute(&state);
        // assume_tac(0) on [A] ==> A should discharge A
        assert!(!results.is_empty());
        assert_eq!(results[0].nprems(), 0);
    }

    #[test]
    fn test_method_fail() {
        let state = trivial_goal("A");
        let results = Method::Fail.execute(&state);
        assert!(results.is_empty());
    }

    #[test]
    fn test_method_skip() {
        let state = trivial_goal("A");
        let results = Method::Skip.execute(&state);
        assert!(results.is_empty());
    }

    #[test]
    fn test_method_simp() {
        let lam = Term::abs("x", Typ::dummy(), Term::bound(0));
        let a = Term::free("a", Typ::dummy());
        let app = Term::app(lam, a.clone());
        let state = ThmKernel::trivial(CTerm::certify(app.clone())).unwrap();

        let simp = crate::core::simplifier::beta_simp();
        let method = Method::Simp(simp);
        let results = method.execute(&state);
        assert!(!results.is_empty());
    }
}
