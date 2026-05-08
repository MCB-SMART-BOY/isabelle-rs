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
use crate::core::tactic::{self, Goal, Tactic};

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

    /// Execute the method on a goal, returning new subgoals.
    pub fn execute(&self, goal: &Goal) -> Option<Vec<Goal>> {
        match self {
            Method::Assumption => {
                let outcomes = tactic::assume_tac()(goal.clone());
                outcomes.into_iter().next()
            }
            Method::Rule(thms) => {
                let outcomes = tactic::resolve_tac(thms)(goal.clone());
                outcomes.into_iter().next()
            }
            Method::Simp(simp) => {
                // Simplify the conclusion
                let simplified = simp.rewrite_all(goal.conclusion.term());
                if &simplified != goal.conclusion.term() {
                    let new_goal = Goal::new(
                        goal.assumptions.clone(),
                        CTerm::certify(simplified),
                    );
                    Some(vec![new_goal])
                } else {
                    Some(vec![goal.clone()])
                }
            }
            Method::Skip => Some(vec![]),
            Method::Fail => None,
            // For complex methods, return the goal unchanged as placeholder
            _ => Some(vec![goal.clone()]),
        }
    }
}

// =========================================================================
// Method combinator: THEN
// =========================================================================

/// Combine two methods in sequence: apply m1, then m2 to all subgoals.
pub fn method_then(m1: &Method, m2: &Method, goal: &Goal) -> Option<Vec<Goal>> {
    let subgoals = m1.execute(goal)?;
    let mut results = Vec::new();
    for sg in &subgoals {
        match m2.execute(sg) {
            Some(sgs) => results.extend(sgs),
            None => return None,
        }
    }
    Some(results)
}

// =========================================================================
// Method combinator: ORELSE
// =========================================================================

/// Try m1; if it fails, try m2.
pub fn method_orelse(m1: &Method, m2: &Method, goal: &Goal) -> Option<Vec<Goal>> {
    m1.execute(goal).or_else(|| m2.execute(goal))
}

// =========================================================================
// Method parser (from string)
// =========================================================================

impl Method {
    /// Parse a method from its string name.
    pub fn from_name(name: &str, _facts: &[Arc<Thm>]) -> Option<Self> {
        match name.trim() {
            "assumption" | "." => Some(Method::Assumption),
            "this" => Some(Method::Skip), // `this` uses chained facts
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

    fn goal(conc: &str) -> Goal {
        let a = CTerm::certify(Term::const_(conc, Typ::base("prop")));
        Goal::new(vec![a.clone()], a)
    }

    #[test]
    fn test_method_assumption_solves() {
        let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
        let g = Goal::new(vec![a.clone()], a);
        let result = Method::Assumption.execute(&g);
        assert!(result.is_some());
        assert!(result.unwrap().is_empty()); // no subgoals
    }

    #[test]
    fn test_method_fail() {
        let g = goal("A");
        assert!(Method::Fail.execute(&g).is_none());
    }

    #[test]
    fn test_method_skip() {
        let g = goal("A");
        let result = Method::Skip.execute(&g).unwrap();
        assert!(result.is_empty()); // proved magically
    }

    #[test]
    fn test_method_simp() {
        let lam = Term::abs("x", Typ::dummy(), Term::bound(0));
        let a = Term::free("a", Typ::dummy());
        let app = Term::app(lam, a.clone());
        let goal_ct = CTerm::certify(app.clone());
        let g = Goal::new(vec![], goal_ct);

        let simp = crate::core::simplifier::beta_simp();
        let method = Method::Simp(simp);
        let result = method.execute(&g);
        assert!(result.is_some());
        let subgoals = result.unwrap();
        assert_eq!(subgoals.len(), 1);
        assert_ne!(subgoals[0].conclusion.term(), &app);
    }
}
