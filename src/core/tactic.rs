//! Tactics and tacticals — the proof search combinators.
//!
//! Corresponds to `src/Pure/tactic.ML` + `src/Pure/tactical.ML`.
//!
//! ## Isabelle's tactic philosophy
//!
//! A **tactic** is a function from a goal to a (lazy) sequence of outcomes.
//! Tactics can succeed (producing subgoals), fail (producing nothing),
//! or produce multiple outcomes (search branching).
//!
//! **Tacticals** combine tactics: `THEN`, `ORELSE`, `REPEAT`, etc.

use std::sync::Arc;

use super::envir::Envir;
use super::term::Term;
use super::thm::{CTerm, Thm, ThmKernel};
use super::types::Typ;
use super::logic::Pure;
use super::unify::{self, UnifyConfig};

// =========================================================================
// Goal — a single proof obligation
// =========================================================================

/// A goal: a list of assumptions and a conclusion to prove.
///
/// In Isabelle's kernel, a goal `[A1, ..., An] ⇒ C` is represented
/// as the theorem `[A1, ..., An] ⊢ C`.
#[derive(Clone, Debug)]
pub struct Goal {
    /// The assumptions (hypotheses).
    pub assumptions: Vec<CTerm>,
    /// The conclusion to prove.
    pub conclusion: CTerm,
}

impl Goal {
    pub fn new(assumptions: Vec<CTerm>, conclusion: CTerm) -> Self {
        Goal { assumptions, conclusion }
    }
}

// =========================================================================
// Tactic — the core type
// =========================================================================

/// A tactic transforms a goal into zero or more sequences of subgoals.
/// Each outcome is a list of new subgoals (empty = proved).
pub type Tactic = Box<dyn Fn(Goal) -> Vec<Vec<Goal>> + Send + Sync>;

// =========================================================================
// Basic tactics
// =========================================================================

/// `all_tac`: identity tactic — passes the goal through unchanged.
pub fn all_tac() -> Tactic {
    Box::new(|goal| vec![vec![goal]])
}

/// `no_tac`: always fails — returns no outcomes.
pub fn no_tac() -> Tactic {
    Box::new(|_| vec![])
}

/// `assume_tac`: solve the goal if the conclusion matches one of the assumptions.
/// Equivalent to Isabelle's `assume_tac`.
pub fn assume_tac() -> Tactic {
    Box::new(|goal| {
        let config = UnifyConfig::default();
        for assm in &goal.assumptions {
            let env = Envir::init();
            if let Some(_) = unify::unifiers(
                &env,
                &[(assm.term().clone(), goal.conclusion.term().clone())],
                &config,
            ) {
                return vec![vec![]]; // proved!
            }
        }
        vec![] // no match found
    })
}

/// `resolve_tac`: apply a list of theorems as resolution rules.
/// Each theorem `Γ ⊢ P` is used to close the goal if `P` unifies with
/// the goal's conclusion (and the assumptions are discharged).
pub fn resolve_tac(theorems: &[Arc<Thm>]) -> Tactic {
    let thms = theorems.to_vec();
    Box::new(move |goal| {
        let mut outcomes = Vec::new();
        let config = UnifyConfig::default();
        for thm in &thms {
            let env = Envir::init();
            // Try to unify the theorem's conclusion with the goal's conclusion
            if let Some(env) = unify::unifiers(
                &env,
                &[(thm.prop().term().clone(), goal.conclusion.term().clone())],
                &config,
            ) {
                // Success: goal is solved; remaining subgoals are
                // the theorem's hypotheses instantiated
                let subgoals: Vec<Goal> = thm.hyps()
                    .iter()
                    .map(|h| {
                        let instantiated = env.norm_term(h.term());
                        Goal::new(vec![], CTerm::certify(instantiated))
                    })
                    .collect();
                outcomes.push(subgoals);
            }
        }
        outcomes
    })
}

// =========================================================================
// Tacticals — tactic combinators
// =========================================================================

/// `THEN`: sequence two tactics. `tac1 THEN tac2` applies `tac1` first,
/// then applies `tac2` to ALL resulting subgoals.
pub fn then_tac(tac1: Tactic, tac2: Tactic) -> Tactic {
    Box::new(move |goal| {
        let mut results = Vec::new();
        for subgoals in tac1(goal.clone()) {
            // For each outcome of tac1, apply tac2 to each subgoal
            if subgoals.is_empty() {
                results.push(vec![]); // tac1 already proved it
            } else {
                // Apply tac2 to each subgoal and collect all combinations
                let mut current = vec![vec![]];
                for sg in &subgoals {
                    let sg_results = tac2(sg.clone());
                    let mut new_current = Vec::new();
                    for prefix in &current {
                        for sg_outcome in &sg_results {
                            let mut combined = prefix.clone();
                            combined.extend(sg_outcome.clone());
                            new_current.push(combined);
                        }
                    }
                    current = new_current;
                }
                results.extend(current);
            }
        }
        results
    })
}

/// `ORELSE`: try first tactic; if it fails, try the second.
pub fn orelse_tac(tac1: Tactic, tac2: Tactic) -> Tactic {
    Box::new(move |goal| {
        let results = tac1(goal.clone());
        if results.is_empty() {
            tac2(goal)
        } else {
            results
        }
    })
}

/// `REPEAT`: apply a tactic repeatedly until it fails.
pub fn repeat_tac(tac: Tactic) -> Tactic {
    Box::new(move |goal| {
        let mut all_outcomes = Vec::new();
        let mut current_goals = vec![goal];
        let mut changed = true;
        while changed {
            changed = false;
            let mut new_goals = Vec::new();
            for g in &current_goals {
                let results = tac(g.clone());
                if results.is_empty() {
                    new_goals.push(g.clone()); // keep this goal
                } else {
                    changed = true;
                    for outcome in results {
                        new_goals.extend(outcome);
                    }
                }
            }
            current_goals = new_goals;
        }
        all_outcomes.push(current_goals);
        all_outcomes
    })
}

/// `EVERY`: apply a list of tactics in sequence (like `THEN` chain).
pub fn every_tac(tactics: Vec<Tactic>) -> Tactic {
    tactics.into_iter().fold(all_tac(), |acc, tac| then_tac(acc, tac))
}

/// `FIRST`: try a list of tactics, return the first successful outcome.
pub fn first_tac(tactics: Vec<Tactic>) -> Tactic {
    tactics.into_iter().fold(no_tac(), |acc, tac| orelse_tac(tac, acc))
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

    #[test]
    fn test_assume_tac_solves() {
        let a = prop("A");
        let goal = Goal::new(vec![a.clone()], a.clone());
        let outcomes = assume_tac()(goal);
        assert!(!outcomes.is_empty());
        assert!(outcomes[0].is_empty()); // no subgoals left
    }

    #[test]
    fn test_assume_tac_fails() {
        let a = prop("A");
        let b = prop("B");
        let goal = Goal::new(vec![a], b);
        let outcomes = assume_tac()(goal);
        assert!(outcomes.is_empty());
    }

    #[test]
    fn test_all_tac() {
        let a = prop("A");
        let goal = Goal::new(vec![], a);
        let outcomes = all_tac()(goal);
        assert_eq!(outcomes.len(), 1);
        assert_eq!(outcomes[0].len(), 1);
    }

    #[test]
    fn test_no_tac() {
        let a = prop("A");
        let goal = Goal::new(vec![], a);
        let outcomes = no_tac()(goal);
        assert!(outcomes.is_empty());
    }

    #[test]
    fn test_then_orelse() {
        let a = prop("A");
        let goal = Goal::new(vec![a.clone()], a);
        // (assume_tac ORELSE all_tac) THEN assume_tac
        let tac = then_tac(
            orelse_tac(assume_tac(), all_tac()),
            assume_tac(),
        );
        let outcomes = tac(goal);
        assert!(!outcomes.is_empty());
    }
}
