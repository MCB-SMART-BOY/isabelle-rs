//! Tactics and tacticals — the proof search combinators.
//!
//! ## V3: Tactic as AST
//!
//! Instead of `Box<dyn Fn>`, tactics are an `enum` (AST), enabling
//! Display/Debug, analysis, optimization, and serialization.

use std::fmt;
use std::sync::Arc;

use super::envir::Envir;
use super::thm::{CTerm, Thm};
use super::unify::{self, UnifyConfig};

#[derive(Clone, Debug)]
pub struct Goal {
    pub assumptions: Vec<CTerm>,
    pub conclusion: CTerm,
}

impl Goal {
    pub fn new(assumptions: Vec<CTerm>, conclusion: CTerm) -> Self {
        Goal { assumptions, conclusion }
    }
}

// =========================================================================
// Tactic AST
// =========================================================================

#[derive(Clone)]
pub enum Tactic {
    All,
    No,
    Assume,
    Resolve(Vec<Arc<Thm>>),
    Then(Box<Tactic>, Box<Tactic>),
    OrElse(Box<Tactic>, Box<Tactic>),
    Repeat(Box<Tactic>),
    Every(Vec<Tactic>),
    First(Vec<Tactic>),
}

impl Tactic {
    pub fn apply(&self, goal: &Goal) -> Vec<Vec<Goal>> {
        match self {
            Tactic::All => vec![vec![goal.clone()]],
            Tactic::No => vec![],
            Tactic::Assume => Self::apply_assume(goal),
            Tactic::Resolve(thms) => Self::apply_resolve(thms, goal),
            Tactic::Then(t1, t2) => Self::apply_then(t1, t2, goal),
            Tactic::OrElse(t1, t2) => {
                let r = t1.apply(goal);
                if r.is_empty() { t2.apply(goal) } else { r }
            }
            Tactic::Repeat(t) => Self::apply_repeat(t, goal),
            Tactic::Every(ts) => ts.iter().fold(Tactic::All, |a, t|
                Tactic::Then(Box::new(a), Box::new(t.clone()))).apply(goal),
            Tactic::First(ts) => ts.iter().fold(Tactic::No, |a, t|
                Tactic::OrElse(Box::new(t.clone()), Box::new(a))).apply(goal),
        }
    }

    fn apply_assume(goal: &Goal) -> Vec<Vec<Goal>> {
        let config = UnifyConfig::default();
        for a in &goal.assumptions {
            let env = Envir::init();
            if unify::unifiers(&env, &[(a.term().clone(), goal.conclusion.term().clone())], &config).is_some() {
                return vec![vec![]];
            }
        }
        vec![]
    }

    fn apply_resolve(thms: &[Arc<Thm>], goal: &Goal) -> Vec<Vec<Goal>> {
        let mut out = Vec::new();
        let config = UnifyConfig::default();
        for thm in thms {
            let env = Envir::init();
            if let Some(env) = unify::unifiers(&env, &[(thm.prop().term().clone(), goal.conclusion.term().clone())], &config) {
                let sgs: Vec<Goal> = thm.hyps().iter().map(|h| {
                    Goal::new(vec![], CTerm::certify(env.norm_term(h.term())))
                }).collect();
                out.push(sgs);
            }
        }
        out
    }

    fn apply_then(t1: &Tactic, t2: &Tactic, goal: &Goal) -> Vec<Vec<Goal>> {
        let mut results = Vec::new();
        for sgs in t1.apply(goal) {
            if sgs.is_empty() {
                results.push(vec![]);
            } else {
                let mut current: Vec<Vec<Goal>> = vec![vec![]];
                for sg in &sgs {
                    let sg_r = t2.apply(sg);
                    let mut nc = Vec::new();
                    for p in &current {
                        for o in &sg_r {
                            let mut c = p.clone();
                            c.extend(o.clone());
                            nc.push(c);
                        }
                    }
                    current = nc;
                }
                results.extend(current);
            }
        }
        results
    }

    fn apply_repeat(t: &Tactic, goal: &Goal) -> Vec<Vec<Goal>> {
        let mut current = vec![goal.clone()];
        let mut changed = true;
        while changed {
            changed = false;
            let mut ng = Vec::new();
            for g in &current {
                let r = t.apply(g);
                if r.is_empty() { ng.push(g.clone()); }
                else { changed = true; for o in r { ng.extend(o); } }
            }
            current = ng;
        }
        vec![current]
    }
}

impl fmt::Debug for Tactic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Tactic::All => write!(f, "all"),
            Tactic::No => write!(f, "no"),
            Tactic::Assume => write!(f, "assume"),
            Tactic::Resolve(ts) => write!(f, "resolve({})", ts.len()),
            Tactic::Then(a, b) => write!(f, "({:?} THEN {:?})", a, b),
            Tactic::OrElse(a, b) => write!(f, "({:?} ORELSE {:?})", a, b),
            Tactic::Repeat(t) => write!(f, "REPEAT({:?})", t),
            Tactic::Every(ts) => write!(f, "EVERY({})", ts.len()),
            Tactic::First(ts) => write!(f, "FIRST({})", ts.len()),
        }
    }
}

impl fmt::Display for Tactic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { fmt::Debug::fmt(self, f) }
}

// =========================================================================
// Constructor functions (backward-compatible)
// =========================================================================

pub fn all_tac() -> Tactic { Tactic::All }
pub fn no_tac() -> Tactic { Tactic::No }
pub fn assume_tac() -> Tactic { Tactic::Assume }
pub fn resolve_tac(thms: &[Arc<Thm>]) -> Tactic { Tactic::Resolve(thms.to_vec()) }
pub fn then_tac(t1: Tactic, t2: Tactic) -> Tactic { Tactic::Then(Box::new(t1), Box::new(t2)) }
pub fn orelse_tac(t1: Tactic, t2: Tactic) -> Tactic { Tactic::OrElse(Box::new(t1), Box::new(t2)) }
pub fn repeat_tac(t: Tactic) -> Tactic { Tactic::Repeat(Box::new(t)) }
pub fn every_tac(ts: Vec<Tactic>) -> Tactic { Tactic::Every(ts) }
pub fn first_tac(ts: Vec<Tactic>) -> Tactic { Tactic::First(ts) }

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::term::Term;
    use crate::core::types::Typ;

    fn prop(name: &str) -> CTerm {
        CTerm::certify(Term::const_(name, Typ::base("prop")))
    }

    #[test]
    fn test_assume_tac_solves() {
        let a = prop("A");
        let goal = Goal::new(vec![a.clone()], a.clone());
        let outcomes = assume_tac().apply(&goal);
        assert!(!outcomes.is_empty());
        assert!(outcomes[0].is_empty());
    }

    #[test]
    fn test_assume_tac_fails() {
        let a = prop("A");
        let b = prop("B");
        let outcomes = assume_tac().apply(&Goal::new(vec![a], b));
        assert!(outcomes.is_empty());
    }

    #[test]
    fn test_all_tac() {
        let a = prop("A");
        let outcomes = all_tac().apply(&Goal::new(vec![], a));
        assert_eq!(outcomes.len(), 1);
        assert_eq!(outcomes[0].len(), 1);
    }

    #[test]
    fn test_no_tac() {
        let a = prop("A");
        assert!(no_tac().apply(&Goal::new(vec![], a)).is_empty());
    }

    #[test]
    fn test_then_orelse() {
        let a = prop("A");
        let goal = Goal::new(vec![a.clone()], a);
        let tac = then_tac(orelse_tac(assume_tac(), all_tac()), assume_tac());
        assert!(!tac.apply(&goal).is_empty());
    }
}
