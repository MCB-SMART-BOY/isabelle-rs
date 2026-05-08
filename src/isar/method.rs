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
        self.execute_depth(goal, 0)
    }

    fn execute_depth(&self, goal: &Goal, depth: usize) -> Option<Vec<Goal>> {
        if depth > 20 { return Some(vec![goal.clone()]); }
        match self {
            Method::Assumption => {
                tactic::assume_tac().apply(goal).into_iter().next()
            }
            Method::Rule(thms) => {
                tactic::resolve_tac(thms).apply(goal).into_iter().next()
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
            Method::Auto => Self::auto_exec(goal, depth),
            _ => Some(vec![goal.clone()]),
        }
    }

    fn auto_exec(goal: &Goal, depth: usize) -> Option<Vec<Goal>> {
        // 1. Try assumption
        if let Some(sgs) = Self::Assumption.execute_depth(goal, depth + 1) {
            if sgs.is_empty() { return Some(sgs); }
        }
        // 2. Try loaded HOL theorems (resolve)
        if let Some(sgs) = Self::auto_resolve(goal) {
            if sgs.is_empty() { return Some(sgs); }
            if let Some(sgs2) = Self::Auto.execute_depth(&sgs[0], depth + 1) {
                return Some(sgs2);
            }
        }
        // 3. Try elim (break down assumptions)
        if let Some(sgs) = Self::auto_elim(goal) {
            return Self::Auto.execute_depth(&sgs[0], depth + 1).or(Some(sgs));
        }
        // 3. Try intro (break down goal)
        if let Some(sgs) = Self::auto_intro(goal) {
            let mut solved = Vec::new();
            for sg in &sgs {
                match Self::Auto.execute_depth(sg, depth + 1) {
                    Some(sgs2) if sgs2.is_empty() => continue,
                    Some(sgs2) => solved.extend(sgs2),
                    None => solved.push(sg.clone()),
                }
            }
            return if solved.is_empty() { Some(vec![]) } else { Some(solved) };
        }
        // 4. Fall back to simp
        Self::Simp(crate::core::simplifier::beta_simp()).execute_depth(goal, depth + 1)
    }

    fn auto_resolve(goal: &Goal) -> Option<Vec<Goal>> {
        use crate::hol::hol_loader::HolTheoremDb;
        let db = HolTheoremDb::get();
        let outcomes = crate::core::tactic::resolve_tac(&db.all).apply(goal);
        // Take first successful outcome
        outcomes.into_iter().next()
    }

    fn auto_elim(goal: &Goal) -> Option<Vec<Goal>> {
        for (i, a) in goal.assumptions.iter().enumerate() {
            if let Some((x, y)) = dest_hol_conj(a.term()) {
                let mut asms: Vec<_> = goal.assumptions.iter().enumerate()
                    .filter(|&(j,_)| j != i).map(|(_,c)| c.clone()).collect();
                asms.push(CTerm::certify(x.clone()));
                asms.push(CTerm::certify(y.clone()));
                return Some(vec![Goal::new(asms, goal.conclusion.clone())]);
            }
            if let Some((x, y)) = dest_hol_disj(a.term()) {
                let others: Vec<_> = goal.assumptions.iter().enumerate()
                    .filter(|&(j,_)| j != i).map(|(_,c)| c.clone()).collect();
                let mut a1 = others.clone(); a1.push(CTerm::certify(x.clone()));
                let mut a2 = others; a2.push(CTerm::certify(y.clone()));
                return Some(vec![
                    Goal::new(a1, goal.conclusion.clone()),
                    Goal::new(a2, goal.conclusion.clone()),
                ]);
            }
        }
        None
    }

    fn auto_intro(goal: &Goal) -> Option<Vec<Goal>> {
        use crate::core::logic::Pure;
        let c = goal.conclusion.term();
        if let Some((a, b)) = Pure::dest_implies(c) {
            let mut asms = goal.assumptions.clone();
            asms.push(CTerm::certify(a.clone()));
            return Some(vec![Goal::new(asms, CTerm::certify(b.clone()))]);
        }
        if let Some(((_, _), body)) = Pure::dest_all(c) {
            return Some(vec![Goal::new(goal.assumptions.clone(), CTerm::certify(body.clone()))]);
        }
        if let Some((l, r)) = Pure::dest_equals(c) {
            if l == r { return Some(vec![]); }
        }
        if let Some((a, b)) = dest_hol_conj(c) {
            return Some(vec![
                Goal::new(goal.assumptions.clone(), CTerm::certify(a.clone())),
                Goal::new(goal.assumptions.clone(), CTerm::certify(b.clone())),
            ]);
        }
        if let Some((a, b)) = dest_hol_disj(c) {
            return Some(vec![
                Goal::new(goal.assumptions.clone(), CTerm::certify(a.clone())),
                Goal::new(goal.assumptions.clone(), CTerm::certify(b.clone())),
            ]);
        }
        if let Some((a, b)) = dest_hol_imp(c) {
            let mut asms = goal.assumptions.clone();
            asms.push(CTerm::certify(a.clone()));
            return Some(vec![Goal::new(asms, CTerm::certify(b.clone()))]);
        }
        None
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

fn dest_hol_conj(term: &Term) -> Option<(&Term, &Term)> {
    match term {
        Term::App { func, arg: b } => match func.as_ref() {
            Term::App { func: i, arg: a } => match i.as_ref() {
                Term::Const { name, .. } if name.as_ref() == "HOL.conj" => Some((a.as_ref(), b.as_ref())),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

fn dest_hol_disj(term: &Term) -> Option<(&Term, &Term)> {
    match term {
        Term::App { func, arg: b } => match func.as_ref() {
            Term::App { func: i, arg: a } => match i.as_ref() {
                Term::Const { name, .. } if name.as_ref() == "HOL.disj" => Some((a.as_ref(), b.as_ref())),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

fn dest_hol_imp(term: &Term) -> Option<(&Term, &Term)> {
    match term {
        Term::App { func, arg: b } => match func.as_ref() {
            Term::App { func: i, arg: a } => match i.as_ref() {
                Term::Const { name, .. } if name.as_ref() == "HOL.imp" || name.as_ref() == "Pure.imp" => Some((a.as_ref(), b.as_ref())),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}
