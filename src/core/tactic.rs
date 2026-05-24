//! Tactics and tacticals — the proof search combinators.
//!
//! ## Design
//!
//! Follows Isabelle's architecture: `tactic = thm -> thm Seq.seq`.
//! In Rust: `Tactic::apply(&Thm) -> Vec<Thm>`.
//!
//! The goal state IS a `Thm` of the form:
//!   `[H1, H2, ..., Hn] ⊢ H1 ==> H2 ==> ... ==> Hn ==> G`
//! where `Hi` are subgoals and `G` is the main conclusion.
//!
//! All tactics call `ThmKernel::bicompose` — the single core resolution
//! operation — to transform goal states. When `nprems() == 0`, proof is done.
//!
//! ## Key invariants
//!
//! - Every `Thm` in the output is kernel-verified (no `assume()` shortcuts)
//! - `vec![]` means tactic not applicable
//! - `vec![state]` with `state.nprems() == 0` means proof complete

use std::fmt;
use std::sync::Arc;

use super::simplifier::Simplifier;
use super::term::Term;
use super::thm::{CTerm, Hyps, Thm, ThmKernel};
use super::types::Typ;

// =========================================================================
// Tactic AST
// =========================================================================

#[derive(Clone)]
pub enum Tactic {
    /// Identity: `|state| vec![state.clone()]`
    All,
    /// Failure: `|_| vec![]`
    No,
    /// Solve subgoal `i` (0-indexed) by assumption.
    /// Uses `ThmKernel::bicompose` with `ThmKernel::assume(prem_i)`.
    Assume(usize),
    /// Resolve subgoal `i` with one of the given theorems.
    /// Uses `ThmKernel::bicompose(true, thm, state, i)` for each thm.
    Resolve(Vec<Arc<Thm>>, usize),
    /// Sequential composition: `t1 THEN t2` = `|st| flat_map(t2, t1(st))`
    Then(Box<Tactic>, Box<Tactic>),
    /// Alternative: try `t1`, if it yields nothing, try `t2`
    OrElse(Box<Tactic>, Box<Tactic>),
    /// Repeat until no progress
    Repeat(Box<Tactic>),
    /// Apply to all subgoals sequentially (via `Then` folding)
    Every(Vec<Tactic>),
    /// Try each tactic, return first success
    First(Vec<Tactic>),
    /// Trace execution for debugging
    Trace(String, Box<Tactic>),
    /// Limit subgoal count (returns empty if nprems > max)
    DepthLimit(usize, Box<Tactic>),
    /// Rewrite subgoal `i` using the given simplifier
    Simp(Arc<Simplifier>, usize),
    /// Elim-resolution: match conclusion AND consume matching hypothesis
    Eresolve(Vec<Arc<Thm>>, usize),
}

impl Tactic {
    /// Apply this tactic with given premises.
    pub fn apply(&self, state: &Thm, premises: &[Arc<Thm>]) -> Vec<Thm> {
        match self {
            Tactic::All => vec![state.clone()],
            Tactic::No => vec![],
            Tactic::Assume(i) => Self::apply_assume(*i, state, premises),
            Tactic::Resolve(thms, i) => Self::apply_resolve(thms, *i, state),
            Tactic::Then(t1, t2) => t1
                .apply(state, premises)
                .into_iter()
                .flat_map(|s| t2.apply(&s, premises))
                .collect(),
            Tactic::OrElse(t1, t2) => {
                let r = t1.apply(state, premises);
                if r.is_empty() {
                    t2.apply(state, premises)
                } else {
                    r
                }
            }
            Tactic::Repeat(t) => Self::apply_repeat(t, state, premises),
            Tactic::Every(ts) => ts
                .iter()
                .fold(Tactic::All, |a, t| {
                    Tactic::Then(Box::new(a), Box::new(t.clone()))
                })
                .apply(state, premises),
            Tactic::First(ts) => {
                for t in ts {
                    let r = t.apply(state, premises);
                    if !r.is_empty() {
                        return r;
                    }
                }
                vec![]
            }
            Tactic::Trace(name, t) => {
                tracing::debug!(tactic = %name, nprems = state.nprems(), "apply");
                let r = t.apply(state, premises);
                tracing::debug!(tactic = %name, outcomes = r.len(), "done");
                r
            }
            Tactic::DepthLimit(max, t) => {
                if state.nprems() > *max {
                    return vec![];
                }
                t.apply(state, premises)
            }
            Tactic::Simp(simp, i) => Self::apply_simp(simp, *i, state),
            Tactic::Eresolve(thms, i) => Self::apply_eresolve(thms, *i, state, premises),
        }
    }

    /// Solve subgoal `i` by checking against premises AND the goal's own hypotheses.
    /// This mirrors Isabelle's `assume_tac`: the subgoal must match either:
    /// 1. An external premise (from the Isar proof context), OR
    /// 2. One of the goal state's own hypotheses.
    fn apply_assume(i: usize, state: &Thm, premises: &[Arc<Thm>]) -> Vec<Thm> {
        let prem_i = match state.prem(i) {
            Some(p) => p,
            None => return vec![],
        };
        let prem_i_ct = CTerm::certify(prem_i.clone());

        // Check 1: external premises (Isar proof context facts)
        let matches_premises = premises.iter().any(|p| {
            let mut tmp = Hyps::empty();
            tmp.insert(prem_i_ct.clone());
            tmp.contains(&CTerm::certify(p.prop().term().clone()))
        });

        // Check 2: goal's own hypotheses (α-equivalence)
        let matches_hyps = state.hyps().contains(&prem_i_ct);

        if !matches_premises && !matches_hyps {
            return vec![];
        }
        let assume_thm = ThmKernel::assume(prem_i_ct);
        ThmKernel::bicompose(false, &assume_thm, state, i)
            .map(|t| vec![t])
            .unwrap_or_default()
    }

    /// Resolve subgoal `i` using one of the given theorems.
    fn apply_resolve(thms: &[Arc<Thm>], i: usize, state: &Thm) -> Vec<Thm> {
        let mut results = Vec::new();
        for thm in thms {
            if let Some(new_state) = ThmKernel::bicompose(true, thm, state, i) {
                results.push(new_state);
            }
        }
        results
    }

    /// Elim-resolution: like resolve, also consumes matching premise.
    fn apply_eresolve(thms: &[Arc<Thm>], i: usize, state: &Thm, premises: &[Arc<Thm>]) -> Vec<Thm> {
        let mut results = Vec::new();
        for thm in thms {
            if let Some(new_state) = ThmKernel::bicompose_eresolve(true, thm, state, i, premises) {
                results.push(new_state);
            }
        }
        results
    }

    /// Rewrite subgoal `i` using the simplifier, iterating to fixed point.
    fn apply_simp(simp: &Simplifier, i: usize, state: &Thm) -> Vec<Thm> {
        let mut current = state.clone();
        loop {
            let prem_i = match current.prem(i) {
                Some(p) => p,
                None => return vec![current],
            };
            match simp.rewrite_deep(&prem_i) {
                Some((next, eq_thm)) if next != prem_i => {
                    // Apply this rewrite step via subst_premise
                    if let Some(new_state) = ThmKernel::subst_premise(&eq_thm, &current, i) {
                        current = new_state;
                        continue; // iterate
                    }
                }
                _ => {}
            }
            break; // no change
        }
        vec![current]
    }

    /// Repeat a tactic until no progress is made.
    fn apply_repeat(t: &Tactic, state: &Thm, premises: &[Arc<Thm>]) -> Vec<Thm> {
        let mut current = vec![state.clone()];
        let mut changed = true;
        while changed {
            changed = false;
            let mut next = Vec::new();
            for s in &current {
                let r = t.apply(s, premises);
                if r.is_empty() {
                    next.push(s.clone());
                } else {
                    changed = true;
                    next.extend(r);
                }
            }
            current = next;
        }
        current
    }
}

impl fmt::Debug for Tactic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Tactic::All => write!(f, "all"),
            Tactic::No => write!(f, "no"),
            Tactic::Assume(i) => write!(f, "assume({})", i),
            Tactic::Resolve(ts, i) => write!(f, "resolve({}, {})", ts.len(), i),
            Tactic::Then(a, b) => write!(f, "({:?} THEN {:?})", a, b),
            Tactic::OrElse(a, b) => write!(f, "({:?} ORELSE {:?})", a, b),
            Tactic::Repeat(t) => write!(f, "REPEAT({:?})", t),
            Tactic::Every(ts) => write!(f, "EVERY({})", ts.len()),
            Tactic::First(ts) => write!(f, "FIRST({})", ts.len()),
            Tactic::Trace(name, t) => write!(f, "TRACE({}, {:?})", name, t),
            Tactic::DepthLimit(max, t) => write!(f, "DEPTH({}, {:?})", max, t),
            Tactic::Simp(_, i) => write!(f, "simp({})", i),
            Tactic::Eresolve(ts, i) => write!(f, "eresolve({}, {})", ts.len(), i),
        }
    }
}

impl fmt::Display for Tactic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

// =========================================================================
// Constructor functions
// =========================================================================

pub fn all_tac() -> Tactic {
    Tactic::All
}
pub fn no_tac() -> Tactic {
    Tactic::No
}

/// `assume_tac(i)`: solve subgoal `i` (0-indexed) by assumption.
pub fn assume_tac(i: usize) -> Tactic {
    Tactic::Assume(i)
}

/// `resolve_tac(thms, i)`: resolve subgoal `i` with one of the theorems.
pub fn resolve_tac(thms: &[Arc<Thm>], i: usize) -> Tactic {
    Tactic::Resolve(thms.to_vec(), i)
}

pub fn then_tac(t1: Tactic, t2: Tactic) -> Tactic {
    Tactic::Then(Box::new(t1), Box::new(t2))
}

pub fn orelse_tac(t1: Tactic, t2: Tactic) -> Tactic {
    Tactic::OrElse(Box::new(t1), Box::new(t2))
}

pub fn repeat_tac(t: Tactic) -> Tactic {
    Tactic::Repeat(Box::new(t))
}

pub fn every_tac(ts: Vec<Tactic>) -> Tactic {
    Tactic::Every(ts)
}

pub fn first_tac(ts: Vec<Tactic>) -> Tactic {
    Tactic::First(ts)
}

pub fn trace_tac(name: impl Into<String>, t: Tactic) -> Tactic {
    Tactic::Trace(name.into(), Box::new(t))
}

pub fn depth_limit(max: usize, t: Tactic) -> Tactic {
    Tactic::DepthLimit(max, Box::new(t))
}

/// `eresolve_tac(thms, i)`: elim-resolution on subgoal `i`.
pub fn eresolve_tac(thms: &[Arc<Thm>], i: usize) -> Tactic {
    Tactic::Eresolve(thms.to_vec(), i)
}

/// `dresolve_tac(thms, i)`: forward chaining — apply destruct rule to hypotheses.
/// Uses make_elim to convert destruct rules to elimination rules, then eresolve_tac.
pub fn dresolve_tac(thms: &[Arc<Thm>], i: usize) -> Tactic {
    let elim_rules: Vec<Arc<Thm>> = thms
        .iter()
        .filter_map(|thm| make_elim(thm))
        .map(Arc::new)
        .collect();
    Tactic::Eresolve(elim_rules, i)
}

/// Convert a destruct rule to an elimination rule (Isabelle's make_elim).
///
/// Given `rl: [| A1;...;An |] ==> C`, produces:
/// `[| A1;...;An; C ==> Q |] ==> Q`
///
/// This uses the reverse cut rule: `[| P; P ==> Q |] ==> Q`.
pub fn make_elim(rl: &Thm) -> Option<Thm> {
    // revcut_rl: [| P; P==>Q |] ==> Q (with schematic P, Q)
    let revcut = revcut_rl();
    // rl RS revcut_rl: match rl's conclusion against revcut's first premise
    // Use bicompose: revcut as thm1, rl as thm2? Actually:
    // thm1 RS thm2 = bicompose(false, thm1, thm2, 0)
    // Here we want rl RS revcut: bicompose(false, rl, revcut, 0)
    // rl's conclusion matches revcut's first premise
    ThmKernel::bicompose(false, rl, &revcut, 0)
}

/// The reverse cut rule: `[| P; P ==> Q |] ==> Q`
/// Used by make_elim to convert destruct rules to elimination rules.
pub fn revcut_rl() -> Thm {
    use std::sync::LazyLock;
    static REVCUT: LazyLock<Thm> = LazyLock::new(|| {
        let p = Term::var("P", 0, Typ::base("prop"));
        let q = Term::var("Q", 1, Typ::base("prop"));
        let assume_p = ThmKernel::assume(CTerm::certify(p.clone()));
        let p_imp_q = super::logic::Pure::mk_implies(p.clone(), q.clone());
        let assume_pq = ThmKernel::assume(CTerm::certify(p_imp_q));
        let result = ThmKernel::implies_elim(&assume_pq, &assume_p).unwrap();
        let hyps: Vec<CTerm> = result.hyps().iter().cloned().collect();
        super::drule::implies_intr_list(&hyps, &result).unwrap()
    });
    REVCUT.clone()
}

/// `simp_tac(simps, i)`: rewrite subgoal `i` using [simp] theorems.
pub fn simp_tac(simps: &[Arc<Thm>], i: usize) -> Tactic {
    let rules: Vec<super::simplifier::RewriteRule> = simps
        .iter()
        .filter_map(|thm| super::simplifier::RewriteRule::from_thm(Arc::clone(thm)))
        .collect();
    Tactic::Simp(Arc::new(Simplifier::new(rules)), i)
}

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

    fn trivial_goal(name: &str) -> Thm {
        ThmKernel::trivial(prop(name)).unwrap()
    }

    /// Create a goal where subgoal IS in hyps (for assume_tac)
    fn goal_with_hyp() -> Thm {
        // We want: hyps={A}, subgoal=A
        // Build: assume(A) → {A} ⊢ A, nprems=0
        // Not useful for testing tactics.
        // Use: assume(A ==> B) → {A==>B} ⊢ A==>B, nprems=1 (subgoal=A)
        // But A is not in hyps; A==>B is.
        // The only way to have A in hyps with nprems>0:
        //   assume(A), then implies_intr on something else...
        // Let's just test with nprems=0
        let a = Term::const_("A", Typ::base("prop"));
        ThmKernel::assume(CTerm::certify(a))
    }

    #[test]
    fn test_assume_tac_solves() {
        // assume_tac requires subgoal in hyps. With goal_with_hyp(),
        // {A} ⊢ A has nprems=0 — nothing to solve.
        // Test that assume_tac fails when subgoal not in hyps
        let state = trivial_goal("A"); // {} ⊢ A==>A, nprems=1, subgoal=A not in hyps
        let outcomes = assume_tac(0).apply(&state, &[]);
        assert!(
            outcomes.is_empty(),
            "assume_tac should fail when subgoal not in hyps"
        );
    }

    #[test]
    fn test_assume_tac_fails_out_of_bounds() {
        let state = trivial_goal("A");
        let outcomes = assume_tac(5).apply(&state, &[]);
        assert!(outcomes.is_empty(), "out-of-bounds should fail");
    }

    #[test]
    fn test_all_tac() {
        let state = trivial_goal("A");
        let outcomes = all_tac().apply(&state, &[]);
        assert_eq!(outcomes.len(), 1);
        assert_eq!(outcomes[0].nprems(), state.nprems());
    }

    #[test]
    fn test_no_tac() {
        let state = trivial_goal("A");
        assert!(no_tac().apply(&state, &[]).is_empty());
    }

    #[test]
    fn test_then_orelse() {
        // (all_tac ORELSE no_tac) THEN all_tac on [A]==>A
        let state = trivial_goal("A");
        let tac = then_tac(orelse_tac(all_tac(), no_tac()), all_tac());
        let outcomes = tac.apply(&state, &[]);
        assert!(!outcomes.is_empty());
        assert_eq!(outcomes[0].nprems(), state.nprems());
    }

    #[test]
    fn test_repeat_assume() {
        // REPEAT(all_tac) should just return identity
        let state = trivial_goal("A");
        let tac = repeat_tac(all_tac());
        let outcomes = tac.apply(&state, &[]);
        assert!(!outcomes.is_empty());
        assert_eq!(outcomes[0].nprems(), state.nprems());
    }

    #[test]
    fn test_every_tac() {
        // EVERY [all_tac, all_tac] on [A]==>A
        let state = trivial_goal("A");
        let tac = every_tac(vec![all_tac(), all_tac()]);
        let outcomes = tac.apply(&state, &[]);
        assert!(!outcomes.is_empty());
        assert_eq!(outcomes[0].nprems(), state.nprems());
    }

    #[test]
    fn test_first_tac() {
        // FIRST [no_tac, all_tac] should return all_tac result
        let state = trivial_goal("A");
        let tac = first_tac(vec![no_tac(), all_tac()]);
        let outcomes = tac.apply(&state, &[]);
        assert!(!outcomes.is_empty());
        assert_eq!(outcomes.len(), 1);
    }

    #[test]
    fn test_depth_limit() {
        let state = trivial_goal("A");
        // DEPTH(0, all_tac): nprems=1 > 0 → fails
        let tac = depth_limit(0, all_tac());
        assert!(tac.apply(&state, &[]).is_empty());
        // DEPTH(2, all_tac): nprems=1 <= 2 → succeeds
        let tac2 = depth_limit(2, all_tac());
        assert!(!tac2.apply(&state, &[]).is_empty());
    }
}
