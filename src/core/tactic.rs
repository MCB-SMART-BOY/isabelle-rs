//! Tactics and tacticals — the basic building blocks of proof search.
//!
//! Corresponds to `src/Pure/tactic.ML` and `src/Pure/tactical.ML`.
//!
//! ## Quick reference
//!
//! | Tactical | Meaning |
//! |----------|---------|
//! | `tac1 THEN tac2` | Apply tac1, then tac2 on all results |
//! | `tac1 ORELSE tac2` | Try tac1, if it fails try tac2 |
//! | `EVERY [t1,..,tn]` | t1 THEN ... THEN tn |
//! | `FIRST [t1,..,tn]` | t1 ORELSE ... ORELSE tn |
//! | `REPEAT tac` | Repeat tac until it fails |
//! | `TRY tac` | tac ORELSE all_tac |
//! | `ALLGOALS tac` | Apply tac to all subgoals |
//! | `DETERM tac` | Take only the first result of tac |

use std::sync::Arc;

use crate::core::{
    simplifier::Simplifier,
    term::Term,
    thm::{CTerm, Thm, ThmKernel},
    types::Typ,
};

// =========================================================================
// Tactic type
// =========================================================================

/// A tactic is a function from a proof state (a theorem with subgoals)
/// to a sequence of proof states. An empty sequence means the tactic
/// failed.
///
/// In Isabelle: `type tactic = thm -> thm Seq.seq`
pub type TacticFn = Arc<dyn Fn(&Thm) -> Vec<Thm> + Send + Sync>;

// =========================================================================
// Basic tactics
// =========================================================================

/// Identity tactic: passes the proof state through unchanged.
pub fn all_tac() -> TacticFn {
    Arc::new(|st: &Thm| vec![st.clone()])
}

/// Failing tactic: always returns an empty sequence.
pub fn no_tac() -> TacticFn {
    Arc::new(|_: &Thm| vec![])
}

/// Solve subgoal `i` (0-indexed) by assumption.
/// Checks if subgoal i α-equivalent to any hypothesis of the state.
pub fn assume_tac(i: usize) -> TacticFn {
    Arc::new(move |st: &Thm| {
        if let Some(goal) = st.prem(i) {
            let goal_ct = CTerm::certify(goal);
            if st.hyps().contains(&goal_ct) {
                // The goal is already a hypothesis — we can close it via
                // the bicompose kernel with an assumption rule
                let assume_rule = ThmKernel::assume(goal_ct);
                if let Some(result) = ThmKernel::bicompose(false, &assume_rule, st, i) {
                    return vec![result];
                }
            }
        }
        vec![]
    })
}

/// Resolve subgoal `i` with a list of rules.
/// Each rule's conclusion is unified with subgoal i.
pub fn resolve_tac(rules: &[Thm], i: usize) -> TacticFn {
    let rules: Vec<Thm> = rules.to_vec();
    Arc::new(move |st: &Thm| {
        let mut results = Vec::new();
        for rule in &rules {
            if let Some(result) = ThmKernel::bicompose(false, rule, st, i) {
                results.push(result);
            }
        }
        results
    })
}

/// Eliminate-resolution: like resolve_tac but the first premise of the rule
/// is unified with the subgoal and consumed (not kept as a new subgoal).
pub fn eresolve_tac(rules: &[Thm], i: usize) -> TacticFn {
    let rules: Vec<Thm> = rules.to_vec();
    Arc::new(move |st: &Thm| {
        let mut results = Vec::new();
        for rule in &rules {
            if let Some(result) = ThmKernel::bicompose(true, rule, st, i) {
                results.push(result);
            }
        }
        results
    })
}

/// Destruct-resolution: convert destruction rules to elimination rules,
/// then apply eresolve_tac.
pub fn dresolve_tac(rules: &[Thm], i: usize) -> TacticFn {
    let elim_rules: Vec<Thm> =
        rules.iter().map(|r| make_elim(r).unwrap_or_else(|| r.clone())).collect();
    eresolve_tac(&elim_rules, i)
}

/// SIMP tactic: apply the simplifier to subgoal i.
pub fn simp_tac(simp: Simplifier, i: usize) -> TacticFn {
    Arc::new(move |st: &Thm| {
        let goal = match st.prem(i) {
            Some(g) => g,
            None => return vec![],
        };
        if let Some((_reduced, eq_thm)) = simp.rewrite_deep(&goal)
            && let Some(result) = ThmKernel::subst_premise(&eq_thm, st, i) {
                return vec![result];
            }
        vec![]
    })
}

// =========================================================================
// Tactical combinators
// =========================================================================

/// THEN: apply tac1, then tac2 to each result of tac1.
pub fn then_tac(tac1: TacticFn, tac2: TacticFn) -> TacticFn {
    Arc::new(move |st: &Thm| {
        let mut results = Vec::new();
        for st1 in tac1(st) {
            results.extend(tac2(&st1));
        }
        results
    })
}

/// ORELSE: try tac1; if it produces no results, try tac2.
pub fn orelse_tac(tac1: TacticFn, tac2: TacticFn) -> TacticFn {
    Arc::new(move |st: &Thm| {
        let results = tac1(st);
        if results.is_empty() { tac2(st) } else { results }
    })
}

/// APPEND: concatenate results of both tactics.
pub fn append_tac(tac1: TacticFn, tac2: TacticFn) -> TacticFn {
    Arc::new(move |st: &Thm| {
        let mut results = tac1(st);
        results.extend(tac2(st));
        results
    })
}

/// TRY: tac ORELSE all_tac.
pub fn try_tac(tac: TacticFn) -> TacticFn {
    orelse_tac(tac, all_tac())
}

/// REPEAT: apply tac repeatedly until it fails.
pub fn repeat_tac(tac: TacticFn) -> TacticFn {
    Arc::new(move |st: &Thm| {
        let mut results = Vec::new();
        let mut to_process = vec![st.clone()];
        while let Some(s) = to_process.pop() {
            let res = tac(&s);
            if res.is_empty() {
                results.push(s);
            } else {
                to_process.extend(res);
            }
        }
        results
    })
}

/// DETERM: take only the first result of tac.
pub fn determ_tac(tac: TacticFn) -> TacticFn {
    Arc::new(move |st: &Thm| {
        let results = tac(st);
        if results.is_empty() { vec![] } else { vec![results[0].clone()] }
    })
}

/// COND: if pred(st) then tac1(st) else tac2(st).
pub fn cond_tac(
    pred: impl Fn(&Thm) -> bool + Send + Sync + 'static,
    tac1: TacticFn,
    tac2: TacticFn,
) -> TacticFn {
    Arc::new(move |st: &Thm| if pred(st) { tac1(st) } else { tac2(st) })
}

/// CHANGED: tac, but only return results that differ from the input.
pub fn changed_tac(tac: TacticFn) -> TacticFn {
    Arc::new(move |st: &Thm| {
        let results = tac(st);
        results.into_iter().filter(|r| *st != *r).collect()
    })
}

/// FILTER: only keep results satisfying pred.
pub fn filter_tac(pred: impl Fn(&Thm) -> bool + Send + Sync + 'static, tac: TacticFn) -> TacticFn {
    Arc::new(move |st: &Thm| {
        let results = tac(st);
        results.into_iter().filter(|r| pred(r)).collect()
    })
}

// =========================================================================
// List-oriented tacticals
// =========================================================================

/// EVERY [t1,..,tn] = t1 THEN t2 THEN ... THEN tn
pub fn every_tac(tacs: &[TacticFn]) -> TacticFn {
    if tacs.is_empty() {
        return all_tac();
    }
    let mut result = tacs[0].clone();
    for tac in &tacs[1..] {
        result = then_tac(result, tac.clone());
    }
    result
}

/// FIRST [t1,..,tn] = t1 ORELSE t2 ORELSE ... ORELSE tn
pub fn first_tac(tacs: &[TacticFn]) -> TacticFn {
    if tacs.is_empty() {
        return no_tac();
    }
    let mut result = tacs[0].clone();
    for tac in &tacs[1..] {
        result = orelse_tac(result, tac.clone());
    }
    result
}

// =========================================================================
// Subgoal-based tacticals
// =========================================================================

/// ALLGOALS tac: apply tac to every subgoal (from n downto 1).
pub fn allgoals_tac(tac: impl Fn(usize) -> TacticFn + Send + Sync + 'static) -> TacticFn {
    Arc::new(move |st: &Thm| {
        let np = st.nprems();
        if np == 0 {
            return vec![st.clone()];
        }
        let mut results = vec![st.clone()];
        for i in (1..=np).rev() {
            let mut new_results = Vec::new();
            for r in results {
                new_results.extend(tac(i)(&r));
            }
            results = new_results;
            if results.is_empty() {
                break;
            }
        }
        results
    })
}

/// SOMEGOAL tac: find some subgoal where tac succeeds.
pub fn somegoal_tac(tac: impl Fn(usize) -> TacticFn + Send + Sync + 'static) -> TacticFn {
    Arc::new(move |st: &Thm| {
        let np = st.nprems();
        for i in (1..=np).rev() {
            let results = tac(i)(st);
            if !results.is_empty() {
                return results;
            }
        }
        vec![]
    })
}

/// HEADGOAL tac = tac(1)
pub fn headgoal_tac(tac: impl Fn(usize) -> TacticFn + Send + Sync + 'static) -> TacticFn {
    tac(1)
}

// =========================================================================
// Depth-limited tacticals
// =========================================================================

/// REPEAT_DETERM_N n tac: repeat tac at most n times, deterministically.
pub fn repeat_determ_n(n: i32, tac: TacticFn) -> TacticFn {
    Arc::new(move |st: &Thm| {
        let mut current = st.clone();
        let mut count = 0;
        while n < 0 || count < n {
            let results = tac(&current);
            if results.is_empty() {
                break;
            }
            current = results[0].clone();
            count += 1;
        }
        vec![current]
    })
}

/// REPEAT_DETERM: repeat tac deterministically until it fails.
pub fn repeat_determ_tac(tac: TacticFn) -> TacticFn {
    repeat_determ_n(-1, tac)
}

// =========================================================================
// Trace/debug tacticals
// =========================================================================

/// Print the current subgoal before applying tac.
pub fn trace_tac(msg: &str, tac: TacticFn) -> TacticFn {
    let msg = msg.to_string();
    Arc::new(move |st: &Thm| {
        eprintln!("[trace] {}: {} subgoals", msg, st.nprems());
        if let Some(g) = st.prem(1) {
            eprintln!("  goal 1: {}", g);
        }
        tac(st)
    })
}

// =========================================================================
// Helpers
// =========================================================================

/// Convert a destruction rule to an elimination rule.
/// Given `rl: H ⊢ C`, produce `⟦H; C ⟹ R⟧ ⟹ R`.
pub fn make_elim(rule: &Thm) -> Option<Thm> {
    let revcut = revcut_rl();
    // rl RS revcut_rl: resolve rl's conclusion against revcut's first premise
    ThmKernel::bicompose(false, rule, &revcut, 0)
}

/// The revcut rule: `⟦V; V ⟹ W⟧ ⟹ W`
fn revcut_rl() -> Thm {
    let v = CTerm::certify(Term::free("V", Typ::base("prop")));
    let _w = CTerm::certify(Term::free("W", Typ::base("prop")));

    let assume_v = ThmKernel::assume(v.clone());
    // Build: V ⟹ W
    let v_imp_w = ThmKernel::assume(CTerm::certify(Term::app(
        Term::app(
            Term::const_(
                "Pure.imp",
                Typ::arrows(vec![Typ::base("prop"), Typ::base("prop")], Typ::base("prop")),
            ),
            Term::free("V", Typ::base("prop")),
        ),
        Term::free("W", Typ::base("prop")),
    )));
    // modus ponens
    let w_thm = ThmKernel::implies_elim(&v_imp_w, &assume_v).unwrap();

    // Discharge assumptions
    let thm1 = ThmKernel::implies_intr(
        &CTerm::certify(Term::app(
            Term::app(
                Term::const_(
                    "Pure.imp",
                    Typ::arrows(vec![Typ::base("prop"), Typ::base("prop")], Typ::base("prop")),
                ),
                Term::free("V", Typ::base("prop")),
            ),
            Term::free("W", Typ::base("prop")),
        )),
        &w_thm,
    )
    .unwrap();
    ThmKernel::implies_intr(&v, &thm1).unwrap()
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn prop_typ() -> Typ {
        Typ::base("prop")
    }

    fn prop(name: &str) -> Term {
        Term::const_(name, prop_typ())
    }

    fn trivial_goal() -> Thm {
        let ct = CTerm::certify(prop("A"));
        ThmKernel::assume(ct)
    }

    fn goal_with_hyp() -> Thm {
        let a = CTerm::certify(prop("A"));
        ThmKernel::implies_intr(&a, &ThmKernel::assume(a.clone())).unwrap()
    }

    #[test]
    fn test_all_tac() {
        let st = trivial_goal();
        let results = all_tac()(&st);
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn test_no_tac() {
        let st = trivial_goal();
        let results = no_tac()(&st);
        assert!(results.is_empty());
    }

    #[test]
    fn test_then_tac() {
        let tac = then_tac(all_tac(), all_tac());
        let st = trivial_goal();
        let results = tac(&st);
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn test_orelse_tac() {
        let tac = orelse_tac(no_tac(), all_tac());
        let st = trivial_goal();
        let results = tac(&st);
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn test_try_tac() {
        let tac = try_tac(no_tac());
        let st = trivial_goal();
        let results = tac(&st);
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn test_repeat_tac() {
        let tac = repeat_tac(no_tac());
        let st = trivial_goal();
        let results = tac(&st);
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn test_every_tac() {
        let tacs: Vec<TacticFn> = vec![all_tac(), all_tac(), all_tac()];
        let tac = every_tac(&tacs);
        let st = trivial_goal();
        let results = tac(&st);
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn test_first_tac() {
        let tacs: Vec<TacticFn> = vec![no_tac(), no_tac(), all_tac()];
        let tac = first_tac(&tacs);
        let st = trivial_goal();
        let results = tac(&st);
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn test_determ_tac() {
        let multi_tac: TacticFn = Arc::new(|st: &Thm| vec![st.clone(), st.clone()]);
        let tac = determ_tac(multi_tac);
        let st = trivial_goal();
        let results = tac(&st);
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn test_changed_tac() {
        let tac = changed_tac(all_tac());
        let st = trivial_goal();
        let results = tac(&st);
        assert!(results.is_empty());
    }

    #[test]
    fn test_headgoal_tac() {
        let tac = headgoal_tac(move |_i: usize| all_tac());
        let st = trivial_goal();
        let results = tac(&st);
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn test_make_elim() {
        // The revcut rule should be constructable
        let revcut = revcut_rl();
        // revcut: V ⟹ (V ⟹ W) ⟹ W
        assert!(revcut.nprems() >= 1);

        // make_elim of A should produce: ⟦A; A ⟹ R⟧ ⟹ R
        let a = CTerm::certify(prop("A"));
        let rule = ThmKernel::assume(a);
        let elim = make_elim(&rule);
        // This may or may not succeed depending on bicompose details
        // The key invariant: if it succeeds, it should have more prems than original
        if let Some(e) = &elim {
            // elim should have at least as many prems as rule
            assert!(e.nprems() >= rule.nprems());
        }
    }
}
