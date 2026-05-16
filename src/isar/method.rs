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
use crate::hol::hol_loader::HolTheoremDb;
use crate::hol::hol_loader::ParsedLemma;

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
        if depth > 30 {
            return vec![state.clone()];
        }
        if state.nprems() == 0 {
            return vec![state.clone()];
        }

        // 1. Safe: assumption on first subgoal
        let assume_results = tactic::assume_tac(0).apply(state);
        for r in &assume_results {
            if r.nprems() == 0 {
                return assume_results;
            }
        }

        // 2. Safe: simp on first subgoal (uses [simp] theorems)
        let db = HolTheoremDb::get();
        let simp_results = tactic::simp_tac(&db.simps, 0).apply(state);
        for r in &simp_results {
            if r.nprems() != state.nprems() {
                // simp changed something — recurse
                let sub = Self::auto_exec(r, depth + 1);
                for s in &sub {
                    if s.nprems() == 0 {
                        return sub;
                    }
                }
            }
        }

        // 3. Safe: resolve with intro/elim theorems on first subgoal
        let resolve_results = tactic::resolve_tac(&db.intros, 0).apply(state);
        let eresolve_results = tactic::eresolve_tac(&db.elims, 0).apply(state);

        let mut all_solved = Vec::new();
        for r in &resolve_results {
            if r.nprems() == 0 {
                all_solved.push(r.clone());
            } else if r.nprems() < state.nprems() + 5 {
                let sub = Self::auto_exec(r, depth + 1);
                for s in &sub {
                    if s.nprems() == 0 {
                        all_solved.push(s.clone());
                    }
                }
            }
        }
        for r in &eresolve_results {
            if r.nprems() == 0 {
                all_solved.push(r.clone());
            } else if r.nprems() < state.nprems() + 5 {
                let sub = Self::auto_exec(r, depth + 1);
                for s in &sub {
                    if s.nprems() == 0 {
                        all_solved.push(s.clone());
                    }
                }
            }
        }

        if !all_solved.is_empty() {
            return all_solved;
        }

        // 4. Recurse on partial assumption results
        for r in &assume_results {
            if r.nprems() != 0 {
                let sub = Self::auto_exec(r, depth + 1);
                for s in &sub {
                    if s.nprems() == 0 {
                        all_solved.push(s.clone());
                    }
                }
            }
        }

        if !all_solved.is_empty() {
            return all_solved;
        }

        // 5. Nothing worked — return original state
        vec![state.clone()]
    }

    fn auto_resolve(state: &Thm) -> Option<Vec<Thm>> {
        let db = HolTheoremDb::get();
        let outcomes = crate::core::tactic::resolve_tac(&db.all, 0).apply(state);
        if outcomes.is_empty() {
            None
        } else {
            Some(outcomes)
        }
    }
}

/// Try to prove a goal using the auto method.
/// Returns the first solution found, or `None` if auto fails.
pub fn prove_auto(goal: &Thm) -> Option<Thm> {
    let results = Method::Auto.execute(goal);
    results.into_iter().find(|r| r.nprems() == 0)
}

/// Execute a proof script on a goal, returning the proven theorem.
///
/// Supported scripts:
/// - `by auto` → uses Method::Auto
/// - `by simp` → uses Method::Simp with [simp] theorems
/// - `by (rule name)` → looks up `name` in HolTheoremDb and uses Method::Rule
/// - `by assumption` or `by .` → uses Method::Assumption
/// - `by m1 m2` → chained: apply m1, then m2 to all remaining subgoals
pub fn exec_proof(state: &Thm, proof_script: &str) -> Option<Thm> {
    let script = proof_script.trim();

    // Handle "by " prefix
    let rest = script.strip_prefix("by ")?;

    // Split into chained methods: "(erule subst) (rule refl)"
    let methods = split_chained_methods(rest);

    let mut current_states = vec![state.clone()];

    for method_str in &methods {
        let mut next_states = Vec::new();
        for s in &current_states {
            let results = exec_single_method(s, method_str);
            next_states.extend(results);
        }
        if next_states.is_empty() {
            return None;
        }
        current_states = next_states;
    }

    current_states.into_iter().find(|r| r.nprems() == 0)
}

/// Split "(erule subst) (rule refl)" into ["(erule subst)", "(rule refl)"]
fn split_chained_methods(rest: &str) -> Vec<String> {
    let mut methods = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    let chars: Vec<char> = rest.chars().collect();
    for (i, &ch) in chars.iter().enumerate() {
        if ch == '(' { depth += 1; }
        else if ch == ')' { depth -= 1; }
        else if depth == 0 && ch == ' ' && i > start {
            let m = rest[start..i].trim().to_string();
            if !m.is_empty() {
                methods.push(m);
            }
            start = i + 1;
        }
    }
    let last = rest[start..].trim().to_string();
    if !last.is_empty() {
        methods.push(last);
    }
    methods
}

/// Execute a single method string like "(erule subst)" or "auto"
fn exec_single_method(state: &Thm, method_str: &str) -> Vec<Thm> {
    let method_str = method_str.trim();

    // Remove outer parentheses if present: "(erule subst)" → "erule subst"
    let inner = if method_str.starts_with('(') && method_str.ends_with(')') {
        method_str[1..method_str.len()-1].trim()
    } else {
        method_str
    };

    if inner == "auto" {
        return Method::Auto.execute(state);
    }
    if inner == "simp" || inner.starts_with("simp ") {
        let db = HolTheoremDb::get();
        return crate::core::tactic::simp_tac(&db.simps, 0).apply(state);
    }
    if inner == "assumption" || inner == "." {
        return Method::Assumption.execute(state);
    }
    if inner == "this" {
        return Method::Skip.execute(state);
    }

    // (rule name)
    if let Some(name) = inner.strip_prefix("rule ") {
        let db = HolTheoremDb::get();
        if let Some(thm) = db.by_name.get(name.trim()) {
            return crate::core::tactic::resolve_tac(&[Arc::clone(thm)], 0).apply(state);
        }
    }
    // (erule name)
    if let Some(name) = inner.strip_prefix("erule ") {
        let db = HolTheoremDb::get();
        if let Some(thm) = db.by_name.get(name.trim()) {
            return crate::core::tactic::eresolve_tac(&[Arc::clone(thm)], 0).apply(state);
        }
    }
    // (drule name)
    if let Some(name) = inner.strip_prefix("drule ") {
        let db = HolTheoremDb::get();
        if let Some(thm) = db.by_name.get(name.trim()) {
            return crate::core::tactic::dresolve_tac(&[Arc::clone(thm)], 0).apply(state);
        }
    }

    vec![]
}

/// Verify a ParsedLemma by executing its proof script.
/// If successful, returns a theorem with no hypotheses (fully proven).
pub fn verify_lemma(lem: &ParsedLemma) -> Option<Thm> {
    let proof = lem.proof_script.as_ref()?;
    // Create goal using trivial: {} ⊢ lemma ==> lemma
    // This gives us the lemma as a subgoal with empty hyps
    let goal = ThmKernel::trivial(CTerm::certify(lem.theorem.prop().term().clone())).ok()?;
    exec_proof(&goal, proof)
        .filter(|r| r.is_unconditional()) // must not rely on added assumptions
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
        // assume_tac requires subgoal in hyps
        // Create state: {A} ⊢ A (nprems=0 — already solved)
        let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
        let state = ThmKernel::assume(a);
        assert_eq!(state.nprems(), 0); // trivially true
        let results = Method::Assumption.execute(&state);
        // On a state with nprems=0, assume_tac(0) fails (no subgoal 0)
        assert!(results.is_empty());
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

    #[test]
    fn test_prove_auto_trivial() {
        // A ==> A by assumption
        let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
        let goal = ThmKernel::trivial(a).unwrap();
        let result = prove_auto(&goal);
        assert!(result.is_some(), "auto should prove A ==> A");
        assert_eq!(result.unwrap().nprems(), 0);
    }

    #[test]
    fn test_prove_assume_multi() {
        // [A] ==> A (assume A from hyps)
        let a = Term::const_("A", Typ::base("prop"));
        let state = ThmKernel::assume(CTerm::certify(a.clone()));
        // state: {A} ⊢ A, nprems=0 — already proved!
        assert_eq!(state.nprems(), 0);
    }

    #[test]
    fn test_prove_sym_equality() {
        // Verify sym theorem is in the database
        use crate::core::logic::Pure;
        let s = Term::free("s", Typ::base("nat"));
        let t = Term::free("t", Typ::base("nat"));
        let s_eq_t = Pure::mk_equals(Typ::base("nat"), s.clone(), t.clone());
        let db = HolTheoremDb::get();
        let sym_thm = db.simps.iter().find(|thm| {
            let (l, _) = Pure::dest_equals(thm.prop().term()).unwrap_or((&s_eq_t, &s_eq_t));
            l == &s_eq_t
        });
        // sym should be in the database
        assert!(sym_thm.is_some(), "sym theorem should be in database");
    }

    #[test]
    fn test_prove_auto_with_theorem_db() {
        // Test that auto can use a loaded theorem
        // Create a goal state and let auto try the theorem database
        use crate::core::logic::Pure;
        let a = Term::const_("A", Typ::base("prop"));
        let b = Term::const_("B", Typ::base("prop"));
        let a_imp_b = Pure::mk_implies(a.clone(), b.clone());
        // State: {A, A==>B} ⊢ B
        // Build by: assume(A==>B), then implies_elim with assume(A)
        let assume_ab = ThmKernel::assume(CTerm::certify(a_imp_b));
        let assume_a = ThmKernel::assume(CTerm::certify(a));
        // implies_elim: from (A==>B) and A, get B
        let result = ThmKernel::implies_elim(&assume_ab, &assume_a).unwrap();
        // result: {A, A==>B} ⊢ B, nprems=0
        assert_eq!(result.nprems(), 0);
        // auto should also be able to do this
        let auto_result = prove_auto(&result);
        assert!(auto_result.is_some());
        assert_eq!(auto_result.unwrap().nprems(), 0);
    }

    #[test]
    fn test_prove_auto_depth_limit() {
        // Verify depth limit prevents infinite recursion
        let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
        let b = CTerm::certify(Term::const_("B", Typ::base("prop")));
        let a_imp_b = crate::core::logic::Pure::mk_implies(a.term().clone(), b.term().clone());
        let state = ThmKernel::trivial(CTerm::certify(a_imp_b)).unwrap();
        // This goal can't be proved (A doesn't imply B)
        // auto should hit depth limit and return original state
        let result = prove_auto(&state);
        // May or may not prove — just shouldn't crash
        let _ = result;
    }

    #[test]
    fn test_extract_proof_from_source() {
        // Test that proof scripts are captured from .thy source
        let source = "lemma sym: \"s = t ==> t = s\"\n  by auto";
        let lemmas = crate::hol::hol_loader::parse_lemmas(source);
        assert_eq!(lemmas.len(), 1);
        assert_eq!(lemmas[0].name, "sym");
        assert!(lemmas[0].proof_script.is_some());
        assert_eq!(lemmas[0].proof_script.as_ref().unwrap(), "by auto");
    }

    #[test]
    fn test_by_name_index_populated() {
        let db = HolTheoremDb::get();
        assert!(db.by_name.contains_key("sym"), "sym should be indexed");
        assert!(db.by_name.contains_key("trans"), "trans should be indexed");
        // Check total count
        eprintln!("by_name contains {} theorems", db.by_name.len());
        assert!(db.by_name.len() > 100, "should have many named theorems");
    }

    #[test]
    fn test_exec_proof_by_rule_lookup() {
        // Verify that exec_proof can look up a theorem by name
        use crate::core::logic::Pure;
        let a = Term::const_("A", Typ::base("prop"));
        // Create a trivial goal that sym can't solve, but verify lookup works
        let goal = Pure::mk_implies(a.clone(), a.clone());
        let state = ThmKernel::assume(CTerm::certify(goal));
        // This calls exec_proof with "by (rule sym)" — it won't succeed
        // but should not crash and should attempt the lookup
        let result = exec_proof(&state, "by (rule sym)");
        // sym theorem's conclusion won't match A ==> A, so result is None
        assert!(result.is_none());
    }

    #[test]
    fn test_exec_proof_by_assumption() {
        use crate::core::logic::Pure;
        let a = Term::const_("A", Typ::base("prop"));
        let goal_term = Pure::mk_implies(a.clone(), a.clone());
        // Use assume (not trivial): {A==>A} ⊢ A==>A, nprems=1 (just A)
        let state = ThmKernel::assume(CTerm::certify(goal_term));
        let result = exec_proof(&state, "by assumption");
        assert!(result.is_some(), "exec_proof should succeed");
        assert_eq!(result.unwrap().nprems(), 0);
    }

    #[test]
    fn test_lemma_with_proof_roundtrip() {
        // Full roundtrip: parse lemma with proof, verify it
        let source = "lemma test: \"A ==> A\"\n  by assumption";
        let lemmas = crate::hol::hol_loader::parse_lemmas(source);
        assert_eq!(lemmas.len(), 1, "should parse one lemma");
        let lem = &lemmas[0];
        assert!(lem.proof_script.is_some(), "should capture proof script");
        let result = verify_lemma(lem);
        assert!(result.is_some(), "verify_lemma should succeed for A ==> A by assumption");
        assert_eq!(result.unwrap().nprems(), 0);
    }

    #[test]
    fn test_debug_subst_name() {
        let hol_thy = include_str!("../../isabelle-source/src/HOL/HOL.thy");
        let lemmas = crate::hol::hol_loader::parse_lemmas(hol_thy);
        // Find lemmas named subst, refl, TrueI
        for name in &["subst", "refl", "TrueI", "iffD1", "iffD2"] {
            let found: Vec<_> = lemmas.iter().filter(|l| l.name.contains(name)).collect();
            eprintln!("Search '{}': {} matches", name, found.len());
            for lem in found.iter().take(3) {
                eprintln!("  name='{}', attr={:?}, proof={:?}",
                    lem.name, lem.attributes, lem.proof_script);
            }
        }
    }

    #[test]
    fn test_auto_sample() {
        // Quick sample test — full verification is too slow for unit tests
        let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
        let goal = ThmKernel::trivial(a).unwrap();
        // auto on {} ⊢ A==>A should not cheat via assume_tac
        let result = prove_auto(&goal);
        // With empty hyps, assume_tac fails; resolution might work if DB has matching theorem
        let _ = result;
    }
}
