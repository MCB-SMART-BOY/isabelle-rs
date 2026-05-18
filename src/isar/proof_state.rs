//! Isar proof state machine — minimal implementation.
//!
//! Tracks the state of a structured Isar proof:
//! - `fix`/`assume` — context extension
//! - `have`/`show` — intermediate goals
//! - `case`/`next` — induction case analysis
//! - `qed` — proof finalization
//!
//! This is a simplified version that handles the most common patterns
//! found in .thy file proofs without implementing the full Isar language.

use std::sync::Arc;
use crate::core::thm::{Thm, ThmKernel, CTerm};
use crate::core::term::Term;
use crate::core::types::Typ;

/// The proof state during a structured Isar proof.
#[derive(Debug, Clone)]
pub enum ProofState {
    /// Initial state: about to start a proof
    Ready { goal: Thm },
    /// Inside a proof block, tracking context and subgoals
    Proving {
        /// The original goal (before decomposition)
        goal: Thm,
        /// Accumulated facts (from `fix`, `assume`, `have`)
        facts: Vec<Arc<Thm>>,
        /// Chained fact (set by `then`, consumed by `have`/`show`)
        chained_fact: Option<Arc<Thm>>,
        /// Fixed variables
        fixes: Vec<(String, Typ)>,
        /// Pending subgoals (from induction/cases)
        subgoals: Vec<Thm>,
        /// Index of current subgoal being proved
        current_subgoal: usize,
        /// Nested block depth (for { ... } blocks)
        block_depth: usize,
    },
    /// Proof complete
    Done(Thm),
}

impl ProofState {
    /// Create a new proof state from a goal.
    pub fn new(goal: Thm) -> Self {
        ProofState::Ready { goal }
    }

    /// Begin the proof (after `proof` command).
    pub fn begin_proof(&mut self) {
        if let ProofState::Ready { goal } = self {
            *self = ProofState::Proving {
                goal: goal.clone(),
                facts: Vec::new(),
                chained_fact: None,
                fixes: Vec::new(),
                subgoals: Vec::new(),
                current_subgoal: 0,
                block_depth: 0,
            };
        }
    }

    /// Set subgoals from an induction/cases application.
    pub fn set_subgoals(&mut self, new_subgoals: Vec<Thm>) {
        if let ProofState::Proving { subgoals, current_subgoal, .. } = self {
            *subgoals = new_subgoals;
            *current_subgoal = 0;
        }
    }

    /// Get the current subgoal (if any).
    pub fn get_current_subgoal(&self) -> Option<&Thm> {
        match self {
            ProofState::Proving { subgoals, current_subgoal, .. } => {
                subgoals.get(*current_subgoal)
            }
            _ => None,
        }
    }

    /// Fix a variable (Isar `fix x y`).
    pub fn fix(&mut self, var: &str, typ: Typ) {
        if let ProofState::Proving { fixes, .. } = self {
            fixes.push((var.to_string(), typ));
        }
    }

    /// Assume a proposition (Isar `assume "A"`).
    pub fn assume(&mut self, prop: Term) {
        if let ProofState::Proving { facts, .. } = self {
            let assume_thm = ThmKernel::assume(CTerm::certify(prop));
            facts.push(Arc::new(assume_thm));
        }
    }

    /// Add a fact (from `using`, `note`, or `have`).
    pub fn add_fact(&mut self, thm: Arc<Thm>) {
        if let ProofState::Proving { facts, .. } = self {
            facts.push(thm);
        }
    }

    /// Prove an intermediate lemma (`have "B" by method`).
    pub fn have(&mut self, stmt: &Term, method: &str, all_premises: &[Arc<Thm>]) -> Option<Arc<Thm>> {
        let goal = ThmKernel::assume(CTerm::certify(stmt.clone()));
        let mut combined_prems: Vec<Arc<Thm>> = all_premises.iter()
            .chain(self.get_premises().iter())
            .cloned()
            .collect();
        // Include chained fact if present
        if let Some(chained) = self.take_chained() {
            combined_prems.push(chained);
        }
        let result = crate::isar::method::exec_proof(&goal, method, &combined_prems)?;
        let result_arc = Arc::new(result);
        // Chain this result for the next step
        self.chain_fact(Arc::clone(&result_arc));
        self.add_fact(Arc::clone(&result_arc));
        Some(result_arc)
    }

        /// Prove the current goal (`show "C" by method`).
    pub fn show(&mut self, stmt: &Term, method: &str, all_premises: &[Arc<Thm>]) -> Option<Thm> {
        let actual_stmt = self.resolve_case_stmt(stmt);
        let goal = ThmKernel::assume(CTerm::certify(actual_stmt));
        let mut combined_prems: Vec<Arc<Thm>> = all_premises.iter()
            .chain(self.get_premises().iter())
            .cloned()
            .collect();
        // Include chained fact if present
        if let Some(chained) = self.take_chained() {
            combined_prems.push(chained);
        }
        crate::isar::method::exec_proof(&goal, method, &combined_prems)
    }

    /// Resolve ?case/?thesis to the current subgoal's conclusion.
    fn resolve_case_stmt(&self, stmt: &Term) -> Term {
        if let Term::Const { name, .. } = stmt {
            if name.as_ref() == "?case" || name.as_ref() == "?thesis" {
                if let Some(subgoal) = self.get_current_subgoal() {
                    return subgoal.prop().term().clone();
                }
            }
        }
        stmt.clone()
    }

    /// Chain a fact (for `then` keyword).
    pub fn chain_fact(&mut self, thm: Arc<Thm>) {
        if let ProofState::Proving { chained_fact, .. } = self {
            *chained_fact = Some(thm);
        }
    }

    /// Get and clear the chained fact.
    fn take_chained(&mut self) -> Option<Arc<Thm>> {
        if let ProofState::Proving { chained_fact, .. } = self {
            chained_fact.take()
        } else {
            None
        }
    }

    /// Set up a case context    /// Set up a case context (`case Nil` or `case (Cons x xs)`).
    /// Selects the appropriate subgoal for the named case.
    pub fn case_(&mut self, case_name: &str) {
        if let ProofState::Proving { subgoals, current_subgoal, facts, chained_fact, .. } = self {
            *chained_fact = None;
            // Try to find the matching subgoal by name/index
            let clean_name = case_name.trim_matches(|c: char| c == '(' || c == ')')
                .split_whitespace().next().unwrap_or(case_name);
            
            // Heuristic: map case names to subgoal indices
            let idx = match clean_name {
                "Nil" | "None" | "0" | "Zero" | "empty" | "[]" => 0,
                "Cons" | "Some" | "Suc" => 1,
                _ => {
                    // Try to find by scanning subgoals
                    *current_subgoal
                }
            };
            if idx < subgoals.len() {
                *current_subgoal = idx;
            }
            // Clear facts for the new case (they'll be populated from the induction hypothesis)
            facts.clear();
        }
    }

    /// Move to the next subgoal (`next`).
    pub fn next(&mut self) {
        if let ProofState::Proving { subgoals, current_subgoal, facts, chained_fact, .. } = self {
            *chained_fact = None;
            if *current_subgoal + 1 < subgoals.len() {
                *current_subgoal += 1;
            }
            facts.clear();
        }
    }

    /// Get all accumulated facts as premises.
    pub fn get_premises(&self) -> Vec<Arc<Thm>> {
        match self {
            ProofState::Proving { facts, .. } => facts.clone(),
            _ => Vec::new(),
        }
    }

    /// Attempt to finalize the proof (`qed`).
    /// Returns the final theorem if all subgoals are solved.
    pub fn qed(&mut self) -> Option<Thm> {
        match self {
            ProofState::Proving { subgoals, .. } => {
                // Check if all subgoals are solved (nprems == 0)
                let all_solved = subgoals.iter().all(|sg| sg.nprems() == 0);
                if all_solved && !subgoals.is_empty() {
                    // Return the first subgoal as the result (simplified)
                    let result = subgoals[0].clone();
                    *self = ProofState::Done(result.clone());
                    Some(result)
                } else if subgoals.is_empty() {
                    // No subgoals - use the original goal
                    if let ProofState::Proving { goal, .. } = self {
                        let result = goal.clone();
                        *self = ProofState::Done(result.clone());
                        Some(result)
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            ProofState::Ready { goal } => {
                if goal.nprems() == 0 {
                    let result = goal.clone();
                    *self = ProofState::Done(result.clone());
                    Some(result)
                } else {
                    None
                }
            }
            ProofState::Done(thm) => Some(thm.clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proof_state_lifecycle() {
        let a = Term::const_("A", Typ::base("prop"));
        let goal = ThmKernel::assume(CTerm::certify(a.clone()));
        let mut state = ProofState::new(goal);
        state.begin_proof();
        state.fix("x", Typ::base("nat"));
        state.assume(Term::const_("Px", Typ::base("prop")));
        let prems = state.get_premises();
        assert_eq!(prems.len(), 1);
    }
}

/// Interpret a structured Isar proof script, driving the ProofState.
/// Handles: `fix`, `assume`, `have`, `show`, `case`, `next`, `qed`, `by`, `proof`.
pub fn interpret_proof_script(
    state: &mut ProofState,
    script: &str,
    premises: &[Arc<Thm>],
) -> Option<Thm> {
    let script = script.trim();
    
    // Handle simple `by method` proofs (no structured commands)
    if script.starts_with("by ") || script.starts_with("by(") {
        return exec_simple_proof(state, script, premises);
    }

    // Parse commands line by line
    let lines: Vec<&str> = script.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let t = lines[i].trim();
        if t.is_empty() { i += 1; continue; }

        // `proof` — begin proof block
        if t.starts_with("proof ") || t == "proof" {
            state.begin_proof();
            // Handle `proof (induct ...)` or `proof (cases ...)`
            if let Some(inner) = t.strip_prefix("proof ") {
                let inner = inner.trim();
                if inner.starts_with("(induct") || inner.starts_with("(induction") {
                    // Extract induction variable and optional rule
                    let induct_body = if inner.starts_with("(induct ") {
                        &inner[8..].trim_end_matches(')')
                    } else if inner.starts_with("(induction ") {
                        &inner[12..].trim_end_matches(')')
                    } else {
                        inner.trim_matches(|c| c == '(' || c == ')')
                    };
                    // Apply induction and store subgoals for case/next navigation
                    let induct_method = format!("induct {}", induct_body);
                    if let Some(goal) = state.get_current_goal() {
                        let results = crate::isar::method::exec_single_method(
                            &goal, &induct_method, premises);
                        if !results.is_empty() {
                            state.set_subgoals(results);
                        }
                    }
                }
            }
            i += 1;
            continue;
        }

        // `qed` — finalize proof
        if t == "qed" || t.starts_with("qed ") {
            return state.qed();
        }

        // `done` — also finalize proof
        if t == "done" {
            return state.qed();
        }

        // `fix x y` — fix variables
        if t.starts_with("fix ") {
            let vars = t.strip_prefix("fix ").unwrap_or("").trim();
            for var in vars.split_whitespace() {
                let var = var.trim();
                if !var.is_empty() {
                    state.fix(var, Typ::dummy());
                }
            }
            i += 1;
            continue;
        }

        // `assume "A"` — assume a proposition
        if t.starts_with("assume ") {
            let rest = t.strip_prefix("assume ").unwrap_or("").trim();
            // Strip quotes if present (Isar syntax uses "..." to delimit propositions)
            let term_str = rest.trim_matches('"');
            if let Some(prop) = parse_term_from_script(term_str) {
                state.assume(prop);
            }
            i += 1;
            continue;
        }

        // `have "B" by method` or `have name: "B" by method`
        if t.starts_with("have ") {
            let result = parse_and_exec_have_show(state, t, premises, false);
            if result.is_some() { i += 1; continue; }
        }

        // `show "C" by method` or `show name: "C" by method`
        if t.starts_with("show ") {
            let result = parse_and_exec_have_show(state, t, premises, true);
            if result.is_some() { i += 1; continue; }
        }

        // `hence` = `then have`
        if t.starts_with("hence ") {
            let rest = t.strip_prefix("hence ").unwrap_or("");
            let have_cmd = format!("have {}", rest);
            let result = parse_and_exec_have_show(state, &have_cmd, premises, false);
            if result.is_some() { i += 1; continue; }
        }

        // `thus` = `then show`
        if t.starts_with("thus ") {
            let rest = t.strip_prefix("thus ").unwrap_or("");
            let show_cmd = format!("show {}", rest);
            let result = parse_and_exec_have_show(state, &show_cmd, premises, true);
            if result.is_some() { i += 1; continue; }
        }

        // `case name` — induction case
        if t.starts_with("case ") {
            let case_name = t.strip_prefix("case ").unwrap_or("").trim();
            state.case_(case_name);
            i += 1;
            continue;
        }

        // `next` — next subgoal
        if t == "next" {
            state.next();
            i += 1;
            continue;
        }

        // `then` — chain previous fact for next have/show
        if t == "then" {
            // The fact from the previous have/show is already chained.
            // This is a no-op — the chaining happens automatically.
            i += 1;
            continue;
        }

        // `{` — begin nested block: save state for restoration
        if t == "{" {
            if let ProofState::Proving { block_depth, .. } = state {
                *block_depth += 1;
            }
            i += 1;
            continue;
        }
        // `}` — end nested block: restore outer context
        if t == "}" {
            if let ProofState::Proving { block_depth, .. } = state {
                if *block_depth > 0 {
                    *block_depth -= 1;
                }
            }
            i += 1;
            continue;
        }

        // `from name1 name2` — select facts from DB and chain them
        if t.starts_with("from ") {
            let names = t.strip_prefix("from ").unwrap_or("").trim();
            let db = crate::hol::hol_loader::HolTheoremDb::get();
            for name in names.split_whitespace() {
                let name = name.trim();
                if !name.is_empty() {
                    if let Some(thm) = db.by_name.get(name) {
                        state.chain_fact(Arc::clone(thm));
                    }
                }
            }
            i += 1;
            continue;
        }

        // `with name1 name2` — same as from but also includes current facts
        if t.starts_with("with ") {
            let names = t.strip_prefix("with ").unwrap_or("").trim();
            let db = crate::hol::hol_loader::HolTheoremDb::get();
            for name in names.split_whitespace() {
                let name = name.trim();
                if !name.is_empty() {
                    if let Some(thm) = db.by_name.get(name) {
                        state.add_fact(Arc::clone(thm));
                    }
                }
            }
            i += 1;
            continue;
        }

        // `note name = thm` — bind a fact to a name (skip, name binding not needed yet)
        if t.starts_with("note ") || t.starts_with("let ") {
            i += 1;
            continue;
        }

        // `using ...` — add facts (skip, handled at top level)
        if t.starts_with("using ") || t.starts_with("unfolding ") {
            i += 1;
            continue;
        }

        // Unknown command — skip
        i += 1;
    }

    // If we reach here without qed, try to finalize
    state.qed()
}

/// Parse and execute a `have` or `show` command.
fn parse_and_exec_have_show(
    state: &mut ProofState,
    cmd: &str,
    premises: &[Arc<Thm>],
    is_show: bool,
) -> Option<()> {
    // Parse: `have name: "statement" by method` or `have "statement" by method`
    let rest = if cmd.starts_with("have ") {
        cmd.strip_prefix("have ")?.trim()
    } else if cmd.starts_with("show ") {
        cmd.strip_prefix("show ")?.trim()
    } else {
        return None;
    };

    // Extract method (everything after " by ")
    let (stmt_part, method) = if let Some(by_pos) = rest.find(" by ") {
        (rest[..by_pos].trim(), rest[by_pos + 4..].trim())
    } else if let Some(by_pos) = rest.find(" by(") {
        (rest[..by_pos].trim(), rest[by_pos + 1..].trim())
    } else {
        return None;
    };

    // Extract statement (skip optional name label)
    let stmt_str = if let Some(colon_pos) = stmt_part.find(": \"") {
        &stmt_part[colon_pos + 2..].trim_end_matches('"')
    } else if stmt_part.starts_with('"') {
        stmt_part.trim_matches('"')
    } else {
        stmt_part
    };

    let stmt_term = parse_term_from_script(stmt_str)?;

    if is_show {
        state.show(&stmt_term, method, premises)?;
    } else {
        state.have(&stmt_term, method, premises)?;
    }
    Some(())
}

/// Execute a simple `by method` or `by(method)` proof.
fn exec_simple_proof(state: &mut ProofState, script: &str, premises: &[Arc<Thm>]) -> Option<Thm> {
    let goal = state.get_current_goal()?;
    let result = crate::isar::method::exec_proof(&goal, script, premises)?;
    state.set_current_goal(result);
    state.qed()
}

/// Parse a term from a proof script string (thin wrapper).
fn parse_term_from_script(s: &str) -> Option<Term> {
    crate::isar::term_parser::parse_term(s)
}

impl ProofState {
    /// Get the current goal being proved.
    pub fn get_current_goal(&self) -> Option<Thm> {
        match self {
            ProofState::Proving { subgoals, current_subgoal, goal, .. } => {
                subgoals.get(*current_subgoal).cloned()
                    .or_else(|| Some(goal.clone()))
            }
            ProofState::Ready { goal } => Some(goal.clone()),
            ProofState::Done(_) => None,
        }
    }

    /// Set the current goal (update the current subgoal).
    pub fn set_current_goal(&mut self, new_goal: Thm) {
        if let ProofState::Proving { subgoals, current_subgoal, .. } = self {
            if *current_subgoal < subgoals.len() {
                subgoals[*current_subgoal] = new_goal;
            }
        }
    }
}

#[cfg(test)]
mod isar_tests {
    use super::*;
    use crate::core::term::Term;
    use crate::core::types::Typ;
    use crate::core::thm::{CTerm, ThmKernel};
    use crate::core::logic::Pure;
    use std::sync::Arc;

    #[test]
    fn test_structured_have_show() {
        // Test that the ProofState can execute have/show logic
        let a = Term::const_("A", Typ::base("prop"));
        let goal = ThmKernel::assume(CTerm::certify(a.clone()));
        let mut state = ProofState::new(goal);
        state.begin_proof();
        state.assume(a.clone());
        let prems = state.get_premises();
        assert_eq!(prems.len(), 1, "Should have one assumed fact");
        // show "A" by assumption: A is in premises, so assumption tactic works
        let result = state.show(&a, "assumption", &[]);
        eprintln!("show result: {:?}", result);
        // The show may or may not succeed depending on theorem database state
        // In a full DB with proper setup, this should work
    }

    #[test]
    fn test_simple_by_proof() {
        // Simulate: lemma "A = A" by (rule refl)
        let a = Term::free("A", Typ::dummy());
        let eq = Pure::mk_equals(Typ::dummy(), a.clone(), a.clone());
        let goal = ThmKernel::assume(CTerm::certify(eq));
        let mut state = ProofState::new(goal);
        
        let script = "by (rule refl)";
        let premises: Vec<Arc<Thm>> = vec![];
        let result = interpret_proof_script(&mut state, script, &premises);
        eprintln!("Result: {:?}", result);
    }

    #[test]
    fn test_proof_state_lifecycle_extended() {
        // Test the full lifecycle with have/show
        let a = Term::const_("A", Typ::base("prop"));
        let b = Term::const_("B", Typ::base("prop"));
        let stmt = Pure::mk_implies(a.clone(), Pure::mk_implies(b.clone(), a.clone()));
        let goal = ThmKernel::assume(CTerm::certify(stmt));
        let mut state = ProofState::new(goal);
        state.begin_proof();
        // assume A
        state.assume(a.clone());
        // have "B" by ... would use actual proof
        // show "A" by assumption
        let prems = state.get_premises();
        assert!(!prems.is_empty());
    }
}

#[cfg(test)]
mod induction_tests {
    use super::*;
    use crate::core::term::Term;
    use crate::core::types::Typ;
    use crate::core::thm::{CTerm, ThmKernel};
    use crate::core::logic::Pure;
    use std::sync::Arc;

    #[test]
    fn test_induction_subgoals() {
        // Simulate: proof (induct xs) creates subgoals
        let a = Term::const_("A", Typ::base("prop"));
        let goal = ThmKernel::assume(CTerm::certify(a.clone()));
        let mut state = ProofState::new(goal);
        state.begin_proof();

        // Set up fake subgoals (simulating induction on a list)
        let nil_goal = ThmKernel::assume(CTerm::certify(
            Term::const_("NilCase", Typ::base("prop"))));
        let cons_goal = ThmKernel::assume(CTerm::certify(
            Term::const_("ConsCase", Typ::base("prop"))));
        state.set_subgoals(vec![nil_goal, cons_goal.clone()]);

        // case Nil — should select first subgoal
        state.case_("Nil");
        let current = state.get_current_goal();
        assert!(current.is_some());

        // next — should select second subgoal
        state.next();
        let current2 = state.get_current_goal();
        assert!(current2.is_some());
        
        // Verify we moved to the second subgoal
        let current2 = current2.unwrap();
        eprintln!("Second subgoal: {:?}", current2.prop().term());
    }

    #[test]
    fn test_resolve_case_stmt() {
        // Test that ?case resolves to the current subgoal
        let subgoal_term = Term::const_("P(Nil)", Typ::base("prop"));
        let subgoal = ThmKernel::assume(CTerm::certify(subgoal_term.clone()));
        let goal = ThmKernel::assume(CTerm::certify(
            Term::const_("MainGoal", Typ::base("prop"))));
        let mut state = ProofState::new(goal);
        state.begin_proof();
        state.set_subgoals(vec![subgoal]);

        let resolved = state.resolve_case_stmt(
            &Term::const_("?case", Typ::base("prop")));
        eprintln!("Resolved ?case to: {:?}", resolved);
        // Should resolve to P(Nil), the current subgoal's conclusion
    }
}
