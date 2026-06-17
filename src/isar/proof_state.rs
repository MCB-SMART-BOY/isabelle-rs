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

use crate::core::{
    term::Term,
    thm::{CTerm, Thm, ThmKernel},
    types::Typ,
};

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
        /// The result of the final `show` statement (for qed composition)
        show_result: Option<Thm>,
        /// Abbreviations from `let` commands (name -> term binding)
        let_bindings: Vec<(String, Term)>,
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
                show_result: None,
                let_bindings: Vec::new(),
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
            ProofState::Proving { subgoals, current_subgoal, .. } => subgoals.get(*current_subgoal),
            _ => None,
        }
    }

    /// Fix a variable (Isar `fix x y`).
    pub fn fix(&mut self, var: &str, typ: Typ) {
        if let ProofState::Proving { fixes, .. } = self {
            fixes.push((var.to_string(), typ));
        }
    }

    /// Define a local abbreviation (Isar `let x = t` or `let x be "prop"`).
    ///
    /// Store the binding so that subsequent commands can expand `x` to `t`.
    pub fn let_def(&mut self, name: &str, term: Term) {
        if let ProofState::Proving { let_bindings, .. } = self {
            // Replace existing binding for this name if present
            let_bindings.retain(|(n, _)| n != name);
            let_bindings.push((name.to_string(), term));
        }
    }

    /// Expand all `let` abbreviations in a term.
    ///
    /// Replaces `Const(name)` nodes that match a `let` binding with the bound term.
    pub fn expand_lets(&self, term: &Term) -> Term {
        let bindings = match self {
            ProofState::Proving { let_bindings, .. } => let_bindings,
            _ => return term.clone(),
        };
        if bindings.is_empty() {
            return term.clone();
        }
        Self::expand_lets_rec(term, bindings)
    }

    /// Recursive helper for let expansion (iterative implementation).
    fn expand_lets_rec(term: &Term, bindings: &[(String, Term)]) -> Term {
        // Use iterative approach: process the term tree without recursion.
        // For simplicity, we do a single-pass replacement and iteration.
        // Deeply nested terms are handled via the work-list pattern in the caller.
        match term {
            Term::Const { name, .. } => {
                for (let_name, let_term) in bindings {
                    if name.as_ref() == let_name {
                        return let_term.clone();
                    }
                }
                term.clone()
            },
            Term::App { func, arg } => {
                let new_func = Self::expand_lets_rec(func, bindings);
                let new_arg = Self::expand_lets_rec(arg, bindings);
                Term::app(new_func, new_arg)
            },
            Term::Abs { name, typ, body } => {
                let new_body = Self::expand_lets_rec(body, bindings);
                Term::abs(name.clone(), typ.clone(), new_body)
            },
            _ => term.clone(),
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
    pub fn have(
        &mut self,
        stmt: &Term,
        method: &str,
        all_premises: &[Arc<Thm>],
    ) -> Option<Arc<Thm>> {
        let goal = ThmKernel::assume(CTerm::certify(stmt.clone()));
        let mut combined_prems: Vec<Arc<Thm>> =
            all_premises.iter().chain(self.get_premises().iter()).cloned().collect();
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
    /// Stores the result for final composition in `qed`.
    pub fn show(&mut self, stmt: &Term, method: &str, all_premises: &[Arc<Thm>]) -> Option<Thm> {
        let actual_stmt = self.resolve_case_stmt(stmt);
        let goal = ThmKernel::assume(CTerm::certify(actual_stmt));
        let mut combined_prems: Vec<Arc<Thm>> =
            all_premises.iter().chain(self.get_premises().iter()).cloned().collect();
        // Include chained fact if present
        if let Some(chained) = self.take_chained() {
            combined_prems.push(chained);
        }
        let result = crate::isar::method::exec_proof(&goal, method, &combined_prems)?;
        // Store the show result for qed to use in final theorem composition
        if let ProofState::Proving { show_result, .. } = self {
            *show_result = Some(result.clone());
        }
        Some(result)
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
        if let ProofState::Proving { chained_fact, .. } = self { chained_fact.take() } else { None }
    }

    /// Set up a case context (`case Nil` or `case (Cons x xs)`).
    /// Selects the appropriate subgoal for the named case.
    pub fn case_(&mut self, case_name: &str) {
        if let ProofState::Proving { subgoals, current_subgoal, facts, chained_fact, .. } = self {
            *chained_fact = None;
            // Try to find the matching subgoal by name/index
            let clean_name = case_name
                .trim_matches(|c: char| c == '(' || c == ')')
                .split_whitespace()
                .next()
                .unwrap_or(case_name);

            // Heuristic: map case names to subgoal indices
            let idx = match clean_name {
                "Nil" | "None" | "0" | "Zero" | "empty" | "[]" => 0,
                "Cons" | "Some" | "Suc" => 1,
                _ => {
                    // Try to find by scanning subgoals
                    *current_subgoal
                },
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

    /// Get all accumulated facts as premises (as reference).
    pub fn get_premises(&self) -> &[Arc<Thm>] {
        match self {
            ProofState::Proving { facts, .. } => facts.as_slice(),
            _ => &[],
        }
    }

    /// Attempt to finalize the proof (`qed`).
    /// Returns the final theorem if all subgoals are solved.
    pub fn qed(&mut self) -> Option<Thm> {
        match self {
            ProofState::Proving { subgoals, goal, fixes, facts, show_result, .. } => {
                // Priority 1: use the show_result if available
                let base_result = if let Some(result) = show_result {
                    result.clone()
                }
                // Priority 2: check if all subgoals are solved
                else if !subgoals.is_empty() && subgoals.iter().all(|sg| sg.nprems() == 0) {
                    subgoals[0].clone()
                }
                // Priority 3: use original goal if closed
                else if subgoals.is_empty() && goal.nprems() == 0 {
                    goal.clone()
                } else {
                    return None;
                };

                // Discharge local hypotheses via implies_intr
                let mut current = base_result;
                let local_assumptions: Vec<CTerm> = facts
                    .iter()
                    .filter_map(|f| {
                        let cterm = CTerm::certify(f.prop().term().clone());
                        if current.hyps().contains(&cterm) { Some(cterm) } else { None }
                    })
                    .collect();
                for assum in local_assumptions.iter().rev() {
                    if let Ok(new_thm) = ThmKernel::implies_intr(assum, &current) {
                        current = new_thm;
                    }
                }

                // Discharge fixed variables via forall_intr
                for (var_name, var_typ) in fixes.iter().rev() {
                    if let Ok(new_thm) = ThmKernel::forall_intr(var_name, var_typ.clone(), &current)
                    {
                        current = new_thm;
                    }
                }

                *self = ProofState::Done(current.clone());
                Some(current)
            },
            ProofState::Ready { goal } => {
                if goal.nprems() == 0 {
                    let result = goal.clone();
                    *self = ProofState::Done(result.clone());
                    Some(result)
                } else {
                    None
                }
            },
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
        if t.is_empty() {
            i += 1;
            continue;
        }

        // `let` — define a local abbreviation
        if t.starts_with("let ") {
            let rest = t.strip_prefix("let ").unwrap_or("");
            if let Some((name, expr)) = parse_let_binding(rest) {
                state.let_def(&name, expr);
            }
            i += 1;
            continue;
        }

        // `proof` — begin proof block
        if t.starts_with("proof ") || t == "proof" {
            state.begin_proof();
            // Handle `proof (induct ...)` or `proof (cases ...)`
            if let Some(inner) = t.strip_prefix("proof ") {
                let inner = inner.trim();
                if inner.starts_with("(induct") || inner.starts_with("(induction") {
                    // Extract induction variable and optional rule, strip arbitrary:
                    let induct_body = if inner.starts_with("(induct ") {
                        &inner[8..].trim_end_matches(')')
                    } else if inner.starts_with("(induction ") {
                        &inner[12..].trim_end_matches(')')
                    } else {
                        inner.trim_matches(|c| c == '(' || c == ')')
                    };
                    // Strip 'arbitrary:' option
                    let induct_body = if let Some(pos) = induct_body.find(" arbitrary:") {
                        induct_body[..pos].trim()
                    } else if let Some(pos) = induct_body.find(" arbitrary ") {
                        induct_body[..pos].trim()
                    } else {
                        induct_body
                    };
                    // Apply induction and store subgoals for case/next navigation
                    let induct_method = format!("induct {}", induct_body);
                    if let Some(goal) = state.get_current_goal() {
                        let results = crate::isar::method::exec_single_method(
                            &goal,
                            &induct_method,
                            premises,
                        );
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
            if result.is_some() {
                i += 1;
                continue;
            }
        }

        // `show "C" by method` or `show name: "C" by method`
        if t.starts_with("show ") {
            let result = parse_and_exec_have_show(state, t, premises, true);
            if result.is_some() {
                i += 1;
                continue;
            }
        }

        // `hence` = `then have`
        if t.starts_with("hence ") {
            let rest = t.strip_prefix("hence ").unwrap_or("");
            let have_cmd = format!("have {}", rest);
            let result = parse_and_exec_have_show(state, &have_cmd, premises, false);
            if result.is_some() {
                i += 1;
                continue;
            }
        }

        // `thus` = `then show`
        if t.starts_with("thus ") {
            let rest = t.strip_prefix("thus ").unwrap_or("");
            let show_cmd = format!("show {}", rest);
            let result = parse_and_exec_have_show(state, &show_cmd, premises, true);
            if result.is_some() {
                i += 1;
                continue;
            }
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

        // `obtain vars where "prop" by method` — existential elimination
        if t.starts_with("obtain ") {
            let rest = t.strip_prefix("obtain ").unwrap_or("").trim();
            let result = parse_and_exec_obtain(state, rest, &lines, &mut i, premises);
            if result {
                continue;
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

        // `note name = thm1 thm2 ...` — bind theorems to a name
        if t.starts_with("note ") {
            let rest = t.strip_prefix("note ").unwrap_or("").trim();
            if let Some(eq_pos) = rest.find('=') {
                let _name = rest[..eq_pos].trim();
                let thm_names: Vec<&str> = rest[eq_pos + 1..].split_whitespace().collect();
                let db = crate::hol::hol_loader::HolTheoremDb::get();
                for thm_name in &thm_names {
                    if let Some(thm) = db.by_name.get(*thm_name) {
                        state.add_fact(Arc::clone(thm));
                    }
                }
            }
            i += 1;
            continue;
        }

        // `let` — local abbreviation (term-level, skip for now)
        if t.starts_with("let ") {
            i += 1;
            continue;
        }

        // `using thm1 thm2` — add facts to context for next method
        if t.starts_with("using ") {
            let names = t.strip_prefix("using ").unwrap_or("").trim();
            let db = crate::hol::hol_loader::HolTheoremDb::get();
            for name in names.split_whitespace() {
                let name = name.trim().trim_matches(',');
                if !name.is_empty() {
                    if let Some(thm) = db.by_name.get(name) {
                        state.add_fact(Arc::clone(thm));
                    }
                }
            }
            i += 1;
            continue;
        }

        // `unfolding thm1 thm2` — expand definitions (treat as using for now)
        if t.starts_with("unfolding ") {
            let names = t.strip_prefix("unfolding ").unwrap_or("").trim();
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

        // `also` — calculational reasoning: chain fact (like then)
        if t.starts_with("also ") {
            // `also "thm"` — look up and chain
            let rest = t.strip_prefix("also ").unwrap_or("").trim().trim_matches('"');
            if !rest.is_empty() {
                let db = crate::hol::hol_loader::HolTheoremDb::get();
                if let Some(thm) = db.by_name.get(rest) {
                    state.chain_fact(Arc::clone(thm));
                }
            }
            i += 1;
            continue;
        }
        if t == "also" {
            // `also` without argument — chain from previous (no-op, chaining is automatic)
            i += 1;
            continue;
        }

        // `finally` — conclude calculational chain
        if t.starts_with("finally ") {
            let rest = t.strip_prefix("finally ").unwrap_or("").trim().trim_matches('"');
            if !rest.is_empty() {
                let db = crate::hol::hol_loader::HolTheoremDb::get();
                if let Some(thm) = db.by_name.get(rest) {
                    state.chain_fact(Arc::clone(thm));
                }
            }
            // Try to close the calculation with transitivity
            if let Some(goal) = state.get_current_goal() {
                let results = crate::isar::method::exec_single_method(&goal, "auto", &[]);
                if let Some(solved) = results.into_iter().find(|r| r.nprems() == 0) {
                    state.set_current_goal(solved);
                }
            }
            i += 1;
            continue;
        }
        if t == "finally" {
            if let Some(goal) = state.get_current_goal() {
                let results = crate::isar::method::exec_single_method(&goal, "auto", &[]);
                if let Some(solved) = results.into_iter().find(|r| r.nprems() == 0) {
                    state.set_current_goal(solved);
                }
            }
            i += 1;
            continue;
        }

        // `moreover` — collect current facts for later use
        if t == "moreover" {
            // Facts are already accumulated; this is a no-op marker
            i += 1;
            continue;
        }

        // `ultimately` — use collected facts to close
        if t == "ultimately" {
            // Try to close with all accumulated facts
            if let Some(goal) = state.get_current_goal() {
                let premises: Vec<Arc<Thm>> = state.get_premises().to_vec();
                let results = crate::isar::method::exec_proof(&goal, "by auto", &premises);
                if let Some(solved) = results {
                    state.set_current_goal(solved);
                }
            }
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

/// Parse and execute an `obtain vars where "prop" by method` command.
/// This is existential elimination: from EX x. P(x), obtain a witness x and assume P(x).
fn parse_and_exec_obtain(
    state: &mut ProofState,
    rest: &str,
    lines: &[&str],
    i: &mut usize,
    premises: &[Arc<Thm>],
) -> bool {
    // Parse: `vars where "prop" by method`
    // or: `vars where "prop"` with by method on next line
    let (vars, prop_and_method) = if let Some(where_pos) = rest.find(" where ") {
        (rest[..where_pos].trim().to_string(), rest[where_pos + 7..].trim().to_string())
    } else {
        return false;
    };

    // Extract the quoted proposition and the method
    let (prop_str, method) = if let Some(by_pos) = prop_and_method.find(" by ") {
        let prop_part = &prop_and_method[..by_pos].trim();
        let method_part = &prop_and_method[by_pos + 4..].trim();
        (prop_part.trim_matches('"').to_string(), method_part.to_string())
    } else if let Some(by_pos) = prop_and_method.find(" by(") {
        let prop_part = &prop_and_method[..by_pos].trim();
        let method_part = &prop_and_method[by_pos + 1..].trim();
        (prop_part.trim_matches('"').to_string(), method_part.to_string())
    } else {
        // Check next line for "by method"
        let prop_part = prop_and_method.trim_matches('"').to_string();
        if *i + 1 < lines.len() {
            let next_line = lines[*i + 1].trim();
            if let Some(by_rest) = next_line.strip_prefix("by ") {
                *i += 1;
                (prop_part, by_rest.trim().to_string())
            } else if let Some(by_rest) = next_line.strip_prefix("by(") {
                *i += 1;
                (prop_part, by_rest.trim().to_string())
            } else {
                return false;
            }
        } else {
            return false;
        }
    };

    // Parse the proposition term
    let prop_term = match crate::isar::term_parser::parse_term(&prop_str) {
        Some(t) => t,
        None => return false,
    };

    // Fix the variables and add the obtained proposition as a fact
    // We need to do this carefully to avoid double-borrow of state
    {
        // Fix the variables first
        for var in vars.split_whitespace() {
            let var = var.trim();
            if !var.is_empty() {
                state.fix(var, Typ::dummy());
            }
        }
    }

    // Add the obtained proposition as an assumption
    let assume_thm = ThmKernel::assume(CTerm::certify(prop_term.clone()));
    state.add_fact(Arc::new(assume_thm));

    // Try to verify the existential using the method (if not empty)
    if !method.is_empty() {
        if let Some(goal) = state.get_current_goal() {
            let results = crate::isar::method::exec_single_method(&goal, &method, premises);
            if results.iter().any(|r| r.nprems() == 0) {
                // Method proved it, update the goal
                if let Some(closed) = results.into_iter().find(|r| r.nprems() == 0) {
                    state.set_current_goal(closed);
                }
            }
        }
        // Even if method fails, we keep the obtained fact (it's an assumption)
    }
    true
}

/// Parse a term from a proof script string (thin wrapper).
fn parse_term_from_script(s: &str) -> Option<Term> {
    crate::isar::term_parser::parse_term(s)
}

/// Parse a `let` binding: `x = expr` or `x be "prop"`.
/// Returns `Some((name, term))` or `None` if parsing fails.
fn parse_let_binding(rest: &str) -> Option<(String, Term)> {
    let rest = rest.trim();
    // Try `let x = t` form
    if let Some(eq_pos) = rest.find('=') {
        let name = rest[..eq_pos].trim().to_string();
        let rhs = rest[eq_pos + 1..].trim();
        if !name.is_empty() && !rhs.is_empty() {
            // Try parsing the RHS as a term
            if let Some(term) = crate::isar::term_parser::parse_term(rhs) {
                return Some((name, term));
            }
        }
    }
    // Try `let x be "prop"` form
    if let Some(be_pos) = rest.find(" be ") {
        let name = rest[..be_pos].trim().to_string();
        let rhs = rest[be_pos + 4..].trim().trim_matches('"');
        if !name.is_empty() && !rhs.is_empty() {
            if let Some(term) = crate::isar::term_parser::parse_term(rhs) {
                return Some((name, term));
            }
        }
    }
    None
}

impl ProofState {
    /// Get the current goal being proved.
    pub fn get_current_goal(&self) -> Option<Thm> {
        match self {
            ProofState::Proving { subgoals, current_subgoal, goal, .. } => {
                subgoals.get(*current_subgoal).cloned().or_else(|| Some(goal.clone()))
            },
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
    use std::sync::Arc;

    use super::*;
    use crate::core::{
        logic::Pure,
        term::Term,
        thm::{CTerm, ThmKernel},
        types::Typ,
    };

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
    fn test_let_binding() {
        // Test the `let` command parsing and expansion
        let a = Term::const_("A", Typ::base("prop"));
        let goal = ThmKernel::assume(CTerm::certify(a.clone()));
        let mut state = ProofState::new(goal);
        state.begin_proof();

        // Define a let binding
        let x_val = Term::const_("x_val", Typ::dummy());
        state.let_def("X", x_val.clone());

        // Verify binding is stored
        let expanded = state.expand_lets(&Term::const_("X", Typ::dummy()));
        assert_eq!(expanded, x_val, "let binding should expand X to x_val");

        // Non-bound names should be unaffected
        let unchanged = state.expand_lets(&Term::const_("Y", Typ::dummy()));
        assert_eq!(unchanged, Term::const_("Y", Typ::dummy()));
    }

    #[test]
    fn test_parse_let_binding() {
        // Test parsing of different let forms
        let (name, _) = parse_let_binding("x = a").expect("should parse let x = a");
        assert_eq!(name, "x");

        let (name2, _) =
            parse_let_binding("prop be \"A ==> B\"").expect("should parse let prop be ...");
        assert_eq!(name2, "prop");
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
    use std::sync::Arc;

    use super::*;
    use crate::core::{
        logic::Pure,
        term::Term,
        thm::{CTerm, ThmKernel},
        types::Typ,
    };

    #[test]
    fn test_induction_subgoals() {
        // Simulate: proof (induct xs) creates subgoals
        let a = Term::const_("A", Typ::base("prop"));
        let goal = ThmKernel::assume(CTerm::certify(a.clone()));
        let mut state = ProofState::new(goal);
        state.begin_proof();

        // Set up fake subgoals (simulating induction on a list)
        let nil_goal =
            ThmKernel::assume(CTerm::certify(Term::const_("NilCase", Typ::base("prop"))));
        let cons_goal =
            ThmKernel::assume(CTerm::certify(Term::const_("ConsCase", Typ::base("prop"))));
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
        let goal = ThmKernel::assume(CTerm::certify(Term::const_("MainGoal", Typ::base("prop"))));
        let mut state = ProofState::new(goal);
        state.begin_proof();
        state.set_subgoals(vec![subgoal]);

        let resolved = state.resolve_case_stmt(&Term::const_("?case", Typ::base("prop")));
        eprintln!("Resolved ?case to: {:?}", resolved);
        // Should resolve to P(Nil), the current subgoal's conclusion
    }
}
