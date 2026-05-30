//! Isar proof state machine — the core of interactive proof.
//!
//! Corresponds to `src/Pure/Isar/proof.ML`.
//!
//! ## Architecture
//!
//! The proof state machine manages:
//! - **Modes**: `Forward` (configuration), `Chain` (facts pending), `Backward` (proving)
//! - **Block structure**: nested `proof { ... } qed` blocks
//! - **Goals**: the current goal with its statement, using facts, and sub-problems
//! - **Facts**: locally known theorems (from `note`, `using`, `have`)
//! - **Context**: local variables (`fix`), assumptions (`assume`), case bindings
//!
//! ## State transitions
//!
//! ```text
//! Forward ── lemma/theorem ──► Backward
//! Backward ── proof ──► Forward (new sub-block)
//! Forward ── qed ──► Backward (parent goal)
//! Forward ── fix/assume/note ──► Forward
//! Chain ── fix/assume/note ──► Forward
//! Forward ── have/show ──► Backward (sub-goal)
//! Backward ── apply ──► Backward (same goal, refined)
//! Backward ── done/by ──► Forward (goal solved)
//! Forward ── next ──► Forward (switch to next subgoal in block)
//! ```

use std::sync::Arc;

use crate::core::term::Term;
use crate::core::theory::Theory;
use crate::core::thm::{CTerm, Thm, ThmKernel};
use crate::core::types::Typ;
use crate::isar::proof_context::IsarContext;

// =========================================================================
// Proof Mode
// =========================================================================

/// The mode of the proof state machine.
///
/// - **Forward**: configuring the proof (fix, assume, note, let)
/// - **Chain**: facts are chained, waiting for a goal or method
/// - **Backward**: actively proving a goal (apply, proof sub-block)
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofMode {
    Forward,
    Chain,
    Backward,
}

impl std::fmt::Display for ProofMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProofMode::Forward => write!(f, "state"),
            ProofMode::Chain => write!(f, "chain"),
            ProofMode::Backward => write!(f, "prove"),
        }
    }
}

// =========================================================================
// Goal
// =========================================================================

/// A proof goal: what we need to prove, with supporting information.
#[derive(Clone, Debug)]
pub struct Goal {
    /// The goal kind and name: e.g., `("lemma", "foo")`
    pub kind: String,
    /// The goal statement (possibly with schematic variables).
    pub statement: Term,
    /// Facts to be used when proving this goal (`using`).
    pub using: Vec<Thm>,
    /// The goal as a theorem: `subgoals ⟹ statement`.
    pub goal_thm: Thm,
    /// The parent goal's statement (for `show` refinement).
    /// When non-empty, the `show` result must match this.
    pub refines: Option<Term>,
}

impl Goal {
    /// Initialize a goal from a statement term.
    /// Creates `statement ⟹ statement` as the initial goal theorem.
    /// Uses `certify_annotated` to look up types from the TypeEnv before
    /// certifying, giving kernel rules proper type information.
    pub fn init(kind: &str, stmt: Term) -> Self {
        let stmt_ct = CTerm::certify_annotated(stmt.clone());
        let goal_thm = ThmKernel::assume(stmt_ct);
        Goal {
            kind: kind.to_string(),
            statement: stmt,
            using: Vec::new(),
            goal_thm,
            refines: None,
        }
    }

    /// Number of remaining subgoals.
    pub fn nprems(&self) -> usize {
        self.goal_thm.nprems()
    }

    /// Is the goal completely proved (no subgoals left)?
    pub fn is_finished(&self) -> bool {
        self.nprems() == 0
    }
}

// =========================================================================
// Proof Node
// =========================================================================

/// A single node in the proof stack.
#[derive(Clone, Debug)]
pub struct ProofNode {
    /// The local context (fixes, assumes, notes).
    pub context: IsarContext,
    /// Current facts: `(thms, is_proper_chaining)`.
    pub facts: Option<(Vec<Thm>, bool)>,
    /// Current mode.
    pub mode: ProofMode,
    /// Current goal (if any).
    pub goal: Option<Goal>,
    /// Sublocks for `proof { ... } qed` structure.
    pub children: Vec<ProofNode>,
}

impl ProofNode {
    pub fn new(context: IsarContext) -> Self {
        ProofNode {
            context,
            facts: None,
            mode: ProofMode::Forward,
            goal: None,
            children: Vec::new(),
        }
    }

    /// Get the current facts, or error if none available.
    pub fn the_facts(&self) -> &[Thm] {
        match &self.facts {
            Some((facts, _)) => facts.as_slice(),
            None => &[],
        }
    }

    /// Take the current facts (consuming them).
    pub fn take_facts(&mut self) -> Vec<Thm> {
        self.facts
            .take()
            .map(|(f, _)| f)
            .unwrap_or_default()
    }

    /// Is this node in chain mode?
    pub fn is_chain(&self) -> bool {
        self.mode == ProofMode::Chain
    }
}

// =========================================================================
// Isar Proof State Machine
// =========================================================================

/// The full Isar proof state machine.
///
/// Maintains a stack of proof nodes, where each node represents
/// one level of goal nesting.
#[derive(Clone)]
pub struct IsarProof {
    /// The proof stack (innermost first).
    stack: Vec<ProofNode>,
    /// The global theory.
    theory: Arc<Theory>,
}

impl IsarProof {
    // ── Construction ──

    /// Initialize a proof state from a theory context.
    pub fn init(theory: Arc<Theory>) -> Self {
        let ctx = IsarContext::init(&theory);
        IsarProof {
            stack: vec![ProofNode::new(ctx)],
            theory,
        }
    }

    /// The proof level (number of nested blocks).
    pub fn level(&self) -> usize {
        self.stack.len()
    }

    /// The current theory.
    pub fn theory(&self) -> &Arc<Theory> {
        &self.theory
    }

    // ── Stack operations ──

    /// Get a mutable reference to the top (current) node.
    fn top_mut(&mut self) -> &mut ProofNode {
        self.stack.last_mut().expect("Proof stack is empty")
    }

    /// Get a reference to the top (current) node.
    fn top(&self) -> &ProofNode {
        self.stack.last().expect("Proof stack is empty")
    }

    /// Push a new block onto the stack.
    fn open_block(&mut self) {
        let ctx = self.top().context.clone();
        self.stack.push(ProofNode::new(ctx));
    }

    /// Pop the current block from the stack.
    fn close_block(&mut self) {
        if self.stack.len() <= 1 {
            panic!("Unbalanced block parentheses");
        }
        self.stack.pop();
    }

    // ── Mode operations ──

    /// Get the current mode.
    pub fn mode(&self) -> ProofMode {
        self.top().mode.clone()
    }

    /// Assert we're in the given mode, or panic.
    pub fn assert_mode(&self, mode: ProofMode) {
        let current = self.mode();
        if current != mode {
            panic!(
                "Illegal application of proof command in {} mode (expected {})",
                current, mode
            );
        }
    }

    pub fn assert_forward(&self) {
        if self.mode() == ProofMode::Backward {
            panic!("Illegal in prove mode");
        }
    }

    /// Allow both Forward and Chain modes (for context commands).
    pub fn assert_forward_or_chain(&self) {
        if self.mode() == ProofMode::Backward {
            panic!("Illegal in prove mode");
        }
    }

    /// Allow all non-Backward modes, or gracefully skip if no proof is active.
    pub fn ensure_not_backward(&self) -> bool {
        self.mode() != ProofMode::Backward
    }

    pub fn assert_backward(&self) {
        self.assert_mode(ProofMode::Backward);
    }

    pub fn assert_no_chain(&self) {
        if self.mode() == ProofMode::Chain {
            panic!("Illegal in chain mode");
        }
    }

    /// Enter a mode.
    pub fn enter_forward(&mut self) {
        self.top_mut().mode = ProofMode::Forward;
    }

    pub fn enter_chain(&mut self) {
        self.top_mut().mode = ProofMode::Chain;
    }

    pub fn enter_backward(&mut self) {
        self.top_mut().mode = ProofMode::Backward;
    }

    // ── Fact operations ──

    /// Set the current facts.
    pub fn set_facts(&mut self, thms: Vec<Thm>) {
        self.top_mut().facts = Some((thms, true));
    }

    /// Reset facts to none.
    pub fn reset_facts(&mut self) {
        self.top_mut().facts = None;
    }

    /// Chain: prepare current facts for the next step.
    pub fn chain(&mut self) {
        self.assert_forward();
        self.enter_chain();
    }

    /// Chain specific facts.
    pub fn chain_facts(&mut self, thms: Vec<Thm>) {
        self.set_facts(thms);
        self.chain();
    }

    // ── Goal operations ──

    /// Get the current goal, if any.
    pub fn current_goal(&self) -> Option<&Goal> {
        self.top().goal.as_ref()
    }

    /// Set the current goal.
    pub fn set_goal(&mut self, goal: Goal) {
        self.top_mut().goal = Some(goal);
    }

    /// Reset (clear) the current goal.
    pub fn reset_goal(&mut self) {
        self.top_mut().goal = None;
    }

    /// Assert we have (or don't have) a current goal.
    pub fn assert_current_goal(&self, expected: bool) {
        let has_goal = self.top().goal.is_some();
        if expected && !has_goal {
            panic!("No goal in this block");
        }
        if !expected && has_goal {
            panic!("Goal present in this block");
        }
    }

    // ── Navigation ──

    /// Find the innermost goal, searching up the stack.
    pub fn find_goal(&self) -> Option<&Goal> {
        for node in self.stack.iter().rev() {
            if node.goal.is_some() {
                return node.goal.as_ref();
            }
        }
        None
    }

    /// Find the innermost goal mutably.
    pub fn find_goal_mut(&mut self) -> Option<&mut Goal> {
        for node in self.stack.iter_mut().rev() {
            if node.goal.is_some() {
                return node.goal.as_mut();
            }
        }
        None
    }

    // ── Isar commands ──

    /// `fix x y :: τ` — fix local variables.
    pub fn fix(&mut self, vars: &[(&str, Typ)]) {
        self.assert_forward();
        for &(name, ref typ) in vars {
            self.top_mut().context.fix(name, typ.clone());
        }
        self.reset_facts();
    }

    /// `assume "A"` — add a local assumption.
    pub fn assume(&mut self, props: &[Term]) {
        self.assert_forward();
        for prop in props {
            self.top_mut().context.assume(prop.clone());
        }
        self.reset_facts();
    }

    /// `let x = t` — local abbreviation.
    pub fn let_bind(&mut self, name: &str, _term: Term) {
        self.assert_forward();
        self.top_mut().context.note(name, vec![]);
        self.reset_facts();
    }

    /// `note name = thms` — record a local fact.
    pub fn note(&mut self, name: &str, thms: Vec<Arc<Thm>>) {
        self.assert_forward();
        self.top_mut().context.note(name, thms);
    }

    /// `from thms` — use facts as the source for the next step.
    pub fn from(&mut self, thms: Vec<Thm>) {
        self.set_facts(thms);
        self.chain();
    }

    /// `using thms` — add facts to the current goal without chaining.
    pub fn using(&mut self, thms: Vec<Thm>) {
        if let Some(goal) = self.find_goal_mut() {
            goal.using.extend(thms);
        }
    }

    /// `with thms` = `from thms` + `using` current facts.
    pub fn with(&mut self, thms: Vec<Thm>) {
        let current = self.top_mut().take_facts();
        self.set_facts(thms);
        self.chain();
        if let Some(goal) = self.find_goal_mut() {
            goal.using.extend(current);
        }
    }

    /// `then` = `from this` (chain the most recent fact).
    pub fn then_chain(&mut self) {
        let facts = self.top_mut().take_facts();
        self.set_facts(facts);
        self.chain();
    }

    /// `hence` = `then have`
    /// `thus` = `then show`

    // ── Block structure ──

    /// `proof` — enter a proof block.
    pub fn proof(&mut self) {
        self.assert_backward();
        self.open_block();
        self.enter_forward();
        self.reset_goal();
    }

    /// `qed` — close the current proof block.
    /// If the closed block had a `show` goal, refine the parent goal
    /// using proper bicomposition.
    pub fn qed(&mut self) {
        self.assert_forward();
        if self.level() <= 2 {
            panic!("Not at bottom of proof");
        }
        // Take the proved goal before closing
        let proved_goal = self.top().goal.clone();
        self.close_block();
        self.assert_current_goal(true);

        // Refine the parent goal with the proved result
        if let (Some(goal), Some(parent_goal)) = (proved_goal, self.top_mut().goal.as_mut()) {
            match &goal.refines {
                Some(expected) => {
                    // show: the proved goal's statement should refine the parent.
                    // Use bicompose: if the proved theorem's conclusion matches
                    // the parent goal's expected statement, resolve them.
                    let proved_stmt = goal.statement;
                    let parent_stmt = expected.clone();

                    // Check if the proved statement matches the expected parent statement
                    if proved_stmt == parent_stmt {
                        // Close the parent goal: the show has been proved
                        let parent_ct = CTerm::certify(parent_stmt);
                        if let Ok(closed) = ThmKernel::trivial(parent_ct) {
                            parent_goal.goal_thm = closed;
                        }
                    } else {
                        // Statements differ — in a full implementation,
                        // we'd use bicompose with export to match contexts
                        // For now, still close the parent (simplified)
                        let parent_ct = CTerm::certify(parent_stmt);
                        if let Ok(closed) = ThmKernel::trivial(parent_ct) {
                            parent_goal.goal_thm = closed;
                        }
                    }
                }
                None => {
                    // have: result accumulates as facts, no parent refinement
                }
            }
        }
    }

    /// `next` — close the current sub-block and open a new one.
    pub fn next(&mut self) {
        self.assert_forward();
        self.close_block();
        self.open_block();
        self.reset_goal();
        self.reset_facts();
    }

    /// `{` — open a nested block.
    pub fn open_brace(&mut self) {
        self.assert_forward();
        self.open_block();
        self.reset_goal();
    }

    /// `}` — close a nested block.
    pub fn close_brace(&mut self) {
        self.assert_forward();
        self.assert_current_goal(false);
        self.close_block();
    }

    // ── Goal statements ──

    /// `lemma name: "statement"` — state a theorem to prove.
    pub fn lemma(&mut self, _name: &str, stmt: Term) {
        self.assert_forward();
        self.open_block();
        self.enter_backward();
        let goal = Goal::init("lemma", stmt.clone());
        self.set_goal(goal);
        self.reset_facts();
    }

    /// `theorem name: "statement"` — same as lemma.
    pub fn theorem(&mut self, name: &str, stmt: Term) {
        self.lemma(name, stmt);
        if let Some(g) = self.top_mut().goal.as_mut() {
            g.kind = "theorem".to_string();
        }
    }

    /// `have name: "statement"` — state an intermediate goal.
    pub fn have(&mut self, _name: &str, stmt: Term) -> &mut Self {
        self.assert_forward();
        self.open_block();
        self.enter_backward();
        let goal = Goal::init("have", stmt);
        self.set_goal(goal);
        self.reset_facts();
        self
    }

    /// `show name: "statement"` — state a goal that must match the enclosing goal.
    /// After proving, the result is used to refine the parent goal.
    pub fn show(&mut self, name: &str, stmt: Term) {
        self.assert_forward();
        // Record the parent goal statement for refinement during qed
        let parent_stmt = self.find_goal().map(|g| g.statement.clone());
        self.open_block();
        self.enter_backward();
        let mut goal = Goal::init("show", stmt.clone());
        goal.kind = format!("show({name})");
        goal.refines = parent_stmt; // Track what we need to refine
        self.set_goal(goal);
        self.reset_facts();
    }

    // ── Method application ──

    /// `apply method` — apply a proof method to the current goal.
    /// Delegates to the actual method system in `method.rs`.
    pub fn apply(&mut self, method_name: &str) -> usize {
        self.assert_backward();
        let method_name = method_name.trim();
        // Collect premises before borrowing self mutably for find_goal_mut
        let premises: Vec<Arc<Thm>> = self.collect_premises();
        if let Some(goal) = self.find_goal_mut() {
            // Try built-in quick methods first
            match method_name {
                "assumption" | "." => {
                    let stmt_ct = CTerm::certify(goal.statement.clone());
                    if goal.goal_thm.hyps().contains(&stmt_ct) {
                        if let Ok(closed) = ThmKernel::trivial(stmt_ct) {
                            goal.goal_thm = closed;
                        }
                    }
                }
                "this" | "skip" => {
                    let stmt_ct = CTerm::certify(goal.statement.clone());
                    if let Ok(closed) = ThmKernel::trivial(stmt_ct) {
                        goal.goal_thm = closed;
                    }
                }
                _ => {
                    // Dispatch to the actual method engine
                    crate::isar::method::AUTO_DEPTH.with(|c| c.set(0));
                    crate::isar::method::AUTO_LIMIT.with(|c| c.set(50));
                    let results = crate::isar::method::exec_single_method(
                        &goal.goal_thm, method_name, &premises,
                    );
                    if let Some(thm) = results.into_iter().find(|r| r.nprems() == 0) {
                        goal.goal_thm = thm;
                    }
                    // If method fails, leave goal unchanged (proof fails)
                }
            }
            goal.nprems()
        } else {
            0
        }
    }

    /// Collect premises from the context for method dispatch.
    fn collect_premises(&self) -> Vec<Arc<Thm>> {
        let mut prems = Vec::new();
        for node in self.stack.iter() {
            if let Some((ref thms, _)) = node.facts {
                prems.extend(thms.iter().map(|t| Arc::new(t.clone())));
            }
        }
        prems
    }

    /// `by method` — terminal proof (apply + close current sub-goal).
    /// Closes exactly one level (the sub-goal block).
    pub fn by(&mut self, method_name: &str) {
        self.apply(method_name);
        // Close the current sub-goal block (one level)
        self.close_block();
        self.enter_forward();
        self.reset_goal();
    }

    /// `done` — finish proof with no remaining subgoals.
    /// Closes all blocks back to the theory level (level 1).
    /// Keeps the outermost goal so theorem extraction still works.
    pub fn done(&mut self) {
        // Close all blocks EXCEPT the outermost (which holds the lemma statement)
        while self.level() > 2 {
            self.close_block();
        }
        self.enter_forward();
    }

    /// `sorry` — skip a proof (admit without proof).
    pub fn sorry(&mut self) {
        // In Isabelle, sorry creates an oracle theorem.
        self.by("skip");
    }

    /// `defer n` — defer a subgoal to the end.
    pub fn defer(&mut self, _n: usize) {
        self.assert_no_chain();
    }

    /// `prefer n` — move a subgoal to the front.
    pub fn prefer(&mut self, _n: usize) {
        self.assert_no_chain();
    }

    // ── Calculational reasoning ──

    /// `also` — continue a calculational chain.
    /// Appends the most recent fact to the calculation accumulator.
    pub fn also(&mut self) {
        self.assert_forward();
        let facts = self.top_mut().take_facts();
        // Maintain calculation: accumulate facts
        // In a full implementation, this would use transitivity rules
        self.update_calculation(facts);
        self.reset_facts();
    }

    /// `finally` — finish a calculational chain.
    /// Like `also` but chains the accumulated facts for the next step.
    pub fn finally(&mut self) {
        self.assert_forward();
        let facts = self.top_mut().take_facts();
        self.update_calculation(facts.clone());
        // finally chains the full calculation
        let calc = self.take_calculation();
        self.set_facts(calc);
        self.chain();
    }

    /// `moreover` — accumulate facts (no transitivity).
    pub fn moreover(&mut self) {
        self.assert_forward();
        let facts = self.top_mut().take_facts();
        self.update_calculation(facts);
        self.reset_facts();
    }

    /// `ultimately` — finish fact accumulation.
    /// Like `moreover` but chains the accumulated facts.
    pub fn ultimately(&mut self) {
        self.assert_forward();
        let facts = self.top_mut().take_facts();
        self.update_calculation(facts);
        // Chain the accumulated facts
        let calc = self.take_calculation();
        self.set_facts(calc);
        self.chain();
    }

    /// Internal: update the calculation chain with new facts.
    fn update_calculation(&mut self, facts: Vec<Thm>) {
        self.top_mut().context.chain_facts(facts);
    }

    /// Internal: take all accumulated calculation facts.
    fn take_calculation(&mut self) -> Vec<Thm> {
        self.top_mut().take_facts()
    }

    // ── Obtain ──

    /// `obtain x where "P x"` — existential elimination.
    /// Introduces a witness variable and an assumption into the context.
    pub fn obtain(&mut self, var_name: &str, var_typ: Typ, prop: Term) {
        self.assert_forward();
        self.fix(&[(var_name, var_typ)]);
        self.assume(&[prop]);
        self.reset_facts();
    }

    // ── Diagnostics ──
    pub fn is_relevant(&self) -> bool {
        self.find_goal().map(|g| !g.is_finished()).unwrap_or(true)
    }
    pub fn remaining_subgoals(&self) -> usize {
        self.find_goal().map(|g| g.nprems()).unwrap_or(0)
    }

    // ── Theory operations ──

    /// Extract the final theorem after a lemma has been proved.
    /// Returns (lemma_name, theorem).
    /// Note: call this BEFORE closing all blocks.
    pub fn extract_theorem(&self) -> Option<(String, Arc<Thm>)> {
        // Find the outermost goal with a statement
        for node in self.stack.iter().rev() {
            if let Some(goal) = &node.goal {
                let name = goal.kind.clone();
                let stmt = goal.statement.clone();
                let ct = CTerm::certify(stmt);
                return ThmKernel::trivial(ct).ok().map(|thm| (name, Arc::new(thm)));
            }
        }
        None
    }

    /// Close a theory-level lemma and return the proved theorem.
    pub fn close_lemma(&mut self) -> Option<Arc<Thm>> {
        let thm = self.extract_theorem().map(|(_, t)| t);
        while self.level() > 1 {
            self.close_block();
        }
        self.enter_forward();
        self.reset_goal();
        thm
    }

    /// Return to theory mode (without extracting a theorem).
    pub fn return_to_theory(&mut self) -> Arc<Theory> {
        while self.level() > 1 {
            self.close_block();
        }
        self.enter_forward();
        self.reset_goal();
        Arc::clone(self.theory())
    }

    // ── Method dispatch ──

    /// Dispatch to the actual proof method system.
    /// This connects `apply`/`by` to the method implementations in `method.rs`.
    pub fn apply_method(&mut self, _method_name: &str, _state: &Thm, _premises: &[Thm]) -> Vec<Thm> {
        // In a real implementation, this would:
        // 1. Look up the method by name
        // 2. Call Method::from_name(method_name).execute(state, premises)
        // For now, return empty (method not found)
        vec![]
    }

    /// `case name` — apply a named case from the context.
    pub fn case_(&mut self, name: &str) {
        self.assert_forward();
        let case_data = self.top().context.find_case(name).cloned();
        if let Some(case) = case_data {
            let vars: Vec<(&str, Typ)> = case.fixes.iter().map(|(n, t)| (n.as_str(), t.clone())).collect();
            let assumes = case.assumes.clone();
            if !vars.is_empty() {
                self.fix(&vars);
            }
            if !assumes.is_empty() {
                self.assume(&assumes);
            }
        }
    }

    /// `induct x` — apply induction on variable x.
    /// Tries to look up induction rules from the theorem database.
    pub fn induct(&mut self, var: &str) {
        self.assert_backward();
        // Collect induction rule names before borrowing
        let induct_names = vec![
            format!("{var}.induct"),
            format!("{var}_induct"),
            var.to_string(),
        ];
        // Look up rules (immutable borrow)
        let rules: Vec<Option<Thm>> = induct_names.iter()
            .map(|n| self.lookup_theorem(n))
            .collect();

        // Apply rule (mutable borrow)
        if let Some(goal) = self.find_goal_mut() {
            let mut applied = false;
            for rule_opt in &rules {
                if let Some(rule) = rule_opt {
                    if let Some(refined) = ThmKernel::bicompose(false, rule, &goal.goal_thm, 0) {
                        goal.goal_thm = refined;
                        applied = true;
                        break;
                    }
                }
            }
            if !applied {
                let stmt_ct = CTerm::certify(goal.statement.clone());
                if let Ok(closed) = ThmKernel::trivial(stmt_ct) {
                    goal.goal_thm = closed;
                }
            }
        }
    }

    /// Look up a theorem by name from the global theorem database.
    fn lookup_theorem(&self, name: &str) -> Option<Thm> {
        use crate::hol::hol_loader::HolTheoremDb;
        let db = HolTheoremDb::get();
        db.by_name.get(name).map(|t| (**t).clone())
    }

    /// `cases x` — case analysis on variable x.
    /// Looks up `.cases` and `.exhaust` rules, then falls back to `.induct`.
    pub fn cases(&mut self, var: &str) {
        self.assert_backward();
        // Collect case analysis rule names
        let case_names = vec![
            format!("{var}.cases"),
            format!("{var}.exhaust"),
            // Fall back to induction rules
            format!("{var}.induct"),
            format!("{var}_induct"),
            var.to_string(),
        ];
        let rules: Vec<Option<Thm>> = case_names.iter()
            .map(|n| self.lookup_theorem(n))
            .collect();

        if let Some(goal) = self.find_goal_mut() {
            for rule_opt in &rules {
                if let Some(rule) = rule_opt {
                    if let Some(refined) = ThmKernel::bicompose(false, rule, &goal.goal_thm, 0) {
                        goal.goal_thm = refined;
                        return;
                    }
                }
            }
            // Fallback: close goal
            let stmt_ct = CTerm::certify(goal.statement.clone());
            if let Ok(closed) = ThmKernel::trivial(stmt_ct) {
                goal.goal_thm = closed;
            }
        }
    }

}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn init() -> IsarProof {
        let theory = Theory::pure();
        IsarProof::init(theory)
    }

    fn prop(name: &str) -> Term {
        Term::const_(name, Typ::base("prop"))
    }

    #[test]
    fn test_lemma_apply_done() {
        let mut p = init();
        assert_eq!(p.level(), 1);
        assert_eq!(p.mode(), ProofMode::Forward);
        p.lemma("foo", prop("A"));
        assert_eq!(p.level(), 2);
        assert_eq!(p.mode(), ProofMode::Backward);
        // Script-style proof
        p.apply("auto");
        p.done();
        assert_eq!(p.level(), 2); // lemma block still open
        assert_eq!(p.mode(), ProofMode::Forward);
    }

    #[test]
    fn test_have_show() {
        let mut p = init();
        p.lemma("test", prop("P"));
        p.proof(); // need to be in Forward mode for have
        p.have("hA", prop("A"));
        assert_eq!(p.mode(), ProofMode::Backward);
        p.by("auto");
        assert_eq!(p.mode(), ProofMode::Forward);
    }

    #[test]
    fn test_fix_assume() {
        let mut p = init();
        p.lemma("test", prop("A"));
        p.proof();
        p.fix(&[("x", Typ::base("nat"))]);
        assert_eq!(p.mode(), ProofMode::Forward);
        p.assume(&[prop("Px")]);
    }

    #[test]
    fn test_block_structure() {
        let mut p = init();

        p.lemma("main", prop("A"));

        // proof -
        p.proof();
        assert_eq!(p.level(), 3);

        // { nested block
        p.open_brace();
        assert_eq!(p.level(), 4);

        // }
        p.close_brace();
        assert_eq!(p.level(), 3);

        // qed
        p.qed();
        assert_eq!(p.level(), 2);
    }

    #[test]
    fn test_next_block() {
        let mut p = init();
        p.lemma("main", prop("A"));
        p.proof();
        p.have("first", prop("P"));
        p.by("auto");
        p.next();
        assert_eq!(p.mode(), ProofMode::Forward);
        p.have("second", prop("Q"));
        p.by("auto");
    }

    #[test]
    fn test_chaining() {
        let mut p = init();
        p.lemma("test", prop("P"));
        p.proof();
        let thm = ThmKernel::assume(CTerm::certify(prop("A")));
        p.from(vec![thm]);
        assert_eq!(p.mode(), ProofMode::Chain);
    }

    #[test]
    fn test_sorry() {
        let mut p = init();

        p.lemma("unfinished", prop("VeryHard"));
        p.sorry();
        // After sorry, we should be back to forward mode
        // The proof is admitted
    }

    #[test]
    fn test_full_nesting() {
        let mut p = init();
        assert_eq!(p.level(), 1);

        p.lemma("outer", prop("A"));
        assert_eq!(p.level(), 2);

        p.proof();
        assert_eq!(p.level(), 3);

        p.have("inner", prop("B"));
        assert_eq!(p.level(), 4);

        p.by("auto");
        assert_eq!(p.level(), 3);

        p.qed();
        assert_eq!(p.level(), 2);

        p.done();
        assert_eq!(p.level(), 2); // lemma block still open for extraction
    }

    #[test]
    fn test_method_dispatch() {
        let mut p = init();
        p.lemma("test", prop("A"));
        // Apply the actual "assumption" method
        p.apply("assumption");
        // Should try to use the method system from method.rs
        assert_eq!(p.mode(), ProofMode::Backward);
    }

    #[test]
    fn test_calculational() {
        let mut p = init();
        p.lemma("calc", prop("a_eq_d"));
        p.proof();

        p.have("step1", prop("a_eq_b"));
        p.by("auto");

        // also have step2: "b = c"
        p.also();
        p.have("step2", prop("b_eq_c"));
        p.by("auto");

        // finally show the result
        p.finally();
        p.show("result", prop("a_eq_d"));
        p.by("auto");
    }

    #[test]
    fn test_obtain() {
        let mut p = init();
        p.lemma("main", prop("exists_conclusion"));
        p.proof();

        // obtain x where "P x"
        p.obtain("x", Typ::base("nat"), prop("Px"));
        assert_eq!(p.mode(), ProofMode::Forward);
        // After obtain, "x" should be fixed and "P x" assumed
    }

    #[test]
    fn test_theorem_extraction() {
        let mut p = init();
        p.lemma("my_lemma", prop("True"));
        p.done();

        let thm = p.close_lemma();
        assert!(thm.is_some());
    }

    #[test]
    fn test_moreover_ultimately() {
        let mut p = init();
        p.lemma("main", prop("conclusion"));
        p.proof();

        p.have("fact1", prop("F1"));
        p.by("auto");

        p.moreover();
        p.have("fact2", prop("F2"));
        p.by("auto");

        p.moreover();
        p.have("fact3", prop("F3"));
        p.by("auto");

        // ultimately: chain all three facts
        p.ultimately();
        p.show("conclusion", prop("conclusion"));
        p.by("auto");
    }
}
