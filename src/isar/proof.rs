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

use super::proof_result::{
    GoalExportError, apply_goal_method, export_scoped_result, validate_proof_result,
};
use crate::{
    core::{
        error::KernelError,
        term::Term,
        theory::Theory,
        thm::{CTerm, KernelCheckMode, Thm, ThmKernel},
        types::Typ,
    },
    hol::hol_loader::HolTheoremDb,
    isar::proof_context::{IsarContext, ProofCertContext},
};

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
    /// The goal as a Strict open theorem (`statement |- statement`).
    /// This represents a proof obligation, not a closed proved lemma.
    pub goal_thm: Thm,
    /// The parent goal's statement (for `show` refinement).
    /// When non-empty, the `show` result must match this.
    pub refines: Option<Term>,
    name: String,
    proof_result: Option<Thm>,
    proof_error: Option<GoalExportError>,
    assumptions_len: usize,
    fixes_len: usize,
    allowed_hypotheses: Vec<CTerm>,
}

impl Goal {
    /// Initialize a proof goal from a checked proposition.
    ///
    /// The internal theorem is a Strict open theorem `A |- A`, representing a
    /// proof obligation. It is not a closed proved lemma and must not be
    /// registered in trusted theorem tables.
    pub fn from_checked_prop(kind: &str, stmt_ct: CTerm) -> Result<Self, KernelError> {
        let statement = stmt_ct.term().clone();
        let goal_thm = ThmKernel::assume(stmt_ct)?;
        goal_thm.check_kernel_invariants(KernelCheckMode::Strict)?;
        Ok(Goal {
            kind: kind.to_string(),
            statement,
            using: Vec::new(),
            goal_thm,
            refines: None,
            proof_result: None,
            proof_error: None,
            assumptions_len: 0,
            fixes_len: 0,
            allowed_hypotheses: Vec::new(),
            name: String::new(),
        })
    }

    /// Initialize a goal from a statement term certified against an explicit
    /// proof context.
    pub fn init_checked_in_context(
        ctx: &ProofCertContext,
        kind: &str,
        stmt: Term,
    ) -> Result<Self, KernelError> {
        let stmt_ct = ctx.certify_prop(stmt)?;
        Self::from_checked_prop(kind, stmt_ct)
    }

    /// Initialize a goal through the checked path using an empty Pure context.
    ///
    /// This intentionally does not auto-declare constants or frees from the
    /// term itself. Call `init_checked_in_context` when user/theory constants
    /// or local frees are expected.
    pub fn init_checked(kind: &str, stmt: Term) -> Result<Self, KernelError> {
        Self::init_checked_in_context(&ProofCertContext::new(), kind, stmt)
    }

    pub fn init_in_isar_context(
        kind: &str,
        stmt: Term,
        ctx: &IsarContext,
    ) -> Result<Self, KernelError> {
        let cert_ctx = ProofCertContext::from_isar_context(ctx);
        let mut goal = Self::init_checked_in_context(&cert_ctx, kind, stmt)?;
        goal.allowed_hypotheses = ctx
            .assumptions()
            .iter()
            .map(|term| cert_ctx.certify_prop(term.clone()))
            .collect::<Result<_, _>>()?;
        goal.assumptions_len = ctx.assumptions().len();
        goal.fixes_len = ctx.fixes().len();
        Ok(goal)
    }

    /// Initialize a goal from a statement term.
    ///
    /// This is now a checked proof-goal boundary. Parser/type-context gaps
    /// should be fixed before calling this path; do not silently fall back to
    /// compatibility theorem construction here.
    pub fn init(kind: &str, stmt: Term) -> Self {
        Self::init_checked(kind, stmt).expect("Goal::init requires a checked proposition")
    }

    /// Initialize a goal from a new-kernel elaborated CProp.
    ///
    /// The CProp is already certified by `ProofContext::certify_prop`.
    /// We convert it to a legacy CTerm and proceed through the existing
    /// strict goal infrastructure.
    pub fn init_from_elaborated_cprop(
        kind: &str,
        cprop: &crate::kernel::CProp,
        ctx: &ProofCertContext,
    ) -> Result<Self, KernelError> {
        let core_term =
            crate::core::kernel_convert::kernel_term_to_core(cprop.term()).map_err(|e| {
                KernelError::BetaConversion(format!("kernel term conversion failed: {}", e))
            })?;
        let stmt_ct = ctx.certify_prop(core_term)?;
        Self::from_checked_prop(kind, stmt_ct)
    }

    /// Number of remaining subgoals.
    pub fn nprems(&self) -> usize {
        usize::from(!self.is_finished())
    }

    /// A goal is finished only by a checked derivation of its entire statement.
    pub fn is_finished(&self) -> bool {
        self.proof_result.as_ref().is_some_and(|result| {
            validate_proof_result(&self.statement, result, &self.allowed_hypotheses).is_ok()
        })
    }
}

// =========================================================================
// Proof Node
// =========================================================================

/// A single node in the proof stack.
#[derive(Clone, Debug)]
pub struct ProofNode {
    /// The local context (fixes, assumes, notes).
    pub context: Arc<IsarContext>,
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
    pub fn new(context: Arc<IsarContext>) -> Self {
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
        self.facts.take().map(|(f, _)| f).unwrap_or_default()
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
        let ctx = Arc::new(IsarContext::init(&theory));
        IsarProof { stack: vec![ProofNode::new(ctx)], theory }
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
        let ctx = Arc::clone(&self.top().context);
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
            panic!("Illegal application of proof command in {} mode (expected {})", current, mode);
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

    /// `fix x y :: τ` — introduce fresh, explicitly typed local variables.
    pub fn fix(&mut self, vars: &[(&str, Typ)]) -> Result<(), GoalExportError> {
        self.require_forward()?;
        for (index, (name, typ)) in vars.iter().enumerate() {
            if typ.contains_dummy()
                || self.top().context.fixes().iter().any(|(old, _)| old.as_ref() == *name)
                || vars[..index].iter().any(|(old, _)| old == name)
            {
                return Err(GoalExportError::InvalidScript { line: 1 });
            }
        }
        for (name, typ) in vars {
            Arc::make_mut(&mut self.top_mut().context).fix(name, typ.clone());
        }
        self.reset_facts();
        Ok(())
    }

    /// `assume "A"` — authorize only propositions certified in the real context.
    pub fn assume(&mut self, props: &[Term]) -> Result<(), GoalExportError> {
        self.require_forward()?;
        let context = ProofCertContext::from_isar_context(&self.top().context);
        for prop in props {
            context.certify_prop(prop.clone())?;
        }
        for prop in props {
            Arc::make_mut(&mut self.top_mut().context).assume(prop.clone());
        }
        self.reset_facts();
        Ok(())
    }

    fn require_forward(&self) -> Result<(), GoalExportError> {
        if self.mode() == ProofMode::Backward {
            return Err(GoalExportError::InvalidScript { line: 1 });
        }
        Ok(())
    }

    /// `let x = t` — local abbreviation.
    pub fn let_bind(&mut self, name: &str, _term: Term) {
        self.assert_forward();
        Arc::make_mut(&mut self.top_mut().context).note(name, vec![]);
        self.reset_facts();
    }

    /// `note name = thms` — record a local fact.
    pub fn note(&mut self, name: &str, thms: Vec<Arc<Thm>>) {
        self.assert_forward();
        Arc::make_mut(&mut self.top_mut().context).note(name, thms);
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

    // ── Block structure ──

    /// `proof` opens a scope without supplying any proof evidence.
    pub fn proof(&mut self) -> Result<(), GoalExportError> {
        if self.mode() != ProofMode::Backward || self.current_goal().is_none() {
            return Err(GoalExportError::InvalidScript { line: 1 });
        }
        self.open_block();
        Ok(())
    }

    /// Close a structured block only after its enclosing goal has a real result.
    pub fn qed(&mut self) -> Result<(), GoalExportError> {
        self.require_forward()?;
        if self.level() <= 2 || self.top().goal.is_some() {
            return Err(GoalExportError::MissingProofResult);
        }
        let parent = &self.stack[self.stack.len() - 2];
        let goal = parent.goal.as_ref().ok_or(GoalExportError::MissingProofResult)?;
        Self::validate_goal_result(goal)?;
        self.close_block();
        self.finish_current_goal()
    }

    fn validate_goal_result(goal: &Goal) -> Result<&Thm, GoalExportError> {
        let result = goal.proof_result.as_ref().ok_or_else(|| {
            goal.proof_error.clone().unwrap_or(GoalExportError::MissingProofResult)
        })?;
        validate_proof_result(&goal.statement, result, &goal.allowed_hypotheses)?;
        Ok(result)
    }

    fn finish_current_goal(&mut self) -> Result<(), GoalExportError> {
        let goal = self.current_goal().ok_or(GoalExportError::MissingProofResult)?;
        let result = Self::validate_goal_result(goal)?.clone();
        if goal.refines.is_some() {
            self.export_show_result(&result)?;
            self.close_block();
        } else if goal.kind == "have" {
            self.close_block();
            self.set_facts(vec![result]);
        }
        self.enter_forward();
        Ok(())
    }

    fn export_show_result(&mut self, result: &Thm) -> Result<(), GoalExportError> {
        let current = self.stack.len() - 1;
        let parent = self.stack[..current]
            .iter()
            .rposition(|node| node.goal.is_some())
            .ok_or(GoalExportError::UnsupportedComposition)?;
        let goal = self.stack[parent].goal.as_ref().ok_or(GoalExportError::MissingProofResult)?;
        let context = &self.top().context;
        let assumptions = Self::certify_assumptions(context)?;
        let local = assumptions
            .get(goal.assumptions_len..)
            .ok_or(GoalExportError::UnsupportedComposition)?;
        let fixes = context
            .fixes()
            .get(goal.fixes_len..)
            .ok_or(GoalExportError::UnsupportedComposition)?
            .iter()
            .map(|(name, typ)| (name.to_string(), typ.clone()))
            .collect::<Vec<_>>();
        let exported = export_scoped_result(
            goal.goal_thm.prop(),
            result,
            local,
            &fixes,
            &goal.allowed_hypotheses,
        )?;
        if let Some(goal) = self.stack[parent].goal.as_mut() {
            goal.proof_result = Some(exported);
            goal.proof_error = None;
        }
        Ok(())
    }

    fn certify_assumptions(context: &IsarContext) -> Result<Vec<CTerm>, GoalExportError> {
        let cert = ProofCertContext::from_isar_context(context);
        context
            .assumptions()
            .iter()
            .map(|term| cert.certify_prop(term.clone()).map_err(GoalExportError::from))
            .collect()
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

    /// State a theory-level goal without granting its synthetic hypothesis.
    pub fn lemma(&mut self, name: &str, stmt: Term) -> Result<(), GoalExportError> {
        if self.find_goal().is_some() {
            return Err(GoalExportError::UnsupportedComposition);
        }
        self.begin_goal("lemma", name, stmt, None)
    }

    pub fn theorem(&mut self, name: &str, stmt: Term) -> Result<(), GoalExportError> {
        self.lemma(name, stmt)?;
        if let Some(goal) = self.find_goal_mut() {
            goal.kind = "theorem".into();
        }
        Ok(())
    }

    /// State an intermediate goal; only its actual result becomes a fact.
    pub fn have(&mut self, name: &str, stmt: Term) -> Result<(), GoalExportError> {
        self.begin_goal("have", name, stmt, None)
    }

    /// The actual show result must export to the complete enclosing goal.
    pub fn show(&mut self, name: &str, stmt: Term) -> Result<(), GoalExportError> {
        let parent = self.find_goal().ok_or(GoalExportError::MissingProofResult)?.statement.clone();
        self.begin_goal("show", name, stmt, Some(parent))
    }

    fn begin_goal(
        &mut self,
        kind: &str,
        name: &str,
        statement: Term,
        refines: Option<Term>,
    ) -> Result<(), GoalExportError> {
        self.require_forward()?;
        let mut goal = Goal::init_in_isar_context(kind, statement, &self.top().context)?;
        goal.refines = refines;
        goal.name = name.to_string();
        self.open_block();
        self.set_goal(goal);
        self.enter_backward();
        Ok(())
    }

    // ── Method application ──

    /// Apply exactly the requested method; failed attempts leave the obligation open.
    pub fn apply(&mut self, method_name: &str, db: &HolTheoremDb) -> usize {
        let attempt = self.apply_checked(method_name, db);
        if let Err(error) = attempt
            && let Some(goal) = self.find_goal_mut()
        {
            goal.proof_result = None;
            goal.proof_error = Some(error);
        }
        self.remaining_subgoals()
    }

    pub(crate) fn apply_checked(
        &mut self,
        method: &str,
        db: &HolTheoremDb,
    ) -> Result<(), GoalExportError> {
        if self.mode() != ProofMode::Backward {
            return Err(GoalExportError::InvalidScript { line: 1 });
        }
        let assumptions = Self::certify_assumptions(&self.top().context)?;
        let premises = self.collect_premises(&assumptions)?;
        let goal = self.find_goal_mut().ok_or(GoalExportError::MissingProofResult)?;
        goal.proof_result = None;
        goal.proof_error = None;
        let result = apply_goal_method(goal.goal_thm.prop(), method, &premises, &assumptions, db)?
            .ok_or(GoalExportError::MissingProofResult)?;
        goal.proof_result = Some(result);
        Ok(())
    }

    fn collect_premises(&self, assumptions: &[CTerm]) -> Result<Vec<Arc<Thm>>, GoalExportError> {
        let mut premises = Vec::new();
        for node in &self.stack {
            if let Some((facts, _)) = &node.facts {
                premises.extend(facts.iter().cloned().map(Arc::new));
            }
        }
        if let Some(goal) = self.find_goal() {
            premises.extend(goal.using.iter().cloned().map(Arc::new));
        }
        for assumption in assumptions {
            premises.push(Arc::new(ThmKernel::assume(assumption.clone())?));
        }
        Ok(premises)
    }

    /// Terminal method application, validated before any scope is closed.
    pub fn by(&mut self, method: &str, db: &HolTheoremDb) -> Result<(), GoalExportError> {
        self.apply_checked(method, db)?;
        self.finish_current_goal()
    }

    /// Finish only an existing result; never manufacture or discard obligations.
    pub fn done(&mut self) -> Result<(), GoalExportError> {
        if self.current_goal().is_none() {
            return self.qed();
        }
        self.finish_current_goal()
    }

    /// An admission is not a completed proof and cannot enter the theorem table.
    pub fn sorry(&mut self) {
        if let Some(goal) = self.find_goal_mut() {
            goal.proof_result = None;
            goal.proof_error = Some(GoalExportError::OracleOrAdmitted);
        }
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
        Arc::make_mut(&mut self.top_mut().context).chain_facts(facts);
    }

    /// Internal: take all accumulated calculation facts.
    fn take_calculation(&mut self) -> Vec<Thm> {
        self.top_mut().take_facts()
    }

    // ── Obtain ──

    /// `obtain x where "P x"` — existential elimination.
    /// Introduces a witness variable and an assumption into the context.
    pub fn obtain(
        &mut self,
        var_name: &str,
        var_typ: Typ,
        prop: Term,
    ) -> Result<(), GoalExportError> {
        self.fix(&[(var_name, var_typ)])?;
        self.assume(&[prop])?;
        self.reset_facts();
        Ok(())
    }

    // ── Diagnostics ──
    pub fn is_relevant(&self) -> bool {
        self.find_goal().map(|g| !g.is_finished()).unwrap_or(true)
    }
    pub fn remaining_subgoals(&self) -> usize {
        self.find_goal().map(|g| g.nprems()).unwrap_or(0)
    }

    // ── Theory operations ──

    /// Extract only the actual, fully checked result of the outermost lemma.
    pub fn extract_theorem(&self) -> Result<(String, Arc<Thm>), GoalExportError> {
        let goal = self
            .stack
            .iter()
            .find_map(|node| node.goal.as_ref())
            .ok_or(GoalExportError::MissingProofResult)?;
        let result = Self::validate_goal_result(goal)?;
        if !matches!(self.stack.as_slice(), [_, ProofNode { mode: ProofMode::Forward, .. }]) {
            return Err(GoalExportError::OpenSubgoals);
        }
        validate_proof_result(&goal.statement, result, &[])?;
        Ok((goal.name.clone(), Arc::new(result.clone())))
    }

    pub fn close_lemma(&mut self) -> Result<Arc<Thm>, GoalExportError> {
        let (_, theorem) = self.extract_theorem()?;
        while self.level() > 1 {
            self.close_block();
        }
        self.enter_forward();
        self.reset_goal();
        Ok(theorem)
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
    pub fn apply_method(
        &mut self,
        _method_name: &str,
        _state: &Thm,
        _premises: &[Thm],
    ) -> Vec<Thm> {
        // In a real implementation, this would:
        // 1. Look up the method by name
        // 2. Call Method::from_name(method_name).execute(state, premises)
        // For now, return empty (method not found)
        vec![]
    }

    /// `case name` — apply a named case from the context.
    pub fn case_(&mut self, name: &str) -> Result<(), GoalExportError> {
        self.require_forward()?;
        let case_data = self.top().context.find_case(name).cloned();
        if let Some(case) = case_data {
            let vars: Vec<(&str, Typ)> =
                case.fixes.iter().map(|(n, t)| (n.as_str(), t.clone())).collect();
            let assumes = case.assumes.clone();
            if !vars.is_empty() {
                self.fix(&vars)?;
            }
            if !assumes.is_empty() {
                self.assume(&assumes)?;
            }
        }
        Ok(())
    }

    /// `induct x` — apply induction on variable x.
    /// Tries to look up induction rules from the theorem database.
    pub fn induct(&mut self, var: &str, db: &HolTheoremDb) {
        self.assert_backward();
        // Collect induction rule names before borrowing
        let induct_names = [format!("{var}.induct"), format!("{var}_induct"), var.to_string()];
        // Look up rules (immutable borrow)
        let rules: Vec<Option<Thm>> =
            induct_names.iter().map(|n| Self::lookup_theorem(n, db)).collect();

        // Apply rule (mutable borrow)
        if let Some(goal) = self.find_goal_mut() {
            let mut applied = false;
            for rule_opt in &rules {
                if let Some(rule) = rule_opt
                    && let Some(refined) = ThmKernel::bicompose(false, rule, &goal.goal_thm, 0)
                {
                    goal.goal_thm = refined;
                    applied = true;
                    break;
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

    /// Look up a theorem by name from the supplied theorem database.
    fn lookup_theorem(name: &str, db: &HolTheoremDb) -> Option<Thm> {
        db.by_name.get(name).map(|t| (**t).clone())
    }

    /// `cases x` — case analysis on variable x.
    /// Looks up `.cases` and `.exhaust` rules, then falls back to `.induct`.
    pub fn cases(&mut self, var: &str, db: &HolTheoremDb) {
        self.assert_backward();
        // Collect case analysis rule names
        let case_names = [
            format!("{var}.cases"),
            format!("{var}.exhaust"),
            // Fall back to induction rules
            format!("{var}.induct"),
            format!("{var}_induct"),
            var.to_string(),
        ];
        let rules: Vec<Option<Thm>> =
            case_names.iter().map(|n| Self::lookup_theorem(n, db)).collect();

        if let Some(goal) = self.find_goal_mut() {
            for rule_opt in &rules {
                if let Some(rule) = rule_opt
                    && let Some(refined) = ThmKernel::bicompose(false, rule, &goal.goal_thm, 0)
                {
                    goal.goal_thm = refined;
                    return;
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
    use crate::core::thm::ThmTrust;

    fn cert_ctx(names: &[&str]) -> ProofCertContext {
        let mut ctx = ProofCertContext::new();
        for name in names {
            ctx.declare_const(name, Typ::base("prop"));
        }
        ctx
    }

    fn prop(name: &str) -> Term {
        Term::const_(name, Typ::base("prop"))
    }

    #[test]
    fn proof_goal_checked_constructor_is_strict_open_theorem() {
        let ctx = cert_ctx(&["A"]);
        let goal = Goal::init_checked_in_context(&ctx, "lemma", prop("A")).unwrap();

        assert_eq!(goal.goal_thm.trust_status(), ThmTrust::Strict);
        assert_eq!(goal.goal_thm.hyps().len(), 1);
        assert!(!goal.goal_thm.is_strict_closed_proved());
    }

    #[test]
    fn proof_goal_checked_constructor_passes_strict_invariant() {
        let ctx = cert_ctx(&["A"]);
        let goal = Goal::init_checked_in_context(&ctx, "lemma", prop("A")).unwrap();

        goal.goal_thm.check_kernel_invariants(KernelCheckMode::Strict).unwrap();
    }

    #[test]
    fn proof_goal_checked_constructor_rejects_compat_cterm() {
        let compat = CTerm::certify(prop("A"));
        let result = Goal::from_checked_prop("lemma", compat);

        assert!(matches!(result, Err(KernelError::CompatCTerm { .. })));
    }

    #[test]
    fn proof_goal_checked_constructor_rejects_dummy_type() {
        let result = Goal::init_checked("lemma", Term::free("x", Typ::dummy()));

        assert!(matches!(result, Err(KernelError::DummyType { .. })));
    }

    #[test]
    fn proof_goal_checked_constructor_rejects_undeclared_const() {
        let result = Goal::init_checked("lemma", prop("Fake.const"));

        assert!(matches!(result, Err(KernelError::UndeclaredConstant(_))));
    }

    #[test]
    fn proof_goal_checked_constructor_accepts_declared_const() {
        let ctx = cert_ctx(&["Declared"]);
        let goal = Goal::init_checked_in_context(&ctx, "lemma", prop("Declared")).unwrap();

        assert_eq!(goal.goal_thm.trust_status(), ThmTrust::Strict);
        assert!(!goal.goal_thm.is_strict_closed_proved());
    }
}
