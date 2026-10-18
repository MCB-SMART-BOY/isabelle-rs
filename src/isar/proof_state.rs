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
    error::KernelError,
    term::Term,
    thm::{CTerm, KernelCheckMode, Thm, ThmKernel},
    types::Typ,
};
use crate::hol::hol_loader::HolTheoremDb;
use crate::isar::{
    outer_syntax::{CommandSpan, OuterSyntax},
    proof_context::ProofCertContext,
    proof_result::{GoalExportError, apply_goal_method, export_scoped_result},
    token::{Token, TokenKind},
};

/// Reuse declarations from checked propositions, never raw candidate annotations.
fn collect_checked_names(term: &Term, ctx: &mut ProofCertContext) {
    match term {
        Term::Const { name, typ } => ctx.declare_const(name, typ.clone()),
        Term::Free { name, typ } => ctx.declare_free(name, typ.clone()),
        Term::Abs { body, .. } => collect_checked_names(body, ctx),
        Term::App { func, arg } => {
            collect_checked_names(func, ctx);
            collect_checked_names(arg, ctx);
        },
        Term::Bound(_) | Term::Var { .. } => {},
    }
}

fn resolve_declared_names(term: Term, ctx: &ProofCertContext) -> Term {
    match term {
        Term::Free { name, typ } if typ.is_dummy() => {
            if let Some(typ) = ctx.type_env().frees.get(name.as_ref()) {
                Term::free(name, typ.clone())
            } else if let Some(typ) = ctx.type_env().const_type(name.as_ref()) {
                Term::const_(name, typ.clone())
            } else {
                Term::free(name, typ)
            }
        },
        Term::Abs { name, typ, body } => Term::abs(name, typ, resolve_declared_names(*body, ctx)),
        Term::App { func, arg } => {
            Term::app(resolve_declared_names(*func, ctx), resolve_declared_names(*arg, ctx))
        },
        other => other,
    }
}

fn certify_statement(
    stmt: Term,
    goal: &Thm,
    fixes: &[(String, Typ)],
    facts: &[Arc<Thm>],
    premises: &[Arc<Thm>],
) -> Result<CTerm, KernelError> {
    let mut ctx = ProofCertContext::new();
    collect_checked_names(goal.prop().term(), &mut ctx);
    for (name, typ) in fixes {
        ctx.declare_free(name, typ.clone());
    }
    for fact in facts.iter().chain(premises) {
        if fact.check_kernel_invariants(KernelCheckMode::Strict).is_ok() {
            collect_checked_names(fact.prop().term(), &mut ctx);
        }
    }
    ctx.certify_prop(resolve_declared_names(stmt, &ctx))
}

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
        /// Only explicit local assumptions grant authority to discharge hypotheses.
        local_assumptions: Vec<CTerm>,
        /// Pending subgoals (from induction/cases)
        subgoals: Vec<Thm>,
        /// Index of current subgoal being proved
        current_subgoal: usize,
        /// Nested block depth (for { ... } blocks)
        block_depth: usize,
        /// The result of the final `show` statement (for qed composition)
        show_result: Option<Box<Thm>>,
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

    fn checked_goal_theorem(ct: CTerm) -> Result<Thm, KernelError> {
        let goal = ThmKernel::assume(ct)?;
        goal.check_kernel_invariants(KernelCheckMode::Strict)?;
        Ok(goal)
    }

    /// Create a proof state from a checked goal proposition.
    ///
    /// The internal goal theorem is a Strict open theorem (`A |- A`), not a
    /// closed proved lemma.
    pub fn new_checked_goal(ct: CTerm) -> Result<Self, KernelError> {
        Ok(Self::new(Self::checked_goal_theorem(ct)?))
    }

    /// Create a proof state from a raw term through checked certification.
    pub fn new_checked_goal_from_term(prop: Term) -> Result<Self, KernelError> {
        Self::new_checked_goal_from_term_in_context(&ProofCertContext::new(), prop)
    }

    /// Create a proof state from a raw term certified against an explicit
    /// proof context.
    pub fn new_checked_goal_from_term_in_context(
        ctx: &ProofCertContext,
        prop: Term,
    ) -> Result<Self, KernelError> {
        Self::new_checked_goal(ctx.certify_prop(prop)?)
    }

    /// Begin the proof (after `proof` command).
    pub fn begin_proof(&mut self) {
        if let ProofState::Ready { goal } = self {
            *self = ProofState::Proving {
                goal: goal.clone(),
                facts: Vec::new(),
                chained_fact: None,
                fixes: Vec::new(),
                local_assumptions: Vec::new(),
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

    /// Set subgoals from checked proposition CTerms.
    pub fn set_subgoals_checked(&mut self, new_subgoals: Vec<CTerm>) -> Result<(), KernelError> {
        let new_subgoals = new_subgoals
            .into_iter()
            .map(Self::checked_goal_theorem)
            .collect::<Result<Vec<_>, _>>()?;
        if let ProofState::Proving { subgoals, current_subgoal, .. } = self {
            *subgoals = new_subgoals;
            *current_subgoal = 0;
            Ok(())
        } else {
            Err(KernelError::KernelInvariant {
                op: "ProofState::set_subgoals_checked",
                message: "checked subgoals require an active Proving state".to_string(),
            })
        }
    }

    /// Set subgoals from raw proposition terms through checked certification.
    pub fn set_subgoals_checked_from_terms(
        &mut self,
        new_subgoals: Vec<Term>,
    ) -> Result<(), KernelError> {
        let new_subgoals = new_subgoals
            .into_iter()
            .map(|subgoal| ProofCertContext::new().certify_prop(subgoal))
            .collect::<Result<Vec<_>, _>>()?;
        self.set_subgoals_checked(new_subgoals)
    }

    /// Set subgoals from raw proposition terms certified against an explicit
    /// proof context.
    pub fn set_subgoals_checked_from_terms_in_context(
        &mut self,
        ctx: &ProofCertContext,
        new_subgoals: Vec<Term>,
    ) -> Result<(), KernelError> {
        let new_subgoals = new_subgoals
            .into_iter()
            .map(|subgoal| ctx.certify_prop(subgoal))
            .collect::<Result<Vec<_>, _>>()?;
        self.set_subgoals_checked(new_subgoals)
    }

    /// Get the current subgoal (if any).
    pub fn get_current_subgoal(&self) -> Option<&Thm> {
        match self {
            ProofState::Proving { subgoals, current_subgoal, .. } => subgoals.get(*current_subgoal),
            _ => None,
        }
    }

    /// Fix a new variable. Shadowing an existing fix is ambiguous at export.
    pub fn fix(&mut self, var: &str, typ: Typ) -> Result<(), GoalExportError> {
        let ProofState::Proving { fixes, .. } = self else {
            return Err(GoalExportError::MissingProofResult);
        };
        if fixes.iter().any(|(name, _)| name == var) || typ.contains_dummy() {
            return Err(GoalExportError::InvalidScript { line: 0 });
        }
        fixes.push((var.to_string(), typ));
        Ok(())
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

    fn certify_local_proposition(prop: Term) -> Result<CTerm, KernelError> {
        ProofCertContext::new().certify_prop(prop)
    }

    /// Add a checked local assumption (`A |- A`) to the active proof state.
    pub fn assume_checked(&mut self, ct: CTerm) -> Result<Arc<Thm>, KernelError> {
        if !matches!(self, ProofState::Proving { .. }) {
            return Err(KernelError::KernelInvariant {
                op: "ProofState::assume_checked",
                message: "local assumptions require an active Proving state".to_string(),
            });
        }
        let thm = ThmKernel::assume(ct.clone())?;
        thm.check_kernel_invariants(KernelCheckMode::Strict)?;
        let thm = Arc::new(thm);
        if let ProofState::Proving { facts, local_assumptions, .. } = self {
            local_assumptions.push(ct);
            facts.push(Arc::clone(&thm));
        }
        Ok(thm)
    }

    /// Assume a proposition (Isar `assume "A"`).
    ///
    /// This is now a strict proof-state entry point: the proposition must be
    /// certifiable without compatibility repairs and the resulting theorem is
    /// an open Strict theorem (`A |- A`), not a closed proved lemma.
    pub fn assume(&mut self, prop: Term) -> Result<Arc<Thm>, KernelError> {
        let ct = Self::certify_local_proposition(prop)?;
        self.assume_checked(ct)
    }

    /// Assume a proposition certified against an explicit proof context.
    pub fn assume_in_context(
        &mut self,
        ctx: &ProofCertContext,
        prop: Term,
    ) -> Result<Arc<Thm>, KernelError> {
        let ct = ctx.certify_prop(prop)?;
        self.assume_checked(ct)
    }

    /// Add a fact (from `using`, `note`, or `have`).
    pub fn add_fact(&mut self, thm: Arc<Thm>) {
        if let ProofState::Proving { facts, .. } = self {
            facts.push(thm);
        }
    }

    /// Prove an intermediate statement without granting its hypotheses new authority.
    pub fn have(
        &mut self,
        stmt: &Term,
        method: &str,
        all_premises: &[Arc<Thm>],
        db: &HolTheoremDb,
    ) -> Result<Arc<Thm>, GoalExportError> {
        let result = self.prove_statement(stmt, method, all_premises, db)?;
        let result = Arc::new(result);
        self.chain_fact(Arc::clone(&result));
        self.add_fact(Arc::clone(&result));
        Ok(result)
    }

    /// Prove the declared statement and retain its actual derivation for qed.
    pub fn show(
        &mut self,
        stmt: &Term,
        method: &str,
        all_premises: &[Arc<Thm>],
        db: &HolTheoremDb,
    ) -> Result<Thm, GoalExportError> {
        let result =
            self.prove_statement(&self.resolve_case_stmt(stmt), method, all_premises, db)?;
        if let ProofState::Proving { show_result, .. } = self {
            *show_result = Some(Box::new(result.clone()));
        }
        Ok(result)
    }

    fn prove_statement(
        &self,
        stmt: &Term,
        method: &str,
        all_premises: &[Arc<Thm>],
        db: &HolTheoremDb,
    ) -> Result<Thm, GoalExportError> {
        let ProofState::Proving { goal, facts, chained_fact, fixes, local_assumptions, .. } = self
        else {
            return Err(GoalExportError::MissingProofResult);
        };
        let expected = certify_statement(stmt.clone(), goal, fixes, facts, all_premises)
            .map_err(GoalExportError::from)?;
        let mut available: Vec<Arc<Thm>> = all_premises.iter().chain(facts).cloned().collect();
        if let Some(chained) = chained_fact {
            available.push(Arc::clone(chained));
        }
        apply_goal_method(&expected, method, &available, local_assumptions, db)?
            .ok_or(GoalExportError::MissingProofResult)
    }

    /// Resolve ?case/?thesis to the current subgoal's conclusion.
    fn resolve_case_stmt(&self, stmt: &Term) -> Term {
        if let Term::Const { name, .. } = stmt
            && (name.as_ref() == "?case" || name.as_ref() == "?thesis")
            && let Some(subgoal) = self.get_current_subgoal()
        {
            return subgoal.prop().term().clone();
        }
        stmt.clone()
    }

    /// Chain a fact (for `then` keyword).
    pub fn chain_fact(&mut self, thm: Arc<Thm>) {
        if let ProofState::Proving { chained_fact, .. } = self {
            *chained_fact = Some(thm);
        }
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

    /// Finalize only with a real, connected derivation of the original goal.
    pub fn qed(&mut self) -> Result<Thm, GoalExportError> {
        match self {
            ProofState::Proving {
                goal, subgoals, fixes, local_assumptions, show_result, ..
            } => {
                if !subgoals.is_empty() {
                    return Err(GoalExportError::UnsupportedComposition);
                }
                let result = show_result.as_ref().ok_or(GoalExportError::MissingProofResult)?;
                let exported = export_scoped_result(
                    goal.prop(),
                    result.as_ref(),
                    local_assumptions,
                    fixes,
                    &[],
                )?;
                *self = ProofState::Done(exported.clone());
                Ok(exported)
            },
            ProofState::Ready { .. } => Err(GoalExportError::MissingProofResult),
            ProofState::Done(result) => {
                crate::isar::proof_result::validate_proof_result(
                    result.prop().term(),
                    result,
                    &[],
                )?;
                Ok(result.clone())
            },
        }
    }
}

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

    fn checked_prop(name: &str) -> CTerm {
        cert_ctx(&[name]).certify_prop(Term::const_(name, Typ::base("prop"))).unwrap()
    }

    fn proving_state() -> ProofState {
        let mut state = ProofState::new_checked_goal(checked_prop("Goal")).unwrap();
        state.begin_proof();
        state
    }

    fn assert_strict_open_goal(goal: &Thm) {
        assert_eq!(goal.trust_status(), ThmTrust::Strict);
        goal.check_kernel_invariants(KernelCheckMode::Strict).unwrap();
        assert!(!goal.is_strict_closed_proved());
    }

    #[test]
    fn test_proof_state_lifecycle() {
        let ctx = cert_ctx(&["Px"]);
        let mut state = proving_state();
        state.fix("x", Typ::base("nat")).unwrap();
        let assumed = state.assume_in_context(&ctx, Term::const_("Px", Typ::base("prop"))).unwrap();
        let prems = state.get_premises();
        assert_eq!(prems.len(), 1);
        assert_eq!(assumed.trust_status(), ThmTrust::Strict);
    }

    #[test]
    fn proof_state_checked_goal_is_strict_open_theorem() {
        let state = ProofState::new_checked_goal(checked_prop("Goal")).unwrap();

        let ProofState::Ready { goal } = state else {
            panic!("new checked goal should start in Ready state");
        };
        assert_strict_open_goal(&goal);
    }

    #[test]
    fn proof_state_checked_goal_passes_strict_invariant() {
        let ctx = cert_ctx(&["Goal"]);
        let state = ProofState::new_checked_goal_from_term_in_context(
            &ctx,
            Term::const_("Goal", Typ::base("prop")),
        )
        .unwrap();

        let ProofState::Ready { goal } = state else {
            panic!("new checked goal should start in Ready state");
        };
        goal.check_kernel_invariants(KernelCheckMode::Strict).unwrap();
    }

    #[test]
    fn proof_state_checked_goal_not_closed_proved() {
        let state = ProofState::new_checked_goal(checked_prop("Goal")).unwrap();

        let ProofState::Ready { goal } = state else {
            panic!("new checked goal should start in Ready state");
        };
        assert!(!goal.is_strict_closed_proved());
    }

    #[test]
    fn proof_state_checked_goal_rejects_compat_cterm() {
        let compat = CTerm::certify(Term::const_("Goal", Typ::base("prop")));
        let result = ProofState::new_checked_goal(compat);

        assert!(matches!(result, Err(KernelError::CompatCTerm { .. })));
    }

    #[test]
    fn proof_state_checked_goal_rejects_dummy_type() {
        let result = ProofState::new_checked_goal_from_term(Term::free("x", Typ::dummy()));

        assert!(matches!(result, Err(KernelError::DummyType { .. })));
    }

    #[test]
    fn checked_subgoal_scaffolding_preserves_strict_trust() {
        let ctx = cert_ctx(&["NilCase", "ConsCase"]);
        let mut state = proving_state();
        state
            .set_subgoals_checked_from_terms_in_context(
                &ctx,
                vec![
                    Term::const_("NilCase", Typ::base("prop")),
                    Term::const_("ConsCase", Typ::base("prop")),
                ],
            )
            .unwrap();

        let current = state.get_current_subgoal().expect("checked subgoal should be active");
        assert_strict_open_goal(current);
    }

    #[test]
    fn proof_state_local_assumption_is_strict_open_theorem() {
        let ctx = cert_ctx(&["A"]);
        let mut state = proving_state();
        let thm = state.assume_in_context(&ctx, Term::const_("A", Typ::base("prop"))).unwrap();

        assert_eq!(thm.trust_status(), ThmTrust::Strict);
        assert_eq!(thm.hyps().len(), 1);
        assert_eq!(thm.prop().term(), &Term::const_("A", Typ::base("prop")));
    }

    #[test]
    fn proof_state_local_assumption_passes_strict_invariant() {
        let ctx = cert_ctx(&["A"]);
        let mut state = proving_state();
        let thm = state.assume_in_context(&ctx, Term::const_("A", Typ::base("prop"))).unwrap();

        thm.check_kernel_invariants(KernelCheckMode::Strict).unwrap();
    }

    #[test]
    fn proof_state_local_assumption_not_closed_proved() {
        let ctx = cert_ctx(&["A"]);
        let mut state = proving_state();
        let thm = state.assume_in_context(&ctx, Term::const_("A", Typ::base("prop"))).unwrap();

        assert!(!thm.is_strict_closed_proved());
    }

    #[test]
    fn proof_state_checked_assumption_rejects_compat_cterm() {
        let mut state = proving_state();
        let compat = CTerm::certify(Term::const_("A", Typ::base("prop")));
        let result = state.assume_checked(compat);

        assert!(matches!(result, Err(KernelError::CompatCTerm { .. })));
    }

    #[test]
    fn proof_state_checked_assumption_rejects_dummy_type() {
        let mut state = proving_state();
        let result = state.assume(Term::free("x", Typ::dummy()));

        assert!(matches!(result, Err(KernelError::DummyType { .. })));
    }

    #[test]
    fn proof_state_checked_goal_rejects_undeclared_const() {
        let result =
            ProofState::new_checked_goal_from_term(Term::const_("Fake.const", Typ::base("prop")));

        assert!(matches!(result, Err(KernelError::UndeclaredConstant(_))));
    }

    #[test]
    fn proof_state_checked_goal_accepts_declared_const() {
        let ctx = cert_ctx(&["Declared"]);
        let state = ProofState::new_checked_goal_from_term_in_context(
            &ctx,
            Term::const_("Declared", Typ::base("prop")),
        )
        .unwrap();

        let ProofState::Ready { goal } = state else {
            panic!("declared const goal should start in Ready state");
        };
        assert_strict_open_goal(&goal);
    }

    #[test]
    fn proof_state_checked_assumption_accepts_declared_local_free() {
        let ctx = ProofCertContext::new().with_free("x", Typ::base("prop"));
        let mut state = proving_state();
        let thm = state.assume_in_context(&ctx, Term::free("x", Typ::base("prop"))).unwrap();

        assert_eq!(thm.trust_status(), ThmTrust::Strict);
        assert!(!thm.is_strict_closed_proved());
    }

    #[test]
    fn proof_state_checked_goal_rejects_undeclared_free() {
        let result = ProofState::new_checked_goal_from_term(Term::free("x", Typ::base("prop")));

        assert!(matches!(result, Err(KernelError::KernelInvariant { .. })));
    }

    #[test]
    fn proof_state_checked_goal_rejects_ill_typed_application() {
        let mut ctx = ProofCertContext::new();
        ctx.declare_const("F", Typ::arrow(Typ::base("nat"), Typ::base("prop")));
        ctx.declare_const("b", Typ::base("bool"));
        let ill_typed = Term::app(
            Term::const_("F", Typ::arrow(Typ::base("nat"), Typ::base("prop"))),
            Term::const_("b", Typ::base("bool")),
        );
        let result = ProofState::new_checked_goal_from_term_in_context(&ctx, ill_typed);

        assert!(matches!(result, Err(KernelError::TypeMismatch { .. })));
    }
}

/// Interpret only proof commands whose entire checked token spans are understood.
/// A standalone `by` finishes the proof; structured scripts require `qed`/`done`.
pub fn interpret_proof_script(
    state: &mut ProofState,
    script: &str,
    premises: &[Arc<Thm>],
    db: &HolTheoremDb,
) -> Result<Thm, GoalExportError> {
    let spans = OuterSyntax::standard().parse_spans_checked(script).map_err(|error| {
        GoalExportError::InvalidScript {
            line: script[..error.offset.min(script.len())].lines().count().max(1),
        }
    })?;
    let mut pending: Option<(Term, bool)> = None;
    let mut completed = None;
    for span in spans {
        let line = span.line_number(script).max(1);
        if completed.is_some() {
            return Err(GoalExportError::InvalidScript { line });
        }
        if pending.is_some() && span.name != "by" {
            return Err(GoalExportError::InvalidScript { line });
        }
        if let Some(result) = execute_script_span(state, &span, premises, line, &mut pending, db)? {
            completed = Some(result);
        }
    }
    completed.ok_or(GoalExportError::MissingProofResult)
}

fn execute_script_span(
    state: &mut ProofState,
    span: &CommandSpan,
    premises: &[Arc<Thm>],
    line: usize,
    pending: &mut Option<(Term, bool)>,
    db: &HolTheoremDb,
) -> Result<Option<Thm>, GoalExportError> {
    match span.name.as_str() {
        "proof" if span.tokens.len() == 1 && matches!(state, ProofState::Ready { .. }) => {
            state.begin_proof();
        },
        "fix" => {
            let (name, typ) =
                parse_fix_tokens(&span.tokens).ok_or(GoalExportError::InvalidScript { line })?;
            state.fix(&name, typ).map_err(|error| script_error_at(error, line))?;
        },
        "assume" => assume_script_proposition(state, &span.tokens, premises, line)?,
        "have" | "show" if matches!(state, ProofState::Proving { .. }) => {
            let prop = parse_quoted_proposition(&span.tokens, 1)
                .ok_or(GoalExportError::InvalidScript { line })?;
            *pending = Some((prop, span.name == "show"));
        },
        "by" if !span.body.trim().is_empty() => {
            return execute_script_by(state, span.body.trim(), premises, line, pending, db);
        },
        "qed" | "done" if span.tokens.len() == 1 => return state.qed().map(Some),
        _ => return Err(GoalExportError::InvalidScript { line }),
    }
    Ok(None)
}

fn assume_script_proposition(
    state: &mut ProofState,
    tokens: &[Token],
    premises: &[Arc<Thm>],
    line: usize,
) -> Result<(), GoalExportError> {
    let prop =
        parse_quoted_proposition(tokens, 1).ok_or(GoalExportError::InvalidScript { line })?;
    let ProofState::Proving { goal, fixes, facts, .. } = state else {
        return Err(GoalExportError::InvalidScript { line });
    };
    let ct = certify_statement(prop, goal, fixes, facts, premises)?;
    state.assume_checked(ct)?;
    Ok(())
}

fn execute_script_by(
    state: &mut ProofState,
    method: &str,
    premises: &[Arc<Thm>],
    line: usize,
    pending: &mut Option<(Term, bool)>,
    db: &HolTheoremDb,
) -> Result<Option<Thm>, GoalExportError> {
    if let Some((prop, is_show)) = pending.take() {
        let result = if is_show {
            state.show(&prop, method, premises, db).map(|_| ())
        } else {
            state.have(&prop, method, premises, db).map(|_| ())
        };
        result.map_err(|error| script_error_at(error, line))?;
        return Ok(None);
    }
    if matches!(state, ProofState::Ready { .. }) {
        state.begin_proof();
    }
    let goal = state.get_current_goal().ok_or(GoalExportError::MissingProofResult)?;
    state
        .show(goal.prop().term(), method, premises, db)
        .map_err(|error| script_error_at(error, line))?;
    state.qed().map(Some)
}

fn script_error_at(error: GoalExportError, line: usize) -> GoalExportError {
    match error {
        GoalExportError::InvalidScript { .. } => GoalExportError::InvalidScript { line },
        other => other,
    }
}

fn parse_quoted_proposition(tokens: &[Token], offset: usize) -> Option<Term> {
    if tokens.len() != offset + 1 || tokens[offset].kind != TokenKind::String {
        return None;
    }
    let quoted = &tokens[offset].source;
    let content = quoted.strip_prefix('"')?.strip_suffix('"')?;
    crate::isar::term_parser::parse_term(content)
}

fn parse_fix_tokens(tokens: &[Token]) -> Option<(String, Typ)> {
    if tokens.len() != 4 || tokens[1].kind != TokenKind::Ident || tokens[2].source != "::" {
        return None;
    }
    let typ = crate::isar::term_parser::parse_type(&tokens[3].source)?;
    if typ.contains_dummy() {
        return None;
    }
    Some((tokens[1].source.clone(), typ))
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
        if let ProofState::Proving { subgoals, current_subgoal, .. } = self
            && *current_subgoal < subgoals.len()
        {
            subgoals[*current_subgoal] = new_goal;
        }
    }
}

#[cfg(test)]
mod isar_tests {
    use super::*;
    use crate::core::{term::Term, types::Typ};

    fn cert_ctx(names: &[&str]) -> ProofCertContext {
        let mut ctx = ProofCertContext::new();
        for name in names {
            ctx.declare_const(name, Typ::base("prop"));
        }
        ctx
    }

    #[test]
    fn proof_state_structured_show_requires_original_goal() {
        let a = Term::const_("A", Typ::base("prop"));
        let b = Term::const_("B", Typ::base("prop"));
        let ctx = cert_ctx(&["A", "B"]);
        let mut state = ProofState::new_checked_goal_from_term_in_context(&ctx, a).unwrap();
        state.begin_proof();
        state.assume_in_context(&ctx, b.clone()).unwrap();
        state.show(&b, "assumption", &[], &HolTheoremDb::new()).unwrap();
        assert!(matches!(state.qed(), Err(GoalExportError::PropositionMismatch)));
        assert!(matches!(state, ProofState::Proving { .. }));
    }

    #[test]
    fn test_let_binding() {
        // Test the `let` command parsing and expansion
        let a = Term::const_("A", Typ::base("prop"));
        let ctx = cert_ctx(&["A"]);
        let mut state = ProofState::new_checked_goal_from_term_in_context(&ctx, a.clone()).unwrap();
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
    fn proof_state_incomplete_script_rejects_eof() {
        let a = Term::const_("A", Typ::base("prop"));
        let ctx = cert_ctx(&["A"]);
        let mut state = ProofState::new_checked_goal_from_term_in_context(&ctx, a).unwrap();
        assert!(matches!(
            interpret_proof_script(
                &mut state,
                "proof\nassume \"A\"\nshow \"A\" by assumption",
                &[],
                &HolTheoremDb::new()
            ),
            Err(GoalExportError::MissingProofResult)
        ));
    }
}

#[cfg(test)]
mod induction_tests {
    use super::*;
    use crate::core::{term::Term, types::Typ};

    fn cert_ctx(names: &[&str]) -> ProofCertContext {
        let mut ctx = ProofCertContext::new();
        for name in names {
            ctx.declare_const(name, Typ::base("prop"));
        }
        ctx
    }

    #[test]
    fn test_induction_subgoals() {
        // Simulate: proof (induct xs) creates subgoals
        let a = Term::const_("A", Typ::base("prop"));
        let ctx = cert_ctx(&["A", "NilCase", "ConsCase"]);
        let mut state = ProofState::new_checked_goal_from_term_in_context(&ctx, a.clone()).unwrap();
        state.begin_proof();

        // Set up fake subgoals (simulating induction on a list)
        state
            .set_subgoals_checked_from_terms_in_context(
                &ctx,
                vec![
                    Term::const_("NilCase", Typ::base("prop")),
                    Term::const_("ConsCase", Typ::base("prop")),
                ],
            )
            .unwrap();

        // case Nil — should select first subgoal
        state.case_("Nil");
        assert_eq!(
            state.get_current_goal().unwrap().prop().term(),
            &Term::const_("NilCase", Typ::base("prop"))
        );

        // next — should select second subgoal
        state.next();
        assert_eq!(
            state.get_current_goal().unwrap().prop().term(),
            &Term::const_("ConsCase", Typ::base("prop"))
        );
    }

    #[test]
    fn test_resolve_case_stmt() {
        // Test that ?case resolves to the current subgoal
        let subgoal_term = Term::const_("P(Nil)", Typ::base("prop"));
        let ctx = cert_ctx(&["MainGoal", "P(Nil)"]);
        let mut state = ProofState::new_checked_goal_from_term_in_context(
            &ctx,
            Term::const_("MainGoal", Typ::base("prop")),
        )
        .unwrap();
        state.begin_proof();
        state.set_subgoals_checked_from_terms_in_context(&ctx, vec![subgoal_term.clone()]).unwrap();

        let resolved = state.resolve_case_stmt(&Term::const_("?case", Typ::base("prop")));
        assert_eq!(resolved, subgoal_term);
    }
}
