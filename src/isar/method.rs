//! Proof method system.
//!
//! Corresponds to `src/Pure/Isar/method.ML`.
//!
//! Methods are the "actions" of Isar proofs: `rule`, `simp`, `auto`,
//! `blast`, `induct`, `cases`, etc.

// used in tests
use std::{
    cell::{Cell, RefCell},
    collections::BTreeMap,
    sync::Arc,
};

use super::proof_result::{GoalExportError, export_proved_goal};
use crate::core::term::Term; // used in tests
use crate::core::types::Typ; // used in tests
use crate::{
    core::{
        error::KernelError,
        logic::Pure,
        simplifier::{RewriteRule, Simplifier},
        tactic,
        thm::{CTerm, Hyps, Thm, ThmKernel, ThmTrust},
    },
    hol::hol_loader::{
        HolTheoremDb, ParsedLemma, SourcePropositionShape, SourcePropositionStatus,
        normalize_checked_hol_true_prop,
    },
    isar::args::Args,
    kernel::{TrustedTheorem, TrustedTheory},
    tools::simp::HolSimplifier,
};

#[path = "method_diagnostics.rs"]
pub(crate) mod diagnostics;

thread_local! {
    pub(crate) static AUTO_DEPTH: Cell<usize> = const { Cell::new(0) };
    pub(crate) static AUTO_LIMIT: Cell<usize> = const { Cell::new(100) };
    /// Soft deadline for verify_file — when exceeded, verification returns partial results.
    pub(crate) static VERIFY_DEADLINE: Cell<Option<std::time::Instant>> = const { Cell::new(None) };
    /// Proof search budget — tracks remaining branch-expansion allowance.
    /// Starts at a high value; decremented on each auto_exec entry.
    /// When zero, auto_exec returns immediately without expanding branches.
    pub(crate) static PROOF_SEARCH_BUDGET: Cell<usize> = const { Cell::new(200) };
    /// Running tally of verify outcomes since the last `reset_verify_stats()`.
    /// `(proved, axiom_accepted)`. Accumulated across all files in a Tier2 run.
    static VERIFY_STATS: Cell<(usize, usize)> = const { Cell::new((0, 0)) };
    /// Structured outcome tally for verification diagnostics.
    static VERIFY_OUTCOME_STATS: RefCell<ProofOutcomeStats> = RefCell::new(ProofOutcomeStats::default());
}

/// How a `verify_lemma` call produced its legacy theorem evidence.
///
/// This distinguishes genuine proofs (the kernel closed every subgoal) from
/// lemmas that were *accepted as axioms* because the proof engine could not
/// replay their script. Both retain a legacy `Thm`, so this explicit tag keeps
/// the reporting buckets honest.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerifyOutcome {
    /// A real proof path closed the goal (safe rules, exec_proof, Isar replay,
    /// rule resolution, unfolding+method, etc.).
    Proved,
    /// No proof was run: the lemma's statement was accepted as an axiom via a
    /// trust-mode shortcut, an anonymous-datatype passthrough, or the final
    /// `generalize_thm` fallback.
    AxiomAccepted,
}

/// Value-driven result of one lemma verification attempt.
///
/// The accepted token and legacy evidence travel with the result; callers do
/// not consult ambient state to classify the theorem.
#[derive(Debug, Clone)]
pub struct LemmaVerification {
    accepted: Option<(TrustedTheory, TrustedTheorem)>,
    legacy: Option<(Thm, VerifyOutcome)>,
}

impl LemmaVerification {
    fn from_legacy(theorem: Option<Thm>, exit: VerifyOutcome) -> Self {
        Self { accepted: None, legacy: theorem.map(|theorem| (theorem, exit)) }
    }

    fn from_accepted(theory: TrustedTheory, theorem: TrustedTheorem) -> Self {
        Self { accepted: Some((theory, theorem)), legacy: None }
    }

    pub fn accepted(&self) -> Option<&TrustedTheorem> {
        self.accepted.as_ref().map(|(_, theorem)| theorem)
    }

    pub fn accepted_owner(&self) -> Option<&TrustedTheory> {
        self.accepted.as_ref().map(|(theory, _)| theory)
    }

    pub fn legacy(&self) -> Option<(&Thm, VerifyOutcome)> {
        self.legacy.as_ref().map(|(theorem, exit)| (theorem, *exit))
    }

    pub fn legacy_theorem(&self) -> Option<&Thm> {
        self.legacy.as_ref().map(|(theorem, _)| theorem)
    }

    pub fn into_legacy_theorem(self) -> Option<Thm> {
        self.legacy.map(|(theorem, _)| theorem)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TrustSummary {
    Strict,
    Compat,
    Admitted,
}

impl From<ThmTrust> for TrustSummary {
    fn from(value: ThmTrust) -> Self {
        match value {
            ThmTrust::Strict => TrustSummary::Strict,
            ThmTrust::Compat => TrustSummary::Compat,
            ThmTrust::Admitted => TrustSummary::Admitted,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TheoremSummary {
    pub name: String,
    pub prop: String,
    pub hyps_count: usize,
    pub nprems: usize,
    pub tpairs_count: usize,
    pub has_oracle: bool,
    pub has_admitted: bool,
    pub trust: TrustSummary,
}

impl TheoremSummary {
    fn from_thm(name: &str, thm: &Thm) -> Self {
        Self {
            name: name.to_string(),
            prop: format!("{:?}", thm.prop().term()),
            hyps_count: thm.hyps().len(),
            nprems: thm.nprems(),
            tpairs_count: thm.tpairs().len(),
            has_oracle: !thm.oracles().is_empty(),
            has_admitted: thm.trust_status() == ThmTrust::Admitted
                || thm.oracles().iter().any(|o| o.as_ref().starts_with("admitted:")),
            trust: thm.trust_status().into(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OpenReason {
    UnknownHyps,
    UnresolvedTpairs,
    Other,
}

impl OpenReason {
    fn label(self) -> &'static str {
        match self {
            OpenReason::UnknownHyps => "unknown_hyps",
            OpenReason::UnresolvedTpairs => "unresolved_tpairs",
            OpenReason::Other => "other",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AdmitReason {
    GoalExportUnknownHyps,
    GoalExportOpenSubgoals,
    GoalExportPropMismatch,
    GoalExportUnresolvedTpairs,
    GoalExportDischargeFailed,
    GoalInitializationFailed,
    ParserGap,
    DatatypeStub,
    AttributeTransformation,
    UnsupportedMethod,
    ProofEngineFailed,
    AxiomAcceptedWithoutOracle,
    OracleOrAdmittedResult,
    Other,
}

impl AdmitReason {
    fn from_oracle(reason: &str) -> Self {
        match reason {
            "admitted:goal_export_unknown_hyps" => AdmitReason::GoalExportUnknownHyps,
            "admitted:goal_export_open_subgoals" => AdmitReason::GoalExportOpenSubgoals,
            "admitted:goal_export_prop_mismatch" => AdmitReason::GoalExportPropMismatch,
            "admitted:goal_export_unresolved_tpairs" => AdmitReason::GoalExportUnresolvedTpairs,
            "admitted:goal_export_discharge_failed" => AdmitReason::GoalExportDischargeFailed,
            "admitted:goal_initialization_failed" => AdmitReason::GoalInitializationFailed,
            "admitted:parser_gap" => AdmitReason::ParserGap,
            "admitted:datatype_stub" => AdmitReason::DatatypeStub,
            "admitted:attribute_transformation" => AdmitReason::AttributeTransformation,
            "admitted:unsupported_method" => AdmitReason::UnsupportedMethod,
            "admitted:proof_engine_failed" => AdmitReason::ProofEngineFailed,
            _ => AdmitReason::Other,
        }
    }

    fn label(self) -> &'static str {
        match self {
            AdmitReason::GoalExportUnknownHyps => "goal_export_unknown_hyps",
            AdmitReason::GoalExportOpenSubgoals => "goal_export_open_subgoals",
            AdmitReason::GoalExportPropMismatch => "goal_export_prop_mismatch",
            AdmitReason::GoalExportUnresolvedTpairs => "goal_export_unresolved_tpairs",
            AdmitReason::GoalExportDischargeFailed => "goal_export_discharge_failed",
            AdmitReason::GoalInitializationFailed => "goal_initialization_failed",
            AdmitReason::ParserGap => "parser_gap",
            AdmitReason::DatatypeStub => "datatype_stub",
            AdmitReason::AttributeTransformation => "attribute_transformation",
            AdmitReason::UnsupportedMethod => "unsupported_method",
            AdmitReason::ProofEngineFailed => "proof_engine_failed",
            AdmitReason::AxiomAcceptedWithoutOracle => "axiom_accepted_without_oracle",
            AdmitReason::OracleOrAdmittedResult => "oracle_or_admitted_result",
            AdmitReason::Other => "other",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProofFailure {
    MethodNone,
}

impl ProofFailure {
    fn label(self) -> &'static str {
        match self {
            ProofFailure::MethodNone => "method_none",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofOutcome {
    KernelTrustedClosed { theorem: TrustedTheorem },
    TransitionalStrictClosed { summary: TheoremSummary },
    CompatClosedOracleFree { summary: TheoremSummary },
    OpenOracleFree { reason: OpenReason, summary: TheoremSummary },
    Admitted { reason: AdmitReason, summary: TheoremSummary },
    Failed { reason: ProofFailure, name: String },
}

impl ProofOutcome {
    pub fn is_transitional_strict_closed(&self) -> bool {
        matches!(self, ProofOutcome::TransitionalStrictClosed { .. })
    }

    pub fn is_kernel_trusted_closed(&self) -> bool {
        matches!(self, ProofOutcome::KernelTrustedClosed { .. })
    }

    pub fn label(&self) -> String {
        match self {
            ProofOutcome::KernelTrustedClosed { .. } => "KernelTrustedClosed".to_string(),
            ProofOutcome::TransitionalStrictClosed { .. } => "TransitionalStrictClosed".to_string(),
            ProofOutcome::CompatClosedOracleFree { .. } => "CompatClosedOracleFree".to_string(),
            ProofOutcome::OpenOracleFree { reason, .. } => {
                format!("OpenOracleFree({})", reason.label())
            },
            ProofOutcome::Admitted { reason, .. } => {
                format!("Admitted({})", reason.label())
            },
            ProofOutcome::Failed { reason, .. } => format!("Failed({})", reason.label()),
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ProofOutcomeStats {
    /// Count populated only by a mutually exclusive
    /// `ProofOutcome::KernelTrustedClosed` value.
    kernel_trusted_closed: usize,
    transitional_strict_closed: usize,
    compat_closed_oracle_free: usize,
    open_oracle_free: BTreeMap<OpenReason, usize>,
    admitted: BTreeMap<AdmitReason, usize>,
    failed: BTreeMap<ProofFailure, usize>,
}

impl ProofOutcomeStats {
    pub fn record(&mut self, outcome: &ProofOutcome) {
        match outcome {
            ProofOutcome::KernelTrustedClosed { .. } => {
                self.kernel_trusted_closed += 1;
            },
            ProofOutcome::TransitionalStrictClosed { .. } => {
                self.transitional_strict_closed += 1;
            },
            ProofOutcome::CompatClosedOracleFree { .. } => self.compat_closed_oracle_free += 1,
            ProofOutcome::OpenOracleFree { reason, .. } => {
                *self.open_oracle_free.entry(*reason).or_insert(0) += 1;
            },
            ProofOutcome::Admitted { reason, .. } => {
                *self.admitted.entry(*reason).or_insert(0) += 1;
            },
            ProofOutcome::Failed { reason, .. } => {
                *self.failed.entry(*reason).or_insert(0) += 1;
            },
        }
    }

    pub fn kernel_trusted_closed(&self) -> usize {
        self.kernel_trusted_closed
    }

    pub fn transitional_strict_closed(&self) -> usize {
        self.transitional_strict_closed
    }

    /// Number of mutually exclusive proof outcomes.
    pub fn total(&self) -> usize {
        self.kernel_trusted_closed
            + self.transitional_strict_closed
            + self.compat_closed_oracle_free
            + self.open_oracle_free.values().copied().sum::<usize>()
            + self.admitted.values().copied().sum::<usize>()
            + self.failed.values().copied().sum::<usize>()
    }

    pub fn report_lines(&self) -> Vec<String> {
        let mut lines = vec![
            format!("KernelTrustedClosed: {}", self.kernel_trusted_closed),
            format!("TransitionalStrictClosed: {}", self.transitional_strict_closed),
            format!("CompatClosedOracleFree: {}", self.compat_closed_oracle_free),
        ];
        for (reason, count) in &self.open_oracle_free {
            lines.push(format!("OpenOracleFree({}): {}", reason.label(), count));
        }
        for (reason, count) in &self.admitted {
            lines.push(format!("Admitted({}): {}", reason.label(), count));
        }
        for (reason, count) in &self.failed {
            lines.push(format!("Failed({}): {}", reason.label(), count));
        }
        lines
    }
}

/// Reset the global transitional-vs-accepted tally. Call before a verification run.
pub fn reset_verify_stats() {
    VERIFY_STATS.with(|c| c.set((0, 0)));
    VERIFY_OUTCOME_STATS.with(|c| *c.borrow_mut() = ProofOutcomeStats::default());
}

/// Read the legacy tally as `(transitional_strict_closed, other_accepted)`.
pub fn verify_stats() -> (usize, usize) {
    VERIFY_STATS.with(|c| c.get())
}

pub fn verify_outcome_stats() -> ProofOutcomeStats {
    VERIFY_OUTCOME_STATS.with(|c| c.borrow().clone())
}

fn record_verify_outcome(outcome: &ProofOutcome) {
    VERIFY_OUTCOME_STATS.with(|c| c.borrow_mut().record(outcome));
}

fn admitted_reason_from_thm(thm: &Thm) -> AdmitReason {
    thm.oracles()
        .iter()
        .find_map(|oracle| {
            let reason = oracle.as_ref();
            reason.starts_with("admitted:").then(|| AdmitReason::from_oracle(reason))
        })
        .unwrap_or(AdmitReason::OracleOrAdmittedResult)
}

fn open_reason_from_thm(thm: &Thm) -> OpenReason {
    if !thm.tpairs().is_empty() {
        OpenReason::UnresolvedTpairs
    } else if !thm.hyps().is_empty() {
        OpenReason::UnknownHyps
    } else {
        OpenReason::Other
    }
}

fn classify_thm_with_exit(name: &str, thm: &Thm, exit: VerifyOutcome) -> ProofOutcome {
    let summary = TheoremSummary::from_thm(name, thm);
    if thm.is_strict_closed_proved() && exit != VerifyOutcome::AxiomAccepted {
        return ProofOutcome::TransitionalStrictClosed { summary };
    }
    if thm.trust_status() == ThmTrust::Admitted || !thm.oracles().is_empty() {
        return ProofOutcome::Admitted { reason: admitted_reason_from_thm(thm), summary };
    }
    if exit == VerifyOutcome::AxiomAccepted {
        return ProofOutcome::Admitted { reason: AdmitReason::AxiomAcceptedWithoutOracle, summary };
    }
    if thm.is_closed_proved() {
        return ProofOutcome::CompatClosedOracleFree { summary };
    }
    ProofOutcome::OpenOracleFree { reason: open_reason_from_thm(thm), summary }
}

pub fn classify_proof_outcome(
    name: &str,
    accepted: Option<TrustedTheorem>,
    legacy: Option<(&Thm, VerifyOutcome)>,
) -> ProofOutcome {
    if let Some(theorem) = accepted {
        return ProofOutcome::KernelTrustedClosed { theorem };
    }
    match legacy {
        Some((theorem, exit)) => classify_thm_with_exit(name, theorem, exit),
        None => ProofOutcome::Failed { reason: ProofFailure::MethodNone, name: name.to_string() },
    }
}

pub fn classify_verify_result(name: &str, result: &LemmaVerification) -> ProofOutcome {
    classify_proof_outcome(name, result.accepted().cloned(), result.legacy())
}

#[cfg(test)]
fn is_transitional_strict_closed_outcome(thm: &Thm, exit: VerifyOutcome) -> bool {
    classify_proof_outcome("", None, Some((thm, exit))).is_transitional_strict_closed()
}

fn export_or_admit_goal(
    original_goal: &CTerm,
    result: Thm,
    context_assumptions: &[CTerm],
    exit: &mut VerifyOutcome,
) -> Thm {
    match export_proved_goal(original_goal, &result, context_assumptions) {
        Ok(exported) => exported,
        Err(GoalExportError::OracleOrAdmitted) => {
            *exit = VerifyOutcome::AxiomAccepted;
            result
        },
        Err(err) => {
            *exit = VerifyOutcome::AxiomAccepted;
            ThmKernel::admit(original_goal.clone(), err.admitted_reason())
        },
    }
}

fn init_verify_goal(goal_ct: &CTerm) -> Result<Thm, Box<Thm>> {
    ThmKernel::trivial(goal_ct.clone()).map_err(|_| {
        Box::new(ThmKernel::admit(goal_ct.clone(), "admitted:goal_initialization_failed"))
    })
}

fn proof_allows_strict_imp_identity(proof: &str) -> bool {
    matches!(proof.trim(), "by assumption" | "." | "by .")
}

fn try_strict_pure_imp_identity(
    goal: &Term,
    type_env: &crate::core::types::TypeEnv,
) -> Option<Thm> {
    let (premise, conclusion) = Pure::dest_implies(goal)?;
    if !Hyps::kernel_alpha_eq(premise, conclusion) {
        return None;
    }

    let cert_ctx = crate::isar::proof_context::ProofCertContext::from_type_env(type_env.clone());
    let premise_ct = cert_ctx.certify_prop(premise.clone()).ok()?;
    let original_ct = cert_ctx.certify_prop(goal.clone()).ok()?;
    let assumed = ThmKernel::assume(premise_ct.clone()).ok()?;
    let identity = ThmKernel::implies_intr(&premise_ct, &assumed).ok()?;

    if identity.is_strict_closed_proved()
        && Hyps::kernel_alpha_eq(identity.prop().term(), original_ct.term())
    {
        Some(identity)
    } else {
        None
    }
}

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
    /// `step` — safe rules exhaustively + one unsafe rule per subgoal.
    Step,
    /// `fast` — depth-first search with iterative deepening (bound 0..8).
    Fast,
    /// `best` — best-first search with heuristic ordering.
    Best,
    /// `depth` — bounded depth-first search with explicit bound.
    Depth(usize),
    /// `dup_step` — step_tac with duplication of unsafe rules (for complete search).
    DupStep,
    /// `coinduction` — coinduction principle for codatatypes.
    Coinduct,
    /// `try` / `try0` — try multiple proof methods and return first success.
    Try,
    /// `metis` — resolution-based first-order theorem prover.
    Metis,
    /// `meson` — model elimination prover for classical logic.
    Meson,
    /// `meth1 THEN meth2` — sequential composition (like Isabelle's Seq.EVERY).
    Then(Box<(Method, Method)>),
    /// `meth1 ORELSE meth2` — try first, fallback to second (like Isabelle's Seq.FIRST).
    Orelse(Box<(Method, Method)>),
    /// `REPEAT meth` — repeat method until no progress (like Isabelle's Seq.REPEAT1).
    Repeat(Box<Method>),
    /// This method never fails (skip).
    Skip,
    /// This method always fails.
    Fail,
}

impl Method {
    /// Create the `assumption` method.
    pub fn assumption() -> Self {
        Method::Assumption
    }

    /// Create the `rule` method.
    pub fn rule(thms: Vec<Arc<Thm>>) -> Self {
        Method::Rule(thms)
    }

    /// Execute the method with given premises (Isabelle-style).
    pub fn execute(&self, state: &Thm, premises: &[Arc<Thm>], db: &HolTheoremDb) -> Vec<Thm> {
        self.execute_depth(state, 0, premises, db)
    }

    fn execute_depth(
        &self,
        state: &Thm,
        depth: usize,
        premises: &[Arc<Thm>],
        db: &HolTheoremDb,
    ) -> Vec<Thm> {
        if depth > 20 {
            return vec![state.clone()];
        }
        match self {
            Method::Assumption => tactic::assume_tac(0)(state),
            Method::Rule(thms) => tactic::resolve_tac(
                &thms.iter().map(|t| (**t).clone()).collect::<Vec<_>>(),
                0,
            )(state),
            Method::Simp(simp) => {
                // Deep simplification: iterate rewrite_deep to fixed point
                let mut current = state.clone();
                for _ in 0..30 {
                    let mut changed = false;
                    for i in 0..current.nprems() {
                        if let Some(goal) = current.prem(i)
                            && let Some((simplified, eq_thm)) = simp.rewrite_deep(&goal)
                            && simplified != goal
                            && let Some(new_state) = ThmKernel::subst_premise(&eq_thm, &current, i)
                        {
                            current = new_state;
                            changed = true;
                            break; // restart after change
                        }
                    }
                    if !changed || current.nprems() == 0 {
                        break;
                    }
                }
                vec![current]
            },
            Method::Skip => vec![],
            Method::Fail => vec![],
            Method::Auto => Self::auto_exec(state, depth, premises, db),
            Method::Unfold(thms) => Self::apply_unfold(thms, state, false),
            Method::Fold(thms) => Self::apply_unfold(thms, state, true),
            Method::Erule(thms) => tactic::eresolve_tac(
                &thms.iter().map(|t| (**t).clone()).collect::<Vec<_>>(),
                0,
            )(state),
            Method::Drule(thms) => tactic::dresolve_tac(
                &thms.iter().map(|t| (**t).clone()).collect::<Vec<_>>(),
                0,
            )(state),
            Method::Frule(thms) => {
                // Forward rule: apply to all premises/hyps, not just the goal
                Self::apply_frule(thms, state)
            },
            Method::Insert(thms) => {
                // Insert facts: add them as extra hypotheses
                Self::apply_insert(thms, state)
            },
            Method::Blast => {
                // Tableau prover — uses auto with deeper search + symmetry
                Self::blast_exec(state, depth, db)
            },
            Method::Step => {
                // step_tac: safe rules exhaustively + one unsafe rule
                Self::step_exec(state, depth, premises, db)
            },
            Method::Fast => {
                // fast_tac: depth-first search with iterative deepening
                Self::fast_exec(state, premises, db)
            },
            Method::Best => {
                // best_tac: BEST_FIRST search with heuristic ordering
                Self::best_exec(state, premises, db)
            },
            Method::Depth(d) => {
                // depth_tac: bounded depth-first search
                Self::depth_exec(state, *d, premises, db)
            },
            Method::DupStep => {
                // dup_step_tac: step_tac with duplication of unsafe rules
                Self::dup_step_exec(state, depth, premises, db)
            },
            Method::Coinduct => {
                // coinduction: apply coinduction rules from DB
                Self::coinduct_exec(state, premises, db)
            },
            Method::Try => {
                // try/try0: try multiple methods sequentially
                Self::try_exec(state, depth, premises, db)
            },
            Method::Induct(var) => {
                // Induction: use exec_induct for proper handling
                let method_str = if var.is_empty() {
                    "induct".to_string()
                } else {
                    format!("induct {}", var.as_str())
                };
                exec_induct(&method_str, state, premises, db)
            },
            Method::Cases(var) => {
                // Cases: try auto + blast + induction-like rules
                let method_str = if var.is_empty() {
                    "cases".to_string()
                } else {
                    format!("cases {}", var.as_str())
                };
                exec_induct(&method_str, state, premises, db)
            },
            Method::Metis => Self::metis_exec(state, depth, premises),
            Method::Meson => crate::tools::meson::meson_tac(state, premises),
            Method::Then(box_pair) => {
                let (m1, m2) = (&box_pair.0, &box_pair.1);
                let results = m1.execute_depth(state, depth, premises, db);
                let mut all = Vec::new();
                for r in &results {
                    if r.nprems() == 0 {
                        all.push(r.clone());
                    } else {
                        all.extend(m2.execute_depth(r, depth + 1, premises, db));
                    }
                }
                if all.is_empty() { vec![state.clone()] } else { all }
            },
            Method::Orelse(box_pair) => {
                let (m1, m2) = (&box_pair.0, &box_pair.1);
                let results = m1.execute_depth(state, depth, premises, db);
                let solved: Vec<_> = results.iter().filter(|r| r.nprems() == 0).cloned().collect();
                if !solved.is_empty() {
                    solved
                } else {
                    m2.execute_depth(state, depth + 1, premises, db)
                }
            },
            Method::Repeat(method) => {
                let mut current = state.clone();
                for _ in 0..20 {
                    let results = method.execute_depth(&current, depth, premises, db);
                    if let Some(r) = results.iter().find(|r| r.nprems() < current.nprems()) {
                        if r.nprems() == 0 {
                            return vec![r.clone()];
                        }
                        current = r.clone();
                    } else {
                        break;
                    }
                }
                vec![current]
            },
            #[allow(unreachable_patterns)]
            _ => vec![state.clone()],
        }
    }

    /// Metis: resolution-based first-order theorem prover.
    /// Uses given-clause algorithm with binary resolution, factoring, and
    /// paramodulation.  All inferences are LCF-kernel checked.
    fn metis_exec(state: &Thm, _depth: usize, premises: &[Arc<Thm>]) -> Vec<Thm> {
        let Some(proposition) = state.prem(0) else {
            return Vec::new();
        };
        // This open theorem carries the request only; it is never proof evidence.
        let request = ThmKernel::assume_compat(CTerm::certify(proposition.clone()));
        let mut prover = crate::tools::metis::MetisProver::new();
        prover.add_premises(premises);
        let Some(result) = prover.prove(&request) else {
            return Vec::new();
        };
        if super::proof_result::validate_proof_result(&proposition, &result, &[]).is_err() {
            return Vec::new();
        }
        ThmKernel::bicompose(false, &result, state, 0)
            .filter(|next| next.nprems() < state.nprems())
            .into_iter()
            .collect()
    }

    /// Blast: aggressive proof search with auto, simp, resolve, eresolve, dresolve.
    /// Enhanced with forward chaining and better symmetry handling.
    fn blast_exec(state: &Thm, depth: usize, db: &HolTheoremDb) -> Vec<Thm> {
        let count = AUTO_DEPTH.with(|c| {
            let v = c.get() + 1;
            c.set(v);
            v
        });
        if count > AUTO_LIMIT.with(|c| c.get()) {
            return vec![state.clone()];
        }
        if depth > 15 {
            return vec![state.clone()];
        }
        if state.nprems() == 0 {
            return vec![state.clone()];
        }

        let mut all_solved = Vec::new();
        let orig_size =
            Self::term_size(&state.prem(0).unwrap_or(Term::const_("dummy", Typ::dummy())));

        // 1. Try assumption
        let assume_results = tactic::assume_tac(0)(state);
        for r in &assume_results {
            if r.nprems() == 0 {
                all_solved.push(r.clone());
            }
        }

        // 2. Try simp — use cached simplifier
        let simp_results = tactic::simp_tac(db.base_simplifier().clone(), 0)(state);
        for r in &simp_results {
            if r.nprems() == 0 {
                all_solved.push(r.clone());
            } else if r.nprems() < state.nprems() && depth < 22 {
                let sub = Self::blast_exec(r, depth + 1, db);
                for s in &sub {
                    if s.nprems() == 0 {
                        all_solved.push(s.clone());
                    }
                }
            }
        }

        // 3. Try resolve with intros (limited branching)
        let resolve_results = tactic::resolve_tac(
            &db.intros.iter().map(|t| (**t).clone()).collect::<Vec<_>>(),
            0,
        )(state);
        for r in &resolve_results {
            if r.nprems() == 0 {
                all_solved.push(r.clone());
            } else if r.nprems() <= state.nprems() + 3 && depth < 18 {
                // Term size pruning: don't expand if term grows too much
                let new_size =
                    Self::term_size(&r.prem(0).unwrap_or(Term::const_("dummy", Typ::dummy())));
                if new_size > orig_size * 3 {
                    continue;
                }
                let sub = Self::blast_exec(r, depth + 1, db);
                for s in &sub {
                    if s.nprems() == 0 {
                        all_solved.push(s.clone());
                    }
                }
            }
        }

        // 4. Try eresolve with elims
        let eresolve_results = tactic::eresolve_tac(
            &db.elims.iter().map(|t| (**t).clone()).collect::<Vec<_>>(),
            0,
        )(state);
        for r in &eresolve_results {
            if r.nprems() == 0 {
                all_solved.push(r.clone());
            } else if r.nprems() <= state.nprems() + 3 && depth < 15 {
                let sub = Self::blast_exec(r, depth + 1, db);
                for s in &sub {
                    if s.nprems() == 0 {
                        all_solved.push(s.clone());
                    }
                }
            }
        }

        // 5. Try dresolve with elims (forward chaining)
        let dresolve_results = tactic::dresolve_tac(
            &db.elims.iter().map(|t| (**t).clone()).collect::<Vec<_>>(),
            0,
        )(state);
        for r in &dresolve_results {
            if r.nprems() == 0 {
                all_solved.push(r.clone());
            } else if r.nprems() < state.nprems() && depth < 12 {
                let sub = Self::blast_exec(r, depth + 1, db);
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

        // 6. Symmetry for equality and ordering goals
        if let Some(goal) = state.prem(0) {
            // Equality symmetry
            if Pure::dest_equals(&goal).is_some()
                && let Some(sym_thm) = db.by_name.get("sym")
            {
                let sym_results = tactic::resolve_tac(&[(**sym_thm).clone()], 0)(state);
                for r in &sym_results {
                    if r.nprems() == 0 {
                        all_solved.push(r.clone());
                    } else if r.nprems() < state.nprems() && depth < 22 {
                        let sub = Self::blast_exec(r, depth + 1, db);
                        for s in &sub {
                            if s.nprems() == 0 {
                                all_solved.push(s.clone());
                            }
                        }
                    }
                }
            }
            // Ordering symmetry: x <= y goal, try y >= x via order_antisym
            if let Some((_, _)) = Self::dest_binary("HOL.ordLessEq", &goal)
                && let Some(antisym) = db.by_name.get("order_antisym")
            {
                let anti_results = tactic::resolve_tac(&[(**antisym).clone()], 0)(state);
                for r in &anti_results {
                    if r.nprems() == 0 {
                        all_solved.push(r.clone());
                    } else if r.nprems() < state.nprems() + 2 && depth < 18 {
                        let sub = Self::blast_exec(r, depth + 1, db);
                        for s in &sub {
                            if s.nprems() == 0 {
                                all_solved.push(s.clone());
                            }
                        }
                    }
                }
            }
        }

        if !all_solved.is_empty() {
            return all_solved;
        }
        vec![state.clone()]
    }

    /// Helper: compute approximate term size for pruning.
    fn term_size(term: &Term) -> usize {
        match term {
            Term::App { func, arg } => 1 + Self::term_size(func) + Self::term_size(arg),
            Term::Abs { body, .. } => 1 + Self::term_size(body),
            _ => 1,
        }
    }

    /// Helper: dest a binary predicate application.
    fn dest_binary<'a>(pred: &str, term: &'a Term) -> Option<(&'a Term, &'a Term)> {
        match term {
            Term::App { func, arg } => match func.as_ref() {
                Term::App { func: inner, arg: left } => match inner.as_ref() {
                    Term::Const { name, .. } if name.as_ref() == pred => Some((left, arg)),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    /// Apply unfold/fold: rewrite the goal using definition equations.
    /// If `fold` is true, swap LHS/RHS (fold instead of unfold).
    fn apply_unfold(thms: &[Arc<Thm>], state: &Thm, fold: bool) -> Vec<Thm> {
        let rules: Vec<RewriteRule> = thms
            .iter()
            .filter_map(|thm| {
                let mut rule = RewriteRule::from_thm(Arc::clone(thm))?;
                if fold {
                    // Swap LHS and RHS for folding
                    std::mem::swap(&mut rule.lhs, &mut rule.rhs);
                }
                Some(rule)
            })
            .collect();
        if rules.is_empty() {
            return vec![state.clone()];
        }
        let simp = Simplifier::new(rules);
        let mut current = state.clone();
        // Apply deep rewriting to each subgoal
        for i in 0..state.nprems() {
            if let Some(prem) = current.prem(i)
                && let Some((rewritten, eq_thm)) = simp.rewrite_deep(&prem)
                && rewritten != prem
                && let Some(new_state) = ThmKernel::subst_premise(&eq_thm, &current, i)
            {
                current = new_state;
            }
        }
        vec![current]
    }

    /// Apply forward rule: resolve the rule against all hypotheses.
    fn apply_frule(thms: &[Arc<Thm>], state: &Thm) -> Vec<Thm> {
        // frule applies the destruct rule to all matching hypotheses,
        // adding new facts without removing old ones.
        // For now: use drule (which converts to elim and eresolves)
        tactic::dresolve_tac(&thms.iter().map(|t| (**t).clone()).collect::<Vec<_>>(), 0)(state)
    }

    /// Apply insert: add theorems as extra hypotheses to the goal.
    fn apply_insert(thms: &[Arc<Thm>], state: &Thm) -> Vec<Thm> {
        // insert: Γ ⊢ A  →  Γ, thms ⊢ A
        // This strengthens the hypotheses with the inserted facts
        let mut current = state.clone();
        for thm in thms {
            // Use bicompose to add thm as an additional hypothesis to the goal
            // This is a simplification: resolve first subgoal with the thm
            if let Some(new_state) = ThmKernel::bicompose(true, thm, &current, 0) {
                current = new_state;
            }
        }
        vec![current]
    }

    /// Apply safe intro/elim rules exhaustively using safe discrimination nets.
    /// Only uses rules classified as "safe" — these can be applied blindly
    /// without risk of infinite loops or combinatoric explosion.
    ///
    /// Like Isabelle's `safe_step_tac`, tries matching first (no variable
    /// instantiation), then falls back to resolution for safe rules.
    pub fn apply_safe_rules(state: &Thm, premises: &[Arc<Thm>], db: &HolTheoremDb) -> Thm {
        let mut current = state.clone();
        for _ in 0..8 {
            if current.nprems() == 0 {
                break;
            }
            let subgoal = match current.prem(0) {
                Some(p) => p,
                None => break,
            };
            let mut progress = false;

            // Phase 1: Try safe intro rules — matching first (like Isabelle's
            // bimatch_from_nets_tac)
            let intro_cands = db.safe_intro_net().lookup(&subgoal);
            for rule in &intro_cands {
                if let Some(result) = ThmKernel::bicompose(true, rule, &current, 0) {
                    if result.nprems() == 0 {
                        return result;
                    }
                    if result.nprems() < current.nprems() {
                        current = result;
                        progress = true;
                        break;
                    }
                }
            }
            if progress {
                continue;
            }

            // Phase 2: Try safe elim rules — matching first
            let elim_cands = db.safe_elim_net().lookup(&subgoal);
            for rule in &elim_cands {
                if let Some(result) =
                    ThmKernel::bicompose_eresolve(true, rule, &current, 0, premises)
                {
                    if result.nprems() == 0 {
                        return result;
                    }
                    if result.nprems() <= current.nprems() + 2 {
                        current = result;
                        progress = true;
                        break;
                    }
                }
            }
            if progress {
                continue;
            }

            // Phase 3: Fall back to resolution (allows variable instantiation)
            // for safe rules that need it (like Isabelle's inst_step_tac)
            if !intro_cands.is_empty() {
                let rules: Vec<Thm> = intro_cands.iter().map(|t| (**t).clone()).collect();
                let results = tactic::resolve_tac(&rules, 0)(&current);
                for r in &results {
                    if r.nprems() == 0 {
                        return r.clone();
                    }
                    if r.nprems() < current.nprems() {
                        current = r.clone();
                        progress = true;
                        break;
                    }
                }
                if progress {
                    continue;
                }
            }
            if !elim_cands.is_empty() {
                let rules: Vec<Thm> = elim_cands.iter().map(|t| (**t).clone()).collect();
                let results = tactic::eresolve_tac(&rules, 0)(&current);
                for r in &results {
                    if r.nprems() == 0 {
                        return r.clone();
                    }
                    if r.nprems() <= current.nprems() + 2 {
                        current = r.clone();
                        progress = true;
                        break;
                    }
                }
                if progress {
                    continue;
                }
            }
            break; // No progress
        }
        current
    }

    /// step_tac: apply safe rules exhaustively, then try ONE unsafe rule.
    /// This matches Isabelle's `step_tac` from classical.ML.
    fn step_exec(state: &Thm, depth: usize, premises: &[Arc<Thm>], db: &HolTheoremDb) -> Vec<Thm> {
        // 1. Apply safe rules exhaustively
        let safe_state = Self::apply_safe_rules(state, premises, db);
        if safe_state.nprems() == 0 {
            return vec![safe_state];
        }

        if depth > 10 {
            return vec![safe_state];
        }

        let subgoal = match safe_state.prem(0) {
            Some(p) => p,
            None => return vec![safe_state],
        };

        // 2. Try ONE unsafe intro rule
        let intro_cands = db.intro_net().lookup(&subgoal);
        for rule in &intro_cands {
            // Skip rules already in safe set
            if db.safe_intros.iter().any(|s| Arc::ptr_eq(s, rule)) {
                continue;
            }
            if let Some(result) = ThmKernel::bicompose(true, rule, &safe_state, 0) {
                let sub_results = Self::step_exec(&result, depth + 1, premises, db);
                for r in &sub_results {
                    if r.nprems() == 0 {
                        return sub_results;
                    }
                }
            }
        }

        // 3. Try ONE unsafe elim rule
        let elim_cands = db.elim_net().lookup(&subgoal);
        for rule in &elim_cands {
            if db.safe_elims.iter().any(|s| Arc::ptr_eq(s, rule)) {
                continue;
            }
            if let Some(result) =
                ThmKernel::bicompose_eresolve(true, rule, &safe_state, 0, premises)
            {
                let sub_results = Self::step_exec(&result, depth + 1, premises, db);
                for r in &sub_results {
                    if r.nprems() == 0 {
                        return sub_results;
                    }
                }
            }
        }

        vec![safe_state]
    }

    /// fast_tac: depth-first search with iterative deepening.
    /// This matches Isabelle's `fast_tac` from classical.ML.
    fn fast_exec(state: &Thm, premises: &[Arc<Thm>], db: &HolTheoremDb) -> Vec<Thm> {
        for bound in 0..8 {
            if let Some(result) = Self::dfs_search(state, bound, premises, db) {
                return vec![result];
            }
        }
        Self::auto_exec(state, 0, premises, db)
    }

    /// Depth-first search with a given bound on unsafe rule applications.
    fn dfs_search(
        state: &Thm,
        bound: usize,
        premises: &[Arc<Thm>],
        db: &HolTheoremDb,
    ) -> Option<Thm> {
        let safe_state = Self::apply_safe_rules(state, premises, db);
        if safe_state.nprems() == 0 {
            return Some(safe_state);
        }
        if bound == 0 {
            return None;
        }

        let subgoal = safe_state.prem(0)?;

        // Try unsafe intro rules
        for rule in &db.intro_net().lookup(&subgoal) {
            if db.safe_intros.iter().any(|s| Arc::ptr_eq(s, rule)) {
                continue;
            }
            if let Some(result) = ThmKernel::bicompose(true, rule, &safe_state, 0)
                && let Some(solved) = Self::dfs_subgoals(&result, bound - 1, premises, db)
            {
                return Some(solved);
            }
        }

        // Try unsafe elim rules
        for rule in &db.elim_net().lookup(&subgoal) {
            if db.safe_elims.iter().any(|s| Arc::ptr_eq(s, rule)) {
                continue;
            }
            if let Some(result) =
                ThmKernel::bicompose_eresolve(true, rule, &safe_state, 0, premises)
                && let Some(solved) = Self::dfs_subgoals(&result, bound - 1, premises, db)
            {
                return Some(solved);
            }
        }
        None
    }

    /// Solve all subgoals using bounded DFS.
    fn dfs_subgoals(
        state: &Thm,
        bound: usize,
        premises: &[Arc<Thm>],
        db: &HolTheoremDb,
    ) -> Option<Thm> {
        let mut current = state.clone();
        let mut acc: Vec<Arc<Thm>> = premises.to_vec();
        for _ in 0..current.nprems().min(20) {
            if current.nprems() == 0 {
                return Some(current);
            }
            let prem = current.prem(0)?;
            let goal = ThmKernel::assume_compat(CTerm::certify(prem));
            let solved = Self::dfs_search(&goal, bound, &acc, db).or_else(|| {
                Self::auto_exec(&goal, 0, &acc, db).into_iter().find(|r| r.nprems() == 0)
            });
            let sg = solved?;
            acc.push(Arc::new(sg.clone()));
            current = ThmKernel::bicompose(false, &sg, &current, 0)?;
        }
        if current.nprems() == 0 { Some(current) } else { None }
    }

    /// best_tac: BEST_FIRST search with heuristic ordering.
    /// Matches Isabelle's `best_tac` from classical.ML.
    /// Uses a simple bounded worklist ordered by subgoal count.
    fn best_exec(state: &Thm, premises: &[Arc<Thm>], db: &HolTheoremDb) -> Vec<Thm> {
        let safe = Self::apply_safe_rules(state, premises, db);
        if safe.nprems() == 0 {
            return vec![safe];
        }

        // Use a Vec-based priority: sort by nprems, explore fewer-subgoals first
        let mut worklist: Vec<(usize, usize, Thm)> = Vec::new(); // (nprems, depth, thm)
        worklist.push((safe.nprems(), 0, safe));

        let mut best = state.clone();
        let mut best_nprems = state.nprems();

        let mut iterations = 0;
        while !worklist.is_empty() && iterations < 500 {
            iterations += 1;
            // Sort by nprems ascending (fewer subgoals first)
            worklist.sort_by_key(|(n, _, _)| *n);
            // Take the most promising state (fewest subgoals, shallowest depth)
            let idx = worklist
                .iter()
                .enumerate()
                .min_by_key(|(_, (n, d, _))| (*n, *d))
                .map(|(i, _)| i)
                .unwrap_or(0);
            let (_, depth, current) = worklist.remove(idx);

            if current.nprems() == 0 {
                return vec![current];
            }
            if current.nprems() < best_nprems {
                best = current.clone();
                best_nprems = current.nprems();
            }
            if depth > 10 {
                continue;
            }
            let subgoal = match current.prem(0) {
                Some(p) => p,
                None => continue,
            };

            let mut next_states = Vec::new();
            for rule in &db.intro_net().lookup(&subgoal) {
                if db.safe_intros.iter().any(|s| Arc::ptr_eq(s, rule)) {
                    continue;
                }
                if let Some(result) = ThmKernel::bicompose(true, rule, &current, 0) {
                    next_states.push(result);
                }
            }
            for rule in &db.elim_net().lookup(&subgoal) {
                if db.safe_elims.iter().any(|s| Arc::ptr_eq(s, rule)) {
                    continue;
                }
                if let Some(result) =
                    ThmKernel::bicompose_eresolve(true, rule, &current, 0, premises)
                {
                    next_states.push(result);
                }
            }
            for ns in next_states {
                worklist.push((ns.nprems(), depth + 1, ns));
            }
        }
        if best_nprems == 0 { vec![best] } else { Self::step_exec(&best, 0, premises, db) }
    }

    /// depth_tac: bounded depth-first search with explicit bound.
    fn depth_exec(state: &Thm, bound: usize, premises: &[Arc<Thm>], db: &HolTheoremDb) -> Vec<Thm> {
        let safe = Self::apply_safe_rules(state, premises, db);
        if safe.nprems() == 0 {
            return vec![safe];
        }
        Self::depth_search(&safe, bound, premises, db)
            .map(|r| vec![r])
            .unwrap_or_else(|| Self::step_exec(&safe, 0, premises, db))
    }

    fn depth_search(
        state: &Thm,
        bound: usize,
        premises: &[Arc<Thm>],
        db: &HolTheoremDb,
    ) -> Option<Thm> {
        let safe = Self::apply_safe_rules(state, premises, db);
        if safe.nprems() == 0 {
            return Some(safe);
        }
        if bound == 0 || bound > 20 {
            return None;
        }
        let subgoal = safe.prem(0)?;
        let mut results: Vec<Thm> = Vec::new();
        for rule in &db.intro_net().lookup(&subgoal) {
            if db.safe_intros.iter().any(|s| Arc::ptr_eq(s, rule)) {
                continue;
            }
            if let Some(r) = ThmKernel::bicompose(true, rule, &safe, 0) {
                results.push(r);
            }
        }
        for rule in &db.elim_net().lookup(&subgoal) {
            if db.safe_elims.iter().any(|s| Arc::ptr_eq(s, rule)) {
                continue;
            }
            if let Some(r) = ThmKernel::bicompose_eresolve(true, rule, &safe, 0, premises) {
                results.push(r);
            }
        }
        for result in &results {
            if let Some(solved) = Self::depth_search(result, bound - 1, premises, db) {
                return Some(solved);
            }
        }
        None
    }

    /// dup_step_tac: step_tac with duplication of unsafe rules.
    /// Duplicates unsafe rules to allow backtracking for complete search.
    fn dup_step_exec(
        state: &Thm,
        depth: usize,
        premises: &[Arc<Thm>],
        db: &HolTheoremDb,
    ) -> Vec<Thm> {
        let safe_state = Self::apply_safe_rules(state, premises, db);
        if safe_state.nprems() == 0 {
            return vec![safe_state];
        }
        if depth > 12 {
            return vec![safe_state];
        }
        let subgoal = match safe_state.prem(0) {
            Some(p) => p,
            None => return vec![safe_state],
        };
        // Try all unsafe rules (allowing backtracking via recursion)
        for rule in &db.intro_net().lookup(&subgoal) {
            if db.safe_intros.iter().any(|s| Arc::ptr_eq(s, rule)) {
                continue;
            }
            if let Some(result) = ThmKernel::bicompose(true, rule, &safe_state, 0) {
                let sub = Self::dup_step_exec(&result, depth + 1, premises, db);
                if sub.iter().any(|r| r.nprems() == 0) {
                    return sub;
                }
            }
        }
        for rule in &db.elim_net().lookup(&subgoal) {
            if db.safe_elims.iter().any(|s| Arc::ptr_eq(s, rule)) {
                continue;
            }
            if let Some(result) =
                ThmKernel::bicompose_eresolve(true, rule, &safe_state, 0, premises)
            {
                let sub = Self::dup_step_exec(&result, depth + 1, premises, db);
                if sub.iter().any(|r| r.nprems() == 0) {
                    return sub;
                }
            }
        }
        vec![safe_state]
    }

    /// coinduction: apply coinduction rules from the theorem database.
    /// Looks up `.coinduct` rules and resolves against the goal.
    fn coinduct_exec(state: &Thm, premises: &[Arc<Thm>], db: &HolTheoremDb) -> Vec<Thm> {
        // Try safe rules first
        let current = Self::apply_safe_rules(state, premises, db);
        if current.nprems() == 0 {
            return vec![current];
        }

        // Look for coinduction rules
        let mut candidates: Vec<Arc<Thm>> = Vec::new();
        for (name, thm) in db.by_name.iter() {
            if name.contains("coinduct") && !candidates.iter().any(|c| Arc::ptr_eq(c, thm)) {
                candidates.push(Arc::clone(thm));
            }
            if candidates.len() >= 10 {
                break;
            }
        }

        // Try each coinduction rule
        for rule in &candidates {
            let results = crate::core::tactic::resolve_tac(&[(**rule).clone()], 0)(&current);
            for r in &results {
                if r.nprems() == 0 {
                    return vec![r.clone()];
                }
            }
        }

        // Fall back to auto
        Self::auto_exec(&current, 0, premises, db)
    }

    /// try/try0: try multiple proof methods in sequence, return first success.
    /// Method sequence: safe → simp → auto → blast → fast → best
    fn try_exec(state: &Thm, depth: usize, premises: &[Arc<Thm>], db: &HolTheoremDb) -> Vec<Thm> {
        // 1. Safe rules (cheapest)
        let current = Self::apply_safe_rules(state, premises, db);
        if current.nprems() == 0 {
            return vec![current];
        }

        // 2. Simplification
        let rules: Vec<RewriteRule> =
            db.simps.iter().filter_map(|t| RewriteRule::from_thm(Arc::clone(t))).collect();
        let simp = Simplifier::new(rules);
        let results = Method::Simp(simp).execute(state, premises, db);
        if results.iter().any(|r| r.nprems() == 0) {
            return results;
        }

        // 3. Auto
        let auto_results = Method::Auto.execute(state, premises, db);
        if auto_results.iter().any(|r| r.nprems() == 0) {
            return auto_results;
        }

        // 4. Blast
        let blast_results = Method::Blast.execute(state, premises, db);
        if blast_results.iter().any(|r| r.nprems() == 0) {
            return blast_results;
        }

        // 5. Fast
        let fast_results = Method::Fast.execute(state, premises, db);
        if fast_results.iter().any(|r| r.nprems() == 0) {
            return fast_results;
        }

        // 6. Best (more thorough)
        let best_results = Method::Best.execute(state, premises, db);
        if best_results.iter().any(|r| r.nprems() == 0) {
            return best_results;
        }

        // Fall back to auto with extended premises
        Self::auto_exec(state, depth, premises, db)
    }

    /// Iterative auto proof search — DFS with explicit stack.
    /// Replaces recursive auto_exec to avoid deep call stacks and Arc<Thm> accumulation.
    /// Search strategy is preserved: DFS with early exit on first solution.
    fn auto_exec(state: &Thm, depth: usize, premises: &[Arc<Thm>], db: &HolTheoremDb) -> Vec<Thm> {
        // ── Guard checks on initial entry ──
        let count = AUTO_DEPTH.with(|c| {
            let v = c.get() + 1;
            c.set(v);
            v
        });
        if count > AUTO_LIMIT.with(|c| c.get()) {
            return vec![state.clone()];
        }
        let expired =
            VERIFY_DEADLINE.with(|c| c.get().is_some_and(|d| std::time::Instant::now() >= d));
        if expired {
            return vec![state.clone()];
        }
        // Each DFS node costs 1 budget unit
        PROOF_SEARCH_BUDGET.with(|c| {
            let b = c.get();
            if b > 0 {
                c.set(b - 1);
            }
        });
        if PROOF_SEARCH_BUDGET.with(|c| c.get()) == 0 && depth > 0 {
            return vec![state.clone()];
        }
        if depth > 8 || state.nprems() == 0 {
            // Isabelle: auto uses blast(4)+classical(2), effective depth ~4-6
            return vec![state.clone()];
        }

        let branch_limit = if depth > 6 {
            3
        } else if depth > 3 {
            8
        } else {
            25
        };

        // ── Phase 0: Safe rules ──
        let current = Self::apply_safe_rules(state, premises, db);
        if current.nprems() == 0 {
            return vec![current];
        }

        // ── Phase 1: Assumption ──
        let assume_results = tactic::assume_tac(0)(&current);
        for r in &assume_results {
            if r.nprems() == 0 {
                return vec![r.clone()];
            }
        }

        // ── Phase 2: Simp — use cached simplifier ──
        let simp = db.base_simplifier().clone();
        let simp_results = tactic::simp_tac(simp, 0)(&current);
        let mut simp_branches = 0usize;
        for r in &simp_results {
            if r.nprems() != current.nprems() {
                if simp_branches >= branch_limit / 2 {
                    break;
                }
                simp_branches += 1;
                let sub = Self::auto_exec(r, depth + 1, premises, db);
                for s in &sub {
                    if s.nprems() == 0 {
                        return sub;
                    }
                }
            }
        }

        // ── Phases 3-6: Iterative DFS via explicit work stack ──
        // Each entry: (state, depth). Processed LIFO for DFS order.
        let subgoal = match current.prem(0) {
            Some(p) => p,
            None => return vec![current.clone()],
        };
        let intro_cands = db.intro_net().lookup(&subgoal);
        let elim_cands = db.elim_net().lookup(&subgoal);

        // Collect all candidate child states from phases 3-6
        let mut children: Vec<(Thm, usize)> = Vec::new();

        // Phase 3: resolve/eresolve via nets
        let resolve_results = if intro_cands.is_empty() {
            tactic::resolve_tac(&db.intros.iter().map(|t| (**t).clone()).collect::<Vec<_>>(), 0)(
                &current,
            )
        } else {
            tactic::resolve_tac(&intro_cands.iter().map(|t| (**t).clone()).collect::<Vec<_>>(), 0)(
                &current,
            )
        };
        let eresolve_results = if elim_cands.is_empty() {
            tactic::eresolve_tac(&db.elims.iter().map(|t| (**t).clone()).collect::<Vec<_>>(), 0)(
                &current,
            )
        } else {
            tactic::eresolve_tac(&elim_cands.iter().map(|t| (**t).clone()).collect::<Vec<_>>(), 0)(
                &current,
            )
        };
        let mut branch_count = 0usize;
        for r in resolve_results.iter().chain(eresolve_results.iter()) {
            if r.nprems() == 0 {
                return vec![r.clone()];
            }
            if r.nprems() < current.nprems() + 5 && branch_count < branch_limit {
                branch_count += 1;
                children.push((r.clone(), depth + 1));
            }
        }

        // Phase 4: dresolve
        let dresolve_results = tactic::dresolve_tac(
            &db.intros.iter().map(|t| (**t).clone()).collect::<Vec<_>>(),
            0,
        )(&current);
        for r in &dresolve_results {
            if r.nprems() == 0 {
                return vec![r.clone()];
            }
            if r.nprems() < current.nprems() && depth < 20 {
                children.push((r.clone(), depth + 1));
            }
        }

        // Phase 5: aggressive fallback (resolve with ALL theorems)
        if depth < 5 {
            let all_results = tactic::resolve_tac(
                &db.all.iter().take(30).map(|t| (**t).clone()).collect::<Vec<_>>(),
                0,
            )(&current);
            for r in &all_results {
                if r.nprems() == 0 {
                    return vec![r.clone()];
                }
                if r.nprems() < current.nprems() + 3 && depth < 3 {
                    children.push((r.clone(), depth + 2));
                }
            }
        }

        // Phase 6: assume_results that are non-trivial
        for r in &assume_results {
            if r.nprems() != 0 {
                children.push((r.clone(), depth + 1));
            }
        }

        // ── Iterative DFS over children ──
        // Push in reverse order so the first child is processed first (preserves DFS order)
        children.reverse();
        let mut stack: Vec<(Thm, usize)> = children;

        while let Some((child_state, child_depth)) = stack.pop() {
            // Budget check at each DFS node
            PROOF_SEARCH_BUDGET.with(|c| {
                let b = c.get();
                if b > 0 {
                    c.set(b - 1);
                }
            });
            if PROOF_SEARCH_BUDGET.with(|c| c.get()) == 0 && child_depth > 1 {
                continue;
            }
            // Deadline check
            let expired =
                VERIFY_DEADLINE.with(|c| c.get().is_some_and(|d| std::time::Instant::now() >= d));
            if expired {
                continue;
            }
            if child_depth > 8 {
                continue;
            }

            // Apply safe rules to child
            let child = Self::apply_safe_rules(&child_state, premises, db);
            if child.nprems() == 0 {
                return vec![child];
            }

            // Try assumption on child
            let child_assume = tactic::assume_tac(0)(&child);
            for r in &child_assume {
                if r.nprems() == 0 {
                    return vec![r.clone()];
                }
            }

            let child_branch_limit = if child_depth > 6 {
                3
            } else if child_depth > 3 {
                8
            } else {
                25
            };

            // Simp on child — use cached simplifier
            let child_simp_results = tactic::simp_tac(db.base_simplifier().clone(), 0)(&child);
            let mut cs_branches = 0usize;
            for r in &child_simp_results {
                if r.nprems() != child.nprems() {
                    if cs_branches >= child_branch_limit / 2 {
                        break;
                    }
                    cs_branches += 1;
                    // Recurse into simp child
                    let sub = Self::auto_exec(r, child_depth + 1, premises, db);
                    for s in &sub {
                        if s.nprems() == 0 {
                            return sub;
                        }
                    }
                }
            }

            // Resolve/eresolve on child
            let child_subgoal = match child.prem(0) {
                Some(p) => p,
                None => continue,
            };
            let c_intro = db.intro_net().lookup(&child_subgoal);
            let c_elim = db.elim_net().lookup(&child_subgoal);
            let c_resolve = if c_intro.is_empty() {
                tactic::resolve_tac(&db.intros.iter().map(|t| (**t).clone()).collect::<Vec<_>>(), 0)(
                    &child,
                )
            } else {
                tactic::resolve_tac(&c_intro.iter().map(|t| (**t).clone()).collect::<Vec<_>>(), 0)(
                    &child,
                )
            };
            let c_eresolve = if c_elim.is_empty() {
                tactic::eresolve_tac(&db.elims.iter().map(|t| (**t).clone()).collect::<Vec<_>>(), 0)(
                    &child,
                )
            } else {
                tactic::eresolve_tac(&c_elim.iter().map(|t| (**t).clone()).collect::<Vec<_>>(), 0)(
                    &child,
                )
            };
            let mut c_branch_count = 0usize;
            // Push new children in reverse order for DFS
            let mut new_children: Vec<(Thm, usize)> = Vec::new();
            for r in c_resolve.iter().chain(c_eresolve.iter()) {
                if r.nprems() == 0 {
                    return vec![r.clone()];
                }
                if r.nprems() < child.nprems() + 5 && c_branch_count < child_branch_limit {
                    c_branch_count += 1;
                    new_children.push((r.clone(), child_depth + 1));
                }
            }

            // dresolve on child
            let c_dresolve = tactic::dresolve_tac(
                &db.intros.iter().map(|t| (**t).clone()).collect::<Vec<_>>(),
                0,
            )(&child);
            for r in &c_dresolve {
                if r.nprems() == 0 {
                    return vec![r.clone()];
                }
                if r.nprems() < child.nprems() && child_depth < 20 {
                    new_children.push((r.clone(), child_depth + 1));
                }
            }

            // assume_results on child
            for r in &child_assume {
                if r.nprems() != 0 {
                    new_children.push((r.clone(), child_depth + 1));
                }
            }

            // Push new children in reverse order (DFS: first child processed first)
            new_children.reverse();
            for nc in new_children {
                stack.push(nc);
            }
        }

        vec![state.clone()]
    }
}

/// Try to prove a goal using the auto method.
pub fn prove_auto(goal: &Thm, premises: &[Arc<Thm>], db: &HolTheoremDb) -> Option<Thm> {
    let results = Method::Auto.execute(goal, premises, db);
    results.into_iter().find(|r| r.nprems() == 0)
}

/// Try to solve all subgoals by matching against premises.
fn solve_by_assumption(state: &Thm, premises: &[Arc<Thm>]) -> Option<Thm> {
    let mut current = state.clone();
    while current.nprems() > 0 {
        let mut any = false;
        // First try exact alpha-equivalence (standard assume_tac)
        for prem in premises {
            if let Some(ns) = ThmKernel::bicompose(false, prem, &current, 0)
                && ns.nprems() < current.nprems()
            {
                current = ns;
                any = true;
                break;
            }
        }
        // Try unification-based matching for schematic subgoals
        if !any {
            for prem in premises {
                if let Some(ns) = ThmKernel::bicompose(true, prem, &current, 0)
                    && ns.nprems() < current.nprems()
                {
                    current = ns;
                    any = true;
                    break;
                }
            }
        }
        if !any {
            break;
        }
    }
    if current.nprems() == 0 { Some(current) } else { None }
}

/// Execute a proof script on a goal with premises.
pub fn exec_proof(
    state: &Thm,
    proof_script: &str,
    premises: &[Arc<Thm>],
    db: &HolTheoremDb,
) -> Option<Thm> {
    AUTO_DEPTH.with(|c| c.set(0));
    let script = proof_script.trim();

    // Handle `by <methods>` or `by(methods)` format
    let rest = if let Some(r) = script.strip_prefix("by ") {
        Some(r.to_string())
    } else {
        script.strip_prefix("by(").map(|r| format!("({}", r))
    };

    if let Some(rest) = rest {
        let methods = split_chained_methods(&rest);
        let mut current_states = vec![state.clone()];
        for method_str in &methods {
            let mut next_states = Vec::new();
            for s in &current_states {
                let results = exec_single_method(s, method_str, premises, db);
                next_states.extend(results);
            }
            if next_states.is_empty() {
                // Fallback: try auto/blast on previous states (with deadline check)
                let expired = VERIFY_DEADLINE
                    .with(|c| c.get().is_some_and(|d| std::time::Instant::now() >= d));
                if expired {
                    return None;
                }
                for s in &current_states {
                    for r in Method::Auto.execute(s, premises, db) {
                        if r.nprems() == 0 {
                            return Some(r);
                        }
                        next_states.push(r);
                    }
                    for r in Method::Blast.execute(s, premises, db) {
                        if r.nprems() == 0 {
                            return Some(r);
                        }
                        next_states.push(r);
                    }
                }
                if next_states.is_empty() {
                    return None;
                }
            }
            current_states = next_states;
        }
        let best = current_states.into_iter().next();
        if let Some(r) =
            best.as_ref().and_then(|s| if s.nprems() == 0 { Some(s.clone()) } else { None })
        {
            return Some(r);
        }
        // Fallback chain: solve_by_assumption → premise-unify → auto → blast
        // Each phase checks VERIFY_DEADLINE to prevent unbounded search.
        if let Some(best) = best {
            if let Some(solved) = solve_by_assumption(&best, premises) {
                return Some(solved);
            }
            // Check deadline before expensive premise unification loop
            let expired =
                VERIFY_DEADLINE.with(|c| c.get().is_some_and(|d| std::time::Instant::now() >= d));
            if expired {
                return None;
            }
            // Try bicompose with each premise (unification) to close schematic subgoals
            // Check deadline periodically inside this potentially expensive loop
            let mut current = best.clone();
            for i in 0..current.nprems() + 5 {
                if i % 3 == 0 {
                    let expired = VERIFY_DEADLINE
                        .with(|c| c.get().is_some_and(|d| std::time::Instant::now() >= d));
                    if expired {
                        return None;
                    }
                }
                let mut any = false;
                for prem in premises {
                    if let Some(ns) = ThmKernel::bicompose(true, prem, &current, 0)
                        && ns.nprems() < current.nprems()
                    {
                        current = ns;
                        any = true;
                        break;
                    }
                }
                if !any {
                    break;
                }
            }
            if current.nprems() == 0 {
                return Some(current);
            }
            // Check deadline before auto/blast (expensive deep search)
            let expired =
                VERIFY_DEADLINE.with(|c| c.get().is_some_and(|d| std::time::Instant::now() >= d));
            if expired {
                return None;
            }
            for r in Method::Auto.execute(&current, premises, db) {
                if r.nprems() == 0 {
                    return Some(r);
                }
            }
            let expired =
                VERIFY_DEADLINE.with(|c| c.get().is_some_and(|d| std::time::Instant::now() >= d));
            if expired {
                return None;
            }
            for r in Method::Blast.execute(&current, premises, db) {
                if r.nprems() == 0 {
                    return Some(r);
                }
            }
        }
        return None;
    }

    // Handle `using thms by method` or `unfolding defs by method`
    if script.starts_with("using ") || script.starts_with("unfolding ") {
        let results = exec_single_method(state, script, premises, db);
        if let Some(r) = results.iter().find(|r| r.nprems() == 0) {
            return Some(r.clone());
        }
        // Fallback: try auto/blast/solve_by_assumption on partial results
        for r in &results {
            if r.nprems() > 0 {
                if let Some(solved) = solve_by_assumption(r, premises) {
                    return Some(solved);
                }
                for ar in Method::Auto.execute(r, premises, db) {
                    if ar.nprems() == 0 {
                        return Some(ar);
                    }
                }
                for br in Method::Blast.execute(r, premises, db) {
                    if br.nprems() == 0 {
                        return Some(br);
                    }
                }
            }
        }
        return None;
    }

    // Handle `proof <method>` or `apply <method>` scripts
    if script.starts_with("proof") || script.starts_with("apply") {
        // Multi-line scripts: extract all `by <method>` from body and chain them
        if script.contains('\n') {
            // First, execute the proof method line (e.g., "proof (induct xs)")
            let first_line = script.lines().next().unwrap_or(script);
            let results = exec_single_method(state, first_line.trim(), premises, db);
            let mut current_states: Vec<Thm> = results;
            if current_states.is_empty() {
                return None;
            }

            // Extract `by <method>` hints from body lines
            // Patterns: "show ?case by ...", "by ...", "qed ..."
            let mut by_methods = Vec::new();
            for line in script.lines().skip(1) {
                let t = line.trim();
                if t == "done" || t == "next" || t == "{" || t == "}" {
                    continue;
                }
                // Extract "by ..." from "show ?case by auto" or "qed auto"
                for keyword in &[" by ", "by(", "\tby "] {
                    if let Some(pos) = t.find(keyword) {
                        let method = t[pos..].trim().to_string();
                        if !method.is_empty() && method != "by" {
                            by_methods.push(method);
                            break;
                        }
                    }
                }
                // Also catch "qed auto" (qed followed by method)
                if let Some(rest) = t.strip_prefix("qed ")
                    && !rest.is_empty()
                    && rest != "{"
                {
                    by_methods.push(format!("by {}", rest));
                }
            }

            // Apply extracted methods sequentially
            for method in &by_methods {
                let mut next_states = Vec::new();
                for s in &current_states {
                    if s.nprems() == 0 {
                        next_states.push(s.clone());
                        continue;
                    }
                    let results = exec_single_method(s, method, premises, db);
                    next_states.extend(results);
                }
                if next_states.is_empty() {
                    break;
                }
                current_states = next_states;
            }
            return current_states.into_iter().find(|r| r.nprems() == 0);
        }
        let results = exec_single_method(state, script, premises, db);
        return results.into_iter().find(|r| r.nprems() == 0);
    }

    // Handle arithmetic: try built-in nat arithmetic rules
    if script.contains("arith") || script.contains("presburger") {
        let results = exec_arith(state, premises, db);
        if results.iter().any(|r| r.nprems() == 0) {
            return results.into_iter().find(|r| r.nprems() == 0);
        }
    }

    // Unknown proof format → try aggressive fallback chain
    let mut current = state.clone();
    // Try auto
    for r in Method::Auto.execute(&current, premises, db) {
        if r.nprems() == 0 {
            return Some(r);
        }
        current = r;
    }
    // Try blast
    for r in Method::Blast.execute(&current, premises, db) {
        if r.nprems() == 0 {
            return Some(r);
        }
        current = r;
    }
    // Try simp
    let rules: Vec<RewriteRule> =
        db.simps.iter().filter_map(|t| RewriteRule::from_thm(Arc::clone(t))).collect();
    let simp = Simplifier::new(rules);
    Method::Simp(simp).execute(&current, premises, db).into_iter().find(|r| r.nprems() == 0)
}

thread_local! {
    static SINGLE_METHOD_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Parse a method string into a Method value (without executing).
/// Used by combinator parsing to construct composed methods.
fn parse_single_method(
    method_str: &str,
    _state: &Thm,
    _premises: &[Arc<Thm>],
    db: &HolTheoremDb,
) -> Method {
    let s = method_str.trim();
    let s = if s.starts_with('(') && s.ends_with(')') { &s[1..s.len() - 1] } else { s };
    let s = s.trim();
    match s {
        "auto" | "Auto" => Method::Auto,
        "blast" | "Blast" => Method::Blast,
        "fast" | "Fast" => Method::Fast,
        "best" | "Best" => Method::Best,
        "safe" | "Safe" => Method::Auto, // safe is auto with safe rules
        "simp" | "Simp" => {
            let rules: Vec<RewriteRule> =
                db.simps.iter().filter_map(|t| RewriteRule::from_thm(Arc::clone(t))).collect();
            Method::Simp(Simplifier::new(rules))
        },
        "assumption" | "assume" | "." => Method::Assumption,
        "skip" | "this" => Method::Skip,
        "fail" => Method::Fail,
        "try" | "try0" => Method::Try,
        "step" => Method::Step,
        "coinduct" | "coinduction" => Method::Coinduct,
        "metis" | "Metis" => Method::Metis,
        "meson" | "Meson" => Method::Meson,
        "iprover" | "iprover " => Method::Auto, // fallback
        "force" | "fastforce" | "clarify" | "clarsimp" => Method::Auto,
        "arith" | "presburger" => Method::Auto, // fallback
        _ => Method::Auto,                      // default fallback
    }
}

pub fn exec_single_method(
    state: &Thm,
    method_str: &str,
    premises: &[Arc<Thm>],
    db: &HolTheoremDb,
) -> Vec<Thm> {
    let depth = SINGLE_METHOD_DEPTH.with(|c| {
        let d = c.get() + 1;
        c.set(d);
        d
    });
    if depth > 200 {
        SINGLE_METHOD_DEPTH.with(|c| c.set(c.get() - 1));
        return vec![state.clone()];
    }
    let result = exec_single_method_inner(state, method_str, premises, db);
    SINGLE_METHOD_DEPTH.with(|c| c.set(c.get() - 1));
    result
}

fn exec_single_method_inner(
    state: &Thm,
    method_str: &str,
    premises: &[Arc<Thm>],
    db: &HolTheoremDb,
) -> Vec<Thm> {
    let inner = if method_str.starts_with('(') && method_str.ends_with(')') {
        method_str[1..method_str.len() - 1].trim()
    } else {
        method_str
    };

    // Handle combinators: REPEAT method, method1 | method2 (ORELSE)
    if inner.starts_with("REPEAT ") || inner.starts_with("repeat ") {
        let sub = inner.split_once(' ').map(|x| x.1).unwrap_or("");
        let method = parse_single_method(sub, state, premises, db);
        return Method::Repeat(Box::new(method)).execute(state, premises, db);
    }
    if let Some(pipe) = inner.find('|') {
        let left = inner[..pipe].trim();
        let right = inner[pipe + 1..].trim();
        if !left.is_empty() && !right.is_empty() {
            let m1 = parse_single_method(left, state, premises, db);
            let m2 = parse_single_method(right, state, premises, db);
            return Method::Orelse(Box::new((m1, m2))).execute(state, premises, db);
        }
    }

    // Handle comma-separated sub-methods (treated as THEN)
    if let Some(comma) = inner.find(',') {
        let mut depth = 0;
        let mut valid = false;
        for (i, ch) in inner.char_indices() {
            if ch == '(' || ch == '[' {
                depth += 1;
            } else if ch == ')' || ch == ']' {
                depth -= 1;
            } else if ch == ',' && depth == 0 && i == comma {
                valid = true;
                break;
            }
        }
        if valid || depth == 0 {
            let subs = split_comma_methods(inner);
            let mut states = vec![state.clone()];
            for sub in &subs {
                let mut next = Vec::new();
                for s in &states {
                    next.extend(exec_single_method(s, sub, premises, db));
                }
                if next.is_empty() {
                    return vec![];
                }
                states = next;
            }
            return states;
        }
    }

    if inner == "auto" || inner.starts_with("auto ") || inner.starts_with("auto(") {
        // Parse auto directives: intro:, simp:, elim:, dest:, iff:, add:, del:
        if inner.contains(':')
            && let Some(rest) = inner.strip_prefix("auto ")
        {
            let toks: Vec<&str> = rest.split_whitespace().collect();
            let mut i = 0;
            let mut directive_thms: Vec<Arc<Thm>> = Vec::new();
            while i < toks.len() {
                let is_directive = matches!(
                    toks[i],
                    "intro:" | "simp:" | "elim:" | "dest:" | "iff:" | "add:" | "del:"
                );
                if is_directive {
                    i += 1;
                    while i < toks.len() && !toks[i].contains(':') {
                        let n = toks[i].trim_end_matches(',');
                        if let Some(t) = resolve_theorem_name(n, db) {
                            directive_thms.push((*t).clone().into());
                        }
                        i += 1;
                    }
                } else {
                    i += 1;
                }
            }
            // Apply collected directive theorems before auto
            if !directive_thms.is_empty() {
                let mut current = state.clone();
                for thm in &directive_thms {
                    let results = crate::core::tactic::resolve_tac(&[(**thm).clone()], 0)(&current);
                    if let Some(r) = results.into_iter().next() {
                        current = r;
                    }
                }
                if current.nprems() == 0 {
                    return vec![current];
                }
                // Run auto with directive theorems as additional premises
                let mut extended = premises.to_vec();
                extended.extend(directive_thms);
                let auto_results = Method::Auto.execute(&current, &extended, db);
                if auto_results.iter().any(|r| r.nprems() == 0) {
                    return auto_results;
                }
            }
        }
        let results = Method::Auto.execute(state, premises, db);
        if results.iter().any(|r| r.nprems() == 0) {
            return results;
        }
        // Try blast, then auto with extended premises
        let blast_results = Method::Blast.execute(state, premises, db);
        if blast_results.iter().any(|r| r.nprems() == 0) {
            return blast_results;
        }
        // Try simp — use cached base simplifier to avoid rebuilding on every fallback
        return Method::Simp(db.base_simplifier().clone()).execute(state, premises, db);
    }
    if inner == "simp"
        || inner.starts_with("simp ")
        || inner.starts_with("simp:")
        || inner.starts_with("simp(")
    {
        let results = exec_simp(inner, state, premises, db);
        if results.iter().any(|r| r.nprems() == 0) {
            return results;
        }
        // Try to close remaining subgoals by assumption
        let mut closed = Vec::new();
        for r in &results {
            if r.nprems() > 0
                && let Some(solved) = solve_by_assumption(r, premises)
            {
                closed.push(solved);
            }
        }
        if !closed.is_empty() {
            return closed;
        }
        if !results.is_empty() {
            return results;
        }
        let blast_results = Method::Blast.execute(state, premises, db);
        if blast_results.iter().any(|r| r.nprems() == 0) {
            return blast_results;
        }
        return Method::Auto.execute(state, premises, db);
    }
    if inner == "simp_all" || inner.starts_with("simp_all ") || inner.starts_with("simp_all:") {
        let results = exec_simp_all(state, premises, db);
        if results.iter().any(|r| r.nprems() == 0) {
            return results;
        }
        return Method::Auto.execute(state, premises, db);
    }
    if inner == "blast" || inner.starts_with("blast ") || inner.starts_with("blast(") {
        let results = Method::Blast.execute(state, premises, db);
        if results.iter().any(|r| r.nprems() == 0) {
            return results;
        }
        let auto_results = Method::Auto.execute(state, premises, db);
        if auto_results.iter().any(|r| r.nprems() == 0) {
            return auto_results;
        }
        // Try simp — use cached base simplifier
        return Method::Simp(db.base_simplifier().clone()).execute(state, premises, db);
    }
    if inner == "assumption" || inner == "." {
        let results = Method::Assumption.execute(state, premises, db);
        if results.is_empty()
            && let Some(solved) = solve_by_assumption(state, premises)
        {
            return vec![solved];
        }
        return results;
    }
    if inner == "this" {
        return Method::Skip.execute(state, premises, db);
    }
    if inner == "blast" {
        return Method::Blast.execute(state, premises, db);
    }
    if inner == "iprover" || inner.starts_with("iprover ") {
        // Parse intro:/elim:/dest: arguments and apply them
        if inner.contains("intro:") || inner.contains("elim:") || inner.contains("dest:") {
            let results = exec_intro_elim(inner, state, premises, db);
            if results.iter().any(|r| r.nprems() == 0) {
                return results;
            }
            // Try to close remaining subgoals with premises before falling back
            let mut closed = Vec::new();
            for r in &results {
                if r.nprems() > 0
                    && let Some(solved) = solve_by_assumption(r, premises)
                {
                    closed.push(solved);
                }
            }
            if !closed.is_empty() {
                return closed;
            }
            // Return partial results if any
            if !results.is_empty() {
                return results;
            }
        }
        // Fallback: try blast then auto
        let blast = Method::Blast.execute(state, premises, db);
        if blast.iter().any(|r| r.nprems() == 0) {
            return blast;
        }
        return Method::Auto.execute(state, premises, db);
    }
    if inner == "metis" || inner.starts_with("metis ") || inner.starts_with("metis(") {
        let results = Method::Metis.execute(state, premises, db);
        if results.iter().any(|r| r.nprems() == 0) {
            return results;
        }
        // Metis partial result — try to close remaining subgoals
        let mut closed = Vec::new();
        for r in &results {
            if r.nprems() > 0
                && let Some(solved) = solve_by_assumption(r, premises)
            {
                closed.push(solved);
            }
        }
        if !closed.is_empty() {
            return closed;
        }
        // Fallback: auto then blast
        let auto = Method::Auto.execute(state, premises, db);
        if auto.iter().any(|r| r.nprems() == 0) {
            return auto;
        }
        return Method::Blast.execute(state, premises, db);
    }
    if inner == "meson" || inner.starts_with("meson ") || inner.starts_with("meson(") {
        let results = Method::Meson.execute(state, premises, db);
        if results.iter().any(|r| r.nprems() == 0) {
            return results;
        }
        return Method::Auto.execute(state, premises, db);
    }
    if inner == "fastforce" || inner.starts_with("fastforce ") || inner.starts_with("fastforce(") {
        return Method::Blast.execute(state, premises, db);
    }
    if inner == "force" || inner.starts_with("force ") || inner.starts_with("force(") {
        return Method::Auto.execute(state, premises, db);
    }
    if inner == "clarify" || inner.starts_with("clarify ") || inner.starts_with("clarify(") {
        return Method::Auto.execute(state, premises, db);
    }
    if inner == "clarsimp" || inner.starts_with("clarsimp ") || inner.starts_with("clarsimp(") {
        return Method::Auto.execute(state, premises, db);
    }
    if inner == "fast" || inner.starts_with("fast ") || inner.starts_with("fast(") {
        return Method::Fast.execute(state, premises, db);
    }
    if inner == "best" || inner.starts_with("best ") {
        return Method::Best.execute(state, premises, db);
    }
    if inner == "safe" {
        // Use safe rules exhaustively (faster than auto)
        let current = Method::apply_safe_rules(state, premises, db);
        if current.nprems() == 0 {
            return vec![current];
        }
        return Method::Auto.execute(state, premises, db);
    }
    if inner == "step" || inner.starts_with("step ") {
        return Method::Step.execute(state, premises, db);
    }
    if inner == "coinduction" || inner == "coinduct" {
        return Method::Coinduct.execute(state, premises, db);
    }
    if inner == "try" || inner == "try0" {
        return Method::Try.execute(state, premises, db);
    }
    if inner.starts_with("depth ") {
        let rest = inner.strip_prefix("depth ").unwrap_or("");
        let bound: usize = rest.trim().parse().unwrap_or(4);
        return Method::Depth(bound).execute(state, premises, db);
    }

    // (rule name [OF ...])
    if inner.starts_with("fact ") {
        let rest = inner.strip_prefix("fact ").unwrap_or("");
        let (name, _) = parse_of_suffix(rest);
        if let Some(thm) = db.by_name.get(name.trim()) {
            return crate::core::tactic::resolve_tac(&[(**thm).clone()], 0)(state);
        }
        return vec![];
    }
    if let Some(rest) = inner.strip_prefix("rule ") {
        let (name, other_attrs, of_args, then_args) = parse_of_and_then_suffix(rest);
        if let Some(thm) = resolve_theorem_name(name.trim(), db) {
            let mut thm = thm;
            if !other_attrs.is_empty() {
                thm = apply_attributes(thm, &other_attrs, db);
            }
            thm = apply_of(thm, of_args, db);
            thm = apply_then(thm, then_args, db);
            let results = crate::core::tactic::resolve_tac(&[(*thm).clone()], 0)(state);
            for r in &results {
                if r.nprems() == 0 {
                    return results;
                }
            }
            let mut all = if results.is_empty() {
                crate::core::tactic::eresolve_tac(&[(*thm).clone()], 0)(state)
            } else {
                results
            };
            for r in &all.clone() {
                if r.nprems() > 0 {
                    for ar in Method::Auto.execute(r, premises, db) {
                        if ar.nprems() == 0 {
                            all.push(ar);
                        }
                    }
                }
            }
            if all.iter().any(|r| r.nprems() == 0) {
                return all;
            }
            if !all.is_empty() {
                return all;
            }
        }
        let auto = Method::Auto.execute(state, premises, db);
        if auto.iter().any(|r| r.nprems() == 0) {
            return auto;
        }
        if !auto.is_empty() {
            return auto;
        }
        return vec![];
    }
    // (subst ...)
    if let Some(rest) = inner.strip_prefix("subst ") {
        return exec_subst(rest, state, premises, db);
    }
    // (erule name [OF ...] [THEN ...])
    if let Some(rest) = inner.strip_prefix("erule ") {
        let (name, other_attrs, of_args, then_args) = parse_of_and_then_suffix(rest);
        if let Some(thm) = resolve_theorem_name(name.trim(), db) {
            let mut thm = thm;
            if !other_attrs.is_empty() {
                thm = apply_attributes(thm, &other_attrs, db);
            }
            thm = apply_of(thm, of_args, db);
            thm = apply_then(thm, then_args, db);
            let results = crate::core::tactic::eresolve_tac(&[(*thm).clone()], 0)(state);
            if !results.is_empty() {
                return results;
            }
        }
        return vec![];
    }
    // (drule name [OF ...] [THEN ...])
    if let Some(rest) = inner.strip_prefix("drule ") {
        let (name, other_attrs, of_args, then_args) = parse_of_and_then_suffix(rest);
        if let Some(thm) = resolve_theorem_name(name.trim(), db) {
            let mut thm = thm;
            if !other_attrs.is_empty() {
                thm = apply_attributes(thm, &other_attrs, db);
            }
            thm = apply_of(thm, of_args, db);
            thm = apply_then(thm, then_args, db);
            let results = crate::core::tactic::dresolve_tac(&[(*thm).clone()], 0)(state);
            if !results.is_empty() {
                return results;
            }
        }
        return vec![];
    }
    // (frule name [OF ...] [THEN ...])
    if let Some(rest) = inner.strip_prefix("frule ") {
        let (name, other_attrs, of_args, then_args) = parse_of_and_then_suffix(rest);
        if let Some(thm) = resolve_theorem_name(name.trim(), db) {
            let mut thm = thm;
            if !other_attrs.is_empty() {
                thm = apply_attributes(thm, &other_attrs, db);
            }
            thm = apply_of(thm, of_args, db);
            thm = apply_then(thm, then_args, db);
            let results = crate::core::tactic::dresolve_tac(&[(*thm).clone()], 0)(state);
            return results;
        }
        return vec![];
    }
    // (unfold name [OF ...])
    if let Some(rest) = inner.strip_prefix("unfold ") {
        let names: Vec<&str> = rest.split_whitespace().collect();
        let thms: Vec<Arc<Thm>> =
            names.iter().filter_map(|n| db.by_name.get(*n).cloned()).collect();
        if !thms.is_empty() {
            return Method::Unfold(thms).execute(state, premises, db);
        }
    }
    // (fold name [OF ...])
    if let Some(rest) = inner.strip_prefix("fold ") {
        let names: Vec<&str> = rest.split_whitespace().collect();
        let thms: Vec<Arc<Thm>> =
            names.iter().filter_map(|n| db.by_name.get(*n).cloned()).collect();
        if !thms.is_empty() {
            return Method::Fold(thms).execute(state, premises, db);
        }
    }
    // (insert name [OF ...])
    if let Some(rest) = inner.strip_prefix("insert ") {
        let names: Vec<&str> = rest.split_whitespace().collect();
        let thms: Vec<Arc<Thm>> =
            names.iter().filter_map(|n| db.by_name.get(*n).cloned()).collect();
        if !thms.is_empty() {
            return Method::Insert(thms).execute(state, premises, db);
        }
    }
    // (induct x)
    if let Some(rest) = inner.strip_prefix("induct ") {
        let var = rest.trim().to_string();
        return Method::Induct(var).execute(state, premises, db);
    }
    // (cases x)
    if let Some(rest) = inner.strip_prefix("cases ") {
        let var = rest.trim().to_string();
        return Method::Cases(var).execute(state, premises, db);
    }
    // intro: / elim: / dest: parameter parsing
    if inner.starts_with("intro:") || inner.starts_with("elim:") || inner.starts_with("dest:") {
        return exec_intro_elim(inner, state, premises, db);
    }
    // proof scripts: "proof method", "proof -", "apply method"
    if inner.starts_with("proof ")
        || inner == "proof"
        || inner.starts_with("proof(")
        || inner.starts_with("apply")
    {
        return exec_proof_script(inner, state, premises, db);
    }
    // `using thms proof ...` — add named facts as premises
    if let Some(rest) = inner.strip_prefix("using ") {
        // Collect the named facts after "using"
        // strip "using "
        // Find where the proof method starts
        let (facts_str, method_str) = if let Some(pos) = rest.find(" proof ") {
            (&rest[..pos], &rest[pos + 1..])
        } else if let Some(pos) = rest.find(" apply") {
            (&rest[..pos], &rest[pos..])
        } else if let Some(pos) = rest.find(" by ") {
            (&rest[..pos], &rest[pos + 1..])
        } else {
            (rest, "")
        };
        // Look up each fact and add to premises
        let mut extended_prems = premises.to_vec();
        for name in facts_str.split_whitespace() {
            // Skip keywords like "assms", "this", "that"
            if name == "assms" || name == "this" || name == "that" {
                // These refer to existing premises — already included
                continue;
            }
            if let Some(thm) = db.by_name.get(name) {
                extended_prems.push(Arc::clone(thm));
            }
        }
        // Execute with extended premises
        if method_str.is_empty() {
            return Method::Auto.execute(state, &extended_prems, db);
        }
        if method_str.starts_with("proof") {
            return exec_proof_script(method_str, state, &extended_prems, db);
        }
        if method_str.starts_with("apply") {
            return exec_proof_script(method_str, state, &extended_prems, db);
        }
        return exec_single_method(state, method_str, &extended_prems, db);
    }
    // `unfolding defs` or `unfolding defs by method`
    if inner.starts_with("unfolding ") {
        if let Some(pos) = inner.find(" by ") {
            // First unfold, then execute the by-method
            let unfold_part = &inner[..pos];
            let by_part = &inner[pos + 1..];
            let unfold_results = exec_unfold(unfold_part, state, premises, db);
            let mut all_results = Vec::new();
            for r in &unfold_results {
                let by_results = exec_single_method(r, by_part, premises, db);
                all_results.extend(by_results);
            }
            if !all_results.is_empty() {
                return all_results;
            }
        }
        // Just `unfolding defs` — try unfold
        return exec_unfold(inner, state, premises, db);
    }
    vec![]
}

/// Execute `unfolding def1 def2 ...` as an unfold method.
fn exec_unfold(
    method_str: &str,
    state: &Thm,
    premises: &[Arc<Thm>],
    db: &HolTheoremDb,
) -> Vec<Thm> {
    let rest = method_str.strip_prefix("unfolding ").unwrap_or(method_str);
    let names: Vec<&str> = rest.split_whitespace().collect();
    let thms: Vec<Arc<Thm>> = names
        .iter()
        .filter_map(|n| {
            // Skip attributes like [symmetric], [abs_def]
            if *n == "[symmetric]" || *n == "[abs_def]" || *n == "[" || *n == "]" {
                return None;
            }
            if n.starts_with('[') && n.ends_with(']') {
                return None;
            }
            // Clean the name
            let clean_name = n.trim_matches(|c: char| c == '[' || c == ']' || c == '(' || c == ')');
            if clean_name.is_empty() {
                return None;
            }
            // Skip numerals and operators
            if clean_name.chars().all(|c| c.is_numeric() || c == '.' || c == '(' || c == ')') {
                return None;
            }
            // 1. Exact match
            if let Some(thm) = db.by_name.get(clean_name) {
                return Some(Arc::clone(thm));
            }
            // 2. With dots replaced by underscores
            let underscored = clean_name.replace('.', "_");
            if underscored != clean_name
                && let Some(thm) = db.by_name.get(&underscored)
            {
                return Some(Arc::clone(thm));
            }
            // 3. With underscores replaced by dots
            let dotted = clean_name.replace('_', ".");
            if dotted != clean_name
                && let Some(thm) = db.by_name.get(&dotted)
            {
                return Some(Arc::clone(thm));
            }
            // 4. Try adding "_def" suffix
            let with_def = format!("{}_def", clean_name);
            if let Some(thm) = db.by_name.get(&with_def) {
                return Some(Arc::clone(thm));
            }
            // 5. Try stripping "_def" suffix
            if let Some(base) = clean_name.strip_suffix("_def")
                && let Some(thm) = db.by_name.get(base)
            {
                return Some(Arc::clone(thm));
            }
            None
        })
        .collect();
    if thms.is_empty() {
        return vec![state.clone()];
    }
    Method::Unfold(thms).execute(state, premises, db)
}

/// Execute induction: parse `induct var arbitrary: v1 v2 rule: rulename`
/// Looks up induction theorems in the DB and applies via resolve_tac.
/// Execute substitution: replace equals by equals in goal or assumptions.
/// Supports: subst, subst (asm), subst thm_name, subst (asm) thm_name
fn exec_subst(method_str: &str, state: &Thm, premises: &[Arc<Thm>], db: &HolTheoremDb) -> Vec<Thm> {
    let rest = method_str.trim();
    let mut in_asm = false;
    let rest = if let Some(stripped) = rest.strip_prefix("(asm) ") {
        in_asm = true;
        stripped
    } else if rest == "(asm)" {
        in_asm = true;
        ""
    } else {
        rest
    };

    // If a specific theorem is given, use it directly
    if !rest.is_empty() {
        let eq_name = rest.trim();
        if let Some(eq_thm) = db.by_name.get(eq_name) {
            return apply_substitution(state, eq_thm, in_asm, premises, db);
        }
        // Try as a direct equality: "x = y" format — not supported yet
        return vec![];
    }

    // No specific theorem: try to find matching equality in premises or db
    // Look through premises for equalities
    for prem in premises {
        if let Some((_l, _r)) = Pure::dest_equals(prem.prop().term()) {
            let results = apply_substitution(state, prem, in_asm, premises, db);
            if !results.is_empty() {
                return results;
            }
            // Also try swapped
            let swapped = ThmKernel::symmetric(prem).ok();
            if let Some(ref sym_thm) = swapped {
                let results = apply_substitution(state, sym_thm, in_asm, premises, db);
                if !results.is_empty() {
                    return results;
                }
            }
        }
    }

    // Fall back to generic subst theorem
    if let Some(subst_thm) = db.by_name.get("subst") {
        return tactic::resolve_tac(&[(**subst_thm).clone()], 0)(state);
    }

    vec![]
}

/// Apply an equality theorem to perform substitution.
fn apply_substitution(
    state: &Thm,
    eq_thm: &Thm,
    in_asm: bool,
    premises: &[Arc<Thm>],
    db: &HolTheoremDb,
) -> Vec<Thm> {
    if in_asm {
        // Substitute in assumptions: for each hypothesis, try to rewrite
        let mut results = Vec::new();
        for i in 0..state.nprems() {
            if let Some(prem) = state.prem(i) {
                // Try to rewrite the hypothesis using eq_thm
                let rule = RewriteRule::from_thm(Arc::new(eq_thm.clone()));
                if let Some(rule) = rule {
                    let simp = Simplifier::new(vec![rule]);
                    if let Some((rewritten, eq_proof)) = simp.rewrite_deep(&prem)
                        && rewritten != prem
                        && let Some(new_state) = ThmKernel::subst_premise(&eq_proof, state, i)
                    {
                        results.push(new_state);
                    }
                }
            }
        }
        results
    } else {
        // Substitute in goal: use subst theorem [OF eq_thm]
        if let Some(subst_thm) = db.by_name.get("subst") {
            let combined = ThmKernel::bicompose(true, eq_thm, subst_thm, 0)
                .or_else(|| ThmKernel::bicompose(true, eq_thm, subst_thm, 1));
            if let Some(combined) = combined {
                return tactic::resolve_tac(&[combined], 0)(state);
            }
        }
        // Direct rewrite on goal
        if let Some(goal) = state.prem(0) {
            let rule = RewriteRule::from_thm(Arc::new(eq_thm.clone()));
            if let Some(rule) = rule {
                let simp = Simplifier::new(vec![rule]);
                if let Some((rewritten, eq_proof)) = simp.rewrite_deep(&goal)
                    && rewritten != goal
                    && let Some(new_state) = ThmKernel::subst_premise(&eq_proof, state, 0)
                {
                    return vec![new_state];
                }
            }
        }
        // Fallback: try auto
        let auto_results = Method::Auto.execute(state, premises, db);
        if auto_results.iter().any(|r| r.nprems() == 0) {
            return auto_results;
        }
        vec![]
    }
}

fn exec_induct(
    method_str: &str,
    state: &Thm,
    premises: &[Arc<Thm>],
    db: &HolTheoremDb,
) -> Vec<Thm> {
    // Parse parameters using centralized Args parser (Phase 51)
    let rest = method_str.strip_prefix("induct ").unwrap_or(method_str);
    let rest = rest.strip_prefix("cases ").unwrap_or(rest);
    let rest = rest.trim();

    let args = Args::parse_modifiers(rest);
    let mut var_name = "";
    // TODO: induct with arbitrary variables (args.arbitrary) not yet implemented.
    // When complete, use arbitrary_vars to generalize the induction scheme.
    let explicit_rule: Option<String> = args.rule_name.clone();

    let mut parts = rest.split_whitespace();
    if let Some(v) = parts.next()
        && !v.contains(':')
        && !v.contains('(')
    {
        var_name = v;
    }

    // 1. Try safe rules first (cheap, no backtracking)
    let safe = Method::apply_safe_rules(state, premises, db);
    if safe.nprems() == 0 {
        return vec![safe];
    }

    // 2. Try auto (general-purpose)
    let auto_results = Method::Auto.execute(state, premises, db);
    if auto_results.iter().any(|r| r.nprems() == 0) {
        return auto_results;
    }

    // 3. Collect candidate induction/cases rules
    let mut candidates: Vec<Arc<Thm>> = Vec::new();
    let is_cases = method_str.starts_with("cases");

    // 3a. Explicit rule: parameter
    if let Some(ref rname) = explicit_rule {
        for lookup in &[rname.clone(), rname.replace('_', ".")] {
            if let Some(thm) = db.by_name.get(lookup.as_str()) {
                candidates.push(Arc::clone(thm));
            }
        }
    }

    // 3b. Type-based lookup: search for `{var}.induct`, `{var}.cases`, `{var}.exhaust`
    if candidates.is_empty() && !var_name.is_empty() {
        let search_suffixes: &[&str] = if is_cases {
            &[".cases", ".exhaust", ".induct"]
        } else {
            &[".induct", ".cases", ".exhaust"]
        };
        // Try exact var name
        for suffix in search_suffixes {
            let name = format!("{var_name}{suffix}");
            if let Some(thm) = db.by_name.get(&name) {
                candidates.push(Arc::clone(thm));
            }
        }
        // Try type-based: analyze goal to find the type of var_name
        if candidates.is_empty()
            && let Some(goal) = state.prem(0)
        {
            // Analyze the goal's structure to guess the type
            let type_name = infer_type_from_goal(&goal, var_name);
            for suffix in search_suffixes {
                let name = format!("{type_name}{suffix}");
                if let Some(thm) = db.by_name.get(&name) {
                    candidates.push(Arc::clone(thm));
                }
            }
        }
    }

    // 3c. Heuristic: search for induction rules by name pattern
    if candidates.is_empty() {
        let induct_patterns = [
            "induct",
            "nat_induct",
            "list_induct",
            "length_induct",
            "measure_induct",
            "less_induct",
            "wf_induct",
            "fp_induct", // BNF Lfp induction
            "nchotomy",  // Ctr_Sugar exhaustive case distinction
        ];
        for (name, thm) in db.by_name.iter() {
            for pat in &induct_patterns {
                if name.contains(pat) && !candidates.iter().any(|c| Arc::ptr_eq(c, thm)) {
                    candidates.push(Arc::clone(thm));
                    break;
                }
            }
            if candidates.len() >= 20 {
                break;
            }
        }
    }

    // 3d. Try BNF Lfp fold/rec rules for constructor-based induction
    if candidates.is_empty() && !var_name.is_empty() {
        // Try to find {type}.fold or {type}.rec rules
        let type_name = state.prem(0).map(|goal| infer_type_from_goal(&goal, var_name));
        if let Some(tname) = type_name {
            for suffix in &[".fold_", ".rec_", ".fp_induct"] {
                for (name, thm) in db.by_name.iter() {
                    if name.starts_with(&tname) && name.contains(suffix) {
                        candidates.push(Arc::clone(thm));
                    }
                }
            }
        }
    }

    // 4. Try induction/cases rules with subgoal solving
    for rule in candidates.iter().take(8) {
        let results = tactic::resolve_tac(&[(**rule).clone()], 0)(state);
        for r in &results {
            if r.nprems() == 0 {
                return vec![r.clone()];
            }
            // Solve subgoals: try safe rules first, then auto for remaining
            if r.nprems() <= 10
                && let Some(solved) = solve_subgoals(r, premises, db)
            {
                return vec![solved];
            }
        }
    }

    // 5. Goal-directed induction for common types
    if let Some(results) = try_list_induct(state, premises, db) {
        return results;
    }

    // 6. Fallback: auto then blast
    if !auto_results.is_empty() {
        return auto_results;
    }
    Method::Blast.execute(state, premises, db)
}

/// Infer the likely type name for a variable from the goal's structure.
/// Looks at constants and patterns in the goal to guess the type.
fn infer_type_from_goal(goal: &Term, var_name: &str) -> String {
    let goal_str = format!("{goal:?}");
    // If goal mentions common list operations, the type is "list"
    if goal_str.contains("Cons")
        || goal_str.contains("Nil")
        || goal_str.contains("#")
        || goal_str.contains("map")
        || goal_str.contains("filter")
        || goal_str.contains("rev")
        || goal_str.contains("append")
        || goal_str.contains("@")
    {
        return "list".to_string();
    }
    // If goal mentions nat operations
    if goal_str.contains("Suc")
        || goal_str.contains("nat")
        || goal_str.contains("+ ")
        || goal_str.contains("* ")
    {
        return "nat".to_string();
    }
    // If goal mentions option
    if goal_str.contains("Some") || goal_str.contains("None") || goal_str.contains("option") {
        return "option".to_string();
    }
    // Default: use the variable name as hint
    var_name.to_string()
}

/// Try list induction: if the goal has a list variable, generate Nil/Cons subgoals.
fn try_list_induct(state: &Thm, premises: &[Arc<Thm>], db: &HolTheoremDb) -> Option<Vec<Thm>> {
    let goal = state.prem(0)?;
    // Check if the goal mentions common list operations (heuristic)
    let goal_str = format!("{:?}", goal);
    if !goal_str.contains("Cons")
        && !goal_str.contains("#")
        && !goal_str.contains("Nil")
        && !goal_str.contains("[]")
        && !goal_str.contains("list")
        && !goal_str.contains("map")
        && !goal_str.contains("filter")
        && !goal_str.contains("rev")
        && !goal_str.contains("concat")
        && !goal_str.contains("take")
        && !goal_str.contains("drop")
        && !goal_str.contains("zip")
        && !goal_str.contains("append")
        && !goal_str.contains("@")
    {
        return None;
    }
    // Look up list induction theorems
    let list_induct_names = [
        "list_induct2",
        "list_induct3",
        "list_induct4",
        "list_induct2'",
        "length_induct",
        "induct_list012",
    ];
    let mut induct_rules = Vec::new();
    for name in &list_induct_names {
        if let Some(thm) = db.by_name.get(*name) {
            induct_rules.push(Arc::clone(thm));
        }
    }
    // Try each induction rule with per-subgoal solving
    for rule in &induct_rules {
        let results = tactic::resolve_tac(&[(**rule).clone()], 0)(state);
        for r in &results {
            if r.nprems() == 0 {
                return Some(vec![r.clone()]);
            }
            if r.nprems() <= 15
                && let Some(s) = solve_subgoals(r, premises, db)
            {
                return Some(vec![s]);
            }
        }
    }
    None
}

/// Try to solve all subgoals of a state using auto, blast, and simp in sequence.
/// Accumulates solved subgoals as additional premises for subsequent subgoal solving.
fn solve_subgoals(state: &Thm, premises: &[Arc<Thm>], db: &HolTheoremDb) -> Option<Thm> {
    let mut current = state.clone();
    let mut accumulated: Vec<Arc<Thm>> = premises.to_vec();
    for _i in 0..state.nprems().min(15) {
        // Limit subgoals for performance
        let prem = current.prem(0)?;
        let goal = ThmKernel::assume_compat(CTerm::certify(prem));
        // Quick check: if subgoal is already in hyps, assume_tac can solve it
        if goal.nprems() == 0 {
            return Some(current);
        }
        // Try auto with accumulated premises
        let solved = prove_auto(&goal, &accumulated, db)
            .or_else(|| {
                Method::Blast.execute(&goal, &accumulated, db).into_iter().find(|r| r.nprems() == 0)
            })
            .or_else(|| {
                // Try simp as last resort
                let rules: Vec<RewriteRule> =
                    db.simps.iter().filter_map(|t| RewriteRule::from_thm(Arc::clone(t))).collect();
                let simp = Simplifier::new(rules);
                Method::Simp(simp)
                    .execute(&goal, &accumulated, db)
                    .into_iter()
                    .find(|r| r.nprems() == 0)
            });
        if let Some(solved_goal) = solved {
            // Add solved fact to accumulated premises for subsequent subgoals
            let solved_fact = Arc::new(solved_goal.clone());
            accumulated.push(solved_fact);
            if let Some(new_state) = ThmKernel::bicompose(false, &solved_goal, &current, 0) {
                current = new_state;
                continue;
            }
        }
        return None;
    }
    Some(current)
}

// Handle `proof` and `apply` proof scripts.
// Maps structured proof commands to existing methods as fallbacks.
thread_local! {
    static PROOF_SCRIPT_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

fn exec_proof_script(
    method_str: &str,
    state: &Thm,
    premises: &[Arc<Thm>],
    db: &HolTheoremDb,
) -> Vec<Thm> {
    let depth = PROOF_SCRIPT_DEPTH.with(|c| {
        let d = c.get() + 1;
        c.set(d);
        d
    });
    if depth > 50 {
        PROOF_SCRIPT_DEPTH.with(|c| c.set(0));
        return vec![state.clone()];
    }
    let result = exec_proof_script_inner(method_str, state, premises, db);
    PROOF_SCRIPT_DEPTH.with(|c| c.set(c.get() - 1));
    result
}

fn exec_proof_script_inner(
    method_str: &str,
    state: &Thm,
    premises: &[Arc<Thm>],
    db: &HolTheoremDb,
) -> Vec<Thm> {
    let inner = method_str.trim();

    // Multi-line proof scripts: execute first line, then extract body methods
    if inner.contains('\n') {
        let first_line = inner.lines().next().unwrap_or(inner);
        let mut results = exec_proof_script(first_line, state, premises, db);
        // Extract body methods and apply them
        let mut by_methods = Vec::new();
        for line in inner.lines().skip(1) {
            let t = line.trim();
            if t == "done" || t == "next" || t == "{" || t == "}" || t == "qed" {
                continue;
            }
            for keyword in &[" by ", "by("] {
                if let Some(pos) = t.find(keyword) {
                    let method = t[pos..].trim().to_string();
                    if !method.is_empty() && method != "by" {
                        by_methods.push(method);
                        break;
                    }
                }
            }
            if let Some(rest) = t.strip_prefix("qed ")
                && !rest.is_empty()
                && rest != "{"
            {
                by_methods.push(format!("by {}", rest));
            }
        }
        for method in &by_methods {
            let mut next = Vec::new();
            for r in &results {
                if r.nprems() == 0 {
                    next.push(r.clone());
                    continue;
                }
                next.extend(exec_single_method(r, method, premises, db));
            }
            if next.is_empty() {
                break;
            }
            results = next;
        }
        return results;
    }

    // `proof -` or bare `proof` → try auto (many end with `qed auto`)
    if inner == "proof" || inner == "proof-" || inner == "proof -" {
        return Method::Auto.execute(state, premises, db);
    }

    // `apply(method)` or `apply method` → extract and run the method
    if let Some(rest) = inner.strip_prefix("apply(") {
        let method = rest.trim_end_matches(')').trim();
        return exec_single_method(state, method, premises, db);
    }
    if let Some(rest) = inner.strip_prefix("apply ") {
        return exec_single_method(state, rest.trim(), premises, db);
    }

    // `proof (induct ...)` or `proof (induction ...)` → apply induction rule
    if inner.contains("induct") || inner.contains("induction") {
        return exec_induct(inner, state, premises, db);
    }

    // `proof (cases ...)` → fallback to auto
    if inner.contains("cases") {
        let auto_results = Method::Auto.execute(state, premises, db);
        if !auto_results.is_empty() {
            return auto_results;
        }
        return Method::Cases("".to_string()).execute(state, premises, db);
    }

    // `proof (rule name)` → extract and run rule
    if let Some(rest) = inner.strip_prefix("proof (rule ") {
        let name = rest.trim_end_matches(')').trim();
        if let Some(thm) = db.by_name.get(name) {
            return tactic::resolve_tac(&[(**thm).clone()], 0)(state);
        }
    }

    // `proof safe` → try auto
    if inner.contains("safe") {
        return Method::Auto.execute(state, premises, db);
    }

    // `proof method` (any other method name) → try to execute it
    if let Some(rest) = inner.strip_prefix("proof ") {
        let method = rest.trim();
        if !method.is_empty() && method != "-" {
            return exec_single_method(state, method, premises, db);
        }
    }

    // Last resort: try auto
    Method::Auto.execute(state, premises, db)
}

/// Execute intro:/elim:/dest: method with parameter extraction.
/// Syntax: `intro thm1 thm2 ...` or `intro: thm1 thm2 elim: thm3 ...`
/// Handles multiple modes (intro + elim + dest) by chaining them.
fn exec_intro_elim(
    method_str: &str,
    state: &Thm,
    _premises: &[Arc<Thm>],
    db: &HolTheoremDb,
) -> Vec<Thm> {
    // Extract intro rules
    let intro_str = if let Some(rest) = method_str.strip_prefix("intro:") {
        // Find where the intro section ends (next mode keyword)
        let end = rest.find(" elim:").or_else(|| rest.find(" dest:")).unwrap_or(rest.len());
        Some(&rest[..end])
    } else {
        method_str.strip_prefix("intro ")
    };

    // Extract elim rules
    let elim_str = if let Some(idx) = method_str.find("elim:") {
        let rest = &method_str[idx + 5..];
        let end = rest.find(" intro:").or_else(|| rest.find(" dest:")).unwrap_or(rest.len());
        Some(&rest[..end])
    } else {
        method_str.strip_prefix("elim ")
    };

    // Extract dest rules
    let dest_str = if let Some(idx) = method_str.find("dest:") {
        let rest = &method_str[idx + 5..];
        let end = rest.find(" intro:").or_else(|| rest.find(" elim:")).unwrap_or(rest.len());
        Some(&rest[..end])
    } else {
        method_str.strip_prefix("dest ")
    };

    if intro_str.is_none() && elim_str.is_none() && dest_str.is_none() {
        return vec![];
    }

    // Parse each section
    let parse_section = |s: &str| -> Vec<Arc<Thm>> {
        let thm_names = parse_thm_names(s.trim());
        thm_names
            .iter()
            .filter_map(|(name, of_args)| {
                db.by_name
                    .get(name.as_str())
                    .map(|thm| apply_of(Arc::clone(thm), of_args.clone(), db))
            })
            .collect()
    };

    let intro_thms: Vec<Arc<Thm>> = intro_str.map(parse_section).unwrap_or_default();
    let elim_thms: Vec<Arc<Thm>> = elim_str.map(parse_section).unwrap_or_default();
    let dest_thms: Vec<Arc<Thm>> = dest_str.map(parse_section).unwrap_or_default();

    // Chain: resolve with intros, then eresolve with elims, then dresolve with dests
    let mut current_states = vec![state.clone()];

    if !intro_thms.is_empty() {
        let mut next = Vec::new();
        for s in &current_states {
            next.extend(tactic::resolve_tac(
                &intro_thms.iter().map(|t| (**t).clone()).collect::<Vec<_>>(),
                0,
            )(s));
        }
        if !next.is_empty() {
            current_states = next;
        }
    }

    if !elim_thms.is_empty() {
        let mut next = Vec::new();
        for s in &current_states {
            next.extend(tactic::eresolve_tac(
                &elim_thms.iter().map(|t| (**t).clone()).collect::<Vec<_>>(),
                0,
            )(s));
        }
        if !next.is_empty() {
            current_states = next;
        }
    }

    if !dest_thms.is_empty() {
        let mut next = Vec::new();
        for s in &current_states {
            next.extend(tactic::dresolve_tac(
                &dest_thms.iter().map(|t| (**t).clone()).collect::<Vec<_>>(),
                0,
            )(s));
        }
        if !next.is_empty() {
            current_states = next;
        }
    }

    current_states
}

/// Basic arithmetic reasoning using built-in rewrite rules.
fn exec_arith(state: &Thm, premises: &[Arc<Thm>], db: &HolTheoremDb) -> Vec<Thm> {
    // Build arithmetic simp set: add_0, add_Suc, mult_0, mult_Suc, etc.
    let mut arith_rules: Vec<RewriteRule> = Vec::new();
    for name in &[
        "add_0_right",
        "add_Suc_right",
        "mult_0_right",
        "mult_Suc_right",
        "add_0",
        "add_Suc",
        "mult_0",
        "mult_Suc",
        "add_assoc",
        "add_commute",
        "mult_assoc",
        "mult_commute",
        "Suc_eq_add_numeral_1_left",
    ] {
        if let Some(thm) = db.by_name.get(*name)
            && let Some(rule) = RewriteRule::from_thm(Arc::clone(thm))
        {
            arith_rules.push(rule);
        }
    }
    if arith_rules.is_empty() {
        // Fallback: try auto
        return Method::Auto.execute(state, premises, db);
    }
    let simp = Simplifier::new(arith_rules);
    Method::Simp(simp).execute(state, premises, db)
}

fn exec_simp(method_str: &str, state: &Thm, premises: &[Arc<Thm>], db: &HolTheoremDb) -> Vec<Thm> {
    // Check soft deadline — avoid expensive rewrite on expired budget
    let expired = VERIFY_DEADLINE.with(|c| c.get().is_some_and(|d| std::time::Instant::now() >= d));
    if expired {
        return vec![];
    }
    let rest = if method_str == "simp" { "" } else { &method_str[4..] };
    let rest = rest.trim();

    // Parse modifiers using the centralized Args parser (Phase 51)
    let parsed = Args::parse_modifiers(rest);
    let use_db = !parsed.only_mode && parsed.add_names.is_empty() && parsed.del_names.is_empty();
    let effective_use_db = use_db || (!parsed.only_mode && rest.is_empty());

    let mut rules: Vec<RewriteRule> = Vec::new();

    // Build DB rules if not restricted
    if effective_use_db {
        for thm in &db.simps {
            if let Some(rule) = RewriteRule::from_thm(Arc::clone(thm)) {
                rules.push(rule);
            }
        }
        rules.extend(HolSimplifier::builtin_rules(db));
    }

    // Add named theorems — first try by_name (single theorem), then attrs_index (named_theorems collection)
    for name in &parsed.add_names {
        if let Some(thm) = db.by_name.get(name.as_str()) {
            if let Some(rule) = RewriteRule::from_thm(Arc::clone(thm)) {
                rules.push(rule);
            }
        } else if let Some(thms) = db.attrs_index.get(name.as_str()) {
            // Named_theorems collection — expand to all tagged theorems
            // e.g., "field_simps" → all theorems with [field_simps] attribute
            for thm in thms {
                if let Some(rule) = RewriteRule::from_thm(Arc::clone(thm)) {
                    rules.push(rule);
                }
            }
        }
    }

    // Remove `del:` theorems
    for name in &parsed.del_names {
        if let Some(del_thm) = db.by_name.get(name.as_str()) {
            rules.retain(|rule| !Arc::ptr_eq(&rule.thm, del_thm));
        }
    }

    let simp = Simplifier::new(rules);
    Method::Simp(simp).execute(state, premises, db)
}

/// Execute `simp_all` — apply simp to all subgoals repeatedly.
fn exec_simp_all(state: &Thm, _premises: &[Arc<Thm>], db: &HolTheoremDb) -> Vec<Thm> {
    let rules: Vec<RewriteRule> =
        db.simps.iter().filter_map(|t| RewriteRule::from_thm(Arc::clone(t))).collect();
    let simp = Simplifier::new(rules);
    let mut current = state.clone();
    for _ in 0..20 {
        let mut changed = false;
        for i in 0..current.nprems() {
            if let Some(goal) = current.prem(i)
                && let Some((simplified, eq)) = simp.rewrite_deep(&goal)
                && simplified != goal
                && let Some(ns) = ThmKernel::subst_premise(&eq, &current, i)
            {
                current = ns;
                changed = true;
                break;
            }
        }
        if !changed {
            break;
        }
    }
    if current.nprems() == 0 { vec![current] } else { vec![state.clone()] }
}

/// Parse a list of theorem names with optional [OF ...] suffixes.
/// Returns Vec<(name, of_args)>.
fn parse_thm_names(args_str: &str) -> Vec<(String, Vec<String>)> {
    let mut results = Vec::new();
    let mut current = String::new();
    let mut depth = 0usize;
    for ch in args_str.chars() {
        match ch {
            '[' => {
                depth += 1;
                current.push(ch);
            },
            ']' => {
                depth -= 1;
                current.push(ch);
            },
            ' ' if depth == 0 => {
                if !current.is_empty() {
                    let (name, of_args) = parse_of_suffix(&current);
                    results.push((name.to_string(), of_args));
                    current.clear();
                }
            },
            _ => current.push(ch),
        }
    }
    if !current.is_empty() {
        let (name, of_args) = parse_of_suffix(&current);
        results.push((name.to_string(), of_args));
    }
    results
}

/// Split comma-separated sub-methods at depth 0.
fn split_comma_methods(inner: &str) -> Vec<String> {
    let mut methods = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    for (i, ch) in inner.char_indices() {
        if ch == '(' || ch == '[' {
            depth += 1;
        } else if ch == ')' || ch == ']' {
            depth = depth.saturating_sub(1);
        } else if depth == 0 && ch == ',' && i > start {
            let m = inner[start..i].trim().to_string();
            if !m.is_empty() {
                methods.push(m);
            }
            start = i + 1;
        }
    }
    let last = inner[start..].trim().to_string();
    if !last.is_empty() {
        methods.push(last);
    }
    methods
}

/// Split "(erule subst) (rule refl)" into ["(erule subst)", "(rule refl)"]
fn split_chained_methods(rest: &str) -> Vec<String> {
    let mut methods = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    let chars: Vec<char> = rest.chars().collect();
    for (i, &ch) in chars.iter().enumerate() {
        if ch == '(' {
            depth += 1;
        } else if ch == ')' {
            depth = depth.saturating_sub(1);
        } else if depth == 0 && ch == ' ' && i > start {
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

/// Split "(rule refl)" or "(drule name)" into the name part.
fn parse_of_suffix(rest: &str) -> (&str, Vec<String>) {
    // Check for [OF ...] suffix
    if let Some(idx) = rest.find(" [OF ") {
        let name = rest[..idx].trim();
        let of_part = &rest[idx + 5..]; // after " [OF "
        // Remove trailing ]
        let of_part = of_part.trim_end_matches(']').trim();
        let args: Vec<String> = of_part.split_whitespace().map(|s| s.to_string()).collect();
        (name, args)
    } else {
        (rest.trim(), Vec::new())
    }
}

/// Apply OF combinator: resolve theorem premises with other theorems.
/// thm OF [thm1, thm2, ...] — for each premise, either:
/// Apply a chain of Isabelle attributes to a theorem.
/// Supports: [symmetric], [simplified], [folded def], [unfolded def],
///           [rule_format], plus OF/THEN handled separately via apply_of/apply_then.
fn apply_attributes(mut thm: Arc<Thm>, attrs: &[String], db: &HolTheoremDb) -> Arc<Thm> {
    fn admit_attribute_transformation(term: Term) -> Arc<Thm> {
        Arc::new(ThmKernel::admit(CTerm::certify(term), "admitted:attribute_transformation"))
    }

    for attr in attrs {
        let a = attr.trim();
        match a {
            "symmetric" | "sym" => {
                if let Ok(sym_thm) = ThmKernel::symmetric(&thm) {
                    thm = Arc::new(sym_thm);
                }
            },
            "simplified" => {
                let rules: Vec<RewriteRule> =
                    db.simps.iter().filter_map(|t| RewriteRule::from_thm(Arc::clone(t))).collect();
                if !rules.is_empty() {
                    let simp = Simplifier::new(rules);
                    if let Some((simplified, _eq)) = simp.rewrite_deep(thm.prop().term()) {
                        thm = admit_attribute_transformation(simplified);
                    }
                }
            },
            a if a.starts_with("folded ") => {
                let def_name = a.strip_prefix("folded ").unwrap_or("");
                if let Some(def_thm) = resolve_theorem_name(def_name, db)
                    && let Some(rule) = RewriteRule::from_thm(def_thm)
                {
                    let simp = Simplifier::new(vec![rule]);
                    if let Some((folded, _eq)) = simp.rewrite_deep(thm.prop().term()) {
                        thm = admit_attribute_transformation(folded);
                    }
                }
            },
            a if a.starts_with("unfolded ") || a.starts_with("unfold ") => {
                let def_name =
                    a.strip_prefix("unfolded ").or_else(|| a.strip_prefix("unfold ")).unwrap_or("");
                if let Some(def_thm) = resolve_theorem_name(def_name, db)
                    && let Some(mut rule) = RewriteRule::from_thm(def_thm)
                {
                    std::mem::swap(&mut rule.lhs, &mut rule.rhs);
                    let simp = Simplifier::new(vec![rule]);
                    if let Some((unfolded, _eq)) = simp.rewrite_deep(thm.prop().term()) {
                        thm = admit_attribute_transformation(unfolded);
                    }
                }
            },
            "rule_format" => {
                let term = thm.prop().term().clone();
                let (prems, concl) = Pure::strip_imp_prems(&term);
                if !prems.is_empty() {
                    let mut result = concl.clone();
                    for p in prems.iter().rev() {
                        result = Pure::mk_implies((*p).clone(), result.clone());
                    }
                    thm = admit_attribute_transformation(result);
                }
            },
            _ => {}, // Unknown or OF/THEN — handled separately
        }
    }
    thm
}

/// - "_": consume premise (resolve with itself via assume_tac)
/// - named: resolve with the named theorem
fn apply_of(mut thm: Arc<Thm>, args: Vec<String>, db: &HolTheoremDb) -> Arc<Thm> {
    for arg in &args {
        if thm.nprems() == 0 {
            break;
        }
        if arg == "_" {
            // Consume first premise by assuming it
            if let Some(prem) = thm.prem(0) {
                let assume_thm = ThmKernel::assume_compat(CTerm::certify(prem));
                if let Some(new_thm) = ThmKernel::bicompose(false, &assume_thm, &thm, 0) {
                    thm = Arc::new(new_thm);
                }
            }
        } else if let Some(arg_thm) = db.by_name.get(arg.as_str())
            && let Some(new_thm) = ThmKernel::bicompose(true, arg_thm, &thm, 0)
        {
            thm = Arc::new(new_thm);
        }
    }
    thm
}

/// Apply THEN combinator: thm [THEN thm2] — compose via bicompose.
fn apply_then(mut thm: Arc<Thm>, args: Vec<String>, db: &HolTheoremDb) -> Arc<Thm> {
    for arg in &args {
        if let Some(arg_thm) = db.by_name.get(arg.as_str())
            && let Some(new_thm) = ThmKernel::bicompose(true, arg_thm, &thm, 0)
        {
            thm = Arc::new(new_thm);
        }
    }
    thm
}

/// Resolve a theorem name with flexible dot/underscore/qualifier matching.
fn resolve_theorem_name(name: &str, db: &HolTheoremDb) -> Option<Arc<Thm>> {
    // Resolve exclusively through the caller's explicit database context.
    if let Some(thm) = db.by_name.get(name) {
        return Some(Arc::clone(thm));
    }
    let dot = name.replace('_', ".");
    if dot != name
        && let Some(thm) = db.by_name.get(&dot)
    {
        return Some(Arc::clone(thm));
    }
    let uscore = name.replace('.', "_");
    if uscore != name
        && let Some(thm) = db.by_name.get(&uscore)
    {
        return Some(Arc::clone(thm));
    }
    if name.contains('.') {
        for k in 1..name.split('.').count() {
            let suffix: String = name.split('.').skip(k).collect::<Vec<_>>().join(".");
            if let Some(thm) = db.by_name.get(&suffix) {
                return Some(Arc::clone(thm));
            }
        }
    }
    if let Some(last) = name.rfind('.') {
        let base = &name[last + 1..];
        if let Some(thm) = db.by_name.get(base) {
            return Some(Arc::clone(thm));
        }
    }
    None
}

/// Parse `name [attr1, attr2, OF a b] [THEN c]` suffix.
/// Returns (name, other_attrs, of_args, then_args).
/// Example: `foo [symmetric, OF bar baz] [THEN qux]` →
///   name="foo", other_attrs=["symmetric"], of_args=["bar","baz"], then_args=["qux"]
fn parse_of_and_then_suffix(rest: &str) -> (&str, Vec<String>, Vec<String>, Vec<String>) {
    let rest = rest.trim();
    // Extract base theorem name (everything before first '[')
    let bracket_start = rest.find('[');
    let name = if let Some(pos) = bracket_start { rest[..pos].trim() } else { rest };
    let bracket_part = if let Some(pos) = bracket_start { &rest[pos..] } else { "" };
    // If no brackets, just return the name
    if bracket_part.is_empty() {
        return (name, Vec::new(), Vec::new(), Vec::new());
    }

    // Parse all bracket groups for OF, THEN, and other attributes
    let mut then_args = Vec::new();
    let mut of_args = Vec::new();
    let mut other_attrs = Vec::new();
    let mut remaining = bracket_part;

    while let Some(bracket_start) = remaining.find('[') {
        let inner_start = bracket_start + 1;
        let bracket_end =
            remaining[inner_start..].find(']').map(|p| inner_start + p).unwrap_or(remaining.len());
        let inner = &remaining[inner_start..bracket_end].trim();
        remaining = &remaining[bracket_end + 1..];

        // Classify inner content
        if let Some(after) = inner.strip_prefix("THEN ") {
            then_args.extend(after.split_whitespace().map(|s| s.to_string()));
        } else if let Some(after) = inner.strip_prefix("OF ") {
            of_args.extend(after.split_whitespace().map(|s| s.to_string()));
        } else {
            // Other attributes: split by comma
            for part in inner.split(',') {
                let part = part.trim();
                if !part.is_empty() {
                    other_attrs.push(part.to_string());
                }
            }
        }
    }

    (name, other_attrs, of_args, then_args)
}

/// Check if a term contains schematic variables (Var).
fn has_schematic_vars(term: &Term) -> bool {
    match term {
        Term::Var { .. } => true,
        Term::App { func, arg } => has_schematic_vars(func) || has_schematic_vars(arg),
        Term::Abs { body, .. } => has_schematic_vars(body),
        _ => false,
    }
}

/// Accept a lemma's statement *without proof*, as an admitted (oracle-backed)
/// theorem.
///
/// This is the verifier's last-resort fallback: when no proof path closes the
/// goal, we generalize its free variables to schematic ones and `admit` the
/// result. The returned theorem is **not** `is_fully_proved()` — it carries
/// an `"admitted:proof_engine_failed"` oracle, so it is honestly distinguishable
/// from a genuine proof at the type level, and that taint propagates into
/// anything derived from it.
fn generalize_thm(thm: &Thm) -> Thm {
    let mut frees: Vec<String> = Vec::new();
    fn collect(term: &Term, out: &mut Vec<String>) {
        match term {
            Term::Free { name, .. } => {
                out.push(name.to_string());
            },
            Term::App { func, arg } => {
                collect(func, out);
                collect(arg, out);
            },
            Term::Abs { body, .. } => {
                collect(body, out);
            },
            _ => {},
        }
    }
    collect(thm.prop().term(), &mut frees);
    let mut seen = std::collections::HashSet::new();
    frees.retain(|n| seen.insert(n.clone()));
    if frees.is_empty() {
        // No free vars to generalize, but still unproved — admit the prop.
        return ThmKernel::admit(
            CTerm::certify(thm.prop().term().clone()),
            "admitted:proof_engine_failed",
        );
    }
    let mut m: std::collections::HashMap<String, Term> = std::collections::HashMap::new();
    for (i, name) in frees.iter().enumerate() {
        m.insert(name.clone(), Term::var(name.as_str(), i, Typ::dummy()));
    }
    fn apply(term: &Term, s: &std::collections::HashMap<String, Term>) -> Term {
        match term {
            Term::Free { name, .. } => {
                s.get(name.as_ref()).cloned().unwrap_or_else(|| term.clone())
            },
            Term::App { func, arg } => Term::app(apply(func, s), apply(arg, s)),
            Term::Abs { name, typ, body } => Term::abs(name.clone(), typ.clone(), apply(body, s)),
            _ => term.clone(),
        }
    }
    ThmKernel::admit(CTerm::certify(apply(thm.prop().term(), &m)), "admitted:proof_engine_failed")
}

/// Set the proof attempt limit (used by auto/fast/best/etc.).
/// Lower values reduce proof search time but may miss valid proofs.
pub fn set_auto_limit(limit: usize) {
    AUTO_LIMIT.with(|c| c.set(limit));
}

/// Set a soft deadline for verification. When exceeded, `verify_file`
/// returns partial results instead of processing all lemmas.
pub fn set_verify_deadline(deadline: std::time::Instant) {
    VERIFY_DEADLINE.with(|c| c.set(Some(deadline)));
}

/// Clear the verification deadline.
pub fn clear_verify_deadline() {
    VERIFY_DEADLINE.with(|c| c.set(None));
}

/// Set the proof search budget — maximum number of recursive auto_exec entries allowed.
/// When exhausted, auto_exec returns immediately without expanding more branches.
/// Use higher values (200-500) for complex files, lower (50-100) for fast scans.
pub fn set_search_budget(budget: usize) {
    PROOF_SEARCH_BUDGET.with(|c| c.set(budget));
}

/// Cached after first call — returns Arc'd rules that can be shared across verify_file calls.
/// Cached core simpset + attrs_index from foundational theories.
struct CoreSimpset {
    simps: Vec<Arc<Thm>>,
    attrs_index: std::collections::HashMap<String, Vec<Arc<Thm>>>,
}

fn load_core_simpset() -> &'static CoreSimpset {
    use std::sync::OnceLock;
    static CACHE: OnceLock<CoreSimpset> = OnceLock::new();
    CACHE.get_or_init(|| {
        let mut simps = Vec::new();
        let mut attrs_index = std::collections::HashMap::new();
        // Core theories in dependency order (imports-first)
        // Groups + Rings added to supply algebra_simps/ac_simps named_theorems
        let core_thys: &[&str] = &[
            include_str!("../../theories/HOL/HOL.thy"),
            include_str!("../../theories/HOL/Orderings.thy"),
            include_str!("../../theories/HOL/Set.thy"),
            include_str!("../../theories/HOL/Nat.thy"),
            include_str!("../../theories/HOL/Fun.thy"),
            include_str!("../../theories/HOL/Lattices.thy"),
            include_str!("../../theories/HOL/Groups.thy"),
            include_str!("../../theories/HOL/Rings.thy"),
        ];
        for source in core_thys {
            let lemmas = crate::hol::hol_loader::parse_lemmas(source);
            for lem in &lemmas {
                let thm = Arc::clone(&lem.theorem);
                // Collect [simp] rules for the simpset
                if lem.attributes.iter().any(|a| a == "simp") {
                    simps.push(Arc::clone(&thm));
                }
                // Build attrs_index for named_theorems expansion
                for attr in &lem.attributes {
                    attrs_index.entry(attr.clone()).or_insert_with(Vec::new).push(Arc::clone(&thm));
                }
            }
        }
        CoreSimpset { simps, attrs_index }
    })
}

/// Verify one .thy file using a local theorem database.
/// Returns `(transitional_strict_closed_count, attempted_count)`.
pub fn verify_file(source: &str) -> (usize, usize) {
    let lemmas = crate::hol::hol_loader::parse_lemmas(source);
    let mut local_db = HolTheoremDb::from_lemmas(&lemmas);
    let _ = enrich_local_db_with_checked_sources(&mut local_db, source);
    HolTheoremDb::add_builtins(&mut local_db);
    // Inject core simpset + attrs_index from parent theories
    // (HOL, Orderings, Set, Nat, Fun, Lattices, Groups, Rings — OnceLock cached)
    let core = load_core_simpset();
    for thm in &core.simps {
        local_db.simps.push(Arc::clone(thm));
    }
    // Merge core attrs_index into local DB for named_theorems expansion
    // (e.g., algebra_simps, ac_simps, field_simps from Groups/Rings)
    for (attr, thms) in &core.attrs_index {
        local_db.attrs_index.entry(attr.clone()).or_default().extend(thms.iter().map(Arc::clone));
    }
    // Only override AUTO_LIMIT if the test hasn't set it to a tighter value
    AUTO_LIMIT.with(|c| {
        let current = c.get();
        if current >= 100 {
            // default is 100 — override with per-file heuristic
            let auto_max = if lemmas.len() > 500 {
                50
            } else if lemmas.len() > 200 {
                80
            } else {
                200
            };
            c.set(auto_max);
        }
        // else: test caller already set a tighter limit, respect it
    });
    // Reset per-file search budget (controls memory via branch pruning)
    PROOF_SEARCH_BUDGET.with(|c| c.set(200));
    verify_lemmas_batch(&lemmas, &local_db)
}

/// Per-lemma verification diagnostic: same setup as `verify_file`, but returns
/// `(name, proof_script, is_proved)` for every attempted lemma instead of a
/// count. Used to analyze which admitted lemmas the prover cannot yet close.
///
/// `is_proved` means `TransitionalStrictClosed`: a legacy `core::Thm` with
/// strict metadata, closed burdens, no dummy types, and no accepted-axiom exit
/// tag. It is not a new-kernel `TrustedTheorem`; open `A |- A` results are not
/// counted.
pub fn verify_file_diagnostic(source: &str) -> Vec<(String, String, bool)> {
    let lemmas = crate::hol::hol_loader::parse_lemmas(source);
    let mut local_db = HolTheoremDb::from_lemmas(&lemmas);
    let _ = enrich_local_db_with_checked_sources(&mut local_db, source);
    HolTheoremDb::add_builtins(&mut local_db);
    let core = load_core_simpset();
    for thm in &core.simps {
        local_db.simps.push(Arc::clone(thm));
    }
    for (attr, thms) in &core.attrs_index {
        local_db.attrs_index.entry(attr.clone()).or_default().extend(thms.iter().map(Arc::clone));
    }
    AUTO_LIMIT.with(|c| {
        if c.get() >= 100 {
            let auto_max = if lemmas.len() > 500 {
                50
            } else if lemmas.len() > 200 {
                80
            } else {
                200
            };
            c.set(auto_max);
        }
    });
    PROOF_SEARCH_BUDGET.with(|c| c.set(200));

    let mut out = Vec::new();
    for lem in &lemmas {
        if lem.proof_script.is_none() {
            continue;
        }
        let script = lem.proof_script.clone().unwrap_or_default();
        let result = verify_lemma(lem, &local_db);
        let outcome = classify_verify_result(&lem.name, &result);
        let proved = outcome.is_transitional_strict_closed();
        out.push((lem.name.clone(), script, proved));
    }
    out
}

/// Verify lemmas using the caller's explicit immutable theorem database.
///
/// The returned verified count is the transitional legacy metric. New-kernel
/// trusted acceptance remains zero until this path returns context-bound
/// `crate::kernel::TrustedTheorem` values.
/// Checks `VERIFY_DEADLINE` before each lemma — returns partial results if exceeded.
pub fn verify_lemmas_batch(lemmas: &[ParsedLemma], db: &HolTheoremDb) -> (usize, usize) {
    let mut verified = 0usize;
    let mut attempted = 0usize;
    for lem in lemmas {
        // Check soft deadline before each lemma
        let expired =
            VERIFY_DEADLINE.with(|c| c.get().is_some_and(|d| std::time::Instant::now() >= d));
        if expired {
            break;
        }
        if lem.proof_script.is_some() {
            attempted += 1;
            let result = verify_lemma(lem, db);
            let outcome = classify_verify_result(&lem.name, &result);
            let proved = outcome.is_transitional_strict_closed();
            if proved {
                verified += 1;
            }
            record_verify_outcome(&outcome);
            VERIFY_STATS.with(|c| {
                let (p, a) = c.get();
                if proved { c.set((p + 1, a)) } else { c.set((p, a + 1)) }
            });
        }
    }
    (verified, attempted)
}

fn enrich_local_db_with_checked_sources(
    db: &mut HolTheoremDb,
    source: &str,
) -> Result<(), KernelError> {
    db.set_verification_source(source);
    let source_env = HolTheoremDb::build_type_env(source);
    db.merge_checked_source_type_env(source_env)?;
    db.extend_checked_definitions_from_source(source);
    Ok(())
}

fn check_true_i_legacy_payload(
    parsed_prop: &CTerm,
    db: &HolTheoremDb,
) -> Result<(), StrictAdapterReject> {
    parsed_prop
        .require_no_dummy_types("check_true_i_legacy_payload")
        .map_err(|err| StrictAdapterReject::CertificationFailed(Arc::new(err)))?;
    match parsed_prop.term() {
        Term::Const { name, typ }
            if matches!(name.as_ref(), "HOL.True" | "True") && typ == &Typ::base("bool") =>
        {
            normalize_checked_hol_true_prop(parsed_prop, &db.type_env)
                .map(|_| ())
                .map_err(|err| StrictAdapterReject::CertificationFailed(Arc::new(err)))
        },
        _ => Err(StrictAdapterReject::PropositionMismatch),
    }
}

/// User-fixable source/payload rejections; nested failures retain their cause.
#[derive(Clone, Debug, thiserror::Error)]
pub enum StrictAdapterReject {
    #[error("complete standalone source proposition required ({status:?}, {shape:?})")]
    SourcePropositionUnverified { status: SourcePropositionStatus, shape: SourcePropositionShape },
    #[error("sampled lemma proposition differs from the accepted source proposition")]
    PropositionMismatch,
    #[error("sampled lemma proof differs from the supported source proof")]
    ProofShapeMismatch,
    #[error("complete theory source is unavailable for sampled TrueI verification")]
    MissingSource,
    /// The candidate does not belong to the complete source bound to this DB.
    #[error("sampled lemma declaration does not match the bound complete theory source")]
    SourceBindingMismatch,
    #[error("sampled legacy payload certification failed: {0}")]
    CertificationFailed(#[source] Arc<KernelError>),
    #[error("sampled source projection failed: {0}")]
    SourceCompilationFailed(#[source] Arc<crate::hol::sampled_true_i::SampledTrueIError>),
    #[error("sampled proposition elaboration failed: {0}")]
    ElaborationFailed(#[source] Arc<crate::isar::elaborator::ElaborationError>),
}

#[derive(Clone, Debug)]
pub enum StrictAdapterResult {
    NotApplicable,
    Proved(Box<(TrustedTheory, TrustedTheorem)>),
    Rejected(StrictAdapterReject),
}

fn strict_adapter_reject_admit_reason(reject: &StrictAdapterReject) -> &'static str {
    match reject {
        StrictAdapterReject::SourcePropositionUnverified { .. } => {
            "admitted:strict_adapter_source_prop_unverified"
        },
        StrictAdapterReject::PropositionMismatch => "admitted:strict_adapter_prop_mismatch",
        StrictAdapterReject::ProofShapeMismatch => "admitted:strict_adapter_proof_shape_mismatch",
        StrictAdapterReject::MissingSource => "admitted:strict_adapter_missing_source",
        StrictAdapterReject::SourceBindingMismatch => {
            "admitted:strict_adapter_source_binding_mismatch"
        },
        StrictAdapterReject::CertificationFailed(_) => {
            "admitted:strict_adapter_certification_failed"
        },
        StrictAdapterReject::SourceCompilationFailed(_) => "admitted:strict_adapter_source_failed",
        StrictAdapterReject::ElaborationFailed(_) => "admitted:strict_adapter_elaboration_failed",
    }
}

fn compile_true_i_for_lemma(
    lem: &ParsedLemma,
    proof: &str,
    db: &HolTheoremDb,
) -> Result<(TrustedTheory, TrustedTheorem), StrictAdapterReject> {
    let status = lem.source_proposition_status();
    let shape = lem.source_proposition_shape();
    if status != SourcePropositionStatus::FullyConsumed
        || shape != SourcePropositionShape::StandaloneHolTrueAlias
    {
        return Err(StrictAdapterReject::SourcePropositionUnverified { status, shape });
    }
    if !proof.split_whitespace().eq(["unfolding", "True_def", "by", "(rule", "refl)"]) {
        return Err(StrictAdapterReject::ProofShapeMismatch);
    }
    if !db.matches_verification_source(lem) {
        return Err(StrictAdapterReject::SourceBindingMismatch);
    }
    // Legacy payload/metadata can only reject; the complete source creates authority.
    check_true_i_legacy_payload(lem.theorem.prop(), db)?;
    let (owner, theorem, command_offset) = db
        .compile_source_true_i()
        .ok_or(StrictAdapterReject::MissingSource)?
        .map_err(StrictAdapterReject::SourceCompilationFailed)?;
    if !db.matches_audited_source_command(lem, command_offset) {
        return Err(StrictAdapterReject::SourceBindingMismatch);
    }
    let context = crate::kernel::ProofContext::new(owner.snapshot().clone());
    let proposition = try_source_elaboration(lem, &context)
        .map_err(|err| StrictAdapterReject::ElaborationFailed(Arc::new(err)))?;
    if !proposition.term().alpha_eq(theorem.prop().term()) {
        return Err(StrictAdapterReject::PropositionMismatch);
    }
    Ok((owner, theorem))
}

pub fn try_strict_adapter(lem: &ParsedLemma, db: &HolTheoremDb) -> StrictAdapterResult {
    let Some(proof) = lem.proof_script.as_deref().filter(|proof| !proof.trim().is_empty()) else {
        return StrictAdapterResult::NotApplicable;
    };
    if !matches!(lem.name.as_str(), "TrueI" | "HOL::TrueI") {
        return StrictAdapterResult::NotApplicable;
    }
    match compile_true_i_for_lemma(lem, proof, db) {
        Ok(accepted) => StrictAdapterResult::Proved(Box::new(accepted)),
        Err(error) => StrictAdapterResult::Rejected(error),
    }
}

/// Verify the source-backed sampled slice first; never convert its token to legacy evidence.
pub fn verify_lemma(lem: &ParsedLemma, db: &HolTheoremDb) -> LemmaVerification {
    match try_strict_adapter(lem, db) {
        StrictAdapterResult::Proved(accepted) => {
            let (owner, theorem) = *accepted;
            return LemmaVerification::from_accepted(owner, theorem);
        },
        StrictAdapterResult::Rejected(reason) => {
            tracing::debug!(lemma = %lem.name, error = %reason, "sampled source verification rejected");
            return LemmaVerification::from_legacy(
                Some(ThmKernel::admit(
                    CTerm::certify(lem.theorem.prop().term().clone()),
                    strict_adapter_reject_admit_reason(&reason),
                )),
                VerifyOutcome::AxiomAccepted,
            );
        },
        StrictAdapterResult::NotApplicable => {},
    }
    verify_legacy_lemma(lem, db)
}

// The legacy strategy dispatcher predates this cutover; keep its search order unchanged.
fn verify_legacy_lemma(lem: &ParsedLemma, db: &HolTheoremDb) -> LemmaVerification {
    AUTO_DEPTH.with(|c| c.set(0));
    let mut exit = VerifyOutcome::Proved;
    let theorem = (|| -> Option<Thm> {
        // ── Source-aware elaboration (Phase 4) ─────────────────────────
        let proof_ctx = build_kernel_proof_context(db);
        let elaborated = try_source_elaboration(lem, &proof_ctx);
        let goal_ct = if let Ok(ref cprop) = elaborated {
            let core_term = crate::core::kernel_convert::kernel_term_to_core(cprop.term())
                .unwrap_or_else(|_| lem.theorem.prop().term().clone());
            CTerm::certify_checked(core_term, &db.type_env)
                .unwrap_or_else(|_| CTerm::certify(lem.theorem.prop().term().clone()))
        } else {
            CTerm::certify(lem.theorem.prop().term().clone())
        };

        // If a built-in Var-override exists, use it directly (skip proof replay).
        // This covers lemmas whose proofs use complex patterns (multi-method chains,
        // [THEN] composition, named iprover premises) that aren't fully supported yet.
        if let Some(builtin) = db.by_name.get(&lem.name) {
            let builtin_term = builtin.prop().term();
            let has_vars = has_schematic_vars(builtin_term);
            let parsed_term = lem.theorem.prop().term();
            let parsed_has_no_vars = !has_schematic_vars(parsed_term);
            // Accept if built-in has Var and parsed version uses Free (intentional override)
            if has_vars && parsed_has_no_vars {
                exit = VerifyOutcome::AxiomAccepted;
                return Some(ThmKernel::admit(
                    CTerm::certify(builtin_term.clone()),
                    "admitted:parser_gap",
                ));
            }
        }

        // Trust mode: if proof_script is missing or empty, use the built-in DB.
        if lem.proof_script.is_none()
            || lem.proof_script.as_deref().is_some_and(|s| s.trim().is_empty())
        {
            exit = VerifyOutcome::AxiomAccepted;
            if let Some(builtin) = db.by_name.get(&lem.name) {
                return Some(builtin.as_ref().clone());
            }
            return Some(ThmKernel::admit(
                CTerm::certify(lem.theorem.prop().term().clone()),
                "admitted:unsupported_method",
            ));
        }

        let proof = lem.proof_script.as_ref()?;
        if proof_allows_strict_imp_identity(proof)
            && let Some(strict_identity) =
                try_strict_pure_imp_identity(lem.theorem.prop().term(), &db.type_env)
        {
            return Some(strict_identity);
        }

        let (prems, concl) = Pure::strip_imp_prems(goal_ct.term());
        let premise_cterms: Vec<CTerm> =
            prems.iter().map(|p| CTerm::certify((*p).clone())).collect();
        let premises: Vec<Arc<Thm>> =
            premise_cterms.iter().map(|p| Arc::new(ThmKernel::assume_compat(p.clone()))).collect();
        let goal = match init_verify_goal(&goal_ct) {
            Ok(goal) => goal,
            Err(admitted) => {
                exit = VerifyOutcome::AxiomAccepted;
                return Some(*admitted);
            },
        };

        // Fast path: single-method proofs that are trivially dispatchable
        if (proof == "by simp"
            || proof == "by auto"
            || proof == "by blast"
            || proof == "by fast"
            || proof == "by iprover"
            || proof == "by force")
            && let Some(results) = exec_proof(&goal, proof, &premises, db)
        {
            return Some(export_or_admit_goal(&goal_ct, results, &premise_cterms, &mut exit));
        }

        // Special handling for anonymous/auto-named datatype lemmas
        let is_anon = lem.name.is_empty() || lem.name.starts_with("[anon:");
        if is_anon {
            let proof_trimmed = proof.trim();
            if proof_trimmed.contains("rule list.induct")
                || proof_trimmed.contains("rule list.exhaust")
                || proof_trimmed.contains("rule list.case")
            {
                exit = VerifyOutcome::AxiomAccepted;
                return Some(ThmKernel::admit(
                    CTerm::certify(lem.theorem.prop().term().clone()),
                    "admitted:datatype_stub",
                ));
            }
        }

        // Try structured Isar proof first
        if proof.contains("\n")
            && (proof.contains("have ")
                || proof.contains("show ")
                || proof.contains("case ")
                || proof.contains("fix ")
                || proof.contains("assume "))
        {
            let mut state = crate::isar::proof_state::ProofState::new(goal.clone());
            if let Ok(result) =
                crate::isar::proof_state::interpret_proof_script(&mut state, proof, &premises, db)
            {
                return Some(export_or_admit_goal(&goal_ct, result, &premise_cterms, &mut exit));
            }
        }

        // Simple "by (rule X)" pattern — look up and resolve
        if proof.starts_with("by (rule ") || proof.starts_with("by(rule ") {
            let rule_name = proof
                .strip_prefix("by (rule ")
                .or_else(|| proof.strip_prefix("by(rule "))
                .map(|r| r.trim_end_matches(')').trim());
            if let Some(rule_name) = rule_name
                && let Some(rule_thm) = resolve_theorem_name(rule_name, db)
            {
                let resolved = crate::core::tactic::resolve_tac(&[(*rule_thm).clone()], 0)(&goal);
                if let Some(thm) = resolved.into_iter().next() {
                    // Resolution may leave open subgoals; only a closed goal is a real proof.
                    if thm.nprems() != 0 {
                        exit = VerifyOutcome::AxiomAccepted;
                    }
                    return Some(export_or_admit_goal(&goal_ct, thm, &premise_cterms, &mut exit));
                }
            }
        }

        // "unfolding X by method" — apply unfolding then method
        if proof.contains("unfolding ") {
            // Split: "unfolding X1 X2 by method"
            if let Some(rest) = proof.strip_prefix("unfolding ")
                && let Some(by_pos) = rest.find(" by ")
            {
                let unfold_names = &rest[..by_pos];
                let method = rest[by_pos + 4..].trim();
                // Look up the unfolding definitions
                let mut current = goal.clone();
                for name in unfold_names.split_whitespace() {
                    if let Some(thm) = resolve_theorem_name(name, db) {
                        current = ThmKernel::bicompose(false, &(*thm).clone(), &current, 0)
                            .unwrap_or(current);
                    }
                }
                // Apply the remaining method
                if let Some(results) = exec_proof(&current, method, &premises, db) {
                    return Some(export_or_admit_goal(
                        &goal_ct,
                        results,
                        &premise_cterms,
                        &mut exit,
                    ));
                }
            }
        }

        // "by (simp add: X1 X2)" — simplification with specific rules
        if proof.starts_with("by (simp add:") || proof.starts_with("by(simp add:") {
            let add_rules = proof
                .strip_prefix("by (simp add:")
                .or_else(|| proof.strip_prefix("by(simp add:"))
                .map(|r| r.trim_end_matches(')').trim());
            if let Some(rules_str) = add_rules {
                let mut current = goal.clone();
                let rule_names: Vec<&str> = rules_str.split_whitespace().collect();
                // Apply each simp rule via bicompose
                for name in &rule_names {
                    if let Some(thm) = resolve_theorem_name(name, db) {
                        // Apply as rewrite: use the theorem as an equality
                        if let Some(new_state) =
                            ThmKernel::bicompose(false, &(*thm).clone(), &current, 0)
                        {
                            current = new_state;
                        }
                    }
                }
                if current.nprems() < goal.nprems() || current != goal {
                    // Only a closed goal (no remaining subgoals) counts as a real proof;
                    // a merely-rewritten-but-open goal is a weak acceptance.
                    if current.nprems() != 0 {
                        exit = VerifyOutcome::AxiomAccepted;
                    }
                    return Some(export_or_admit_goal(
                        &goal_ct,
                        current,
                        &premise_cterms,
                        &mut exit,
                    ));
                }
            }
        }

        // "by (auto intro: X)" — auto with specific introduction rules
        if proof.starts_with("by (auto intro:") || proof.starts_with("by(auto intro:") {
            let intro_rule = proof
                .strip_prefix("by (auto intro:")
                .or_else(|| proof.strip_prefix("by(auto intro:"))
                .map(|r| r.trim_end_matches(')').trim());
            if let Some(rule_name) = intro_rule {
                // Try resolving with the specific intro rule first
                if let Some(rule_thm) = resolve_theorem_name(rule_name, db) {
                    let resolved =
                        crate::core::tactic::resolve_tac(&[(*rule_thm).clone()], 0)(&goal);
                    if let Some(thm) = resolved.into_iter().next() {
                        // Resolution may leave open subgoals; only a closed goal is a real proof.
                        if thm.nprems() != 0 {
                            exit = VerifyOutcome::AxiomAccepted;
                        }
                        return Some(export_or_admit_goal(
                            &goal_ct,
                            thm,
                            &premise_cterms,
                            &mut exit,
                        ));
                    }
                }
                // Fall back to auto
                if let Some(results) = exec_proof(&goal, "auto", &premises, db) {
                    return Some(export_or_admit_goal(
                        &goal_ct,
                        results,
                        &premise_cterms,
                        &mut exit,
                    ));
                }
            }
        }

        // For lemmas with premises, try Goal.init-style FIRST (bare conclusion)
        // This allows rules like subst/nat_induct to match the conclusion directly.
        if !prems.is_empty() {
            let alt_goal = ThmKernel::trivial(CTerm::certify(concl.clone())).unwrap();
            if let Some(r) = exec_proof(&alt_goal, proof, &premises, db) {
                let mut final_thm = r;
                for p in prems.iter().rev() {
                    let cterm = CTerm::certify((*p).clone());
                    if let Ok(thm) = ThmKernel::implies_intr(&cterm, &final_thm) {
                        final_thm = thm;
                    }
                }
                return Some(export_or_admit_goal(&goal_ct, final_thm, &premise_cterms, &mut exit));
            }
            // Direct resolution for "using assms by (rule X)"
            if proof.contains("using assms") {
                let rule_name = proof
                    .strip_prefix("using assms by (rule ")
                    .or_else(|| proof.strip_prefix("by (rule "))
                    .map(|r| r.trim_end_matches(')'));
                if let Some(rule_name) = rule_name
                    && let Some(rule_thm) = resolve_theorem_name(rule_name, db)
                {
                    let resolved =
                        crate::core::tactic::resolve_tac(&[(*rule_thm).clone()], 0)(&alt_goal);
                    if let Some(mut current) = resolved.into_iter().next() {
                        for _ in 0..20 {
                            if current.nprems() == 0 {
                                break;
                            }
                            let mut closed = false;
                            for prem in &premises {
                                if let Some(ns) = ThmKernel::bicompose(false, prem, &current, 0)
                                    && ns.nprems() < current.nprems()
                                {
                                    current = ns;
                                    closed = true;
                                    break;
                                }
                            }
                            if !closed {
                                break;
                            }
                        }
                        if current.nprems() == 0 {
                            let mut final_thm = current;
                            for p in prems.iter().rev() {
                                let cterm = CTerm::certify((*p).clone());
                                if let Ok(thm) = ThmKernel::implies_intr(&cterm, &final_thm) {
                                    final_thm = thm;
                                }
                            }
                            return Some(export_or_admit_goal(
                                &goal_ct,
                                final_thm,
                                &premise_cterms,
                                &mut exit,
                            ));
                        }
                    }
                }
            }
        }

        // Fall back to standard approach — wrapped in catch_unwind to survive panics
        let proof_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            exec_proof(&goal, proof, &premises, db)
        }));
        match proof_result {
            Ok(Some(result)) => {
                return Some(export_or_admit_goal(&goal_ct, result, &premise_cterms, &mut exit));
            },
            Ok(None) => {},
            Err(_panic) => {
                // Proof engine panicked on this lemma's proof script.
                // This is expected for complex Isar patterns not yet supported.
            },
        }
        // Last resort: generalize and accept as axiom
        exit = VerifyOutcome::AxiomAccepted;
        Some(generalize_thm(&lem.theorem))
    })();
    LemmaVerification::from_legacy(theorem, exit)
}

// =========================================================================
// Method combinator: THEN
// =========================================================================

/// Combine two methods in sequence: apply m1, then m2 to all results.
pub fn method_then(
    m1: &Method,
    m2: &Method,
    state: &Thm,
    premises: &[Arc<Thm>],
    db: &HolTheoremDb,
) -> Vec<Thm> {
    m1.execute(state, premises, db).into_iter().flat_map(|s| m2.execute(&s, premises, db)).collect()
}

// =========================================================================
// Method combinator: ORELSE
// =========================================================================

/// Try m1; if it yields nothing, try m2.
pub fn method_orelse(
    m1: &Method,
    m2: &Method,
    state: &Thm,
    premises: &[Arc<Thm>],
    db: &HolTheoremDb,
) -> Vec<Thm> {
    let r = m1.execute(state, premises, db);
    if r.is_empty() { m2.execute(state, premises, db) } else { r }
}

// =========================================================================
// Method parser (from string)
// =========================================================================

impl Method {
    /// Parse a method from its string name.
    pub fn from_name(name: &str, _facts: &[Arc<Thm>], db: &HolTheoremDb) -> Option<Self> {
        match name.trim() {
            "assumption" | "." => Some(Method::Assumption),
            "this" => Some(Method::Skip),
            "rule" | "intro" => Some(Method::Rule(vec![])),
            "simp" => {
                let rules: Vec<RewriteRule> = db
                    .simps
                    .iter()
                    .filter_map(|thm| RewriteRule::from_thm(Arc::clone(thm)))
                    .collect();
                Some(Method::Simp(Simplifier::new(rules)))
            },
            "auto" => Some(Method::Auto),
            "blast" => Some(Method::Blast),
            "fast" | "fastforce" | "force" => Some(Method::Fast),
            "best" => Some(Method::Best),
            "step" => Some(Method::Step),
            "safe" | "clarify" => Some(Method::Step),
            "coinduction" | "coinduct" => Some(Method::Coinduct),
            "try" | "try0" => Some(Method::Try),
            "fail" => Some(Method::Fail),
            "skip" => Some(Method::Skip),
            _ if name.starts_with("induct ") => {
                let var = name.strip_prefix("induct ")?.to_string();
                Some(Method::Induct(var))
            },
            _ if name.starts_with("cases ") => {
                let var = name.strip_prefix("cases ")?.to_string();
                Some(Method::Cases(var))
            },
            _ if name.starts_with("unfold ") => {
                let rest = name.strip_prefix("unfold ")?;
                let thms: Vec<Arc<Thm>> =
                    rest.split_whitespace().filter_map(|n| db.by_name.get(n).cloned()).collect();
                if thms.is_empty() { None } else { Some(Method::Unfold(thms)) }
            },
            _ if name.starts_with("fold ") => {
                let rest = name.strip_prefix("fold ")?;
                let thms: Vec<Arc<Thm>> =
                    rest.split_whitespace().filter_map(|n| db.by_name.get(n).cloned()).collect();
                if thms.is_empty() { None } else { Some(Method::Fold(thms)) }
            },
            _ if name.starts_with("insert ") => {
                let rest = name.strip_prefix("insert ")?;
                let thms: Vec<Arc<Thm>> =
                    rest.split_whitespace().filter_map(|n| db.by_name.get(n).cloned()).collect();
                if thms.is_empty() { None } else { Some(Method::Insert(thms)) }
            },
            _ if name.starts_with("erule ") => {
                let rest = name.strip_prefix("erule ")?;
                let thms: Vec<Arc<Thm>> =
                    rest.split_whitespace().filter_map(|n| db.by_name.get(n).cloned()).collect();
                if thms.is_empty() { None } else { Some(Method::Erule(thms)) }
            },
            _ if name.starts_with("drule ") => {
                let rest = name.strip_prefix("drule ")?;
                let thms: Vec<Arc<Thm>> =
                    rest.split_whitespace().filter_map(|n| db.by_name.get(n).cloned()).collect();
                if thms.is_empty() { None } else { Some(Method::Drule(thms)) }
            },
            _ if name.starts_with("frule ") => {
                let rest = name.strip_prefix("frule ")?;
                let thms: Vec<Arc<Thm>> =
                    rest.split_whitespace().filter_map(|n| db.by_name.get(n).cloned()).collect();
                if thms.is_empty() { None } else { Some(Method::Frule(thms)) }
            },
            _ if name.starts_with("depth ") => {
                let rest = name.strip_prefix("depth ")?;
                let bound: usize = rest.trim().parse().ok()?;
                Some(Method::Depth(bound))
            },
            _ => None,
        }
    }
}

// =========================================================================
// Tests
// =========================================================================

/// Build a new-kernel `ProofContext` from the legacy `HolTheoremDb`'s type environment.
fn build_kernel_proof_context(db: &HolTheoremDb) -> crate::kernel::ProofContext {
    let signature = db.kernel_signature_from_type_env();
    let snapshot = crate::kernel::TheorySnapshot::root("legacy", signature);
    crate::kernel::ProofContext::new(snapshot)
}
/// Try source-aware elaboration using the provided kernel proof context.
/// Returns the elaborated `CProp` on success, or an `ElaborationError` on failure.
fn try_source_elaboration(
    lem: &ParsedLemma,
    proof_ctx: &crate::kernel::ProofContext,
) -> Result<crate::kernel::CProp, crate::isar::elaborator::ElaborationError> {
    use crate::isar::elaborator::elaborate_proposition;
    use crate::isar::source_ast::SourceId;
    use crate::isar::source_parser::parse_source_proposition;

    let source_text = lem
        .source_proposition_text()
        .filter(|_| {
            lem.source_proposition_status() == SourcePropositionStatus::FullyConsumed
                && lem.source_proposition_shape() != SourcePropositionShape::Contextual
        })
        .ok_or_else(|| {
            crate::isar::elaborator::ElaborationError::ElaborationInternal(format!(
                "complete standalone source proposition unavailable for lemma {}",
                lem.name
            ))
        })?;
    let source_id = SourceId::new(lem.name.as_str());
    let source_prop = parse_source_proposition(source_text, source_id).ok_or_else(|| {
        crate::isar::elaborator::ElaborationError::ElaborationInternal(format!(
            "failed to parse source proposition for lemma {}",
            lem.name
        ))
    })?;

    elaborate_proposition(&source_prop, proof_ctx)
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        core::types::Typ,
        hol::hol_loader::{load_theory_files, scan_theory_files},
    };

    fn trivial_goal(name: &str) -> Thm {
        let ct = CTerm::certify(Term::const_(name, Typ::base("prop")));
        ThmKernel::trivial(ct).unwrap()
    }

    fn prop_ct(name: &str) -> CTerm {
        CTerm::certify(Term::const_(name, Typ::base("prop")))
    }

    fn verify_named_from(source: &str, name: &str) -> Thm {
        let lemmas = crate::hol::hol_loader::parse_lemmas(source);
        let mut db = HolTheoremDb::from_lemmas(&lemmas);
        enrich_local_db_with_checked_sources(&mut db, source).unwrap();
        HolTheoremDb::add_builtins(&mut db);
        let lem = lemmas.iter().find(|l| l.name == name).expect("lemma should parse");
        verify_lemma(lem, &db).into_legacy_theorem().expect("lemma should return a theorem")
    }

    fn certify_export_term(term: Term) -> CTerm {
        let mut context = crate::isar::proof_context::ProofCertContext::new();
        for name in ["A", "B", "C", "X"] {
            context.declare_const(name, Typ::base("prop"));
        }
        context.certify_prop(term).unwrap()
    }

    #[test]
    fn proof_closure_single_assumption_exports_strict_identity() {
        let a = certify_export_term(Term::const_("A", Typ::base("prop")));
        let expected = certify_export_term(Pure::mk_implies(a.term().clone(), a.term().clone()));
        let proof = ThmKernel::assume(a.clone()).unwrap();
        let result = export_proved_goal(&expected, &proof, &[a]).unwrap();
        assert!(result.is_strict_closed_proved());
        assert_eq!(result.prop().term(), expected.term());
    }

    #[test]
    fn proof_closure_two_assumptions_preserves_full_proposition() {
        let a = certify_export_term(Term::const_("A", Typ::base("prop")));
        let b = Term::const_("B", Typ::base("prop"));
        let implication = certify_export_term(Pure::mk_implies(a.term().clone(), b.clone()));
        let result = ThmKernel::implies_elim(
            &ThmKernel::assume(implication.clone()).unwrap(),
            &ThmKernel::assume(a.clone()).unwrap(),
        )
        .unwrap();
        let expected = certify_export_term(Pure::mk_implies(
            a.term().clone(),
            Pure::mk_implies(implication.term().clone(), b),
        ));
        let exported = export_proved_goal(&expected, &result, &[a, implication]).unwrap();
        assert!(exported.is_strict_closed_proved());
        assert_eq!(exported.prop().term(), expected.term());
    }

    #[test]
    fn proof_closure_unknown_hypothesis_is_rejected() {
        let a = certify_export_term(Term::const_("A", Typ::base("prop")));
        let result = ThmKernel::assume(a.clone()).unwrap();
        assert!(matches!(
            export_proved_goal(&a, &result, &[]),
            Err(GoalExportError::UnknownHypotheses)
        ));
    }

    #[test]
    fn proof_closure_admitted_result_is_rejected() {
        let a = certify_export_term(Term::const_("A", Typ::base("prop")));
        let result = ThmKernel::admit(a.clone(), "admitted:proof_engine_failed");
        assert!(matches!(
            export_proved_goal(&a, &result, &[]),
            Err(GoalExportError::OracleOrAdmitted)
        ));
    }

    #[test]
    fn proof_closure_wrong_complete_proposition_is_rejected() {
        let a = certify_export_term(Term::const_("A", Typ::base("prop")));
        let expected = certify_export_term(Term::const_("B", Typ::base("prop")));
        let result = ThmKernel::trivial(a).unwrap();
        assert!(matches!(
            export_proved_goal(&expected, &result, &[]),
            Err(GoalExportError::PropositionMismatch)
        ));
    }

    #[test]
    fn proof_closure_rejects_unresolved_tpairs() {
        let a = certify_export_term(Term::const_("A", Typ::base("prop")));
        let result = ThmKernel::trivial(a.clone()).unwrap().with_test_tpair(
            Term::var("x", 0, Typ::base("nat")),
            Term::var("y", 0, Typ::base("nat")),
        );

        let err = export_proved_goal(&a, &result, &[]).unwrap_err();

        assert!(matches!(err, GoalExportError::UnresolvedTpairs));
    }

    #[test]
    fn proof_closure_alpha_equivalent_proposition_discharges() {
        let prop = Typ::base("prop");
        let lambda_x = Term::abs("x", prop.clone(), Term::bound(0));
        let lambda_y = Term::abs("y", prop.clone(), Term::bound(0));
        let function_type = Typ::arrow(prop.clone(), prop);
        let hyp =
            certify_export_term(Pure::mk_equals(function_type.clone(), lambda_x.clone(), lambda_x));
        let alpha = certify_export_term(Pure::mk_equals(function_type, lambda_y.clone(), lambda_y));
        let expected =
            certify_export_term(Pure::mk_implies(alpha.term().clone(), hyp.term().clone()));
        let result = ThmKernel::assume(hyp).unwrap();
        let exported = export_proved_goal(&expected, &result, &[alpha]).unwrap();
        assert!(exported.is_strict_closed_proved());
        assert!(Hyps::kernel_alpha_eq(exported.prop().term(), expected.term()));
    }

    #[test]
    fn goal_initialization_does_not_return_self_hyp() {
        let a = prop_ct("A");

        let goal = init_verify_goal(&a).expect("trivial goal initialization should succeed");

        assert!(goal.hyps().is_empty(), "goal initialization must not create A |- A self-hyp");
        assert_eq!(goal.nprems(), 1);
    }

    #[test]
    fn verify_hol_trans_no_open_hyps() {
        let thm = verify_named_from(include_str!("../../theories/HOL/HOL.thy"), "trans");

        assert!(
            thm.hyps().is_empty(),
            "trans should not retain proof-state hyps: prop={:?}, hyps={:?}, trust={:?}",
            thm.prop().term(),
            thm.hyps().iter().map(|h| format!("{:?}", h.term())).collect::<Vec<_>>(),
            thm.trust_status()
        );
    }

    #[test]
    fn verify_nat_suc_not_zero_no_self_hyp() {
        let thm = verify_named_from(include_str!("../../theories/HOL/Nat.thy"), "Suc_not_Zero");

        assert!(
            thm.hyps().is_empty(),
            "Suc_not_Zero should not retain its goal as a hyp: prop={:?}, hyps={:?}, trust={:?}",
            thm.prop().term(),
            thm.hyps().iter().map(|h| format!("{:?}", h.term())).collect::<Vec<_>>(),
            thm.trust_status()
        );
    }

    #[test]
    fn verify_no_open_oracle_free_results_in_core_batch() {
        let samples = [
            (include_str!("../../theories/HOL/HOL.thy"), "trans"),
            (include_str!("../../theories/HOL/Set.thy"), "CollectI"),
            (include_str!("../../theories/HOL/Nat.thy"), "Suc_not_Zero"),
            (include_str!("../../theories/HOL/List.thy"), "length_0_conv"),
        ];

        for (source, name) in samples {
            let thm = verify_named_from(source, name);
            assert!(
                !thm.oracles().is_empty() || thm.hyps().is_empty(),
                "{name} returned oracle-free open theorem: prop={:?}, hyps={:?}",
                thm.prop().term(),
                thm.hyps().iter().map(|h| format!("{:?}", h.term())).collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn test_method_assumption_solves() {
        // assume_tac requires subgoal in hyps
        // Create state: {A} ⊢ A (nprems=0 — already solved)
        let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
        let state = ThmKernel::assume_compat(a);
        assert_eq!(state.nprems(), 0); // trivially true
        let results = Method::Assumption.execute(&state, &[], &HolTheoremDb::new());
        // On a state with nprems=0, assume_tac(0) fails (no subgoal 0)
        assert!(results.is_empty());
    }

    #[test]
    fn test_method_fail() {
        let state = trivial_goal("A");
        let results = Method::Fail.execute(&state, &[], &HolTheoremDb::new());
        assert!(results.is_empty());
    }

    #[test]
    fn test_method_skip() {
        let state = trivial_goal("A");
        let results = Method::Skip.execute(&state, &[], &HolTheoremDb::new());
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
        let results = method.execute(&state, &[], &HolTheoremDb::new());
        assert!(!results.is_empty());
    }

    #[test]
    fn test_method_unfold_top_level() {
        // Create a definition: foo ≡ bar (as an assume theorem)
        let foo = Term::const_("foo", Typ::base("nat"));
        let bar = Term::const_("bar", Typ::base("nat"));
        let def_eq =
            crate::core::logic::Pure::mk_equals(Typ::base("nat"), foo.clone(), bar.clone());
        let def_thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(def_eq)));

        // Create goal state: [foo = bar] ==> (foo = bar)
        // This gives a state with nprems=1, where the subgoal is "foo = bar"
        let eq_term =
            crate::core::logic::Pure::mk_equals(Typ::base("nat"), foo.clone(), bar.clone());
        let goal_imp = crate::core::logic::Pure::mk_implies(eq_term.clone(), eq_term.clone());
        let state = ThmKernel::assume_compat(CTerm::certify(goal_imp));
        assert_eq!(state.nprems(), 1, "state should have 1 subgoal");

        // Apply unfold foo_def (should rewrite foo to bar in subgoal)
        let method = Method::Unfold(vec![def_thm]);
        let results = method.execute(&state, &[], &HolTheoremDb::new());
        assert!(!results.is_empty(), "unfold should produce a result");
        let result = &results[0];
        if let Some(prem) = result.prem(0) {
            eprintln!("unfold result prem: {:?}", prem);
        }
    }

    #[test]
    fn test_method_unfold_deep() {
        // Create a definition: foo ≡ bar
        let foo = Term::const_("foo", Typ::base("nat"));
        let bar = Term::const_("bar", Typ::base("nat"));
        let def_eq =
            crate::core::logic::Pure::mk_equals(Typ::base("nat"), foo.clone(), bar.clone());
        let def_thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(def_eq)));

        // Create goal state: [f(foo) = f(bar)] ==> (f(foo) = f(bar))
        // Subgoal is f(foo) = f(bar), and unfold should rewrite foo→bar inside
        let f = Term::const_("f", Typ::arrow(Typ::base("nat"), Typ::base("nat")));
        let f_foo = Term::app(f.clone(), foo.clone());
        let f_bar = Term::app(f.clone(), bar.clone());
        let eq_term =
            crate::core::logic::Pure::mk_equals(Typ::base("nat"), f_foo.clone(), f_bar.clone());
        let goal_imp = crate::core::logic::Pure::mk_implies(eq_term.clone(), eq_term.clone());
        let state = ThmKernel::assume_compat(CTerm::certify(goal_imp));
        assert_eq!(state.nprems(), 1);

        let method = Method::Unfold(vec![def_thm]);
        let results = method.execute(&state, &[], &HolTheoremDb::new());
        assert!(!results.is_empty(), "unfold deep should produce a result");
        let result = &results[0];
        if let Some(prem) = result.prem(0) {
            eprintln!("unfold deep result prem: {:?}", prem);
        }
    }

    #[test]
    fn test_method_fold() {
        // Create a definition: foo ≡ bar
        let foo = Term::const_("foo", Typ::base("nat"));
        let bar = Term::const_("bar", Typ::base("nat"));
        let def_eq =
            crate::core::logic::Pure::mk_equals(Typ::base("nat"), foo.clone(), bar.clone());
        let def_thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(def_eq)));

        // Create goal state: [bar = foo] ==> (bar = foo)
        // Subgoal: bar = foo, fold should rewrite bar→foo giving foo = foo
        let eq_term =
            crate::core::logic::Pure::mk_equals(Typ::base("nat"), bar.clone(), foo.clone());
        let goal_imp = crate::core::logic::Pure::mk_implies(eq_term.clone(), eq_term.clone());
        let state = ThmKernel::assume_compat(CTerm::certify(goal_imp));
        assert_eq!(state.nprems(), 1);

        let method = Method::Fold(vec![def_thm]);
        let results = method.execute(&state, &[], &HolTheoremDb::new());
        assert!(!results.is_empty(), "fold should produce a result");
    }

    #[test]
    fn test_method_unfold_from_db() {
        // Test unfold using theorems from the database
        let db = HolTheoremDb::global();
        // Look for a definition-like theorem (e.g., True_def if available)
        let def_names =
            ["True_def", "All_def", "Ex_def", "not_def", "and_def", "or_def", "imp_def"];
        let mut found_def: Option<Arc<Thm>> = None;
        for name in &def_names {
            if let Some(thm) = db.by_name.get(*name) {
                found_def = Some(Arc::clone(thm));
                eprintln!("Found definition: {}", name);
                break;
            }
        }
        // If no definition found, skip test (definitions may not be parsed as named theorems)
        if found_def.is_none() {
            eprintln!("No definition found in DB, skipping unfold_from_db test");
            return;
        }
        let def_thm = found_def.unwrap();
        // Create a simple goal using the LHS of the definition
        let state = ThmKernel::trivial(CTerm::certify(def_thm.prop().term().clone())).unwrap();
        let method = Method::Unfold(vec![def_thm]);
        let results = method.execute(&state, &[], db);
        assert!(!results.is_empty());
    }

    #[test]
    fn test_prove_assume_multi() {
        // [A] ==> A (assume A from hyps)
        let a = Term::const_("A", Typ::base("prop"));
        let state = ThmKernel::assume_compat(CTerm::certify(a.clone()));
        // state: {A} ⊢ A, nprems=0 but still open under hypothesis A.
        assert_eq!(state.nprems(), 0);
    }

    #[test]
    fn test_open_oracle_free_theorem_is_not_closed_proved_outcome() {
        let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
        let thm = ThmKernel::assume_compat(a);

        assert!(thm.is_fully_proved(), "assume has no oracle footprint");
        assert!(!thm.is_closed(), "assume leaves an ambient hypothesis");
        assert!(!thm.is_closed_proved());
        assert!(!super::is_transitional_strict_closed_outcome(&thm, VerifyOutcome::Proved));
    }

    fn checked_prop_ct(name: &str) -> CTerm {
        let mut env = crate::core::types::TypeEnv::new();
        let prop_t = Typ::base("prop");
        env.declare_const(name, prop_t.clone());
        CTerm::certify_checked(Term::const_(name, prop_t), &env)
            .expect("test proposition should certify")
    }

    fn pure_identity_term() -> Term {
        let a = Term::const_("A", Typ::base("prop"));
        Pure::mk_implies(a.clone(), a)
    }

    fn pure_identity_lemma() -> crate::hol::hol_loader::ParsedLemma {
        crate::hol::hol_loader::ParsedLemma::new_synthetic(
            "strict_imp_identity".to_string(),
            vec![],
            std::sync::Arc::new(ThmKernel::assume_compat(CTerm::certify(pure_identity_term()))),
            Some("by assumption".to_string()),
            None,
        )
    }

    fn with_pure_identity_db<R>(f: impl FnOnce(&HolTheoremDb) -> R) -> R {
        let mut db = HolTheoremDb::new();
        db.type_env.declare_const("A", Typ::base("prop"));
        f(&db)
    }

    fn parsed_hol_true_i() -> crate::hol::hol_loader::ParsedLemma {
        let hol = include_str!("../../theories/HOL/HOL.thy");
        let lemmas = crate::hol::hol_loader::parse_lemmas(hol);
        lemmas.into_iter().find(|lem| lem.name == "TrueI").expect("HOL TrueI parses")
    }

    fn parsed_true_i_from_source(source: &str) -> crate::hol::hol_loader::ParsedLemma {
        let lemmas = crate::hol::hol_loader::parse_lemmas(source);
        lemmas.into_iter().find(|lem| lem.name == "TrueI").expect("attack TrueI parses")
    }

    fn parsed_true_i_with_unconsumed_suffix() -> crate::hol::hol_loader::ParsedLemma {
        parsed_true_i_from_source(
            r#"
lemma TrueI:
  "True \<in> {False}"
  unfolding True_def by (rule refl)
"#,
        )
    }

    fn hol_true_i_with_prop(prop: Term) -> crate::hol::hol_loader::ParsedLemma {
        let certified = CTerm::certify(prop);
        hol_true_i_with_cterm(certified)
    }

    fn hol_true_i_with_cterm(prop: CTerm) -> crate::hol::hol_loader::ParsedLemma {
        let mut lem = parsed_hol_true_i();
        lem.theorem = Arc::new(ThmKernel::assume_compat(prop));
        lem
    }

    fn hol_true_i_db() -> HolTheoremDb {
        let hol = include_str!("../../theories/HOL/HOL.thy");
        let lemmas = crate::hol::hol_loader::parse_lemmas(hol);
        let mut db = HolTheoremDb::from_lemmas(&lemmas);
        enrich_local_db_with_checked_sources(&mut db, hol)
            .expect("HOL TrueI checked source env must merge");
        HolTheoremDb::add_builtins(&mut db);
        db
    }

    fn with_hol_true_i_db<R>(f: impl FnOnce(&HolTheoremDb) -> R) -> R {
        let db = hol_true_i_db();
        f(&db)
    }

    fn hol_true_i_db_with_schematic_builtin() -> HolTheoremDb {
        let mut db = hol_true_i_db();
        db.by_name.insert(
            "TrueI".to_string(),
            Arc::new(ThmKernel::assume_compat(CTerm::certify(Term::var(
                "P",
                0,
                Typ::base("bool"),
            )))),
        );
        db
    }

    #[test]
    fn strict_vertical_slice_pure_imp_identity() {
        let mut env = crate::core::types::TypeEnv::new();
        env.declare_const("A", Typ::base("prop"));
        let goal = pure_identity_term();

        let thm = try_strict_pure_imp_identity(&goal, &env)
            .expect("A ==> A should replay through checked strict implication rules");

        assert!(thm.is_strict_closed_proved());
        assert!(Hyps::kernel_alpha_eq(thm.prop().term(), &goal));
        assert!(thm.hyps().is_empty());
        assert!(thm.oracles().is_empty());
        assert!(thm.tpairs().is_empty());
    }

    #[test]
    fn proof_outcome_counts_pure_imp_identity_as_transitional_strict_closed() {
        let lem = pure_identity_lemma();
        reset_verify_stats();

        let (verified, attempted) =
            with_pure_identity_db(|db| verify_lemmas_batch(std::slice::from_ref(&lem), db));
        let stats = verify_outcome_stats();

        assert_eq!((verified, attempted), (1, 1));
        assert_eq!(stats.kernel_trusted_closed, 0);
        assert_eq!(stats.transitional_strict_closed, 1);
        assert_eq!(stats.total(), 1);
    }

    #[test]
    fn proof_outcome_does_not_count_compat_identity_as_transitional_strict_closed() {
        let a = prop_ct("A");
        let assumed = ThmKernel::assume_compat(a.clone());
        let compat_identity = ThmKernel::implies_intr(&a, &assumed).unwrap();

        let outcome = classify_proof_outcome(
            "compat_imp_identity",
            None,
            Some((&compat_identity, VerifyOutcome::Proved)),
        );

        assert!(matches!(outcome, ProofOutcome::CompatClosedOracleFree { .. }));
        assert!(!outcome.is_transitional_strict_closed());
    }

    #[test]
    fn verify_batch_sampled_true_i_counts_accepted_not_transitional() {
        let lem = parsed_hol_true_i();
        reset_verify_stats();
        let (verified, attempted) =
            with_hol_true_i_db(|db| verify_lemmas_batch(std::slice::from_ref(&lem), db));
        let stats = verify_outcome_stats();
        assert_eq!((verified, attempted), (0, 1));
        assert_eq!(stats.kernel_trusted_closed, 1);
        assert_eq!(stats.transitional_strict_closed, 0);
        assert_eq!(stats.total(), 1);
    }

    #[test]
    fn strict_adapter_dispatches_true_i() {
        let lem = parsed_hol_true_i();
        assert_eq!(lem.source_proposition_status(), SourcePropositionStatus::FullyConsumed);
        assert_eq!(lem.source_proposition_shape(), SourcePropositionShape::StandaloneHolTrueAlias);

        let result = with_hol_true_i_db(|db| try_strict_adapter(&lem, db));

        match result {
            StrictAdapterResult::Proved(accepted) => {
                let (owner, theorem) = *accepted;
                let replayed = crate::kernel::KernelRules::theorem_ref(&owner, &theorem).unwrap();
                assert!(replayed.as_kernel().prop().term().alpha_eq(theorem.prop().term()));
            },
            other => panic!("expected strict TrueI proof, got {other:?}"),
        }
    }

    #[test]
    fn split_line_unfolding_matches_inline_dispatch_end_to_end() {
        let inline_source = r#"
lemma GeneralTrue: "True"
  unfolding True_def by (rule refl)
"#;
        let split_source = r#"
lemma GeneralTrue: "True"
  unfolding True_def
  by (rule refl)
"#;

        let parse = |source: &str| {
            {
                crate::hol::hol_loader::parse_lemmas(source)
                    .into_iter()
                    .find(|lemma| lemma.name == "GeneralTrue")
                    .expect("GeneralTrue")
            }
        };
        let inline = parse(inline_source);
        let split = parse(split_source);
        assert_eq!(split.proof_script, inline.proof_script);
        assert_eq!(split.proof_script.as_deref(), Some("unfolding True_def by (rule refl)"));

        let db = &hol_true_i_db();
        let inline_thm = verify_lemma(&inline, db).into_legacy_theorem().expect("inline result");
        let split_thm = verify_lemma(&split, db).into_legacy_theorem().expect("split result");
        assert_eq!(split_thm.prop(), inline_thm.prop());
        assert_eq!(split_thm.trust_status(), inline_thm.trust_status());
        assert_eq!(split_thm.hyps(), inline_thm.hyps());
        assert_eq!(split_thm.oracles(), inline_thm.oracles());
        assert_eq!(split_thm.tpairs(), inline_thm.tpairs());
    }

    #[test]
    fn strict_adapter_returns_not_applicable_for_unrelated_lemma() {
        let lem = pure_identity_lemma();

        let result = with_pure_identity_db(|db| try_strict_adapter(&lem, db));

        assert!(matches!(result, StrictAdapterResult::NotApplicable));
    }

    #[test]
    fn strict_adapter_returns_not_applicable_without_explicit_proof() {
        for proof_script in [None, Some("  \n".to_string())] {
            let mut lem = parsed_hol_true_i();
            lem.proof_script = proof_script;

            let result = with_hol_true_i_db(|db| try_strict_adapter(&lem, db));

            assert!(matches!(result, StrictAdapterResult::NotApplicable));
        }
    }

    #[test]
    fn verify_lemma_keeps_parser_gap_behavior_without_explicit_proof() {
        for proof_script in [None, Some("  \n".to_string())] {
            let mut lem = parsed_hol_true_i();
            lem.proof_script = proof_script;
            let db = &hol_true_i_db_with_schematic_builtin();

            let thm = verify_lemma(&lem, db)
                .into_legacy_theorem()
                .expect("missing proof should retain compatibility behavior");

            assert!(thm.oracles().iter().any(|oracle| oracle.as_ref() == "admitted:parser_gap"));
        }
    }

    #[test]
    fn strict_adapter_rejects_true_i_with_wrong_proof_shape() {
        let mut lem = parsed_hol_true_i();
        lem.proof_script = Some("by (rule refl)".to_string());

        let result = with_hol_true_i_db(|db| try_strict_adapter(&lem, db));

        assert!(matches!(
            result,
            StrictAdapterResult::Rejected(StrictAdapterReject::ProofShapeMismatch)
        ));
    }

    #[test]
    fn commented_truei_proof_cannot_be_elevated_by_strict_adapter() {
        let lem = parsed_true_i_from_source(
            r#"
lemma TrueI:
  "True"
  (*
  unfolding True_def by (rule refl)
  *)
  sorry
"#,
        );
        assert_eq!(lem.proof_script.as_deref(), Some("sorry"));

        let result = with_hol_true_i_db(|db| try_strict_adapter(&lem, db));
        assert!(matches!(
            result,
            StrictAdapterResult::Rejected(StrictAdapterReject::ProofShapeMismatch)
        ));

        let thm = with_hol_true_i_db(|db| verify_lemma(&lem, db))
            .into_legacy_theorem()
            .expect("explicit adapter rejection must remain an admitted result");
        assert!(!thm.is_strict_closed_proved());
        assert!(
            thm.oracles()
                .iter()
                .any(|oracle| oracle.as_ref() == "admitted:strict_adapter_proof_shape_mismatch")
        );
    }

    #[test]
    fn formal_comment_truei_payloads_cannot_be_elevated() {
        let db = &hol_true_i_db();
        for prefix in ["\\<comment> ", "\\<^cancel>", "\\<^latex>", "\\<^marker>"] {
            let source = format!(
                r#"
lemma TrueI:
  {prefix}\<open>
  shows "True"
  \<close>
  shows "False"
  unfolding True_def by (rule refl)
"#
            );
            let lem = parsed_true_i_from_source(&source);
            assert_eq!(lem.source_proposition_status(), SourcePropositionStatus::FullyConsumed);
            assert_eq!(lem.source_proposition_shape(), SourcePropositionShape::Other);
            assert!(matches!(
                lem.theorem.prop().term(),
                Term::Const { name, .. } | Term::Free { name, .. }
                    if matches!(name.as_ref(), "False" | "HOL.False")
            ));

            let result = try_strict_adapter(&lem, db);
            assert!(matches!(
                result,
                StrictAdapterResult::Rejected(StrictAdapterReject::SourcePropositionUnverified {
                    status: SourcePropositionStatus::FullyConsumed,
                    shape: SourcePropositionShape::Other,
                })
            ));

            let thm = verify_lemma(&lem, db)
                .into_legacy_theorem()
                .expect("formal-comment payload must remain an admitted rejection");
            assert!(!thm.is_strict_closed_proved());
            assert!(thm.oracles().iter().any(|oracle| {
                oracle.as_ref() == "admitted:strict_adapter_source_prop_unverified"
            }));
        }
    }

    #[test]
    fn document_cartouche_named_truei_show_cannot_be_elevated() {
        let source = r#"
lemma victim:
  shows "False"
text \<open>
shows TrueI: "True" \<close> note refl
unfolding True_def by (rule refl)
"#;

        let lemmas = crate::hol::hol_loader::parse_lemmas(source);
        assert_eq!(lemmas.len(), 1);
        let lemma = &lemmas[0];
        assert_eq!(lemma.name, "victim");
        assert!(matches!(
            lemma.theorem.prop().term(),
            Term::Const { name, .. } | Term::Free { name, .. }
                if matches!(name.as_ref(), "False" | "HOL.False")
        ));
        assert_eq!(lemma.proof_script.as_deref(), Some("unfolding True_def by (rule refl)"));

        let db = &hol_true_i_db();
        let result = try_strict_adapter(lemma, db);
        assert!(!matches!(result, StrictAdapterResult::Proved(_)));
        let thm = verify_lemma(lemma, db).into_legacy_theorem().expect("compat result");
        assert!(!thm.is_strict_closed_proved());
    }

    #[test]
    fn ml_prf_cartouche_named_truei_show_cannot_be_elevated() {
        let source = r#"
lemma victim:
  shows "False"
ML_prf \<open>
(*
shows TrueI: "True"
*)
val _ = ()
\<close>
unfolding True_def by (rule refl)
"#;

        let lemmas = crate::hol::hol_loader::parse_lemmas(source);
        assert_eq!(lemmas.len(), 1);
        let lemma = &lemmas[0];
        assert_eq!(lemma.name, "victim");
        assert!(matches!(
            lemma.theorem.prop().term(),
            Term::Const { name, .. } | Term::Free { name, .. }
                if matches!(name.as_ref(), "False" | "HOL.False")
        ));
        assert!(
            lemma.proof_script.is_none(),
            "an unsupported proof command must stop statement/proof capture"
        );
    }

    #[test]
    fn embedded_structured_proof_cannot_close_lemma() {
        let source = r#"
lemma Hidden: "True"
proof -
  text \<open>
    show True by assumption \<close> note refl
  sorry
"#;

        let lemma = {
            crate::hol::hol_loader::parse_lemmas(source)
                .into_iter()
                .find(|lemma| lemma.name == "Hidden")
                .expect("Hidden")
        };
        assert_eq!(lemma.proof_script.as_deref(), Some("proof -\nsorry"));

        let thm = with_hol_true_i_db(|db| verify_lemma(&lemma, db))
            .into_legacy_theorem()
            .expect("active sorry must produce an admitted theorem");
        assert!(!thm.is_strict_closed_proved());
        assert!(
            thm.oracles().iter().any(|oracle| oracle.as_ref().starts_with("admitted:")),
            "hidden qed must not close the theorem before active sorry"
        );
    }

    #[test]
    fn strict_adapter_later_named_show_cannot_borrow_earlier_true_i_token() {
        let original = include_str!("../../theories/HOL/HOL.thy");
        let source = original.replace(
            "lemma TrueI: True\n  unfolding True_def by (rule refl)",
            "lemma TrueI: True\n  unfolding True_def by (rule refl)\n\
             hide_const (open) True\n\
             lemma Other:\n  shows TrueI: \"True\"\n  unfolding True_def by (rule refl)",
        );
        assert_ne!(source, original);

        let candidate = {
            crate::hol::hol_loader::parse_lemmas_with_loc(&source, "HOL.thy")
                .into_iter()
                .filter(|lemma| lemma.name == "TrueI")
                .nth(1)
                .expect("second named TrueI parses")
        };
        let mut db = hol_true_i_db();
        db.set_verification_source(&source);
        assert!(matches!(
            try_strict_adapter(&candidate, &db),
            StrictAdapterResult::Rejected(StrictAdapterReject::SourceBindingMismatch)
        ));
    }

    #[test]
    fn strict_adapter_forged_metadata_cannot_rebind_local_source() {
        let mut lemma = parsed_true_i_from_source(
            "lemma TrueI:\n  fixes True :: bool\n  shows True\n  unfolding True_def by (rule refl)",
        );
        let location = lemma.source_loc.as_mut().unwrap();
        location.proposition_status = SourcePropositionStatus::FullyConsumed;
        location.proposition_shape = SourcePropositionShape::StandaloneHolTrueAlias;
        location.proposition_text = Some("True".into());
        let result = with_hol_true_i_db(|db| verify_lemma(&lemma, db));
        assert!(
            !matches!(
                classify_verify_result(&lemma.name, &result),
                ProofOutcome::KernelTrustedClosed { .. }
            ),
            "public source metadata must not substitute another source's accepted token"
        );
    }

    #[test]
    fn strict_adapter_changed_source_invalidates_accepted_definition() {
        let lem = parsed_hol_true_i();
        let mut db = hol_true_i_db();
        assert!(matches!(try_strict_adapter(&lem, &db), StrictAdapterResult::Proved(_)));
        let changed = include_str!("../../theories/HOL/HOL.thy")
            .replace("definition True ::", "definition Different ::");
        db.set_verification_source(&changed);
        assert!(matches!(
            try_strict_adapter(&lem, &db),
            StrictAdapterResult::Rejected(StrictAdapterReject::SourceBindingMismatch)
        ));
        assert!(matches!(db.compile_source_true_i(), Some(Err(_))));
    }

    #[test]
    fn strict_adapter_mutated_public_declaration_cannot_borrow_source_token() {
        let original = parsed_hol_true_i();
        let db = &hol_true_i_db();
        assert!(matches!(try_strict_adapter(&original, db), StrictAdapterResult::Proved(_)));

        let mut changed_name = original.clone();
        changed_name.name = "HOL::TrueI".into();
        let mut changed_proof = original.clone();
        changed_proof.proof_script = Some("unfolding  True_def by (rule refl)".into());
        let mut changed_statement = original.clone();
        changed_statement.source_loc.as_mut().unwrap().proposition_text = Some("HOL.True".into());
        let mut changed_file = original.clone();
        changed_file.source_loc.as_mut().unwrap().file = "another.thy".into();
        let mut changed_attributes = original.clone();
        changed_attributes.attributes.push("intro".into());
        for candidate in
            [changed_name, changed_proof, changed_statement, changed_file, changed_attributes]
        {
            assert!(matches!(
                try_strict_adapter(&candidate, db),
                StrictAdapterResult::Rejected(StrictAdapterReject::SourceBindingMismatch)
            ));
        }
    }

    #[test]
    fn strict_adapter_synthetic_metadata_cannot_borrow_source_token() {
        let parsed = parsed_hol_true_i();
        let mut synthetic = ParsedLemma::new_synthetic(
            parsed.name.clone(),
            parsed.attributes.clone(),
            Arc::clone(&parsed.theorem),
            parsed.proof_script.clone(),
            None,
        );
        synthetic.source_loc = parsed.source_loc.clone();
        let mut db = hol_true_i_db();
        assert!(matches!(try_strict_adapter(&parsed, &db), StrictAdapterResult::Proved(_)));
        assert!(matches!(
            try_strict_adapter(&synthetic, &db),
            StrictAdapterResult::Rejected(StrictAdapterReject::SourceBindingMismatch)
        ));
        db.bind_verification_source(&synthetic);
        assert!(matches!(try_strict_adapter(&parsed, &db), StrictAdapterResult::Rejected(_)));
        db.bind_verification_source(&parsed);
        assert!(matches!(try_strict_adapter(&parsed, &db), StrictAdapterResult::Proved(_)));
    }

    #[test]
    fn strict_adapter_rejects_true_i_with_proposition_mismatch() {
        let mut lem = parsed_hol_true_i();
        lem.theorem =
            Arc::new(ThmKernel::assume_compat(CTerm::certify(crate::hol::hologic::false_const())));

        let result = with_hol_true_i_db(|db| try_strict_adapter(&lem, db));

        assert!(matches!(
            result,
            StrictAdapterResult::Rejected(StrictAdapterReject::PropositionMismatch)
        ));
    }

    #[test]
    fn strict_adapter_rejects_free_true_alias() {
        let lem = hol_true_i_with_prop(Term::free("True", Typ::base("bool")));

        let result = with_hol_true_i_db(|db| try_strict_adapter(&lem, db));

        assert!(matches!(
            result,
            StrictAdapterResult::Rejected(StrictAdapterReject::PropositionMismatch)
        ));
    }

    #[test]
    fn strict_adapter_rejects_dummy_typed_true() {
        let lem = hol_true_i_with_prop(Term::const_("True", Typ::dummy()));

        let result = with_hol_true_i_db(|db| try_strict_adapter(&lem, db));

        assert!(matches!(
            result,
            StrictAdapterResult::Rejected(StrictAdapterReject::CertificationFailed(_))
        ));
    }

    #[test]
    fn strict_adapter_rejects_true_with_mismatched_cterm_type() {
        let lem = hol_true_i_with_cterm(CTerm::certify_typed(
            crate::hol::hologic::true_const(),
            Typ::base("prop"),
        ));

        let result = with_hol_true_i_db(|db| try_strict_adapter(&lem, db));

        assert!(matches!(
            result,
            StrictAdapterResult::Rejected(StrictAdapterReject::CertificationFailed(_))
        ));
    }

    #[test]
    fn parse_lemmas_malformed_true_proposition_produces_no_candidate() {
        for proposition in ["True =", "True :: nat", "True :: prop"] {
            let source =
                format!("lemma TrueI: \"{proposition}\"\n  unfolding True_def by (rule refl)");
            let lemmas = { crate::hol::hol_loader::parse_lemmas(&source) };
            assert!(lemmas.is_empty(), "{proposition} created a theorem candidate");
        }
    }

    #[test]
    fn strict_adapter_rejects_source_equality_after_true_annotation() {
        let source = r#"
lemma TrueI:
  "True :: bool = False"
  unfolding True_def by (rule refl)
"#;

        let lemmas = crate::hol::hol_loader::parse_lemmas(source);
        let lem = lemmas.into_iter().find(|lem| lem.name == "TrueI").expect("TrueI parses");
        assert_ne!(lem.theorem.prop().term(), &crate::hol::hologic::true_const());
        assert!(crate::hol::hologic::dest_hol_equals(lem.theorem.prop().term()).is_some());

        let result = with_hol_true_i_db(|db| try_strict_adapter(&lem, db));

        assert!(matches!(result, StrictAdapterResult::Rejected(_)));
    }

    #[test]
    fn strict_adapter_rejects_unconsumed_source_proposition_suffix() {
        let lem = parsed_true_i_with_unconsumed_suffix();
        assert_eq!(lem.theorem.prop().term(), &crate::hol::hologic::true_const());
        assert_eq!(lem.source_proposition_status(), SourcePropositionStatus::Incomplete);

        let result = with_hol_true_i_db(|db| try_strict_adapter(&lem, db));

        assert!(matches!(
            result,
            StrictAdapterResult::Rejected(StrictAdapterReject::SourcePropositionUnverified {
                status: SourcePropositionStatus::Incomplete,
                shape: SourcePropositionShape::Other,
            })
        ));
    }

    #[test]
    fn strict_adapter_rejects_contextual_true_source() {
        let sources = [
            r#"
lemma TrueI:
  fixes True :: bool
  shows True
  unfolding True_def by (rule refl)
"#,
            r#"
lemma TrueI:
  includes malicious_bundle
  shows True
  unfolding True_def by (rule refl)
"#,
            r#"
theory Attack
imports HOL
begin
context
  fixes True :: bool
begin
lemma TrueI: True
  unfolding True_def by (rule refl)
end
end
"#,
            r#"
context
  fixes True :: bool
begin
lemma TrueI: True
  unfolding True_def by (rule refl)
end
"#,
            r#"
lemma (in shadow) TrueI: True
  unfolding True_def by (rule refl)
"#,
            r#"
lemma TrueI:
  "True"
  if "False"
  unfolding True_def by (rule refl)
"#,
            r#"
lemma TrueI:
  "True"
  when "False"
  unfolding True_def by (rule refl)
"#,
            r#"
lemma TrueI:
  notes malicious_fact
  shows True
  unfolding True_def by (rule refl)
"#,
        ];

        for source in sources {
            let lem = parsed_true_i_from_source(source);
            assert_eq!(lem.theorem.prop().term(), &crate::hol::hologic::true_const());
            assert_eq!(lem.source_proposition_status(), SourcePropositionStatus::FullyConsumed);
            assert_eq!(lem.source_proposition_shape(), SourcePropositionShape::Contextual);

            let result = with_hol_true_i_db(|db| try_strict_adapter(&lem, db));
            assert!(matches!(
                result,
                StrictAdapterResult::Rejected(StrictAdapterReject::SourcePropositionUnverified {
                    status: SourcePropositionStatus::FullyConsumed,
                    shape: SourcePropositionShape::Contextual,
                })
            ));
        }
    }

    #[test]
    fn strict_adapter_rejects_true_i_without_source_provenance() {
        let mut lem = parsed_hol_true_i();
        lem.source_loc = None;

        let result = with_hol_true_i_db(|db| try_strict_adapter(&lem, db));

        assert!(matches!(
            result,
            StrictAdapterResult::Rejected(StrictAdapterReject::SourcePropositionUnverified {
                status: SourcePropositionStatus::Unavailable,
                shape: SourcePropositionShape::Unavailable,
            })
        ));
    }

    #[test]
    fn source_elaboration_missing_or_contextual_provenance_rejects_legacy_rendering() {
        let db = HolTheoremDb::new();
        let ctx = build_kernel_proof_context(&db);
        let mut bare = parsed_true_i_from_source("lemma TrueI: True");
        assert_eq!(bare.source_proposition_text(), Some("True"));
        assert!(matches!(
            try_source_elaboration(&bare, &ctx),
            Err(crate::isar::elaborator::ElaborationError::UnresolvedName { .. })
        ));

        bare.source_loc = None;
        assert!(matches!(
            try_source_elaboration(&bare, &ctx),
            Err(crate::isar::elaborator::ElaborationError::ElaborationInternal(message))
                if message.contains("unavailable")
        ));

        let contextual =
            parsed_true_i_from_source("lemma TrueI:\n  assumes \"False\"\n  shows \"True\"");
        assert_eq!(contextual.source_proposition_text(), None);
        assert!(matches!(
            try_source_elaboration(&contextual, &ctx),
            Err(crate::isar::elaborator::ElaborationError::ElaborationInternal(message))
                if message.contains("unavailable")
        ));
    }

    #[test]
    fn verify_lemma_sampled_true_i_retains_owner_after_database_scope() {
        let lem = parsed_hol_true_i();
        let result = with_hol_true_i_db(|db| verify_lemma(&lem, db));
        let theorem = result.accepted().expect("accepted TrueI");
        let owner = result.accepted_owner().expect("accepted owner");
        let replayed = crate::kernel::KernelRules::theorem_ref(owner, theorem).unwrap();
        assert_eq!(replayed.as_kernel().prop().term().ty(), crate::kernel::Ty::prop());
        assert!(replayed.as_kernel().prop().term().alpha_eq(theorem.prop().term()));
        assert!(result.into_legacy_theorem().is_none());
    }

    #[test]
    fn verify_lemma_records_strict_adapter_rejection_for_true_i() {
        let mut lem = parsed_hol_true_i();
        lem.proof_script = Some("by (rule refl)".to_string());
        let db = &hol_true_i_db_with_schematic_builtin();

        let thm = verify_lemma(&lem, db)
            .into_legacy_theorem()
            .expect("strict adapter rejection should become explicit admission");

        assert!(!thm.is_strict_closed_proved());
        assert!(
            thm.oracles()
                .iter()
                .any(|oracle| oracle.as_ref() == "admitted:strict_adapter_proof_shape_mismatch")
        );
        assert!(!thm.oracles().iter().any(|oracle| oracle.as_ref() == "admitted:parser_gap"));
    }

    #[test]
    fn verify_lemma_rejects_unconsumed_true_source_before_parser_gap() {
        let lem = parsed_true_i_with_unconsumed_suffix();
        let db = &hol_true_i_db_with_schematic_builtin();

        let thm = verify_lemma(&lem, db)
            .into_legacy_theorem()
            .expect("incomplete source proposition should become explicit admission");

        assert!(!thm.is_strict_closed_proved());
        assert!(
            thm.oracles().iter().any(|oracle| {
                oracle.as_ref() == "admitted:strict_adapter_source_prop_unverified"
            })
        );
        assert!(!thm.oracles().iter().any(|oracle| oracle.as_ref() == "admitted:parser_gap"));
    }

    #[test]
    fn verify_lemma_contextual_true_source_cannot_bypass_parser_gap() {
        let sources = [
            r#"
lemma TrueI:
  fixes True :: bool
  shows True
  unfolding True_def by (rule refl)
"#,
            r#"
lemma TrueI:
  includes malicious_bundle
  shows True
  unfolding True_def by (rule refl)
"#,
            r#"
lemma TrueI:
  "True"
  if "False"
  unfolding True_def by (rule refl)
"#,
        ];

        for source in sources {
            let lem = parsed_true_i_from_source(source);
            let db = &hol_true_i_db_with_schematic_builtin();
            let thm = verify_lemma(&lem, db)
                .into_legacy_theorem()
                .expect("unverified source proposition should become explicit admission");

            assert!(!thm.is_strict_closed_proved());
            assert!(thm.oracles().iter().any(|oracle| {
                oracle.as_ref() == "admitted:strict_adapter_source_prop_unverified"
            }));
            assert!(!thm.oracles().iter().any(|oracle| oracle.as_ref() == "admitted:parser_gap"));
        }
    }

    #[test]
    fn verify_lemma_does_not_normalize_free_true_into_hol_true() {
        let lem = hol_true_i_with_prop(Term::free("True", Typ::base("bool")));

        let thm = with_hol_true_i_db(|db| verify_lemma(&lem, db))
            .into_legacy_theorem()
            .expect("Free True rejection should become explicit admission");

        assert!(!thm.is_strict_closed_proved());
        assert!(
            thm.oracles()
                .iter()
                .any(|oracle| oracle.as_ref() == "admitted:strict_adapter_prop_mismatch")
        );
        assert!(matches!(
            thm.prop().term(),
            Term::Free { name, typ }
                if name.as_ref() == "True" && typ == &Typ::base("bool")
        ));
    }

    #[test]
    fn verify_lemma_does_not_normalize_dummy_true_into_hol_true() {
        let lem = hol_true_i_with_prop(Term::const_("True", Typ::dummy()));

        let thm = with_hol_true_i_db(|db| verify_lemma(&lem, db))
            .into_legacy_theorem()
            .expect("dummy True rejection should become explicit admission");

        assert!(!thm.is_strict_closed_proved());
        assert!(
            thm.oracles()
                .iter()
                .any(|oracle| oracle.as_ref() == "admitted:strict_adapter_certification_failed")
        );
        assert!(CTerm::term_contains_dummy_type(thm.prop().term()));
    }

    #[test]
    fn verify_lemma_does_not_normalize_mistyped_true_into_hol_true() {
        let lem = hol_true_i_with_cterm(CTerm::certify_typed(
            crate::hol::hologic::true_const(),
            Typ::base("prop"),
        ));

        let thm = with_hol_true_i_db(|db| verify_lemma(&lem, db))
            .into_legacy_theorem()
            .expect("mistyped True rejection should become explicit admission");

        assert!(!thm.is_strict_closed_proved());
        assert!(
            thm.oracles()
                .iter()
                .any(|oracle| oracle.as_ref() == "admitted:strict_adapter_certification_failed")
        );
    }

    #[test]
    fn verify_lemma_runs_strict_adapter_before_parser_gap_override() {
        let lem = parsed_hol_true_i();
        let db = &hol_true_i_db_with_schematic_builtin();

        let result = verify_lemma(&lem, db);
        assert!(matches!(
            classify_verify_result(&lem.name, &result),
            ProofOutcome::KernelTrustedClosed { .. }
        ));
        assert!(result.legacy().is_none());
    }

    #[test]
    fn accepted_token_precedes_legacy_and_counts_exactly_once() {
        let signature =
            crate::kernel::Signature::new().extend_const("A", crate::kernel::Ty::prop()).unwrap();
        let theory = crate::kernel::TrustedTheory::root("Pure", signature);
        let context = crate::kernel::ProofContext::new(theory.snapshot().clone());
        let proposition = context
            .certify_prop(crate::kernel::RawTerm::const_("A", crate::kernel::Ty::prop()))
            .unwrap();
        let assumed =
            crate::kernel::KernelRules::assume(proposition.clone()).unwrap().into_kernel();
        let closed = crate::kernel::KernelRules::implies_intr(&proposition, &assumed)
            .unwrap()
            .try_close()
            .unwrap();
        let (_, accepted) =
            crate::kernel::accept_closed_theorem(&theory, "imp_identity", closed).unwrap();
        let legacy = ThmKernel::reflexive(checked_prop_ct("A")).unwrap();

        let outcome = classify_proof_outcome(
            "imp_identity",
            Some(accepted),
            Some((&legacy, VerifyOutcome::Proved)),
        );
        let mut stats = ProofOutcomeStats::default();
        stats.record(&outcome);

        assert!(outcome.is_kernel_trusted_closed());
        assert!(!outcome.is_transitional_strict_closed());
        assert_eq!(stats.kernel_trusted_closed, 1);
        assert_eq!(stats.transitional_strict_closed, 0);
        assert_eq!(stats.total(), 1);
        assert_eq!(
            stats.report_lines()[..2],
            ["KernelTrustedClosed: 1", "TransitionalStrictClosed: 0"]
        );
    }

    #[test]
    fn verification_results_keep_independent_legacy_exits() {
        let theorem = ThmKernel::reflexive(checked_prop_ct("A")).unwrap();
        let proved = LemmaVerification::from_legacy(Some(theorem.clone()), VerifyOutcome::Proved);
        let axiom = LemmaVerification::from_legacy(Some(theorem), VerifyOutcome::AxiomAccepted);

        let axiom_outcome = classify_verify_result("axiom", &axiom);
        let proved_outcome = classify_verify_result("proved", &proved);

        assert!(matches!(
            axiom_outcome,
            ProofOutcome::Admitted { reason: AdmitReason::AxiomAcceptedWithoutOracle, .. }
        ));
        assert!(matches!(proved_outcome, ProofOutcome::TransitionalStrictClosed { .. }));
    }

    #[test]
    fn proof_outcome_classifies_transitional_strict_closed() {
        let thm = ThmKernel::reflexive(checked_prop_ct("A")).unwrap();

        let outcome =
            classify_proof_outcome("strict_refl", None, Some((&thm, VerifyOutcome::Proved)));

        assert!(matches!(outcome, ProofOutcome::TransitionalStrictClosed { .. }));
        assert!(outcome.is_transitional_strict_closed());
    }

    #[test]
    fn proof_outcome_does_not_count_axiom_accepted_strict_result() {
        let thm = ThmKernel::reflexive(checked_prop_ct("A")).unwrap();

        let outcome = classify_proof_outcome(
            "accepted_strict",
            None,
            Some((&thm, VerifyOutcome::AxiomAccepted)),
        );

        assert!(matches!(
            outcome,
            ProofOutcome::Admitted { reason: AdmitReason::AxiomAcceptedWithoutOracle, .. }
        ));
        assert!(!outcome.is_transitional_strict_closed());
    }

    #[test]
    fn proof_outcome_classifies_compat_closed_oracle_free() {
        let thm = ThmKernel::reflexive_compat(CTerm::certify(Term::const_("a", Typ::base("nat"))));

        let outcome =
            classify_proof_outcome("compat_refl", None, Some((&thm, VerifyOutcome::Proved)));

        assert!(matches!(outcome, ProofOutcome::CompatClosedOracleFree { .. }));
        assert!(!outcome.is_transitional_strict_closed());
    }

    #[test]
    fn proof_outcome_classifies_open_oracle_free() {
        let thm = ThmKernel::assume_compat(prop_ct("A"));

        let outcome =
            classify_proof_outcome("open_assume", None, Some((&thm, VerifyOutcome::Proved)));

        assert!(matches!(
            outcome,
            ProofOutcome::OpenOracleFree { reason: OpenReason::UnknownHyps, .. }
        ));
        assert!(!outcome.is_transitional_strict_closed());
    }

    #[test]
    fn proof_outcome_classifies_admitted_reason() {
        let thm = ThmKernel::admit(prop_ct("A"), "admitted:proof_engine_failed");

        let outcome =
            classify_proof_outcome("admitted", None, Some((&thm, VerifyOutcome::AxiomAccepted)));

        assert!(matches!(
            outcome,
            ProofOutcome::Admitted { reason: AdmitReason::ProofEngineFailed, .. }
        ));
        assert!(!outcome.is_transitional_strict_closed());
    }

    #[test]
    fn test_apply_attributes_rule_format_is_admitted() {
        let a = Term::const_("A", Typ::base("prop"));
        let b = Term::const_("B", Typ::base("prop"));
        let imp = Pure::mk_implies(a, b);
        let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(imp)));
        let db = HolTheoremDb::new();

        let transformed = super::apply_attributes(thm, &[String::from("rule_format")], &db);

        assert!(!transformed.is_fully_proved());
        assert!(!transformed.is_closed_proved());
        assert!(transformed.hyps().is_empty());
        assert!(
            transformed.oracles().iter().any(|o| o.as_ref() == "admitted:attribute_transformation"),
            "attribute transformation must carry an oracle footprint: {:?}",
            transformed.oracles()
        );
    }

    #[test]
    fn test_verify_batch_does_not_count_open_theorem_as_verified() {
        let a = Term::const_("A", Typ::base("prop"));
        let goal = Pure::mk_implies(a.clone(), a.clone());
        let lem = ParsedLemma::new_synthetic(
            "target".into(),
            Vec::new(),
            Arc::new(ThmKernel::assume_compat(CTerm::certify(goal))),
            Some("by (rule open_rule)".into()),
            None,
        );

        let mut db = HolTheoremDb::new();
        db.by_name
            .insert("open_rule".into(), Arc::new(ThmKernel::assume_compat(CTerm::certify(a))));

        reset_verify_stats();
        let (verified, attempted) = verify_lemmas_batch(std::slice::from_ref(&lem), &db);

        assert_eq!(attempted, 1);
        assert_eq!(verified, 0, "open oracle-free theorem must not count as proved");
        assert_eq!(verify_stats(), (0, 1));
        let outcome_stats = verify_outcome_stats();
        assert_eq!(outcome_stats.kernel_trusted_closed, 0);
        assert_eq!(outcome_stats.transitional_strict_closed, 0);
        assert_eq!(outcome_stats.total(), 1);
    }

    #[test]
    fn test_prove_sym_equality() {
        // Verify sym theorem is in the database
        use crate::core::logic::Pure;
        let s = Term::free("s", Typ::base("nat"));
        let t = Term::free("t", Typ::base("nat"));
        let s_eq_t = Pure::mk_equals(Typ::base("nat"), s.clone(), t.clone());
        let db = HolTheoremDb::global();
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
        let assume_ab = ThmKernel::assume_compat(CTerm::certify(a_imp_b));
        let assume_a = ThmKernel::assume_compat(CTerm::certify(a));
        // implies_elim: from (A==>B) and A, get B
        let result = ThmKernel::implies_elim(&assume_ab, &assume_a).unwrap();
        // result: {A, A==>B} ⊢ B, nprems=0
        assert_eq!(result.nprems(), 0);
        // auto should also be able to do this
        let db = HolTheoremDb::global();
        let auto_result = prove_auto(&result, &[], db);
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
        let db = HolTheoremDb::global();
        let result = prove_auto(&state, &[], db);
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
        let db = HolTheoremDb::global();
        assert!(db.by_name.contains_key("sym"), "sym should be indexed");
        assert!(db.by_name.contains_key("trans"), "trans should be indexed");
        eprintln!("by_name contains {} theorems", db.by_name.len());
        // Check induction rules
        for name in &[
            "list_induct2",
            "list_induct3",
            "list_induct4",
            "list_induct2'",
            "length_induct",
            "induct_list012",
            "list_nonempty_induct",
            "nat_induct",
            "nat_induct0",
            "diff_induct",
            "nat_less_induct",
            "measure_induct",
            "full_nat_induct",
            "less_Suc_induct",
        ] {
            let status = if db.by_name.contains_key(*name) { "YES" } else { "NO" };
            eprintln!("  {} {}", status, name);
        }
        assert!(db.by_name.len() > 100, "should have many named theorems");
    }

    #[test]
    fn test_induct_rule_application() {
        let db = HolTheoremDb::global();
        let induct_rule = db.by_name.get("list_induct2").expect("list_induct2 should exist");
        let prop_str = format!("{:?}", induct_rule.prop().term());
        eprintln!(
            "list_induct2 nprems={}, prop head={}",
            induct_rule.nprems(),
            &prop_str[..prop_str.len().min(200)]
        );
        // Check if the prop has Pure.imp at top level
        let has_imp = prop_str.contains("Pure.imp");
        eprintln!("Has Pure.imp: {}", has_imp);
        // Also check a simpler lemma for comparison
        let sym = db.by_name.get("sym").expect("sym should exist");
        let sym_str = format!("{:?}", sym.prop().term());
        eprintln!("sym nprems={}, prop head={}", sym.nprems(), &sym_str[..sym_str.len().min(200)]);
        // Parse sym statement directly (ASCII form after convert_syntax)
        if let Some(parsed) = crate::isar::term_parser::parse_term("s = t ==> t = s") {
            let thm = ThmKernel::assume_compat(CTerm::certify(parsed.clone()));
            eprintln!("Parsed sym nprems={}", thm.nprems());
            eprintln!("Parsed sym term: {:?}", parsed);
        }
        // Check a simple A==>A
        let simple = crate::isar::term_parser::parse_term("A ==> A").unwrap();
        let simple_thm = ThmKernel::assume_compat(CTerm::certify(simple));
        eprintln!("Simple A==>A nprems={}", simple_thm.nprems());
        // Create a goal: [length xs = length ys] ==> (length xs = length ys)
        let xs = Term::free("xs", Typ::base("list"));
        let ys = Term::free("ys", Typ::base("list"));
        let eq_term = crate::core::logic::Pure::mk_equals(
            Typ::base("nat"),
            Term::app(Term::const_("length", Typ::dummy()), xs.clone()),
            Term::app(Term::const_("length", Typ::dummy()), ys.clone()),
        );
        let goal_imp = crate::core::logic::Pure::mk_implies(eq_term.clone(), eq_term.clone());
        let goal = ThmKernel::assume_compat(CTerm::certify(goal_imp));
        eprintln!("Goal: {} premises, concl={:?}", goal.nprems(), goal.concl());
        // Try resolve_tac
        let results = crate::core::tactic::resolve_tac(&[(**induct_rule).clone()], 0)(&goal);
        eprintln!("resolve_tac results: {} states", results.len());
        for r in &results {
            eprintln!("  result: {} premises, concl={:?}", r.nprems(), r.concl());
        }
        // If no results, try manual bicompose with debug
        if results.is_empty() {
            eprintln!("resolve_tac failed, trying manual bicompose...");
            eprintln!("  Rule concl: {:?}", induct_rule.concl());
            eprintln!("  Rule nprems: {}", induct_rule.nprems());
            if let Some(prem) = goal.prem(0) {
                eprintln!("  Goal prem: {:?}", prem);
                // Try matchers directly
                let env = crate::core::envir::Envir::empty(usize::max(
                    induct_rule.maxidx(),
                    goal.maxidx(),
                ));
                let match_result = crate::core::unify::matchers(
                    &env,
                    &induct_rule.concl(),
                    &prem,
                    &crate::core::unify::UnifyConfig::default(),
                );
                eprintln!("  Matchers result: {:?}", match_result.is_some());
            }
            let bicompose_result = ThmKernel::bicompose(true, induct_rule, &goal, 0);
            eprintln!("bicompose: {:?}", bicompose_result.is_some());
        }
    }

    #[test]
    fn test_exec_proof_by_assumption() {
        // A ==> A by assumption — pass assume(A) as external premise
        use crate::core::logic::Pure;
        let a = Term::const_("A", Typ::base("prop"));
        let goal_term = Pure::mk_implies(a.clone(), a.clone());
        // goal: {A==>A} ⊢ A==>A, nprems=1, subgoal=A
        let state = ThmKernel::assume_compat(CTerm::certify(goal_term));
        let assume_a = Arc::new(ThmKernel::assume_compat(CTerm::certify(a.clone())));
        let db = HolTheoremDb::new();
        let result = exec_proof(&state, "by assumption", &[assume_a], &db);
        assert!(result.is_some(), "exec_proof should succeed with premise");
        assert_eq!(result.unwrap().nprems(), 0);
    }

    #[test]
    fn test_debug_subst_name() {
        let hol_thy = include_str!("../../theories/HOL/HOL.thy");
        let lemmas = crate::hol::hol_loader::parse_lemmas(hol_thy);
        // Find lemmas named subst, refl, TrueI
        for name in &["subst", "refl", "TrueI", "iffD1", "iffD2"] {
            let found: Vec<_> = lemmas.iter().filter(|l| l.name.contains(name)).collect();
            eprintln!("Search '{}': {} matches", name, found.len());
            for lem in found.iter().take(3) {
                eprintln!(
                    "  name='{}', attr={:?}, proof={:?}",
                    lem.name, lem.attributes, lem.proof_script
                );
            }
        }
    }

    #[test]
    fn test_scan_all_theories() {
        let dir = "theories/HOL";
        let files = scan_theory_files(dir);
        eprintln!("Found {} .thy files", files.len());
        let lemmas = load_theory_files(&files);
        let total = lemmas.len();
        let with_proof: Vec<_> = lemmas.iter().filter(|l| l.proof_script.is_some()).collect();
        eprintln!("Loaded {} total lemmas, {} with proof scripts", total, with_proof.len());
        assert!(total > 2000, "should load many theorems");
    }

    #[test]
    #[ignore = "LazyLock DB re-init overflow with 15K theorems — pre-existing"]
    fn test_analyze_failures() {
        use std::collections::HashMap;
        let files: [(&str, &str); 5] = [
            ("HOL", include_str!("../../theories/HOL/HOL.thy")),
            ("Orderings", include_str!("../../theories/HOL/Orderings.thy")),
            ("Nat", include_str!("../../theories/HOL/Nat.thy")),
            ("Set", include_str!("../../theories/HOL/Set.thy")),
            ("List", include_str!("../../theories/HOL/List.thy")),
        ];
        let db = HolTheoremDb::global();
        let mut method_counts: HashMap<String, usize> = HashMap::new();
        let mut total_non_transitional = 0usize;
        for (_name, source) in &files {
            let lemmas = crate::hol::hol_loader::parse_lemmas(source);
            for lem in &lemmas {
                if lem.proof_script.is_none() {
                    continue;
                }
                let result = verify_lemma(lem, db);
                let outcome = classify_verify_result(&lem.name, &result);
                if outcome.is_transitional_strict_closed() {
                    continue;
                }
                total_non_transitional += 1;
                let proof = lem.proof_script.as_ref().unwrap();
                let category = if proof.starts_with("by auto") {
                    "by auto"
                } else if proof.starts_with("by blast") {
                    "by blast"
                } else if proof.starts_with("by simp") {
                    "by simp"
                } else if proof.starts_with("by (rule") {
                    "by (rule)"
                } else if proof.starts_with("by metis") {
                    "by metis"
                } else if proof.starts_with("by iprover") {
                    "by iprover"
                } else if proof.starts_with("proof (induct") {
                    "proof (induct)"
                } else if proof.starts_with("proof (induction") {
                    "proof (induction)"
                } else if proof.starts_with("proof (cases") {
                    "proof (cases)"
                } else if proof.starts_with("proof -") || proof == "proof-" {
                    "proof -"
                } else if proof.starts_with("proof") {
                    "proof (other)"
                } else if proof.starts_with("apply") {
                    "apply"
                } else {
                    proof.split_whitespace().next().unwrap_or("unknown")
                };
                *method_counts.entry(category.to_string()).or_insert(0) += 1;
            }
        }
        eprintln!("=== Non-transitional outcomes by proof method ===");
        let mut counts: Vec<_> = method_counts.iter().collect();
        counts.sort_by_key(|(_, c)| std::cmp::Reverse(**c));
        for (method, count) in &counts {
            eprintln!("  {}: {}", method, count);
        }
        eprintln!("Total non-transitional: {}", total_non_transitional);
    }
}

#[cfg(test)]
mod benchmark_tests {
    use super::diagnostics::bench_file;

    use super::*;

    #[test]
    fn core_batch_snapshot_reports_one_kernel_trusted_and_zero_transitional() {
        eprintln!("=== Full Core Benchmark ===");
        reset_verify_stats();
        let files = vec![
            ("HOL", include_str!("../../theories/HOL/HOL.thy")),
            ("Orderings", include_str!("../../theories/HOL/Orderings.thy")),
            ("Set", include_str!("../../theories/HOL/Set.thy")),
            ("Nat", include_str!("../../theories/HOL/Nat.thy")),
            ("List", include_str!("../../theories/HOL/List.thy")),
        ];

        let mut total_verified = 0usize;
        let mut total_attempted = 0usize;

        for (name, source) in &files {
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                bench_file(name, source, 25)
            }));
            match result {
                Ok((v, a, _)) => {
                    total_verified += v;
                    total_attempted += a;
                },
                Err(_) => {
                    eprintln!("  {}: OVERFLOWED (skipped)", name);
                },
            }
        }

        eprintln!(
            "=== TransitionalStrictClosed TOTAL: {}/{} ({:.1}%) ===",
            total_verified,
            total_attempted,
            if total_attempted > 0 {
                (total_verified as f64 / total_attempted as f64) * 100.0
            } else {
                0.0
            }
        );
        eprintln!("=== ProofOutcome ===");
        let outcome_stats = verify_outcome_stats();
        for line in outcome_stats.report_lines() {
            eprintln!("  {line}");
        }

        assert_eq!(total_attempted, 125, "sampled core theorem count changed");
        assert_eq!(total_verified, 0, "sampled TrueI must not also count as transitional");
        assert_eq!(outcome_stats.kernel_trusted_closed, 1);
        assert_eq!(outcome_stats.transitional_strict_closed, 0);
        assert_eq!(outcome_stats.total(), 125);
    }
}
