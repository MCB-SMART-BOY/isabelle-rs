//! Shared legacy proof export checks. This module grants no strict-kernel token.

use std::sync::Arc;

use crate::core::{
    error::KernelError,
    term::Term,
    thm::{CTerm, Hyps, KernelCheckMode, Thm, ThmKernel, ThmTrust},
    types::Typ,
};
use crate::hol::hol_loader::HolTheoremDb;

/// Failure to connect a real legacy derivation to its requested goal.
#[derive(Debug, Clone, thiserror::Error)]
pub enum GoalExportError {
    /// A tactic obligation remains unresolved.
    #[error("proof still has open subgoals")]
    OpenSubgoals,
    /// The candidate depends on an unproved oracle or admission.
    #[error("proof depends on an oracle or admission")]
    OracleOrAdmitted,
    /// Higher-order unification constraints remain unresolved.
    #[error("proof has unresolved unification pairs")]
    UnresolvedTpairs,
    /// The candidate uses hypotheses outside the actual local context.
    #[error("proof contains unauthorized hypotheses")]
    UnknownHypotheses,
    /// The complete proven proposition differs from the goal.
    #[error("proof proposition does not match the complete goal")]
    PropositionMismatch,
    /// A local assumption could not be exported.
    #[error("proof assumption discharge failed")]
    DischargeFailed,
    /// No executed proof has supplied a result.
    #[error("no actual proof result is available")]
    MissingProofResult,
    /// Separate subgoals have no checked composition into the original goal.
    #[error("subgoal composition is unsupported")]
    UnsupportedComposition,
    /// Compatibility data cannot authorize proof completion.
    #[error("proof result lacks strict checked construction")]
    UntrustedResult,
    /// A primitive rule or invariant check rejected the proof.
    #[error("proof kernel check failed: {source}")]
    Kernel { source: Arc<KernelError> },
    /// The source contains an unknown, malformed, or unsupported proof command.
    #[error("invalid or unsupported proof script at line {line}")]
    InvalidScript { line: usize },
}

impl GoalExportError {
    pub(crate) fn admitted_reason(&self) -> &'static str {
        match self {
            Self::OpenSubgoals => "admitted:goal_export_open_subgoals",
            Self::UnresolvedTpairs => "admitted:goal_export_unresolved_tpairs",
            Self::UnknownHypotheses => "admitted:goal_export_unknown_hyps",
            Self::PropositionMismatch => "admitted:goal_export_prop_mismatch",
            Self::DischargeFailed => "admitted:goal_export_discharge_failed",
            Self::OracleOrAdmitted
            | Self::MissingProofResult
            | Self::UnsupportedComposition
            | Self::UntrustedResult
            | Self::Kernel { .. }
            | Self::InvalidScript { .. } => "admitted:proof_engine_failed",
        }
    }
}

impl From<KernelError> for GoalExportError {
    fn from(source: KernelError) -> Self {
        Self::Kernel { source: Arc::new(source) }
    }
}

fn validate_result_burdens(result: &Thm) -> Result<(), GoalExportError> {
    if !result.oracles().is_empty() || result.trust_status() == ThmTrust::Admitted {
        return Err(GoalExportError::OracleOrAdmitted);
    }
    if !result.tpairs().is_empty() {
        return Err(GoalExportError::UnresolvedTpairs);
    }
    if result.trust_status() != ThmTrust::Strict
        || !result.prop().is_checked()
        || result.prop().contains_dummy_type()
        || result.hyps().iter().any(|hyp| !hyp.is_checked() || hyp.contains_dummy_type())
    {
        return Err(GoalExportError::UntrustedResult);
    }
    result.check_kernel_invariants(KernelCheckMode::Strict)?;
    Ok(())
}

fn has_allowed_hypotheses(result: &Thm, allowed: &[CTerm]) -> bool {
    result.hyps().iter().all(|hyp| {
        allowed.iter().any(|permission| {
            permission.is_checked() && Hyps::kernel_alpha_eq(hyp.term(), permission.term())
        })
    })
}

/// Validate an actual derivation of the entire proposition, not its conclusion.
pub fn validate_proof_result(
    expected: &Term,
    result: &Thm,
    allowed_hypotheses: &[CTerm],
) -> Result<(), GoalExportError> {
    validate_result_burdens(result)?;
    if !has_allowed_hypotheses(result, allowed_hypotheses) {
        return Err(GoalExportError::UnknownHypotheses);
    }
    if !Hyps::kernel_alpha_eq(expected, result.prop().term()) {
        return Err(GoalExportError::PropositionMismatch);
    }
    Ok(())
}

/// Discharge only assumptions and fixes introduced inside this goal's scope.
pub fn export_scoped_result(
    original_goal: &CTerm,
    result: &Thm,
    local_assumptions: &[CTerm],
    local_fixes: &[(String, Typ)],
    parent_allowed_hypotheses: &[CTerm],
) -> Result<Thm, GoalExportError> {
    original_goal.require_checked("export_scoped_result")?;
    validate_result_burdens(result)?;
    let is_authorized = result.hyps().iter().all(|hyp| {
        local_assumptions.iter().chain(parent_allowed_hypotheses).any(|allowed| {
            allowed.is_checked() && Hyps::kernel_alpha_eq(hyp.term(), allowed.term())
        })
    });
    if !is_authorized {
        return Err(GoalExportError::UnknownHypotheses);
    }
    if Hyps::kernel_alpha_eq(original_goal.term(), result.prop().term())
        && has_allowed_hypotheses(result, parent_allowed_hypotheses)
    {
        return Ok(result.clone());
    }
    let mut exported = result.clone();
    for assumption in local_assumptions.iter().rev() {
        match ThmKernel::implies_intr(assumption, &exported) {
            Ok(next) => exported = next,
            // An unused assumption contributes no proof burden to discharge.
            Err(KernelError::HypothesisNotFound) => {},
            Err(source) => return Err(source.into()),
        }
    }
    for (name, typ) in local_fixes.iter().rev() {
        exported = ThmKernel::forall_intr(name, typ.clone(), &exported)?;
    }
    validate_proof_result(original_goal.term(), &exported, parent_allowed_hypotheses)?;
    Ok(exported)
}

pub(crate) fn export_proved_goal(
    original_goal: &CTerm,
    result: &Thm,
    context_assumptions: &[CTerm],
) -> Result<Thm, GoalExportError> {
    export_scoped_result(original_goal, result, context_assumptions, &[], &[])
}

/// Execute only the named checked method; search fallback is not source semantics.
pub fn apply_goal_method(
    expected: &CTerm,
    method: &str,
    facts: &[Arc<Thm>],
    allowed_hypotheses: &[CTerm],
    db: &HolTheoremDb,
) -> Result<Option<Thm>, GoalExportError> {
    expected.require_checked("apply_goal_method")?;
    let parsed = parse_checked_method(method, db)?;
    if let CheckedMethod::Fact = parsed {
        return Ok(facts
            .iter()
            .find(|fact| validate_proof_result(expected.term(), fact, allowed_hypotheses).is_ok())
            .map(|fact| (**fact).clone()));
    }
    let CheckedMethod::Tactic(method) = parsed else {
        return Ok(None);
    };
    // The trivial theorem is a tactic obligation, never evidence for expected.
    let obligation = ThmKernel::trivial(expected.clone())?;
    Ok(method
        .execute(&obligation, facts, db)
        .into_iter()
        .find(|result| validate_proof_result(expected.term(), result, allowed_hypotheses).is_ok()))
}

enum CheckedMethod {
    Fact,
    Tactic(super::method::Method),
}

fn parse_checked_method(source: &str, db: &HolTheoremDb) -> Result<CheckedMethod, GoalExportError> {
    use super::{
        method::Method,
        token::{Lexer, TokenKind},
    };
    let invalid = || GoalExportError::InvalidScript { line: 1 };
    let tokens = Lexer::new(source).tokenize_checked().map_err(|_| invalid())?;
    let meaningful = tokens.iter().filter(|token| token.kind != TokenKind::EOF).collect::<Vec<_>>();
    let mut body = meaningful.as_slice();
    if body.first().is_some_and(|token| token.source == "(") {
        if !body.last().is_some_and(|token| token.source == ")") {
            return Err(invalid());
        }
        body = &body[1..body.len() - 1];
    }
    let [name, arguments @ ..] = body else {
        return Err(invalid());
    };
    let method = match (name.source.as_str(), arguments) {
        ("assumption" | "this" | ".", []) => return Ok(CheckedMethod::Fact),
        ("auto", []) => Method::Auto,
        ("blast", []) => Method::Blast,
        ("fast", []) => Method::Fast,
        ("best", []) => Method::Best,
        ("step", []) => Method::Step,
        ("metis", []) => Method::Metis,
        ("meson", []) => Method::Meson,
        ("fail" | "skip", []) => Method::Fail,
        ("simp", []) => {
            let rules = db
                .simps
                .iter()
                .filter_map(|fact| crate::core::simplifier::RewriteRule::from_thm(Arc::clone(fact)))
                .collect();
            Method::Simp(crate::core::simplifier::Simplifier::new(rules))
        },
        ("rule" | "erule" | "drule" | "frule" | "unfold" | "fold" | "insert", [_, ..]) => {
            parse_named_method(&name.source, arguments, db)?
        },
        _ => return Err(invalid()),
    };
    Ok(CheckedMethod::Tactic(method))
}

fn parse_named_method(
    name: &str,
    arguments: &[&super::token::Token],
    db: &HolTheoremDb,
) -> Result<super::method::Method, GoalExportError> {
    use super::{method::Method, token::TokenKind};
    let mut facts = Vec::with_capacity(arguments.len());
    for argument in arguments {
        if !matches!(argument.kind, TokenKind::Ident | TokenKind::LongIdent) {
            return Err(GoalExportError::InvalidScript { line: 1 });
        }
        let fact = db
            .by_name
            .get(&argument.source)
            .cloned()
            .ok_or(GoalExportError::InvalidScript { line: 1 })?;
        facts.push(fact);
    }
    Ok(match name {
        "rule" => Method::Rule(facts),
        "erule" => Method::Erule(facts),
        "drule" => Method::Drule(facts),
        "frule" => Method::Frule(facts),
        "unfold" => Method::Unfold(facts),
        "fold" => Method::Fold(facts),
        "insert" => Method::Insert(facts),
        _ => return Err(GoalExportError::InvalidScript { line: 1 }),
    })
}
