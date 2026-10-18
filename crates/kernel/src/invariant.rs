mod derive;
mod rebuild;
mod replay_environment;
#[cfg(test)]
mod variable_attacks;
#[cfg(test)]
mod variable_scope_attacks;

use rebuild::ReplayFrame;
use replay_environment::ReplayEnvironment;

use super::{
    CProp, CTerm, ContextStamp, Derivation, InstEntry, KernelError, KernelThm, ProofContext,
    obligations::ProofPayload,
    theory::{DependencySet, TrustedTheory},
};

/// Canonical result reconstructed by owner-parameterized accepting replay.
pub(crate) struct ReplayResult {
    context: ContextStamp,
    hyps: Vec<CProp>,
    prop: CProp,
    dependencies: DependencySet,
    payload: ProofPayload,
    max_index: Option<usize>,
}

impl ReplayResult {
    fn from_kernel(theorem: KernelThm, dependencies: DependencySet) -> Self {
        Self {
            context: theorem.context(),
            hyps: theorem.hyps().to_vec(),
            prop: theorem.prop().clone(),
            payload: theorem.payload().clone(),
            dependencies,
            max_index: theorem.max_var_index(),
        }
    }

    pub(crate) fn context(&self) -> ContextStamp {
        self.context
    }

    pub(crate) fn hyps(&self) -> &[CProp] {
        &self.hyps
    }

    pub(crate) fn prop(&self) -> &CProp {
        &self.prop
    }
    pub(crate) fn payload(&self) -> &ProofPayload {
        &self.payload
    }
    pub(crate) fn max_var_index(&self) -> Option<usize> {
        self.max_index
    }

    pub(crate) fn dependencies(&self) -> &DependencySet {
        &self.dependencies
    }
}

fn require_same_context(expected: ContextStamp, actual: ContextStamp) -> Result<(), KernelError> {
    if expected != actual {
        return Err(KernelError::MixedContext {
            expected: Box::new(expected),
            actual: Box::new(actual),
        });
    }
    Ok(())
}

fn preflight_substitution_contexts(
    expected: ContextStamp,
    subst: &[InstEntry],
) -> Result<(), KernelError> {
    for entry in subst {
        require_same_context(expected, entry.replacement().context())?;
    }
    Ok(())
}

fn validate_cprop(
    expected: ContextStamp,
    validator: Option<&ReplayEnvironment>,
    prop: &CProp,
) -> Result<(), KernelError> {
    require_same_context(expected, prop.context())?;
    if let Some(context) = validator {
        context.validate_cprop(prop, false)?;
    } else if !prop.term().ty().is_prop() {
        return Err(KernelError::NotProposition(prop.term().ty()));
    }
    Ok(())
}

fn validate_cterm(
    expected: ContextStamp,
    validator: Option<&ReplayEnvironment>,
    term: &CTerm,
) -> Result<(), KernelError> {
    require_same_context(expected, term.context())?;
    if let Some(context) = validator {
        context.validate_cterm(term)?;
    }
    Ok(())
}

fn validate_substitution(
    expected: ContextStamp,
    validator: Option<&ReplayEnvironment>,
    subst: &[InstEntry],
) -> Result<(), KernelError> {
    preflight_substitution_contexts(expected, subst)?;
    for entry in subst {
        validate_cterm(expected, validator, entry.replacement())?;
        if entry.replacement().ty() != *entry.var_ty() {
            return Err(KernelError::TypeMismatch {
                expected: entry.var_ty().clone(),
                actual: entry.replacement().ty(),
            });
        }
    }
    Ok(())
}

fn validate_theorem_fields(
    expected: ContextStamp,
    validator: Option<&ReplayEnvironment>,
    theorem: &KernelThm,
) -> Result<(), KernelError> {
    require_same_context(expected, theorem.context())?;
    if theorem.prop().context() != expected {
        return Err(if validator.is_some() {
            KernelError::MixedContext {
                expected: Box::new(expected),
                actual: Box::new(theorem.prop().context()),
            }
        } else {
            KernelError::Invariant("theorem context does not match proposition context".into())
        });
    }
    for hypothesis in theorem.hyps() {
        if hypothesis.context() != expected {
            return Err(if validator.is_some() {
                KernelError::MixedContext {
                    expected: Box::new(expected),
                    actual: Box::new(hypothesis.context()),
                }
            } else {
                KernelError::Invariant("theorem context does not match hypothesis context".into())
            });
        }
    }

    validate_proposition_mode(expected, validator, theorem)?;
    for hypothesis in theorem.hyps() {
        validate_cprop(expected, validator, hypothesis)?;
        if hypothesis.term().has_schematic_hypothesis() {
            return Err(KernelError::SchematicHypothesis);
        }
    }
    for (left, right) in theorem.payload().flex_pairs() {
        validate_cterm(expected, validator, left)?;
        validate_cterm(expected, validator, right)?;
        if left.ty() != right.ty() {
            return Err(KernelError::TypeMismatch { expected: left.ty(), actual: right.ty() });
        }
    }
    if let Some(context) = validator {
        for (ty, _) in theorem.payload().sort_obligations() {
            context.context.validate_type(ty)?;
        }
    }
    if theorem.max_var_index() < theorem.observed_max_var_index() {
        return Err(KernelError::Invariant(
            "declared theorem max index is smaller than an actual payload index".into(),
        ));
    }
    if validator.is_some() {
        ProofContext::validate_theorem_type_identities(
            theorem.prop(),
            theorem.hyps(),
            theorem.payload().flex_pairs(),
        )?;
    }
    Ok(())
}

fn validate_proposition_mode(
    expected: ContextStamp,
    validator: Option<&ReplayEnvironment>,
    theorem: &KernelThm,
) -> Result<(), KernelError> {
    if !matches!(theorem.payload().mode(), crate::obligations::ProofMode::SortErased) {
        return validate_cprop(expected, validator, theorem.prop());
    }
    // Scheme-sort erasure is certified by the originating export replay;
    // it does not exempt the resulting term from structural validation.
    if let Some(context) = validator {
        context.validate_cprop(theorem.prop(), true)
    } else if theorem.prop().term().ty().is_prop() {
        Ok(())
    } else {
        Err(KernelError::NotProposition(theorem.prop().term().ty()))
    }
}

fn collect_const_term_evidence(
    owner: &TrustedTheory,
    term: &super::Term,
    is_erased: bool,
    dependencies: &mut DependencySet,
) -> Result<(), KernelError> {
    term.visit_const_occurrences(&mut |name, ty| {
        if is_erased && owner.signature().certify_const_instance(name, ty).is_err() {
            // The source-replayed export transport alone authorizes this use;
            // validate_sort_erased_cprop already rejected monomorphic mismatch.
            return Ok(());
        }
        let evidence = crate::class_proof::certify_const_scheme_evidence(owner, name, ty, &[])?;
        dependencies.extend(evidence.dependencies());
        Ok(())
    })
}

fn collect_const_dependencies(
    owner: &TrustedTheory,
    theorem: &KernelThm,
    dependencies: &mut DependencySet,
) -> Result<(), KernelError> {
    let is_erased = matches!(theorem.payload().mode(), crate::obligations::ProofMode::SortErased);
    collect_const_term_evidence(owner, theorem.prop().term(), is_erased, dependencies)?;
    for hypothesis in theorem.hyps() {
        collect_const_term_evidence(owner, hypothesis.term(), false, dependencies)?;
    }
    for (left, right) in theorem.payload().flex_pairs() {
        collect_const_term_evidence(owner, left.term(), false, dependencies)?;
        collect_const_term_evidence(owner, right.term(), false, dependencies)?;
    }
    Ok(())
}

fn collect_recorded_operand_dependencies(
    owner: &TrustedTheory,
    derivation: &Derivation,
    dependencies: &mut DependencySet,
) -> Result<(), KernelError> {
    let mut collect =
        |term: &super::Term| collect_const_term_evidence(owner, term, false, dependencies);
    match derivation {
        Derivation::Assume { prop }
        | Derivation::Weaken { assumption: prop, .. }
        | Derivation::ImpliesIntr { assumption: prop, .. } => collect(prop.term())?,
        Derivation::Reflexive { term }
        | Derivation::BetaConversion { redex: term }
        | Derivation::EtaConversion { redex: term }
        | Derivation::ForallIntr { variable: term, .. }
        | Derivation::ForallElim { arg: term, .. } => collect(term.term())?,
        Derivation::LiftRule { goal, .. } => collect(goal.term())?,
        Derivation::Instantiate { subst, .. }
        | Derivation::SourceInstantiate { subst, .. }
        | Derivation::Resolve1Match { subst, .. } => {
            for entry in subst {
                collect(entry.replacement().term())?;
            }
        },
        Derivation::AxiomInstance { term_inst, .. } => {
            for term in term_inst {
                collect(term.term())?;
            }
        },
        _ => {},
    }
    Ok(())
}

fn rebuild_premise(
    expected: ContextStamp,
    validator: Option<&ProofContext>,
    dependencies: &mut DependencySet,
    theorem: &KernelThm,
    logic_basis: Option<&super::LogicBasis>,
    owner: Option<&TrustedTheory>,
) -> Result<KernelThm, KernelError> {
    let environment = validator.map(ReplayEnvironment::new);
    let frame = ReplayFrame { expected, environment: environment.as_ref(), logic_basis, owner };
    Ok(frame.rebuild(dependencies, theorem)?.theorem)
}

/// Structural diagnostic replay. It proves no owning-theory authorization and
/// cannot construct a [`super::TrustedTheorem`].
pub fn check_kernel_thm(theorem: &KernelThm) -> Result<(), KernelError> {
    let mut dependencies = DependencySet::empty();
    rebuild_premise(theorem.context(), None, &mut dependencies, theorem, None, None)?;
    Ok(())
}

/// Rebuild an open source under its exact owner before a proof transformation.
pub(crate) fn replay_source_in(
    owner: &TrustedTheory,
    context: &ProofContext,
    theorem: &KernelThm,
    dependencies: &mut DependencySet,
) -> Result<KernelThm, KernelError> {
    require_same_context(owner.stamp(), context.stamp())?;
    rebuild_premise(
        context.stamp(),
        Some(context),
        dependencies,
        theorem,
        owner.logic_basis(),
        Some(owner),
    )
}

/// Replay a kernel-issued local capsule only in its exact owning world.
pub(crate) fn replay_scoped_source_in(
    owner: &TrustedTheory,
    context: &ProofContext,
    theorem: &KernelThm,
    dependencies: &mut DependencySet,
) -> Result<KernelThm, KernelError> {
    require_same_context(owner.stamp(), context.theory().stamp())?;
    rebuild_premise(
        context.stamp(),
        Some(context),
        dependencies,
        theorem,
        owner.logic_basis(),
        Some(owner),
    )
}

/// Replay one closed candidate under the exact immutable owner context.
pub(crate) fn replay_closed_theorem_in(
    theory: &TrustedTheory,
    theorem: &super::ClosedThm,
) -> Result<ReplayResult, KernelError> {
    let expected = theory.stamp();
    let validator = ProofContext::new(theory.snapshot().clone());
    let environment = ReplayEnvironment::new(&validator);
    theorem
        .as_kernel()
        .payload()
        .validate_closed(theorem.as_kernel().prop(), theorem.as_kernel().hyps())?;
    // Final accepted data is certified with no lexical or capsule permissions.
    validate_theorem_fields(expected, Some(&environment), theorem.as_kernel())?;
    let mut dependencies = DependencySet::empty();
    let replayed = rebuild_premise(
        expected,
        Some(&validator),
        &mut dependencies,
        theorem.as_kernel(),
        theory.logic_basis(),
        Some(theory),
    )?;
    replayed.payload().validate_closed(replayed.prop(), replayed.hyps())?;
    Ok(ReplayResult::from_kernel(replayed, dependencies))
}
