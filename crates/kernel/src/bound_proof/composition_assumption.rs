//! Assumption with a finite unifier proposal; eq_assumption remains exact matching.
use crate::{
    CTerm, DependencySet, Derivation, InstEntry, KernelError, KernelRules, KernelThm, ProofContext,
    Term, TrustedTheory,
};

use super::{
    BoundProof, BoundProofError, Sources, check, composition, composition_env, composition_index,
    source_instantiate,
};

fn validate_assumption_substitutions(
    source: &KernelThm,
    assignments: &[InstEntry],
) -> Result<(), KernelError> {
    let variables = composition_index::collect_source_variables(source)?;
    for assignment in assignments {
        let key = (assignment.name().clone(), assignment.index(), assignment.var_ty().clone());
        if !variables.vars.contains(&key) {
            return Err(BoundProofError::AbsentAssignment { name: key.0, index: key.1 }.into());
        }
    }
    Ok(())
}

/// Distinct source and residual proof slots from the recorded assumption step.
pub(crate) struct AssumptionReplay<'a> {
    pub selected: usize,
    pub choice: usize,
    pub source_assumptions: usize,
    pub residual: &'a [(CTerm, CTerm)],
    pub proof: &'a BoundProof,
}

pub(crate) fn replay_assumption(
    owner: &TrustedTheory,
    context: &ProofContext,
    source: KernelThm,
    replay: AssumptionReplay<'_>,
) -> Result<(KernelThm, DependencySet), KernelError> {
    let AssumptionReplay { selected, choice, source_assumptions, residual, proof } = replay;
    for (left, right) in residual {
        context.validate_cterm(left)?;
        context.validate_cterm(right)?;
        if left.ty() != right.ty() {
            return Err(KernelError::TypeMismatch { expected: left.ty(), actual: right.ty() });
        }
    }
    let (outer, _) = source.prop().term().dest_imp_chain();
    let goal = outer.get(selected).ok_or(BoundProofError::SelectedSubgoalOutOfRange {
        index: selected,
        nprems: outer.len(),
    })?;
    if source_assumptions > composition::count_outer_assumptions(goal) {
        return Err(BoundProofError::InvalidEliminationChoice { choice }.into());
    }
    let (proposition, expected_proof) = composition::build_assumption_proof(
        &source,
        selected,
        choice,
        residual,
        Some(source_assumptions),
        false,
    )?;
    if proof != &expected_proof {
        return Err(BoundProofError::StatementMismatch.into());
    }
    let sources = Sources::collect(&source);
    let (checked, mut sorts, mut dependencies) = check::check_closed_with_source(
        context,
        owner,
        &sources,
        &proof.root,
        check::CheckTransport {
            source: source.prop().term(),
            target: &proposition,
            is_canonical_adapter: true,
            flex_pairs: residual,
        },
    )?;
    let hyps = source.hyps().to_vec();
    let expected = Term::mk_imp_chain(
        &hyps.iter().map(|hyp| hyp.term().clone()).collect::<Vec<_>>(),
        &proposition,
    )?;
    if !checked.alpha_eq(&expected) {
        return Err(BoundProofError::StatementMismatch.into());
    }
    let (used_sorts, used_dependencies) = composition::check_source_flex(
        owner,
        context,
        &sources,
        source.payload().flex_pairs(),
        residual,
        "assumption F",
        source.prop().term(),
    )?;
    sorts.extend(used_sorts);
    dependencies.extend(&used_dependencies);
    let certified = crate::thm::prop_from_term(proposition, context.stamp());
    let payload = crate::obligations::ProofPayload::with_residual_flex(
        source.payload(),
        residual,
        &hyps,
        &certified,
    );
    if !sorts.is_subset(payload.shyps()) {
        return Err(BoundProofError::StatementMismatch.into());
    }
    let result = KernelThm::new_with_payload(
        hyps,
        certified,
        payload,
        Derivation::Assumption {
            state: Box::new(source),
            selected,
            choice,
            source_assumptions,
            residual_pairs: residual.to_vec(),
            proof: proof.clone(),
        },
    );
    Ok((result, dependencies))
}

impl KernelRules {
    /// Check one finite assumption unifier against a selected goal (one-based `i`).
    /// The candidate's state assignments are checked on the complete source DAG;
    /// unresolved equations remain in F and cannot be sealed as a theorem.
    pub fn assumption_candidate(
        owner: &TrustedTheory,
        context: &ProofContext,
        i: usize,
        state: &KernelThm,
        candidate: &super::CompositionCandidate,
    ) -> Result<KernelThm, KernelError> {
        let selected = i.checked_sub(1).ok_or(KernelError::SubgoalIndexOutOfRange {
            index: i,
            nprems: state.prop().term().nprems(),
        })?;
        if let Some(first) = candidate.rule_subst.first() {
            return Err(BoundProofError::AbsentAssignment {
                name: first.name().clone(),
                index: first.index(),
            }
            .into());
        }
        let source = composition::replay_current_source(owner, context, state)?;
        let (original_premises, _) = source.prop().term().dest_imp_chain();
        let original_goal =
            original_premises.get(selected).ok_or(KernelError::SubgoalIndexOutOfRange {
                index: i,
                nprems: original_premises.len(),
            })?;
        let source_assumption_count = composition::count_outer_assumptions(original_goal);
        validate_assumption_substitutions(&source, &candidate.state_subst)?;
        let types = composition_env::normalize_types(context, &candidate.type_inst)?;
        let assignments =
            composition_env::normalize_terms(context, &types, &[], &candidate.state_subst)?;
        validate_assumption_substitutions(&source, &assignments)?;
        let source = if types.iter().next().is_none() && assignments.is_empty() {
            source
        } else {
            source_instantiate::replay_source_instantiation(
                owner,
                context,
                source,
                &types,
                &assignments,
            )?
            .0
        };
        let (premises, _) = source.prop().term().dest_imp_chain();
        let goal = premises
            .get(selected)
            .ok_or(KernelError::SubgoalIndexOutOfRange { index: i, nprems: premises.len() })?;
        let (_, choice, _) = composition::inspect_assumption_spine(
            goal,
            candidate.elimination_choice,
            &candidate.residual_pairs,
            Some(source_assumption_count),
            false,
        )?;
        let (_, proof) = composition::build_assumption_proof(
            &source,
            selected,
            choice,
            &candidate.residual_pairs,
            Some(source_assumption_count),
            false,
        )?;
        Ok(replay_assumption(
            owner,
            context,
            source,
            AssumptionReplay {
                selected,
                choice,
                source_assumptions: source_assumption_count,
                residual: &candidate.residual_pairs,
                proof: &proof,
            },
        )?
        .0)
    }
}
