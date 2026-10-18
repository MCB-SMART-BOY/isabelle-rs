//! Replay a recursive unifier environment without conflating original typed keys.
use crate::{
    CProp, CTerm, DependencySet, Derivation, InstEntry, KernelError, KernelThm, ProofContext,
    TrustedTheory, TypeInstantiation,
};

use super::{BoundProofError, Sources, check, composition_index, lower, terms, transform};

fn validate_source_entries(
    context: &ProofContext,
    source: &KernelThm,
    types: &TypeInstantiation,
    substitutions: &[InstEntry],
) -> Result<(), KernelError> {
    context.validate_type_instantiation(types)?;
    let variables = composition_index::collect_source_variables(source)?;
    let mut seen = std::collections::BTreeSet::new();
    for entry in substitutions {
        let key = (entry.name().clone(), entry.index(), entry.var_ty().clone());
        if !seen.insert(key.clone()) {
            return Err(KernelError::DuplicateSubstitution { name: key.0, index: key.1 });
        }
        if !variables.vars.contains(&key) {
            return Err(BoundProofError::AbsentAssignment { name: key.0, index: key.1 }.into());
        }
        context.validate_cterm(entry.replacement())?;
        let expected = entry.var_ty().subst_type_vars(types)?;
        if entry.replacement().ty() != expected {
            return Err(KernelError::TypeMismatch { expected, actual: entry.replacement().ty() });
        }
    }
    Ok(())
}

fn transform_flex_pairs(
    context: &ProofContext,
    source: &KernelThm,
    types: &TypeInstantiation,
    substitutions: &[InstEntry],
) -> Result<Vec<(CTerm, CTerm)>, KernelError> {
    source
        .payload()
        .flex_pairs()
        .iter()
        .map(|(left, right)| {
            let convert = |original: &CTerm| -> Result<CTerm, KernelError> {
                let term =
                    terms::instantiate_source_order(original.term(), 0, types, substitutions)?;
                let certified = CTerm::from_certified_subterm(term, context.stamp());
                context.validate_cterm(&certified)?;
                Ok(certified)
            };
            let converted = (convert(left)?, convert(right)?);
            if converted.0.ty() != converted.1.ty() {
                return Err(KernelError::TypeMismatch {
                    expected: converted.0.ty(),
                    actual: converted.1.ty(),
                });
            }
            Ok(converted)
        })
        .collect()
}

pub(crate) fn replay_source_instantiation(
    owner: &TrustedTheory,
    context: &ProofContext,
    source: KernelThm,
    types: &TypeInstantiation,
    substitutions: &[InstEntry],
) -> Result<(KernelThm, DependencySet), KernelError> {
    validate_source_entries(context, &source, types, substitutions)?;
    let proposition =
        terms::instantiate_source_order(source.prop().term(), 0, types, substitutions)?;
    let hyps = source
        .hyps()
        .iter()
        .map(|hyp| {
            let term = terms::instantiate_source_order(hyp.term(), 0, types, substitutions)?;
            if !term.alpha_eq(hyp.term()) {
                return Err(KernelError::SchematicHypothesis);
            }
            Ok(hyp.clone())
        })
        .collect::<Result<Vec<CProp>, KernelError>>()?;
    let flex_pairs = transform_flex_pairs(context, &source, types, substitutions)?;
    let sources = Sources::collect(&source);
    let original = lower::lower_theorem(&source, &sources)?;
    let proof = super::source_normalize::normalize_source_proof(
        context,
        owner,
        &sources,
        transform::instantiate_source_order(original, types, substitutions)?,
        source.prop().term(),
        &proposition,
        &flex_pairs,
    )?;
    let (checked, sorts, dependencies) = check::check_closed_with_source(
        context,
        owner,
        &sources,
        &proof,
        check::CheckTransport {
            source: source.prop().term(),
            target: &proposition,
            is_canonical_adapter: true,
            flex_pairs: &flex_pairs,
        },
    )?;
    let target_hyps: Vec<_> = hyps.iter().map(|hyp| hyp.term().clone()).collect();
    let expected = crate::Term::mk_imp_chain(&target_hyps, &proposition)?;
    if !checked.alpha_eq(&expected) {
        return Err(BoundProofError::StatementMismatch.into());
    }
    let certified = crate::thm::prop_from_term(proposition, context.stamp());
    let payload = crate::obligations::ProofPayload::instantiate_source_order(
        source.payload(),
        types,
        substitutions,
        &hyps,
        &certified,
        flex_pairs,
    )?;
    if !sorts.is_subset(payload.shyps()) {
        return Err(BoundProofError::StatementMismatch.into());
    }
    let result = KernelThm::new_with_payload(
        hyps,
        certified,
        payload,
        Derivation::SourceInstantiate {
            type_inst: types.clone(),
            subst: substitutions.to_vec(),
            premise: Box::new(source),
            proof: super::BoundProof { root: proof },
        },
    );
    Ok((result, dependencies))
}
