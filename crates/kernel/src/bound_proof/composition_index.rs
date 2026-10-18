//! Capture-free schematic index shifting over the complete replayed rule proof.
use std::collections::BTreeMap;

use crate::{
    CProp, CTerm, DependencySet, Derivation, InstEntry, KernelError, KernelRules, KernelThm,
    ProofContext, Term, TrustedTheory, Ty, TypeInstantiation, TypeVarId,
};

use super::{
    BoundProof, BoundProofError, Sources, check, inspect::ProofVariables, lower, terms, transform,
};
impl KernelRules {
    /// Rename schematic identities in the complete replayed proof. A local
    /// theorem must first leave its fixed-type scope via `export_scope`.
    pub fn incr_indexes(
        owner: &TrustedTheory,
        context: &ProofContext,
        theorem: &KernelThm,
        increment: usize,
    ) -> Result<KernelThm, KernelError> {
        let mut dependencies = DependencySet::empty();
        let source =
            crate::invariant::replay_source_in(owner, context, theorem, &mut dependencies)?;
        if increment == 0 {
            return Ok(source);
        }
        freshen_rule(owner, context, &source, increment)
    }
}

pub(super) fn collect_source_variables(rule: &KernelThm) -> Result<ProofVariables, KernelError> {
    let sources = Sources::collect(rule);
    let proof = lower::lower_theorem(rule, &sources)?;
    let mut variables = ProofVariables::collect(&proof);
    variables.visit_term(rule.prop().term());
    for hyp in rule.hyps() {
        variables.visit_term(hyp.term());
    }
    for (left, right) in rule.payload().flex_pairs() {
        variables.visit_term(left.term());
        variables.visit_term(right.term());
    }
    for (ty, _) in rule.payload().sort_obligations() {
        variables.visit_type(ty);
    }
    Ok(variables)
}

fn prepare_type_indices(
    variables: &ProofVariables,
    increment: usize,
) -> Result<TypeInstantiation, KernelError> {
    let mut bindings = BTreeMap::new();
    for atom in &variables.atoms {
        let mut keys = Vec::new();
        atom.for_each_type_var(&mut |name, index, sort| {
            keys.push((name.clone(), index, sort.clone()));
        });
        for (name, index, sort) in keys {
            let shifted = index.checked_add(increment).ok_or(BoundProofError::IndexOverflow)?;
            let source = TypeVarId::new(
                name.clone(),
                u32::try_from(index).map_err(|_| KernelError::TypeVariableIndexOutOfRange {
                    name: name.clone(),
                    index,
                })?,
                sort.clone(),
            );
            let replacement = Ty::tvar(name.clone(), shifted, sort);
            replacement.validate_type_variable()?;
            bindings.insert(source, replacement);
        }
    }
    TypeInstantiation::try_new(bindings)
}

fn prepare_term_indices(
    context: &ProofContext,
    variables: &ProofVariables,
    type_inst: &TypeInstantiation,
    increment: usize,
) -> Result<Vec<InstEntry>, KernelError> {
    let mut entries = Vec::with_capacity(variables.vars.len());
    for (name, index, ty) in &variables.vars {
        let shifted = index.checked_add(increment).ok_or(BoundProofError::IndexOverflow)?;
        let typed = ty.subst_type_vars(type_inst)?;
        let replacement = CTerm::from_certified_subterm(
            Term::Var { name: name.clone(), index: shifted, ty: typed.clone() },
            context.stamp(),
        );
        context.validate_cterm(&replacement)?;
        entries.push(InstEntry::new(name.clone(), *index, ty.clone(), replacement));
    }
    Ok(entries)
}

fn rename_flex_pairs(
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
            let rename = |original: &CTerm| -> Result<CTerm, KernelError> {
                let term =
                    terms::instantiate_source_order_raw(original.term(), 0, types, substitutions)?;
                let certified = CTerm::from_certified_subterm(term, context.stamp());
                context.validate_cterm(&certified)?;
                Ok(certified)
            };
            let pair = (rename(left)?, rename(right)?);
            if pair.0.ty() != pair.1.ty() {
                return Err(KernelError::TypeMismatch {
                    expected: pair.0.ty(),
                    actual: pair.1.ty(),
                });
            }
            Ok(pair)
        })
        .collect()
}

pub(crate) fn replay_index_rename(
    owner: &TrustedTheory,
    context: &ProofContext,
    source: KernelThm,
    increment: usize,
    expected: Option<&BoundProof>,
) -> Result<(KernelThm, DependencySet), KernelError> {
    if increment == 0 {
        return Err(BoundProofError::IndexOverflow.into());
    }
    let variables = collect_source_variables(&source)?;
    let types = prepare_type_indices(&variables, increment)?;
    context.validate_type_instantiation(&types)?;
    let substitutions = prepare_term_indices(context, &variables, &types, increment)?;
    let proposition =
        terms::instantiate_source_order_raw(source.prop().term(), 0, &types, &substitutions)?;
    let hyps = source
        .hyps()
        .iter()
        .map(|hyp| {
            let term = terms::instantiate_source_order_raw(hyp.term(), 0, &types, &substitutions)?;
            if !term.alpha_eq(hyp.term()) {
                return Err(KernelError::SchematicHypothesis);
            }
            Ok(hyp.clone())
        })
        .collect::<Result<Vec<CProp>, KernelError>>()?;
    let flex_pairs = rename_flex_pairs(context, &source, &types, &substitutions)?;
    let sources = Sources::collect(&source);
    let proof = transform::rename_source_indices(
        lower::lower_theorem(&source, &sources)?,
        &types,
        &substitutions,
    )?;
    if expected.is_some_and(|recorded| recorded.root != proof) {
        return Err(BoundProofError::StatementMismatch.into());
    }
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
    if !checked.alpha_eq(&Term::mk_imp_chain(&target_hyps, &proposition)?) {
        return Err(BoundProofError::StatementMismatch.into());
    }
    let certified = crate::thm::prop_from_term(proposition, context.stamp());
    let payload = crate::obligations::ProofPayload::rename_source_indices(
        source.payload(),
        &hyps,
        &certified,
        flex_pairs,
    );
    if !sorts.is_subset(payload.shyps()) {
        return Err(BoundProofError::StatementMismatch.into());
    }
    let result = KernelThm::new_with_payload(
        hyps,
        certified,
        payload,
        Derivation::SourceRenameIndex {
            increment,
            premise: Box::new(source),
            proof: BoundProof { root: proof },
        },
    );
    Ok((result, dependencies))
}
/// Shift indices in P, F and proof-only operands; retain C unchanged.
pub(super) fn freshen_rule(
    owner: &TrustedTheory,
    context: &ProofContext,
    rule: &KernelThm,
    increment: usize,
) -> Result<KernelThm, KernelError> {
    if increment == 0 {
        return Ok(rule.clone());
    }
    let shifted = replay_index_rename(owner, context, rule.clone(), increment, None)?.0;
    let requested = rule
        .max_var_index()
        .map(|index| index.checked_add(increment).ok_or(BoundProofError::IndexOverflow))
        .transpose()?;
    let shifted = KernelRules::adjust_max_index(&shifted, requested);
    let mut dependencies = crate::DependencySet::empty();
    crate::invariant::replay_source_in(owner, context, &shifted, &mut dependencies)
}
