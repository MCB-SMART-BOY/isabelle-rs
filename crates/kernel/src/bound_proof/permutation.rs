//! Pure premise permutations are adapters over a replayed source proof, not
//! theorem constructors. Every reordered premise is discharged by its own
//! lexical proof slot, including when propositions happen to be identical.
use std::sync::Arc;

use crate::{KernelError, KernelRules, KernelThm, Name, ProofContext, Term, TrustedTheory, Ty};

use super::{BoundProof, BoundProofError, Node, Proof, Sources, check, lower};

impl KernelRules {
    /// Rotate the outer implication tail, leaving its first `fixed` premises untouched.
    /// A negative rotation `k` denotes `tail.len() + k` (not modular arithmetic).
    pub fn permute_prems(
        owner: &TrustedTheory,
        context: &ProofContext,
        theorem: &KernelThm,
        fixed: usize,
        rotation: isize,
    ) -> Result<KernelThm, KernelError> {
        let mut dependencies = crate::DependencySet::empty();
        crate::invariant::replay_source_in(owner, context, theorem, &mut dependencies)?;
        let (proposition, proof) = build_permutation(theorem, fixed, rotation)?;
        Ok(check_candidate(owner, context, theorem, proposition, proof, true, |source, proof| {
            crate::Derivation::PermutePrems { premise: Box::new(source), fixed, rotation, proof }
        })?
        .0)
    }

    /// Rotate only the selected outer subgoal's leading foralls and implication chain.
    /// The selected subgoal index is zero-based; other outer premises stay in place.
    pub fn rotate_rule(
        owner: &TrustedTheory,
        context: &ProofContext,
        theorem: &KernelThm,
        selected_subgoal_index: usize,
        rotation: isize,
    ) -> Result<KernelThm, KernelError> {
        let mut dependencies = crate::DependencySet::empty();
        crate::invariant::replay_source_in(owner, context, theorem, &mut dependencies)?;
        let (proposition, proof) = build_rotation(theorem, selected_subgoal_index, rotation)?;
        Ok(check_candidate(owner, context, theorem, proposition, proof, true, |source, proof| {
            crate::Derivation::RotateRule {
                premise: Box::new(source),
                selected_subgoal_index,
                rotation,
                proof,
            }
        })?
        .0)
    }
}

pub(crate) fn replay_permutation(
    owner: &TrustedTheory,
    context: &ProofContext,
    source: KernelThm,
    fixed: usize,
    rotation: isize,
    proof: &BoundProof,
) -> Result<(KernelThm, crate::DependencySet), KernelError> {
    let (proposition, expected) = build_permutation(&source, fixed, rotation)?;
    let is_canonical_adapter = proof == &expected;
    check_candidate(
        owner,
        context,
        &source,
        proposition,
        proof.clone(),
        is_canonical_adapter,
        |source, proof| crate::Derivation::PermutePrems {
            premise: Box::new(source),
            fixed,
            rotation,
            proof,
        },
    )
}

pub(crate) fn replay_rotation(
    owner: &TrustedTheory,
    context: &ProofContext,
    source: KernelThm,
    selected: usize,
    rotation: isize,
    proof: &BoundProof,
) -> Result<(KernelThm, crate::DependencySet), KernelError> {
    let (proposition, expected) = build_rotation(&source, selected, rotation)?;
    let is_canonical_adapter = proof == &expected;
    check_candidate(
        owner,
        context,
        &source,
        proposition,
        proof.clone(),
        is_canonical_adapter,
        |source, proof| crate::Derivation::RotateRule {
            premise: Box::new(source),
            selected_subgoal_index: selected,
            rotation,
            proof,
        },
    )
}

fn normalize_rotation(rotation: isize, nprems: usize) -> Result<usize, KernelError> {
    let invalid = || BoundProofError::RotationOutOfRange { rotation, nprems };
    if rotation >= 0 {
        return usize::try_from(rotation)
            .ok()
            .filter(|&value| value <= nprems)
            .ok_or_else(|| invalid().into());
    }
    let backwards = rotation.unsigned_abs();
    nprems.checked_sub(backwards).ok_or_else(|| invalid().into())
}

fn rotate_terms(prems: &[Term], amount: usize) -> Vec<Term> {
    prems[amount..].iter().chain(&prems[..amount]).cloned().collect()
}

fn permutation_statement(
    source: &KernelThm,
    fixed: usize,
    rotation: isize,
) -> Result<(Term, Vec<Term>), KernelError> {
    let (original, conclusion) = source.prop().term().dest_imp_chain();
    if fixed > original.len() {
        return Err(
            BoundProofError::FixedPremiseOutOfRange { fixed, nprems: original.len() }.into()
        );
    }
    let amount = normalize_rotation(rotation, original.len() - fixed)?;
    let mut reordered = original[..fixed].to_vec();
    reordered.extend(rotate_terms(&original[fixed..], amount));
    Ok((Term::mk_imp_chain(&reordered, conclusion)?, reordered))
}

fn build_permutation(
    source: &KernelThm,
    fixed: usize,
    rotation: isize,
) -> Result<(Term, BoundProof), KernelError> {
    let (proposition, reordered) = permutation_statement(source, fixed, rotation)?;
    let (original, _) = source.prop().term().dest_imp_chain();
    let amount = normalize_rotation(rotation, original.len() - fixed)?;
    let hyps: Vec<_> = source.hyps().iter().map(|hyp| hyp.term().clone()).collect();
    let mut proof = lower::lower_theorem(source, &Sources::collect(source))?;
    for index in 0..hyps.len() {
        proof = elim(proof, hyp_at(hyps.len() + reordered.len(), index)?);
    }
    for index in 0..original.len() {
        let position = if index < fixed {
            index
        } else {
            fixed + (index - fixed + original.len() - fixed - amount) % (original.len() - fixed)
        };
        proof = elim(proof, hyp_at(hyps.len() + reordered.len(), hyps.len() + position)?);
    }
    let proof = lower::introduce(&hyps, lower::introduce(&reordered, proof));
    Ok((proposition, BoundProof { root: proof }))
}

type RotationStatement = (Term, Vec<Term>, Vec<(Name, Ty)>, usize);

fn rotation_statement(
    source: &KernelThm,
    selected: usize,
    rotation: isize,
) -> Result<RotationStatement, KernelError> {
    let (mut outer, conclusion) = source.prop().term().dest_imp_chain();
    let count = outer.len();
    let subgoal = outer
        .get_mut(selected)
        .ok_or(BoundProofError::SelectedSubgoalOutOfRange { index: selected, nprems: count })?;
    let mut inner = &*subgoal;
    let mut parameters = Vec::new();
    while let Some((name, ty, body)) = inner.dest_forall() {
        parameters.push((name.clone(), ty.clone()));
        inner = body;
    }
    let (assumptions, inner_conclusion) = inner.dest_imp_chain();
    let amount = normalize_rotation(rotation, assumptions.len())?;
    let rotated = Term::mk_imp_chain(&rotate_terms(&assumptions, amount), inner_conclusion)?;
    *subgoal = parameters.iter().rev().fold(rotated, |body, (name, ty)| Term::Forall {
        name: name.clone(),
        param_ty: ty.clone(),
        body: Box::new(body),
    });
    Ok((Term::mk_imp_chain(&outer, conclusion)?, outer, parameters, amount))
}

fn build_rotation(
    source: &KernelThm,
    selected: usize,
    rotation: isize,
) -> Result<(Term, BoundProof), KernelError> {
    let (proposition, outer, parameters, amount) = rotation_statement(source, selected, rotation)?;
    let (old_outer, _) = source.prop().term().dest_imp_chain();
    let hyps: Vec<_> = source.hyps().iter().map(|hyp| hyp.term().clone()).collect();
    let depth = hyps.len() + outer.len();
    let mut proof = lower::lower_theorem(source, &Sources::collect(source))?;
    for index in 0..hyps.len() {
        proof = elim(proof, hyp_at(depth, index)?);
    }
    for (index, old_goal) in old_outer.iter().enumerate().take(outer.len()) {
        let argument = if index == selected {
            adapt_subgoal(old_goal, &parameters, amount, depth, hyps.len() + index)?
        } else {
            hyp_at(depth, hyps.len() + index)?
        };
        proof = elim(proof, argument);
    }
    Ok((proposition, BoundProof { root: lower::introduce(&hyps, lower::introduce(&outer, proof)) }))
}

fn adapt_subgoal(
    old: &Term,
    parameters: &[(Name, Ty)],
    amount: usize,
    outer_depth: usize,
    selected_slot: usize,
) -> Result<Proof, KernelError> {
    let mut inner = old;
    for _ in parameters {
        inner = inner.dest_forall().ok_or(KernelError::NotForall)?.2;
    }
    let (assumptions, _) = inner.dest_imp_chain();
    let n = assumptions.len();
    let mut new_proof = hyp_at(outer_depth + n, selected_slot)?;
    for (index, (_, ty)) in parameters.iter().enumerate() {
        let bound = Term::Bound { index: parameters.len() - 1 - index, ty: ty.clone() };
        new_proof = Arc::new(Node::ForallElim { premise: new_proof, argument: bound });
    }
    for position in 0..n {
        let original_index = (position + amount) % n;
        new_proof = elim(new_proof, hyp_at(outer_depth + n, outer_depth + original_index)?);
    }
    let mut proof = lower::introduce(&assumptions, new_proof);
    for (name, ty) in parameters.iter().rev() {
        proof = Arc::new(Node::ForallIntro { name: name.clone(), ty: ty.clone(), body: proof });
    }
    Ok(proof)
}

fn hyp_at(depth: usize, position: usize) -> Result<Proof, KernelError> {
    let slot = depth
        .checked_sub(position)
        .and_then(|distance| distance.checked_sub(1))
        .ok_or(BoundProofError::IndexOverflow)?;
    Ok(Arc::new(Node::Hyp(slot)))
}

fn elim(major: Proof, minor: Proof) -> Proof {
    Arc::new(Node::ImpliesElim(major, minor))
}

fn check_candidate(
    owner: &TrustedTheory,
    context: &ProofContext,
    source: &KernelThm,
    proposition: Term,
    proof: BoundProof,
    is_canonical_adapter: bool,
    derivation: impl FnOnce(KernelThm, BoundProof) -> crate::Derivation,
) -> Result<(KernelThm, crate::DependencySet), KernelError> {
    let (checked, _, dependencies) = check::check_closed_with_source(
        context,
        owner,
        &Sources::collect(source),
        &proof.root,
        check::CheckTransport {
            source: source.prop().term(),
            target: &proposition,
            is_canonical_adapter,
            flex_pairs: source.payload().flex_pairs(),
        },
    )?;
    let hyps: Vec<_> = source.hyps().iter().map(|hyp| hyp.term().clone()).collect();
    if !checked.alpha_eq(&Term::mk_imp_chain(&hyps, &proposition)?) {
        return Err(BoundProofError::StatementMismatch.into());
    }
    let certified = crate::thm::prop_from_term(proposition, source.context());
    let payload = source.payload().clone();
    payload.validate_present_sorts(&certified, source.hyps())?;
    Ok((
        KernelThm::new_with_payload(
            source.hyps().to_vec(),
            certified,
            payload,
            derivation(source.clone(), proof),
        ),
        dependencies,
    ))
}
