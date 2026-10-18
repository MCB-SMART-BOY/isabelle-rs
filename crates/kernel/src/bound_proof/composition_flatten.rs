//! Source-preserving normalization of nested Pure parameters in rule premises.
//! Flattening changes proof-state presentation, never discharges a real H entry.
use std::sync::Arc;

use crate::{KernelError, Name, Term, Ty};

use super::{BoundProofError, Node, Proof, terms};

enum Step {
    Forall(Name, Ty),
    Implies(Term),
}

fn collect_steps(proposition: &Term) -> Vec<Step> {
    let mut steps = Vec::new();
    let mut current = proposition;
    loop {
        match current {
            Term::Forall { name, param_ty, body } => {
                steps.push(Step::Forall(name.clone(), param_ty.clone()));
                current = body;
            },
            Term::Imp { premise, conclusion } => {
                steps.push(Step::Implies((**premise).clone()));
                current = conclusion;
            },
            _ => return steps,
        }
    }
}

fn remove_nested_parameters(
    source: &Term,
    remaining: usize,
    omitted: usize,
) -> Result<Term, KernelError> {
    match source {
        Term::Forall { body, .. } => remove_nested_parameters(
            body,
            remaining.checked_sub(1).ok_or(BoundProofError::IndexOverflow)?,
            omitted,
        ),
        Term::Imp { premise, conclusion } => {
            if omitted == 1 {
                return remove_nested_parameters(conclusion, remaining, 0);
            }
            let next = omitted.saturating_sub(1);
            Term::mk_imp(
                terms::lift_term(premise, remaining)?,
                remove_nested_parameters(conclusion, remaining, next)?,
            )
        },
        _ if omitted == 0 => Ok(source.clone()),
        _ => Err(BoundProofError::InvalidEliminationChoice { choice: omitted - 1 }.into()),
    }
}

pub(super) fn flatten_premise(source: &Term, omitted: usize) -> Result<Term, KernelError> {
    let steps = collect_steps(source);
    let mut parameters: Vec<_> = steps
        .iter()
        .filter_map(|step| {
            if let Step::Forall(name, ty) = step { Some((name.clone(), ty.clone())) } else { None }
        })
        .collect();
    let mut flattened = remove_nested_parameters(source, parameters.len(), omitted)?;
    while let Some((name, param_ty)) = parameters.pop() {
        flattened = Term::Forall { name, param_ty, body: Box::new(flattened) };
    }
    Ok(flattened)
}

fn apply_flattened_hypothesis(
    source: &[Step],
    depth: usize,
    position: usize,
    omitted: usize,
) -> Result<Proof, KernelError> {
    let assumptions = source.iter().filter(|step| matches!(step, Step::Implies(_))).count();
    let parameters: Vec<_> = source
        .iter()
        .filter_map(|step| if let Step::Forall(_, ty) = step { Some(ty) } else { None })
        .collect();
    let slot = depth
        .checked_add(assumptions)
        .and_then(|depth| depth.checked_sub(position + 1))
        .ok_or(BoundProofError::IndexOverflow)?;
    let mut proof = Arc::new(Node::Hyp(slot));
    for (index, ty) in parameters.iter().enumerate() {
        let binder =
            parameters.len().checked_sub(index + 1).ok_or(BoundProofError::IndexOverflow)?;
        proof = Arc::new(Node::ForallElim {
            premise: proof,
            argument: Term::Bound { index: binder, ty: (*ty).clone() },
        });
    }
    for index in 0..assumptions {
        if omitted == index + 1 {
            continue;
        }
        proof = Arc::new(Node::ImpliesElim(proof, Arc::new(Node::Hyp(assumptions - index - 1))));
    }
    Ok(proof)
}

pub(super) fn prove_original_premise(
    source: &Term,
    depth: usize,
    position: usize,
    omitted: usize,
) -> Result<Proof, KernelError> {
    let steps = collect_steps(source);
    let mut proof = apply_flattened_hypothesis(&steps, depth, position, omitted)?;
    for step in steps.into_iter().rev() {
        proof = Arc::new(match step {
            Step::Forall(name, ty) => Node::ForallIntro { name, ty, body: proof },
            Step::Implies(assumption) => Node::ImpliesIntro { assumption, body: proof },
        });
    }
    Ok(proof)
}
