//! Deterministic beta normalization emits only existing, independently checked
//! Pure equality nodes. A normalized proposition is never itself proof authority.
use std::{collections::BTreeMap, sync::Arc};

use crate::{KernelError, Term};

use super::{BinaryRule, BoundProofError, Node, Proof, composition, composition_env, terms};

fn rewrite_first_beta(term: &Term) -> Result<Option<Term>, KernelError> {
    match term {
        Term::App { func, arg, ty } => {
            if let Term::Abs { param_ty, body, .. } = func.as_ref() {
                if param_ty != &arg.ty() {
                    return Err(KernelError::TypeMismatch {
                        expected: param_ty.clone(),
                        actual: arg.ty(),
                    });
                }
                terms::check_beta_reduction_budget(body, arg, &mut 0)?;
                return Ok(Some(Term::instantiate_bound0(body, arg)));
            }
            if let Some(next) = rewrite_first_beta(func)? {
                return Ok(Some(Term::App {
                    func: Box::new(next),
                    arg: arg.clone(),
                    ty: ty.clone(),
                }));
            }
            Ok(rewrite_first_beta(arg)?.map(|next| Term::App {
                func: func.clone(),
                arg: Box::new(next),
                ty: ty.clone(),
            }))
        },
        Term::Abs { name, param_ty, body, ty } => {
            Ok(rewrite_first_beta(body)?.map(|next| Term::Abs {
                name: name.clone(),
                param_ty: param_ty.clone(),
                body: Box::new(next),
                ty: ty.clone(),
            }))
        },
        Term::Forall { name, param_ty, body } => Ok(rewrite_first_beta(body)?.map(|next| {
            Term::Forall { name: name.clone(), param_ty: param_ty.clone(), body: Box::new(next) }
        })),
        Term::Eq { lhs, rhs, .. } => {
            if let Some(next) = rewrite_first_beta(lhs)? {
                return Ok(Some(Term::mk_eq(next, (**rhs).clone())?));
            }
            Ok(rewrite_first_beta(rhs)?
                .map(|next| Term::mk_eq((**lhs).clone(), next))
                .transpose()?)
        },
        Term::Imp { premise, conclusion } => {
            if let Some(next) = rewrite_first_beta(premise)? {
                return Ok(Some(Term::mk_imp(next, (**conclusion).clone())?));
            }
            Ok(rewrite_first_beta(conclusion)?
                .map(|next| Term::mk_imp((**premise).clone(), next))
                .transpose()?)
        },
        Term::Const { .. } | Term::Free { .. } | Term::Var { .. } | Term::Bound { .. } => Ok(None),
    }
}

pub(super) fn prove_beta_normalization(
    original: &Term,
    target: &Term,
) -> Result<Proof, KernelError> {
    let expected = terms::normalize_beta(original.clone())?;
    if !expected.alpha_eq(target) {
        return Err(BoundProofError::StatementMismatch.into());
    }
    let mut current = original.clone();
    let mut proof = None;
    let empty = BTreeMap::new();
    for _ in 0..composition_env::MAX_CANDIDATE_DEPTH {
        if current.alpha_eq(target) {
            return Ok(proof.unwrap_or_else(|| Arc::new(Node::Reflexive(current))));
        }
        let next = rewrite_first_beta(&current)?.ok_or(BoundProofError::StatementMismatch)?;
        composition_env::estimate_term_expansion(&next, &empty, &BTreeMap::new())?;
        let step = composition::prove_equation(&current, &next, &[])
            .ok_or(BoundProofError::StatementMismatch)?;
        proof = Some(match proof {
            None => step,
            Some(previous) => {
                Arc::new(Node::Binary { rule: BinaryRule::Transitive, left: previous, right: step })
            },
        });
        current = next;
    }
    Err(BoundProofError::CandidateResourceLimit {
        kind: "beta normalization",
        resource: "steps",
        limit: composition_env::MAX_CANDIDATE_DEPTH,
    }
    .into())
}
