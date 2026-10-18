//! Apply the exact residual F equality to already-bound parameters, then
//! justify every beta contraction with the existing conversion proof nodes.
use std::sync::Arc;

use crate::{CTerm, Term, Ty};

use super::{BinaryRule, Node, Proof, composition_beta, terms};

fn apply_bound_arguments(
    mut left: Term,
    mut right: Term,
    bounds: &[Ty],
    mut equality: Proof,
) -> Option<(Term, Term, Proof)> {
    for (position, bound_type) in bounds.iter().enumerate() {
        let index = bounds.len().checked_sub(position + 1)?;
        let left_type = left.ty();
        let right_type = right.ty();
        let (domain, result) = left_type.dest_arrow()?;
        let (other_domain, other_result) = right_type.dest_arrow()?;
        if domain != bound_type || other_domain != bound_type || result != other_result {
            return None;
        }
        let result_type = result.clone();
        let argument = Term::Bound { index, ty: bound_type.clone() };
        equality = Arc::new(Node::Binary {
            rule: BinaryRule::Combination,
            left: equality,
            right: Arc::new(Node::Reflexive(argument.clone())),
        });
        left = Term::App {
            func: Box::new(left),
            arg: Box::new(argument.clone()),
            ty: result_type.clone(),
        };
        right = Term::App { func: Box::new(right), arg: Box::new(argument), ty: result_type };
    }
    Some((left, right, equality))
}

fn justify_bound_equality(
    left: &Term,
    right: &Term,
    source_left: Term,
    source_right: Term,
    equality: Proof,
) -> Option<Proof> {
    if !terms::normalize_beta(source_left.clone()).ok()?.alpha_eq(left)
        || !terms::normalize_beta(source_right.clone()).ok()?.alpha_eq(right)
    {
        return None;
    }
    let left_conversion = composition_beta::prove_beta_normalization(&source_left, left).ok()?;
    let right_conversion = composition_beta::prove_beta_normalization(&source_right, right).ok()?;
    Some(Arc::new(Node::Binary {
        rule: BinaryRule::Transitive,
        left: Arc::new(Node::Binary {
            rule: BinaryRule::Transitive,
            left: Arc::new(Node::EqSym(left_conversion)),
            right: equality,
        }),
        right: right_conversion,
    }))
}

pub(super) fn prove_bound_flex(
    left: &Term,
    right: &Term,
    residual: &[(CTerm, CTerm)],
    bounds: &[Ty],
) -> Option<Proof> {
    if bounds.is_empty() {
        return None;
    }
    for (slot, (source_left, source_right)) in residual.iter().enumerate() {
        let Some((applied_left, applied_right, equality)) = apply_bound_arguments(
            source_left.term().clone(),
            source_right.term().clone(),
            bounds,
            Arc::new(Node::EqFlex(slot)),
        ) else {
            continue;
        };
        if let Some(proof) =
            justify_bound_equality(left, right, applied_left, applied_right, equality)
        {
            return Some(proof);
        }
    }
    None
}
