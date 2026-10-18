//! Source-checked lifting of a Pure rule over a selected goal's local binders.
use std::sync::Arc;

use crate::{
    CTerm, DependencySet, Derivation, KernelError, KernelRules, KernelThm, Name, ProofContext,
    Term, TrustedTheory, Ty,
};

use super::{
    BinaryRule, BoundProof, BoundProofError, Node, Proof, Sources, check, composition_index, lower,
    terms, transform,
};

enum GoalStep {
    Forall(Name, Ty),
    Implies(Term),
}

fn collect_goal_steps(goal: &Term) -> Vec<GoalStep> {
    let mut steps = Vec::new();
    let mut current = goal;
    loop {
        match current {
            Term::Forall { name, param_ty, body } => {
                steps.push(GoalStep::Forall(name.clone(), param_ty.clone()));
                current = body;
            },
            Term::Imp { premise, conclusion } => {
                steps.push(GoalStep::Implies((**premise).clone()));
                current = conclusion;
            },
            _ => return steps,
        }
    }
}

fn apply_lifted_variables(
    source: &Term,
    parameters: &[Ty],
    depth: usize,
) -> Result<Term, KernelError> {
    terms::rewrite_term(
        source,
        depth,
        &mut |node, local_depth| {
            let Term::Var { name, index, ty } = node else { return Ok(None) };
            if parameters.is_empty() {
                return Ok(None);
            }
            let function_ty = parameters
                .iter()
                .rev()
                .fold(ty.clone(), |result, parameter| Ty::arrow(parameter.clone(), result));
            let mut applied = Term::Var { name: name.clone(), index: *index, ty: function_ty };
            for (position, parameter) in parameters.iter().enumerate() {
                let index = local_depth
                    .checked_add(parameters.len() - position - 1)
                    .ok_or(BoundProofError::IndexOverflow)?;
                let result_ty = applied
                    .ty()
                    .dest_arrow()
                    .ok_or_else(|| KernelError::NotFunctionType(applied.ty()))?
                    .1
                    .clone();
                applied = Term::App {
                    func: Box::new(applied),
                    arg: Box::new(Term::Bound { index, ty: parameter.clone() }),
                    ty: result_ty,
                };
            }
            Ok(Some(applied))
        },
        &mut |ty| Ok(ty.clone()),
    )
}

fn lift_proof(
    source: &Proof,
    parameters: &[Ty],
    flex_pairs: &[(CTerm, CTerm)],
) -> Result<Proof, KernelError> {
    transform::map_proof_with_leaves(
        source,
        transform::ProofScope {
            term_depth: 0,
            hypothesis_depth: 0,
            is_source_normalization: false,
        },
        &mut |term, depth| apply_lifted_variables(term, parameters, depth),
        &mut |ty| Ok(ty.clone()),
        &mut |instance, _, is_transport| {
            Ok(if is_transport {
                Node::ClosedExportTransport(instance)
            } else {
                Node::AuthorizedLeaf(instance)
            })
        },
        &mut |slot, depth| lift_flex_proof(slot, depth, parameters, flex_pairs),
    )
}

fn lift_flex_proof(
    slot: usize,
    depth: usize,
    parameters: &[Ty],
    flex_pairs: &[(CTerm, CTerm)],
) -> Result<Proof, KernelError> {
    let (left, right) = flex_pairs
        .get(slot)
        .ok_or(BoundProofError::UnboundFlexPair { slot, pairs: flex_pairs.len() })?;
    let (mut left, mut right) = (left.term().clone(), right.term().clone());
    let mut proof = Arc::new(Node::EqFlex(slot));
    for (position, parameter) in parameters.iter().enumerate() {
        let index = depth
            .checked_add(parameters.len() - position - 1)
            .ok_or(BoundProofError::IndexOverflow)?;
        let argument = Term::Bound { index, ty: parameter.clone() };
        let left_ty = left.ty();
        let right_ty = right.ty();
        let left_result = left_ty
            .dest_arrow()
            .ok_or_else(|| KernelError::NotFunctionType(left_ty.clone()))?
            .1
            .clone();
        let right_result = right_ty
            .dest_arrow()
            .ok_or_else(|| KernelError::NotFunctionType(right_ty.clone()))?
            .1
            .clone();
        let left_app =
            Term::App { func: Box::new(left), arg: Box::new(argument.clone()), ty: left_result };
        let right_app =
            Term::App { func: Box::new(right), arg: Box::new(argument.clone()), ty: right_result };
        let (_, _, left_body) = left_app
            .dest_app()
            .and_then(|(function, _)| function.dest_abs())
            .ok_or_else(|| KernelError::BetaRedexExpected(left_app.ty()))?;
        let (_, _, right_body) = right_app
            .dest_app()
            .and_then(|(function, _)| function.dest_abs())
            .ok_or_else(|| KernelError::BetaRedexExpected(right_app.ty()))?;
        left = Term::instantiate_bound0(left_body, &argument);
        right = Term::instantiate_bound0(right_body, &argument);
        proof = Arc::new(Node::Binary {
            rule: BinaryRule::Combination,
            left: proof,
            right: Arc::new(Node::Reflexive(argument)),
        });
        proof = Arc::new(Node::Binary {
            rule: BinaryRule::Transitive,
            left: Arc::new(Node::EqSym(Arc::new(Node::Beta(left_app)))),
            right: proof,
        });
        proof = Arc::new(Node::Binary {
            rule: BinaryRule::Transitive,
            left: proof,
            right: Arc::new(Node::Beta(right_app)),
        });
    }
    Ok(proof)
}

fn lift_flex_side(source: &Term, parameters: &[(Name, Ty)]) -> Result<Term, KernelError> {
    let types: Vec<_> = parameters.iter().map(|(_, ty)| ty.clone()).collect();
    let mut result = apply_lifted_variables(source, &types, 0)?;
    for (name, ty) in parameters.iter().rev() {
        let arrow = Ty::arrow(ty.clone(), result.ty());
        result = Term::Abs {
            name: name.clone(),
            param_ty: ty.clone(),
            body: Box::new(result),
            ty: arrow,
        };
    }
    Ok(result)
}

fn lift_flex_pairs(
    source: &KernelThm,
    parameters: &[(Name, Ty)],
) -> Result<Vec<(CTerm, CTerm)>, KernelError> {
    source
        .payload()
        .flex_pairs()
        .iter()
        .map(|(left, right)| {
            Ok((
                CTerm::from_certified_subterm(
                    lift_flex_side(left.term(), parameters)?,
                    source.context(),
                ),
                CTerm::from_certified_subterm(
                    lift_flex_side(right.term(), parameters)?,
                    source.context(),
                ),
            ))
        })
        .collect()
}

fn lift_proposition(
    steps: &[GoalStep],
    parameters: &[Ty],
    source: &Term,
) -> Result<Term, KernelError> {
    let mut result = apply_lifted_variables(source, parameters, 0)?;
    for step in steps.iter().rev() {
        result = match step {
            GoalStep::Forall(name, ty) => {
                Term::Forall { name: name.clone(), param_ty: ty.clone(), body: Box::new(result) }
            },
            GoalStep::Implies(assumption) => Term::mk_imp(assumption.clone(), result)?,
        };
    }
    Ok(result)
}

fn lower_lifted_premise(
    steps: &[GoalStep],
    total_depth: usize,
    position: usize,
) -> Result<Proof, KernelError> {
    let target_hyps = steps.iter().filter(|step| matches!(step, GoalStep::Implies(_))).count();
    let total_params = steps.len() - target_hyps;
    let slot = total_depth.checked_sub(position + 1).ok_or(BoundProofError::IndexOverflow)?;
    let mut proof = Arc::new(Node::Hyp(slot));
    let mut seen_params = 0;
    let mut seen_hyps = 0;
    for step in steps {
        proof = match step {
            GoalStep::Forall(_, ty) => {
                let index = total_params
                    .checked_sub(seen_params + 1)
                    .ok_or(BoundProofError::IndexOverflow)?;
                seen_params += 1;
                Arc::new(Node::ForallElim {
                    premise: proof,
                    argument: Term::Bound { index, ty: ty.clone() },
                })
            },
            GoalStep::Implies(_) => {
                let slot =
                    target_hyps.checked_sub(seen_hyps + 1).ok_or(BoundProofError::IndexOverflow)?;
                seen_hyps += 1;
                Arc::new(Node::ImpliesElim(proof, Arc::new(Node::Hyp(slot))))
            },
        };
    }
    Ok(proof)
}

type LiftedProof = (Term, BoundProof, Vec<(CTerm, CTerm)>);

fn build_lift_proof(source: &KernelThm, goal: &CTerm) -> Result<LiftedProof, KernelError> {
    let steps = collect_goal_steps(goal.term());
    let parameter_names: Vec<_> = steps
        .iter()
        .filter_map(|step| match step {
            GoalStep::Forall(name, ty) => Some((name.clone(), ty.clone())),
            GoalStep::Implies(_) => None,
        })
        .collect();
    let parameters: Vec<_> = parameter_names.iter().map(|(_, ty)| ty.clone()).collect();
    let flex_pairs = lift_flex_pairs(source, &parameter_names)?;
    let (premises, conclusion) = source.prop().term().dest_imp_chain();
    let lifted: Vec<_> = premises
        .iter()
        .map(|term| lift_proposition(&steps, &parameters, term))
        .collect::<Result<_, _>>()?;
    let proposition =
        Term::mk_imp_chain(&lifted, &lift_proposition(&steps, &parameters, conclusion)?)?;
    let hyps: Vec<_> = source.hyps().iter().map(|hyp| hyp.term().clone()).collect();
    let sources = Sources::collect(source);
    let mut proof = lift_proof(&lower::lower_theorem(source, &sources)?, &parameters, &flex_pairs)?;
    let target_hyps = steps.iter().filter(|step| matches!(step, GoalStep::Implies(_))).count();
    let base_depth = hyps.len() + lifted.len();
    let total_depth = base_depth.checked_add(target_hyps).ok_or(BoundProofError::IndexOverflow)?;
    for position in 0..hyps.len() {
        let slot = total_depth.checked_sub(position + 1).ok_or(BoundProofError::IndexOverflow)?;
        proof = Arc::new(Node::ImpliesElim(proof, Arc::new(Node::Hyp(slot))));
    }
    for position in 0..premises.len() {
        let argument = lower_lifted_premise(&steps, total_depth, hyps.len() + position)?;
        proof = Arc::new(Node::ImpliesElim(proof, argument));
    }
    for step in steps.into_iter().rev() {
        proof = Arc::new(match step {
            GoalStep::Forall(name, ty) => Node::ForallIntro { name, ty, body: proof },
            GoalStep::Implies(assumption) => Node::ImpliesIntro { assumption, body: proof },
        });
    }
    Ok((
        proposition,
        BoundProof { root: lower::introduce(&hyps, lower::introduce(&lifted, proof)) },
        flex_pairs,
    ))
}

pub(crate) fn replay_lift_rule(
    owner: &TrustedTheory,
    context: &ProofContext,
    source: KernelThm,
    goal: &CTerm,
    proof: &BoundProof,
) -> Result<(KernelThm, DependencySet), KernelError> {
    context.validate_cterm(goal)?;
    if goal.ty() != Ty::prop() {
        return Err(KernelError::NotProposition(goal.ty()));
    }
    let (proposition, expected_proof, flex_pairs) = build_lift_proof(&source, goal)?;
    for (left, right) in &flex_pairs {
        context.validate_cterm(left)?;
        context.validate_cterm(right)?;
        if left.ty() != right.ty() {
            return Err(KernelError::TypeMismatch { expected: left.ty(), actual: right.ty() });
        }
    }
    if &expected_proof != proof {
        return Err(BoundProofError::StatementMismatch.into());
    }
    let sources = Sources::collect(&source);
    let (checked, sorts, dependencies) = check::check_closed_with_source(
        context,
        owner,
        &sources,
        &proof.root,
        check::CheckTransport {
            source: source.prop().term(),
            target: &proposition,
            is_canonical_adapter: true,
            flex_pairs: &flex_pairs,
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
    let certified = crate::thm::prop_from_term(proposition, context.stamp());
    let payload = crate::obligations::ProofPayload::lift_rule(
        source.payload(),
        goal,
        &hyps,
        &certified,
        &flex_pairs,
    )?;
    if !sorts.is_subset(payload.shyps()) {
        return Err(BoundProofError::StatementMismatch.into());
    }
    let lifted = KernelThm::new_with_payload(
        hyps,
        certified,
        payload,
        Derivation::LiftRule {
            premise: Box::new(source),
            goal: goal.clone(),
            proof: proof.clone(),
        },
    );
    Ok((lifted, dependencies))
}

impl KernelRules {
    /// Lift a checked rule over the local spine of a certified selected goal.
    /// Schematic indices are freshened against the certified goal's recorded bound.
    pub fn lift_rule(
        owner: &TrustedTheory,
        context: &ProofContext,
        goal: &CTerm,
        rule: &KernelThm,
    ) -> Result<KernelThm, KernelError> {
        context.validate_cterm(goal)?;
        if goal.ty() != Ty::prop() {
            return Err(KernelError::NotProposition(goal.ty()));
        }
        let source = super::composition::replay_current_source(owner, context, rule)?;
        let increment = goal
            .max_var_index()
            .map_or(Ok(0), |index| index.checked_add(1).ok_or(BoundProofError::IndexOverflow))?;
        let source = composition_index::freshen_rule(owner, context, &source, increment)?;
        let (_, proof, _) = build_lift_proof(&source, goal)?;
        Ok(replay_lift_rule(owner, context, source, goal, &proof)?.0)
    }
}
