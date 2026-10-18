//! Source-order lowering for Pure proof-state assumption discharge.
//! Every selected implication is a private proof slot, never a real H entry.
use std::sync::Arc;

use crate::{
    CProp, CTerm, InstEntry, KernelError, KernelRules, KernelThm, Name, ProofContext, Term,
    TrustedTheory, Ty, TypeInstantiation,
};

use super::{
    BinaryRule, BoundProof, BoundProofError, Node, Proof, Sources, check, composition_env,
    composition_flatten, composition_index, lower, transform,
};

/// Isabelle composition's independently checked source flags.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CompositionFlags {
    /// The rule was lifted across the selected subgoal's binder spine.
    pub is_lifted: bool,
    /// Move nested rule-premise parameters to their front, after source lifting.
    pub is_flattened: bool,
    /// No variable or type assignment may change the proof state.
    pub is_match: bool,
    /// The caller has already increased the rule's schematic index namespace.
    pub is_incremented: bool,
}

/// Non-authoritative parameters for selecting an exact composition proposal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompositionOptions {
    pub flags: CompositionFlags,
    pub is_elimination: bool,
    pub premise_count: usize,
    /// One-based selected subgoal index.
    pub subgoal_index: usize,
}

/// Finite, untrusted unifier proposal; proof checking, not this value,
/// establishes any equation or authorizes a theorem.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompositionCandidate {
    pub type_inst: TypeInstantiation,
    pub rule_subst: Vec<InstEntry>,
    pub state_subst: Vec<InstEntry>,
    /// Ordered remaining unsolved equations, never silently discarded.
    pub residual_pairs: Vec<(CTerm, CTerm)>,
    /// Zero-based premise slot inside the first rule premise for eresolution.
    pub elimination_choice: Option<usize>,
}

pub(super) fn replay_current_source(
    owner: &TrustedTheory,
    context: &ProofContext,
    source: &KernelThm,
) -> Result<KernelThm, KernelError> {
    let source = if source.context() == context.stamp() {
        source.clone()
    } else {
        crate::rules::transfer_with_dependencies(owner, source)?.0
    };
    let mut dependencies = crate::DependencySet::empty();
    crate::invariant::replay_source_in(owner, context, &source, &mut dependencies)
}

fn collect_full_prop_variables(theorem: &KernelThm) -> super::inspect::ProofVariables {
    let mut variables = super::inspect::ProofVariables::default();
    variables.visit_term(theorem.prop().term());
    for (left, right) in theorem.payload().flex_pairs() {
        variables.visit_term(left.term());
        variables.visit_term(right.term());
    }
    variables
}

fn check_common_var_types(
    rule: &super::inspect::ProofVariables,
    state: &super::inspect::ProofVariables,
    types: &TypeInstantiation,
) -> Result<(), KernelError> {
    for (name, index, rule_ty) in &rule.vars {
        for (_, _, state_ty) in
            state.vars.iter().filter(|(other, i, _)| other == name && i == index)
        {
            let expected = rule_ty.subst_type_vars(types)?;
            let actual = state_ty.subst_type_vars(types)?;
            if expected != actual {
                return Err(KernelError::TypeMismatch { expected, actual });
            }
        }
    }
    for atom in &rule.atoms {
        let mut source = None;
        atom.for_each_type_var(&mut |name, index, sort| {
            source = Some((name.clone(), index, sort.clone()));
        });
        let Some((name, index, sort)) = source else {
            continue;
        };
        for other in &state.atoms {
            let mut error = None;
            other.for_each_type_var(&mut |other_name, other_index, other_sort| {
                if other_name != &name || other_index != index {
                    return;
                }
                if other_sort != &sort {
                    error = Some(KernelError::TypeIdentityMismatch {
                        name: name.clone(),
                        index: Some(index),
                        expected: sort.clone(),
                        actual: other_sort.clone(),
                    });
                }
            });
            if let Some(error) = error {
                return Err(error);
            }
        }
    }
    Ok(())
}

fn validate_candidate_membership(
    rule: &super::inspect::ProofVariables,
    state: &super::inspect::ProofVariables,
    types: &TypeInstantiation,
    candidate: &CompositionCandidate,
    is_match: bool,
) -> Result<(), KernelError> {
    if is_match {
        for (key, _) in types.iter() {
            let atom = Ty::tvar(key.name.clone(), key.index as usize, key.sort.clone());
            if state.atoms.contains(&atom) {
                return Err(BoundProofError::MatchStateAssignment.into());
            }
        }
    }
    for entry in candidate.rule_subst.iter().chain(&candidate.state_subst) {
        let key = (entry.name().clone(), entry.index(), entry.var_ty().clone());
        let is_rule = rule.vars.contains(&key);
        let is_state = state.vars.contains(&key);
        if is_match && is_state {
            return Err(BoundProofError::MatchStateAssignment.into());
        }
        if !is_rule && !is_state {
            return Err(BoundProofError::AbsentAssignment { name: key.0, index: key.1 }.into());
        }
    }
    Ok(())
}

fn split_candidate_substitutions(
    rule: &super::inspect::ProofVariables,
    state: &super::inspect::ProofVariables,
    substitutions: &[InstEntry],
) -> (Vec<InstEntry>, Vec<InstEntry>) {
    let mut rule_entries = Vec::new();
    let mut state_entries = Vec::new();
    for entry in substitutions {
        let key = (entry.name().clone(), entry.index(), entry.var_ty().clone());
        if rule.vars.contains(&key) {
            rule_entries.push(entry.clone());
        }
        if state.vars.contains(&key) {
            state_entries.push(entry.clone());
        }
    }
    (rule_entries, state_entries)
}

fn apply_candidate_to_source(
    owner: &TrustedTheory,
    context: &ProofContext,
    source: KernelThm,
    types: &TypeInstantiation,
    substitutions: &[InstEntry],
) -> Result<KernelThm, KernelError> {
    if types.iter().next().is_none() && substitutions.is_empty() {
        return Ok(source);
    }
    Ok(super::source_instantiate::replay_source_instantiation(
        owner,
        context,
        source,
        types,
        substitutions,
    )?
    .0)
}

pub(super) enum SpineStep {
    Forall(Name, Ty),
    Implies(Term),
}

pub(super) fn count_outer_assumptions(goal: &Term) -> usize {
    let mut current = goal;
    while let Term::Forall { body, .. } = current {
        current = body;
    }
    let mut count = 0;
    while let Term::Imp { conclusion, .. } = current {
        count += 1;
        current = conclusion;
    }
    count
}

pub(super) fn inspect_assumption_spine(
    goal: &Term,
    requested: Option<usize>,
    residual: &[(CTerm, CTerm)],
    maximum: Option<usize>,
    is_eta_only: bool,
) -> Result<(Vec<SpineStep>, usize, Option<Proof>), KernelError> {
    let mut steps = Vec::new();
    let mut current = goal;
    while let Term::Forall { name, param_ty, body } = current {
        steps.push(SpineStep::Forall(name.clone(), param_ty.clone()));
        current = body;
    }
    let mut assumptions = 0;
    while let Term::Imp { premise, conclusion } = current {
        if maximum.is_some_and(|limit| assumptions >= limit) {
            break;
        }
        steps.push(SpineStep::Implies((**premise).clone()));
        current = conclusion;
        assumptions += 1;
    }
    if let Some(requested) = requested
        && requested >= assumptions
    {
        return Err(BoundProofError::InvalidEliminationChoice { choice: requested }.into());
    }
    let mut bound_types = steps
        .iter()
        .filter_map(|step| match step {
            SpineStep::Forall(_, ty) => Some(ty.clone()),
            SpineStep::Implies(_) => None,
        })
        .collect();
    for (choice, step) in steps
        .iter()
        .filter_map(|step| match step {
            SpineStep::Implies(premise) => Some(premise),
            SpineStep::Forall(_, _) => None,
        })
        .enumerate()
    {
        if requested.is_some_and(|requested| requested != choice) {
            continue;
        }
        if step.alpha_eq(current) {
            return Ok((steps, choice, None));
        }
        if let Some(equality) =
            prove_equation_with_mode(step, current, residual, !is_eta_only, &mut bound_types)
        {
            return Ok((steps, choice, Some(equality)));
        }
    }
    Err(KernelError::AntecedentMismatch)
}

fn prove_assumption(
    goal: &Term,
    expected_choice: usize,
    residual: &[(CTerm, CTerm)],
    maximum: Option<usize>,
    is_eta_only: bool,
) -> Result<Proof, KernelError> {
    let (steps, choice, equality) =
        inspect_assumption_spine(goal, Some(expected_choice), residual, maximum, is_eta_only)?;
    let count = steps.iter().filter(|step| matches!(step, SpineStep::Implies(_))).count();
    let slot = count.checked_sub(choice + 1).ok_or(BoundProofError::IndexOverflow)?;
    let mut proof = Arc::new(Node::Hyp(slot));
    if let Some(equality) = equality {
        proof =
            Arc::new(Node::Binary { rule: BinaryRule::EqualElim, left: equality, right: proof });
    }
    for step in steps.into_iter().rev() {
        proof = Arc::new(match step {
            SpineStep::Forall(name, ty) => Node::ForallIntro { name, ty, body: proof },
            SpineStep::Implies(assumption) => Node::ImpliesIntro { assumption, body: proof },
        });
    }
    Ok(proof)
}

fn hypothesis_at(depth: usize, position: usize) -> Result<Proof, KernelError> {
    let slot = depth.checked_sub(position + 1).ok_or(BoundProofError::IndexOverflow)?;
    Ok(Arc::new(Node::Hyp(slot)))
}

pub(super) fn build_assumption_proof(
    source: &KernelThm,
    selected: usize,
    choice: usize,
    residual: &[(CTerm, CTerm)],
    maximum: Option<usize>,
    is_eta_only: bool,
) -> Result<(Term, BoundProof), KernelError> {
    let (outer, conclusion) = source.prop().term().dest_imp_chain();
    let selected_goal = outer.get(selected).ok_or(BoundProofError::SelectedSubgoalOutOfRange {
        index: selected,
        nprems: outer.len(),
    })?;
    let mut remaining = outer.clone();
    remaining.remove(selected);
    let proposition = Term::mk_imp_chain(&remaining, conclusion)?;
    let hypotheses: Vec<_> = source.hyps().iter().map(|hyp| hyp.term().clone()).collect();
    let depth = hypotheses.len() + remaining.len();
    let sources = Sources::collect(source);
    let mut proof = lower::lower_theorem(source, &sources)?;
    proof = rebase_flex_proof(&proof, source.payload().flex_pairs(), residual)?;
    for position in 0..hypotheses.len() {
        proof = Arc::new(Node::ImpliesElim(proof, hypothesis_at(depth, position)?));
    }
    for position in 0..outer.len() {
        let argument = if position == selected {
            prove_assumption(selected_goal, choice, residual, maximum, is_eta_only)?
        } else {
            let new_position = if position < selected { position } else { position - 1 };
            hypothesis_at(depth, hypotheses.len() + new_position)?
        };
        proof = Arc::new(Node::ImpliesElim(proof, argument));
    }
    Ok((
        proposition,
        BoundProof { root: lower::introduce(&hypotheses, lower::introduce(&remaining, proof)) },
    ))
}

fn introduce_hypotheses(
    mut proof: Proof,
    source_hyps: &[CProp],
    all_hyps: &[CProp],
    depth: usize,
) -> Result<Proof, KernelError> {
    for hypothesis in source_hyps {
        let index = all_hyps
            .iter()
            .position(|candidate| candidate.term().alpha_eq(hypothesis.term()))
            .ok_or(BoundProofError::MissingHypothesis)?;
        proof = Arc::new(Node::ImpliesElim(proof, hypothesis_at(depth, index)?));
    }
    Ok(proof)
}

fn peel_rule(rule: &Term, count: usize) -> Result<(Vec<Term>, &Term), KernelError> {
    let mut premises = Vec::new();
    let mut remainder = rule;
    for _ in 0..count {
        let (premise, conclusion) =
            remainder.dest_imp().ok_or(BoundProofError::RulePremisesOutOfRange {
                requested: count,
                available: premises.len(),
            })?;
        premises.push(premise.clone());
        remainder = conclusion;
    }
    Ok((premises, remainder))
}

pub(super) fn prove_equation(
    left: &Term,
    right: &Term,
    residual: &[(CTerm, CTerm)],
) -> Option<Proof> {
    prove_equation_with_mode(left, right, residual, true, &mut Vec::new())
}

fn prove_equation_with_mode(
    left: &Term,
    right: &Term,
    residual: &[(CTerm, CTerm)],
    is_beta_allowed: bool,
    bounds: &mut Vec<Ty>,
) -> Option<Proof> {
    if left.alpha_eq(right) {
        return Some(Arc::new(Node::Reflexive(left.clone())));
    }
    for (slot, (first, second)) in residual.iter().enumerate() {
        let direct = first.term().alpha_eq(left) && second.term().alpha_eq(right);
        if direct {
            return Some(Arc::new(Node::EqFlex(slot)));
        }
        let reverse = first.term().alpha_eq(right) && second.term().alpha_eq(left);
        if reverse {
            return Some(Arc::new(Node::EqSym(Arc::new(Node::EqFlex(slot)))));
        }
    }
    if is_beta_allowed
        && let Some(proof) =
            super::composition_flex::prove_bound_flex(left, right, residual, bounds)
    {
        return Some(proof);
    }
    let beta_reduces_to = |from: &Term, to: &Term| {
        from.dest_app()
            .and_then(|(function, argument)| {
                let (_, parameter, body) = function.dest_abs()?;
                (parameter == &argument.ty()).then(|| Term::instantiate_bound0(body, argument))
            })
            .is_some_and(|reduced| reduced.alpha_eq(to))
    };
    if is_beta_allowed {
        if beta_reduces_to(left, right) {
            return Some(Arc::new(Node::Beta(left.clone())));
        }
        if beta_reduces_to(right, left) {
            return Some(Arc::new(Node::EqSym(Arc::new(Node::Beta(right.clone())))));
        }
    }
    if crate::rules::contract_eta(left).is_ok_and(|reduced| reduced.alpha_eq(right)) {
        return Some(Arc::new(Node::Eta(left.clone())));
    }
    if crate::rules::contract_eta(right).is_ok_and(|reduced| reduced.alpha_eq(left)) {
        return Some(Arc::new(Node::EqSym(Arc::new(Node::Eta(right.clone())))));
    }
    prove_congruence(left, right, residual, is_beta_allowed, bounds)
}
fn combine(rule: BinaryRule, left: Proof, right: Proof) -> Proof {
    Arc::new(Node::Binary { rule, left, right })
}

fn prove_imp_congruence(
    left: &Term,
    right: &Term,
    residual: &[(CTerm, CTerm)],
    is_beta_allowed: bool,
    bounds: &mut Vec<Ty>,
) -> Option<Proof> {
    let (a, b) = left.dest_imp()?;
    let (c, d) = right.dest_imp()?;
    let eq_a = prove_equation_with_mode(a, c, residual, is_beta_allowed, bounds)?;
    let eq_b = prove_equation_with_mode(b, d, residual, is_beta_allowed, bounds)?;
    let forward_a =
        combine(BinaryRule::EqualElim, Arc::new(Node::EqSym(eq_a.clone())), Arc::new(Node::Hyp(0)));
    let forward_b = Arc::new(Node::ImpliesElim(Arc::new(Node::Hyp(1)), forward_a));
    let forward_d = combine(BinaryRule::EqualElim, eq_b.clone(), forward_b);
    let forward = Arc::new(Node::ImpliesIntro {
        assumption: left.clone(),
        body: Arc::new(Node::ImpliesIntro { assumption: c.clone(), body: forward_d }),
    });
    let reverse_c = combine(BinaryRule::EqualElim, eq_a, Arc::new(Node::Hyp(0)));
    let reverse_d = Arc::new(Node::ImpliesElim(Arc::new(Node::Hyp(1)), reverse_c));
    let reverse_b = combine(BinaryRule::EqualElim, Arc::new(Node::EqSym(eq_b)), reverse_d);
    let reverse = Arc::new(Node::ImpliesIntro {
        assumption: right.clone(),
        body: Arc::new(Node::ImpliesIntro { assumption: a.clone(), body: reverse_b }),
    });
    Some(combine(BinaryRule::EqualIntr, forward, reverse))
}

fn prove_forall_congruence(
    left: &Term,
    right: &Term,
    residual: &[(CTerm, CTerm)],
    is_beta_allowed: bool,
    bounds: &mut Vec<Ty>,
) -> Option<Proof> {
    let (name, ty, a) = left.dest_forall()?;
    let (_, other_ty, b) = right.dest_forall()?;
    if ty != other_ty {
        return None;
    }
    bounds.push(ty.clone());
    let equality = prove_equation_with_mode(a, b, residual, is_beta_allowed, bounds);
    bounds.pop();
    let equality = equality?;
    let arg = Term::Bound { index: 0, ty: ty.clone() };
    let build = |from: &Term, eq: Proof| {
        Arc::new(Node::ImpliesIntro {
            assumption: from.clone(),
            body: Arc::new(Node::ForallIntro {
                name: name.clone(),
                ty: ty.clone(),
                body: combine(
                    BinaryRule::EqualElim,
                    eq,
                    Arc::new(Node::ForallElim {
                        premise: Arc::new(Node::Hyp(0)),
                        argument: arg.clone(),
                    }),
                ),
            }),
        })
    };
    let forward = build(left, equality.clone());
    let reverse = build(right, Arc::new(Node::EqSym(equality)));
    Some(combine(BinaryRule::EqualIntr, forward, reverse))
}

fn prove_object_equality_congruence(
    left: &Term,
    right: &Term,
    residual: &[(CTerm, CTerm)],
    is_beta_allowed: bool,
    bounds: &mut Vec<Ty>,
) -> Option<Proof> {
    let (ty, a, b) = left.dest_eq()?;
    let (other_ty, c, d) = right.dest_eq()?;
    if ty != other_ty {
        return None;
    }
    let eq_a = prove_equation_with_mode(a, c, residual, is_beta_allowed, bounds)?;
    let eq_b = prove_equation_with_mode(b, d, residual, is_beta_allowed, bounds)?;
    let forward = combine(
        BinaryRule::Transitive,
        combine(
            BinaryRule::Transitive,
            Arc::new(Node::EqSym(eq_a.clone())),
            Arc::new(Node::Hyp(0)),
        ),
        eq_b.clone(),
    );
    let reverse = combine(
        BinaryRule::Transitive,
        combine(BinaryRule::Transitive, eq_a, Arc::new(Node::Hyp(0))),
        Arc::new(Node::EqSym(eq_b)),
    );
    let forward = Arc::new(Node::ImpliesIntro { assumption: left.clone(), body: forward });
    let reverse = Arc::new(Node::ImpliesIntro { assumption: right.clone(), body: reverse });
    Some(combine(BinaryRule::EqualIntr, forward, reverse))
}

fn prove_congruence(
    left: &Term,
    right: &Term,
    residual: &[(CTerm, CTerm)],
    is_beta_allowed: bool,
    bounds: &mut Vec<Ty>,
) -> Option<Proof> {
    match (left, right) {
        (
            Term::App { func: left_fn, arg: left_arg, .. },
            Term::App { func: right_fn, arg: right_arg, .. },
        ) => Some(combine(
            BinaryRule::Combination,
            prove_equation_with_mode(left_fn, right_fn, residual, is_beta_allowed, bounds)?,
            prove_equation_with_mode(left_arg, right_arg, residual, is_beta_allowed, bounds)?,
        )),
        (
            Term::Abs { name, param_ty, body: left_body, .. },
            Term::Abs { param_ty: right_ty, body: right_body, .. },
        ) if param_ty == right_ty => {
            bounds.push(param_ty.clone());
            let equality =
                prove_equation_with_mode(left_body, right_body, residual, is_beta_allowed, bounds);
            bounds.pop();
            Some(Arc::new(Node::EqAbs {
                name: name.clone(),
                ty: param_ty.clone(),
                body: equality?,
            }))
        },
        (Term::Imp { .. }, Term::Imp { .. }) => {
            prove_imp_congruence(left, right, residual, is_beta_allowed, bounds)
        },
        (Term::Forall { .. }, Term::Forall { .. }) => {
            prove_forall_congruence(left, right, residual, is_beta_allowed, bounds)
        },
        (Term::Eq { .. }, Term::Eq { .. }) => {
            prove_object_equality_congruence(left, right, residual, is_beta_allowed, bounds)
        },
        _ => None,
    }
}

fn rebase_flex_proof(
    proof: &Proof,
    old: &[(CTerm, CTerm)],
    residual: &[(CTerm, CTerm)],
) -> Result<Proof, KernelError> {
    if old.is_empty() {
        return Ok(proof.clone());
    }
    transform::map_proof_with_leaves(
        proof,
        transform::ProofScope {
            term_depth: 0,
            hypothesis_depth: 0,
            is_source_normalization: false,
        },
        &mut |term, _| Ok(term.clone()),
        &mut |ty| Ok(ty.clone()),
        &mut |instance, _, is_transport| {
            Ok(if is_transport {
                Node::ClosedExportTransport(instance)
            } else {
                Node::AuthorizedLeaf(instance)
            })
        },
        &mut |slot, _| {
            let pair =
                old.get(slot).ok_or(BoundProofError::UnboundFlexPair { slot, pairs: old.len() })?;
            prove_equation(pair.0.term(), pair.1.term(), residual)
                .ok_or(BoundProofError::UnprovedEquation { operation: "source F", slot }.into())
        },
    )
}

#[derive(Clone, Copy)]
struct RuleProofInputs<'a> {
    hypotheses: &'a [CProp],
    depth: usize,
    premise_start: usize,
    premises: &'a [Term],
    is_flattened: bool,
    elimination_choice: Option<usize>,
    residual: &'a [(CTerm, CTerm)],
    elimination_limit: Option<usize>,
}

fn prove_rule(
    rule: &KernelThm,
    sources: &Sources<'_>,
    inputs: &RuleProofInputs<'_>,
) -> Result<Proof, KernelError> {
    let RuleProofInputs {
        hypotheses,
        depth,
        premise_start,
        premises,
        is_flattened,
        elimination_choice,
        residual,
        elimination_limit,
    } = *inputs;
    let proof = lower::lower_theorem(rule, sources)?;
    let proof = rebase_flex_proof(&proof, rule.payload().flex_pairs(), residual)?;
    let mut proof = introduce_hypotheses(proof, rule.hyps(), hypotheses, depth)?;
    for (offset, premise) in premises.iter().enumerate() {
        let argument = if offset == 0
            && let Some(choice) = elimination_choice
        {
            prove_assumption(premise, choice, residual, elimination_limit, false)?
        } else {
            let position = hypotheses.len() + premise_start + offset
                - usize::from(elimination_choice.is_some());
            if is_flattened {
                composition_flatten::prove_original_premise(
                    premise,
                    depth,
                    position,
                    elimination_choice.map_or(0, |choice| choice + 1),
                )?
            } else {
                hypothesis_at(depth, position)?
            }
        };
        proof = Arc::new(Node::ImpliesElim(proof, argument));
    }
    Ok(proof)
}

fn prove_selected_goal(
    rule: &KernelThm,
    sources: &Sources<'_>,
    inputs: &RuleProofInputs<'_>,
    goal: &Term,
    remainder: &Term,
) -> Result<Proof, KernelError> {
    let proof = prove_rule(rule, sources, inputs)?;
    let residual = inputs.residual;
    let instantiated = remainder;
    if instantiated.alpha_eq(goal) {
        return Ok(proof);
    }
    let equality = prove_equation(instantiated, goal, residual)
        .ok_or(BoundProofError::UnprovedEquation { operation: "rule conclusion", slot: 0 })?;
    Ok(Arc::new(Node::Binary { rule: BinaryRule::EqualElim, left: equality, right: proof }))
}

fn build_exact_resolution(
    rule: &KernelThm,
    state: &KernelThm,
    selected: usize,
    count: usize,
    flags: CompositionFlags,
    residual: &[(CTerm, CTerm)],
    elimination_choice: Option<usize>,
) -> Result<(Term, BoundProof), KernelError> {
    let (premises, remainder) = peel_rule(rule.prop().term(), count)?;
    let (outer, conclusion) = state.prop().term().dest_imp_chain();
    let goal = outer.get(selected).ok_or(BoundProofError::SelectedSubgoalOutOfRange {
        index: selected,
        nprems: outer.len(),
    })?;
    if let Some(choice) = elimination_choice {
        let first = premises.first().ok_or(BoundProofError::InvalidEliminationChoice { choice })?;
        prove_assumption(first, choice, residual, Some(count_outer_assumptions(goal)), false)?;
    }
    let displayed: Vec<Term> = if flags.is_flattened {
        let omitted = elimination_choice.map_or(0, |choice| choice + 1);
        premises
            .iter()
            .enumerate()
            .map(|(index, premise)| {
                if index == 0 && elimination_choice.is_some() {
                    Ok(premise.clone())
                } else {
                    composition_flatten::flatten_premise(premise, omitted)
                }
            })
            .collect::<Result<_, KernelError>>()?
    } else {
        premises.clone()
    };
    let removed = usize::from(elimination_choice.is_some());
    let mut result_prems = outer[..selected].to_vec();
    result_prems.extend_from_slice(&displayed[removed..]);
    result_prems.extend_from_slice(&outer[selected + 1..]);
    let proposition = Term::mk_imp_chain(&result_prems, conclusion)?;
    let hypotheses = crate::thm::union_hyps(rule.hyps(), state.hyps());
    let all_hyps: Vec<_> = hypotheses.iter().map(|hyp| hyp.term().clone()).collect();
    let depth = hypotheses.len() + result_prems.len();
    let sources = Sources::collect_pair(rule, state);
    let state_proof = lower::lower_theorem(state, &sources)?;
    let state_proof = rebase_flex_proof(&state_proof, state.payload().flex_pairs(), residual)?;
    let mut proof = introduce_hypotheses(state_proof, state.hyps(), &hypotheses, depth)?;
    for position in 0..outer.len() {
        let argument = if position == selected {
            prove_selected_goal(
                rule,
                &sources,
                &RuleProofInputs {
                    hypotheses: &hypotheses,
                    depth,
                    premise_start: selected,
                    premises: &premises,
                    is_flattened: flags.is_flattened,
                    elimination_choice,
                    residual,
                    elimination_limit: elimination_choice.map(|_| count_outer_assumptions(goal)),
                },
                goal,
                remainder,
            )?
        } else {
            let offset =
                if position < selected { position } else { position - 1 + count - removed };
            hypothesis_at(depth, hypotheses.len() + offset)?
        };
        proof = Arc::new(Node::ImpliesElim(proof, argument));
    }
    Ok((
        proposition,
        BoundProof { root: lower::introduce(&all_hyps, lower::introduce(&result_prems, proof)) },
    ))
}

pub(crate) fn replay_eq_assumption(
    owner: &TrustedTheory,
    context: &ProofContext,
    source: KernelThm,
    selected: usize,
    choice: usize,
    proof: &BoundProof,
) -> Result<(KernelThm, crate::DependencySet), KernelError> {
    let (proposition, canonical) =
        build_assumption_proof(&source, selected, choice, &[], None, true)?;
    if proof != &canonical {
        return Err(BoundProofError::StatementMismatch.into());
    }
    let (checked, _, dependencies) = check::check_closed_with_source(
        context,
        owner,
        &Sources::collect(&source),
        &proof.root,
        check::CheckTransport {
            source: source.prop().term(),
            target: &proposition,
            is_canonical_adapter: true,
            flex_pairs: source.payload().flex_pairs(),
        },
    )?;
    let expected = Term::mk_imp_chain(
        &source.hyps().iter().map(|hyp| hyp.term().clone()).collect::<Vec<_>>(),
        &proposition,
    )?;
    if !checked.alpha_eq(&expected) {
        return Err(BoundProofError::StatementMismatch.into());
    }
    let certified = crate::thm::prop_from_term(proposition, source.context());
    source.payload().validate_present_sorts(&certified, source.hyps())?;
    let result = KernelThm::new_with_payload(
        source.hyps().to_vec(),
        certified,
        source.payload().clone(),
        crate::Derivation::EqAssumption {
            state: Box::new(source),
            selected,
            choice,
            proof: proof.clone(),
        },
    );
    Ok((result, dependencies))
}

pub(super) fn check_source_flex(
    owner: &TrustedTheory,
    context: &ProofContext,
    sources: &Sources<'_>,
    old: &[(CTerm, CTerm)],
    residual: &[(CTerm, CTerm)],
    operation: &'static str,
    state_prop: &Term,
) -> Result<(std::collections::BTreeSet<crate::Sort>, crate::DependencySet), KernelError> {
    let mut sorts = std::collections::BTreeSet::new();
    let mut dependencies = crate::DependencySet::empty();
    for (slot, (left, right)) in old.iter().enumerate() {
        let proof = prove_equation(left.term(), right.term(), residual)
            .ok_or(BoundProofError::UnprovedEquation { operation, slot })?;
        let expected = Term::mk_eq(left.term().clone(), right.term().clone())?;
        let (checked, used_sorts, used_dependencies) = check::check_closed_with_source(
            context,
            owner,
            sources,
            &proof,
            check::CheckTransport {
                source: state_prop,
                target: &expected,
                is_canonical_adapter: false,
                flex_pairs: residual,
            },
        )?;
        if !checked.alpha_eq(&expected) {
            return Err(BoundProofError::StatementMismatch.into());
        }
        sorts.extend(used_sorts);
        dependencies.extend(&used_dependencies);
    }
    Ok((sorts, dependencies))
}

/// Replay parameters come from the recorded derivation, never caller authority.
pub(crate) struct ResolutionReplay<'a> {
    pub selected: usize,
    pub premise_count: usize,
    pub flags: CompositionFlags,
    pub residual: &'a [(CTerm, CTerm)],
    pub elimination_choice: Option<usize>,
    pub proof: &'a BoundProof,
}

pub(crate) fn replay_exact_resolution(
    owner: &TrustedTheory,
    context: &ProofContext,
    rule: KernelThm,
    state: KernelThm,
    replay: ResolutionReplay<'_>,
) -> Result<(KernelThm, crate::DependencySet), KernelError> {
    let ResolutionReplay { selected, premise_count, flags, residual, elimination_choice, proof } =
        replay;
    for (left, right) in residual {
        context.validate_cterm(left)?;
        context.validate_cterm(right)?;
        if left.ty() != right.ty() {
            return Err(KernelError::TypeMismatch { expected: left.ty(), actual: right.ty() });
        }
    }
    let (proposition, canonical) = build_exact_resolution(
        &rule,
        &state,
        selected,
        premise_count,
        flags,
        residual,
        elimination_choice,
    )?;
    if proof != &canonical {
        return Err(BoundProofError::StatementMismatch.into());
    }
    let hyps = crate::thm::union_hyps(rule.hyps(), state.hyps());
    let sources = Sources::collect_pair(&rule, &state);
    let (checked, mut sorts, mut dependencies) = check::check_closed_with_source(
        context,
        owner,
        &sources,
        &proof.root,
        check::CheckTransport {
            source: state.prop().term(),
            target: &proposition,
            is_canonical_adapter: true,
            flex_pairs: residual,
        },
    )?;
    let expected = Term::mk_imp_chain(
        &hyps.iter().map(|hyp| hyp.term().clone()).collect::<Vec<_>>(),
        &proposition,
    )?;
    if !checked.alpha_eq(&expected) {
        return Err(BoundProofError::StatementMismatch.into());
    }
    for (source, operation) in [(rule.payload(), "rule F"), (state.payload(), "state F")] {
        let (used_sorts, used_dependencies) = check_source_flex(
            owner,
            context,
            &sources,
            source.flex_pairs(),
            residual,
            operation,
            state.prop().term(),
        )?;
        sorts.extend(used_sorts);
        dependencies.extend(&used_dependencies);
    }
    let certified = crate::thm::prop_from_term(proposition, context.stamp());
    let payload = crate::obligations::ProofPayload::compose_source_order(
        rule.payload(),
        state.payload(),
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
        crate::Derivation::Bicompose {
            rule: Box::new(rule),
            state: Box::new(state),
            selected,
            premise_count,
            flags,
            residual_pairs: residual.to_vec(),
            elimination_choice,
            proof: proof.clone(),
        },
    );
    Ok((result, dependencies))
}

fn select_elimination_choice(
    is_elimination: bool,
    candidate: &CompositionCandidate,
    source_premises: &[Term],
    source_elimination_limit: usize,
) -> Result<Option<usize>, KernelError> {
    let choice = if is_elimination {
        Some(
            candidate
                .elimination_choice
                .ok_or(BoundProofError::InvalidEliminationChoice { choice: 0 })?,
        )
    } else {
        if candidate.elimination_choice.is_some() {
            return Err(BoundProofError::InvalidEliminationChoice {
                choice: candidate.elimination_choice.unwrap_or(0),
            }
            .into());
        }
        None
    };
    if let Some(choice) = choice {
        let first =
            source_premises.first().ok_or(BoundProofError::InvalidEliminationChoice { choice })?;
        let available = count_outer_assumptions(first).min(source_elimination_limit);
        if choice >= available {
            return Err(BoundProofError::InvalidEliminationChoice { choice }.into());
        }
    }
    Ok(choice)
}

impl KernelRules {
    /// Check a finite Pure bicomposition proposal against both complete source proofs.
    /// `options.subgoal_index` is one-based; `options.premise_count` is the
    /// exact number of rule premises to insert. Neither options nor candidate
    /// are a unifier certificate or theorem authority.
    pub fn bicompose_candidate(
        owner: &TrustedTheory,
        context: &ProofContext,
        options: CompositionOptions,
        rule: &KernelThm,
        state: &KernelThm,
        candidate: &CompositionCandidate,
    ) -> Result<KernelThm, KernelError> {
        let CompositionOptions { flags, is_elimination, premise_count: m, subgoal_index: i } =
            options;
        let selected = i.checked_sub(1).ok_or(KernelError::SubgoalIndexOutOfRange {
            index: i,
            nprems: state.prop().term().nprems(),
        })?;
        let rule = replay_current_source(owner, context, rule)?;
        let state = replay_current_source(owner, context, state)?;
        // Isabelle selects the source slots before the proposed environment is
        // applied. An assignment must not manufacture a new m-th rule premise
        // or an elimination/assumption branch inside A1.
        let (source_premises, _) = peel_rule(rule.prop().term(), m)?;
        let (state_premises, _) = state.prop().term().dest_imp_chain();
        let source_goal =
            state_premises.get(selected).ok_or(BoundProofError::SelectedSubgoalOutOfRange {
                index: selected,
                nprems: state_premises.len(),
            })?;
        let source_elimination_limit = count_outer_assumptions(source_goal).saturating_add(1);
        let rule_vars = composition_index::collect_source_variables(&rule)?;
        let state_vars = composition_index::collect_source_variables(&state)?;
        let types = composition_env::normalize_types(context, &candidate.type_inst)?;
        if !flags.is_incremented {
            check_common_var_types(
                &collect_full_prop_variables(&rule),
                &collect_full_prop_variables(&state),
                &types,
            )?;
        }
        validate_candidate_membership(&rule_vars, &state_vars, &types, candidate, flags.is_match)?;
        let terms = composition_env::normalize_terms(
            context,
            &types,
            &candidate.rule_subst,
            &candidate.state_subst,
        )?;
        let (rule_terms, state_terms) =
            split_candidate_substitutions(&rule_vars, &state_vars, &terms);
        let choice = select_elimination_choice(
            is_elimination,
            candidate,
            &source_premises,
            source_elimination_limit,
        )?;
        let rule = apply_candidate_to_source(owner, context, rule, &types, &rule_terms)?;
        let state = apply_candidate_to_source(owner, context, state, &types, &state_terms)?;
        let (_, proof) = build_exact_resolution(
            &rule,
            &state,
            selected,
            m,
            flags,
            &candidate.residual_pairs,
            choice,
        )?;
        Ok(replay_exact_resolution(
            owner,
            context,
            rule,
            state,
            ResolutionReplay {
                selected,
                premise_count: m,
                flags,
                residual: &candidate.residual_pairs,
                elimination_choice: choice,
                proof: &proof,
            },
        )?
        .0)
    }

    /// Discharge subgoal `i` using its first alpha-equal implication premise.
    /// `i` is Isabelle's one-based outer premise index.
    pub fn eq_assumption(
        owner: &TrustedTheory,
        context: &ProofContext,
        i: usize,
        state: &KernelThm,
    ) -> Result<KernelThm, KernelError> {
        let selected = i.checked_sub(1).ok_or(KernelError::SubgoalIndexOutOfRange {
            index: i,
            nprems: state.prop().term().nprems(),
        })?;
        let source = replay_current_source(owner, context, state)?;
        let (outer, _) = source.prop().term().dest_imp_chain();
        let goal = outer
            .get(selected)
            .ok_or(KernelError::SubgoalIndexOutOfRange { index: i, nprems: outer.len() })?;
        let (_, choice, _) = inspect_assumption_spine(goal, None, &[], None, true)?;
        let (_, proof) = build_assumption_proof(&source, selected, choice, &[], None, true)?;
        Ok(replay_eq_assumption(owner, context, source, selected, choice, &proof)?.0)
    }
}
