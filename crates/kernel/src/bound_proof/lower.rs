use std::{collections::BTreeMap, sync::Arc};

use crate::{CProp, Derivation, KernelError, KernelThm, Term};

use super::{
    BinaryRule, BoundProofError, LeafInstance, Node, Proof, Sources, TermKey, terms, transform,
};

pub(super) fn lower_theorem(
    theorem: &KernelThm,
    sources: &Sources<'_>,
) -> Result<Proof, KernelError> {
    let hypotheses: Vec<_> = theorem.hyps().iter().map(|hyp| hyp.term().clone()).collect();
    let body = lower_body(theorem, &hypotheses, sources)?;
    Ok(introduce(&hypotheses, body))
}

pub(super) fn introduce(hypotheses: &[Term], mut body: Proof) -> Proof {
    for assumption in hypotheses.iter().rev() {
        body = Arc::new(Node::ImpliesIntro { assumption: assumption.clone(), body });
    }
    body
}

fn find_hypothesis(proposition: &Term, scope: &[Term]) -> Result<Proof, KernelError> {
    let slot = scope
        .iter()
        .rev()
        .position(|hyp| hyp.alpha_eq(proposition))
        .ok_or(BoundProofError::MissingHypothesis)?;
    Ok(Arc::new(Node::Hyp(slot)))
}

fn use_closed(
    mut proof: Proof,
    hypotheses: &[CProp],
    scope: &[Term],
) -> Result<Proof, KernelError> {
    for hypothesis in hypotheses {
        proof = Arc::new(Node::ImpliesElim(proof, find_hypothesis(hypothesis.term(), scope)?));
    }
    Ok(proof)
}

fn use_premise(
    theorem: &KernelThm,
    scope: &[Term],
    sources: &Sources<'_>,
) -> Result<Proof, KernelError> {
    use_closed(lower_theorem(theorem, sources)?, theorem.hyps(), scope)
}

// Exhaustive source table. Each recursive premise is lowered *before* applying
// the recorded transformation; substitutions never move below source binders.
fn lower_body(
    theorem: &KernelThm,
    scope: &[Term],
    sources: &Sources<'_>,
) -> Result<Proof, KernelError> {
    let use_proof = |premise| use_premise(premise, scope, sources);
    let binary = |rule, left, right| {
        Ok(Arc::new(Node::Binary { rule, left: use_proof(left)?, right: use_proof(right)? }))
    };
    let result = match theorem.derivation() {
        Derivation::Assume { prop } => return find_hypothesis(prop.term(), scope),
        Derivation::Weaken { premise, .. } => return use_proof(premise),

        Derivation::Reflexive { term } => Node::Reflexive(term.term().clone()),
        Derivation::BetaConversion { redex } => Node::Beta(redex.term().clone()),
        Derivation::EtaConversion { redex } => Node::Eta(redex.term().clone()),

        Derivation::Symmetric { premise } => Node::EqSym(use_proof(premise)?),
        Derivation::Transitive { left, right } => {
            return binary(BinaryRule::Transitive, left, right);
        },
        Derivation::Combination { function, argument } => {
            return binary(BinaryRule::Combination, function, argument);
        },
        Derivation::EqualIntr { left, right } => return binary(BinaryRule::EqualIntr, left, right),
        Derivation::EqualElim { equality, minor } => {
            return binary(BinaryRule::EqualElim, equality, minor);
        },
        Derivation::ImpliesElim { major, minor } => {
            Node::ImpliesElim(use_proof(major)?, use_proof(minor)?)
        },
        Derivation::ImpliesIntr { assumption, premise } => {
            let mut nested = scope.to_vec();
            nested.push(assumption.term().clone());
            Node::ImpliesIntro {
                assumption: assumption.term().clone(),
                body: use_premise(premise, &nested, sources)?,
            }
        },
        Derivation::ForallIntr { variable, premise } => {
            let Term::Free { name, ty } = variable.term() else {
                return Err(KernelError::NotAbstractable(variable.ty()));
            };
            Node::ForallIntro {
                name: name.clone(),
                ty: ty.clone(),
                body: transform::bind_free(use_proof(premise)?, name, ty)?,
            }
        },
        Derivation::ForallElim { forall, arg } => {
            Node::ForallElim { premise: use_proof(forall)?, argument: arg.term().clone() }
        },
        Derivation::Abstraction { variable_name, variable_type, premise } => Node::EqAbs {
            name: variable_name.clone(),
            ty: variable_type.clone(),
            body: transform::bind_free(use_proof(premise)?, variable_name, variable_type)?,
        },
        Derivation::Generalize { type_names, term_names, index, premise, .. } => {
            return transform::generalize(use_proof(premise)?, type_names, term_names, *index);
        },
        Derivation::ExportScope { scope: capsule, premise } => {
            return super::scope_lower::lower_export_scope(theorem, capsule, use_proof(premise)?);
        },
        Derivation::Instantiate { type_inst, subst, premise } => {
            let proof = transform::instantiate(lower_theorem(premise, sources)?, type_inst, subst)?;
            return use_closed(proof, premise.hyps(), scope);
        },
        Derivation::SubstPremise { equality, goal_state, selected_subgoal_index } => {
            return lower_subst(equality, goal_state, *selected_subgoal_index, scope, sources);
        },
        Derivation::Resolve1Match { rule, goal_state, selected_subgoal_index, subst } => {
            return lower_resolution(
                rule,
                goal_state,
                *selected_subgoal_index,
                subst,
                scope,
                sources,
            );
        },
        Derivation::SolveConstraints { premise, .. }
        | Derivation::AdjustMaxIndex { premise, .. }
        | Derivation::Transfer { premise } => return use_proof(premise),
        Derivation::Bicompose { rule, state, proof, .. } => {
            let local = Sources::collect_pair(rule, state);
            let occurrences = local
                .leaves
                .iter()
                .map(|leaf| {
                    sources.indexes.get(&std::ptr::from_ref(*leaf)).copied().ok_or(
                        BoundProofError::UnauthorizedLeaf { leaf: sources.leaves.len() }.into(),
                    )
                })
                .collect::<Result<Vec<_>, KernelError>>()?;
            let rebound = transform::rebind_sources(&proof.root, &occurrences)?;
            return use_closed(rebound, theorem.hyps(), scope);
        },
        Derivation::SourceInstantiate { premise, proof, .. }
        | Derivation::StripShyps { premise, proof }
        | Derivation::EqAssumption { state: premise, proof, .. }
        | Derivation::Assumption { state: premise, proof, .. }
        | Derivation::SourceRenameIndex { premise, proof, .. }
        | Derivation::PermutePrems { premise, proof, .. }
        | Derivation::LiftRule { premise, proof, .. }
        | Derivation::RotateRule { premise, proof, .. } => {
            // The owner's replay checked this exact recorded adapter proof.
            // Re-deriving it here could lose source-local sort witnesses or
            // beta conversions introduced by instantiation. Its leaf slots
            // refer to the immediate source, not this outer proof; rebind
            // only those source occurrences.
            let local = Sources::collect(premise);
            let occurrences = local
                .leaves
                .iter()
                .map(|leaf| {
                    sources.indexes.get(&std::ptr::from_ref(*leaf)).copied().ok_or(
                        BoundProofError::UnauthorizedLeaf { leaf: sources.leaves.len() }.into(),
                    )
                })
                .collect::<Result<Vec<_>, KernelError>>()?;
            let rebound = transform::rebind_sources(&proof.root, &occurrences)?;
            return use_closed(rebound, premise.hyps(), scope);
        },
        Derivation::UnconstrainT { .. } => {
            let source = sources
                .indexes
                .get(&std::ptr::from_ref(theorem))
                .copied()
                .ok_or(BoundProofError::UnauthorizedLeaf { leaf: sources.leaves.len() })?;
            Node::ClosedExportTransport(make_leaf_instance(source, theorem)?)
        },
        Derivation::AxiomInstance { .. }
        | Derivation::ConservativeDefinition { .. }
        | Derivation::OfClass { .. }
        | Derivation::TheoremRef { .. } => {
            let source = sources
                .indexes
                .get(&std::ptr::from_ref(theorem))
                .copied()
                .ok_or(BoundProofError::UnauthorizedLeaf { leaf: sources.leaves.len() })?;
            Node::AuthorizedLeaf(make_leaf_instance(source, theorem)?)
        },
    };
    Ok(Arc::new(result))
}

pub(super) fn make_leaf_instance(
    source: usize,
    theorem: &KernelThm,
) -> Result<LeafInstance, KernelError> {
    if !theorem.hyps().is_empty() {
        return Err(BoundProofError::UnauthorizedLeaf { leaf: source }.into());
    }
    let mut atoms = std::collections::BTreeSet::new();
    terms::collect_type_atoms(theorem.prop().term(), &mut atoms);
    let types = atoms.into_iter().map(|ty| (ty.clone(), ty)).collect();
    let mut terms = BTreeMap::new();
    collect_variables(theorem.prop().term(), &mut terms);
    Ok(LeafInstance { source, types, terms })
}

fn collect_variables(term: &Term, variables: &mut BTreeMap<TermKey, Term>) {
    if let Some(key) = TermKey::from_term(term) {
        variables.entry(key).or_insert_with(|| term.clone());
        return;
    }
    match term {
        Term::Abs { body, .. } | Term::Forall { body, .. } => collect_variables(body, variables),
        Term::App { func: left, arg: right, .. }
        | Term::Eq { lhs: left, rhs: right, .. }
        | Term::Imp { premise: left, conclusion: right } => {
            collect_variables(left, variables);
            collect_variables(right, variables);
        },
        _ => {},
    }
}

fn lower_subst(
    equality: &KernelThm,
    goal: &KernelThm,
    selected: usize,
    scope: &[Term],
    sources: &Sources<'_>,
) -> Result<Proof, KernelError> {
    let (_, _, rhs) = equality.prop().term().dest_eq().ok_or(KernelError::NotEquality)?;
    let (mut premises, _) = goal.prop().term().dest_imp_chain();
    let count = premises.len();
    *premises
        .get_mut(selected)
        .ok_or(KernelError::SubgoalIndexOutOfRange { index: selected, nprems: count })? =
        rhs.clone();
    let mut nested = scope.to_vec();
    nested.extend_from_slice(&premises);
    let mut proof = use_premise(goal, &nested, sources)?;
    for (index, premise) in premises.iter().enumerate() {
        let mut argument = find_hypothesis(premise, &nested)?;
        if index == selected {
            argument = Arc::new(Node::Binary {
                rule: BinaryRule::EqualElim,
                left: Arc::new(Node::EqSym(use_premise(equality, &nested, sources)?)),
                right: argument,
            });
        }
        proof = Arc::new(Node::ImpliesElim(proof, argument));
    }
    Ok(introduce(&premises, proof))
}

fn lower_resolution(
    rule: &KernelThm,
    goal: &KernelThm,
    selected: usize,
    substitutions: &[crate::InstEntry],
    scope: &[Term],
    sources: &Sources<'_>,
) -> Result<Proof, KernelError> {
    let (source_premises, _) = rule.prop().term().dest_imp_chain();
    let rule_premises: Vec<_> =
        source_premises.iter().map(|premise| premise.instantiate_vars(substitutions)).collect();
    let result = goal.prop().term().replace_subgoal_with_premises(selected, &rule_premises)?;
    let (premises, _) = result.dest_imp_chain();
    let mut nested = scope.to_vec();
    nested.extend_from_slice(&premises);
    let mut proof = use_premise(goal, &nested, sources)?;
    let (goal_premises, _) = goal.prop().term().dest_imp_chain();
    for (index, premise) in goal_premises.iter().enumerate() {
        let argument = if index == selected {
            let root = transform::instantiate(
                lower_theorem(rule, sources)?,
                &crate::TypeInstantiation::empty(),
                substitutions,
            )?;
            let mut argument = use_closed(root, rule.hyps(), &nested)?;
            for premise in &rule_premises {
                argument =
                    Arc::new(Node::ImpliesElim(argument, find_hypothesis(premise, &nested)?));
            }
            argument
        } else {
            find_hypothesis(premise, &nested)?
        };
        proof = Arc::new(Node::ImpliesElim(proof, argument));
    }
    Ok(introduce(&premises, proof))
}
