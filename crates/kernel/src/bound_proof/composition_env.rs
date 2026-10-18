//! A proposed unifier is finite data, never proof authority.
use std::collections::{BTreeMap, BTreeSet};

use crate::{
    CTerm, InstEntry, KernelError, Name, ProofContext, Term, Ty, TypeInstantiation, TypeVarId,
};

use super::{BoundProofError, inspect::ProofVariables};

pub(super) type TermKey = (Name, usize, Ty);

// Bound materialized candidates before recursive term/type validation and DAG replay.
const MAX_CANDIDATE_ASSIGNMENTS: usize = 4096;
pub(super) const MAX_CANDIDATE_NODES: usize = 65_536;
pub(super) const MAX_CANDIDATE_DEPTH: usize = 256;

#[derive(Clone, Copy)]
pub(super) struct TermCost {
    pub(super) nodes: usize,
    pub(super) annotations: usize,
    pub(super) depth: usize,
}

pub(super) fn local_annotations(term: &Term) -> [Option<&Ty>; 2] {
    match term {
        Term::Const { ty, .. }
        | Term::Free { ty, .. }
        | Term::Var { ty, .. }
        | Term::Bound { ty, .. }
        | Term::App { ty, .. } => [Some(ty), None],
        Term::Abs { param_ty, ty, .. } => [Some(param_ty), Some(ty)],
        Term::Forall { param_ty, .. } => [Some(param_ty), None],
        Term::Eq { object_ty, .. } => [Some(object_ty), None],
        Term::Imp { .. } => [None, None],
    }
}

pub(super) fn check_candidate_budget(
    kind: &'static str,
    resource: &'static str,
    size: usize,
    limit: usize,
) -> Result<(), KernelError> {
    if size > limit {
        return Err(BoundProofError::CandidateResourceLimit { kind, resource, limit }.into());
    }
    Ok(())
}

pub(super) fn estimate_term_expansion(
    term: &Term,
    known_terms: &BTreeMap<TermKey, TermCost>,
    known_types: &BTreeMap<TypeVarId, (usize, usize)>,
) -> Result<TermCost, KernelError> {
    let mut stack = vec![(term, 1usize)];
    let mut cost = TermCost { nodes: 0, annotations: 0, depth: 0 };
    while let Some((current, level)) = stack.pop() {
        let replacement = match current {
            Term::Var { name, index, ty } => {
                known_terms.get(&(name.clone(), *index, ty.clone())).copied()
            },
            _ => None,
        };
        let local = replacement.unwrap_or(TermCost { nodes: 1, annotations: 0, depth: 1 });
        cost.nodes = cost.nodes.saturating_add(local.nodes);
        cost.annotations = cost.annotations.saturating_add(local.annotations);
        cost.depth = cost.depth.max(level.saturating_add(local.depth - 1));
        check_candidate_budget("term", "nodes", cost.nodes, MAX_CANDIDATE_NODES)?;
        check_candidate_budget("term", "depth", cost.depth, MAX_CANDIDATE_DEPTH)?;
        if replacement.is_none() {
            for ty in local_annotations(current).into_iter().flatten() {
                let (size, _) = estimate_type_expansion(ty, known_types)?;
                cost.annotations = cost.annotations.saturating_add(size);
            }
            check_candidate_budget(
                "term type",
                "total nodes",
                cost.annotations,
                MAX_CANDIDATE_NODES,
            )?;
        }
        match current {
            Term::Abs { body, .. } | Term::Forall { body, .. } => stack.push((body, level + 1)),
            Term::App { func, arg, .. } => {
                stack.extend([(func.as_ref(), level + 1), (arg.as_ref(), level + 1)])
            },
            Term::Eq { lhs, rhs, .. } => {
                stack.extend([(lhs.as_ref(), level + 1), (rhs.as_ref(), level + 1)])
            },
            Term::Imp { premise, conclusion } => {
                stack.extend([(premise.as_ref(), level + 1), (conclusion.as_ref(), level + 1)])
            },
            _ => {},
        }
    }
    Ok(cost)
}

pub(super) fn estimate_type_expansion(
    ty: &Ty,
    known: &BTreeMap<TypeVarId, (usize, usize)>,
) -> Result<(usize, usize), KernelError> {
    let mut stack = vec![(ty, 1usize)];
    let (mut nodes, mut depth) = (0usize, 0usize);
    while let Some((current, level)) = stack.pop() {
        let mut size_height = (1, 1);
        if let Some((_, args)) = current.dest_type() {
            stack.extend(args.iter().map(|arg| (arg, level + 1)));
        } else {
            let mut key = None;
            current.for_each_type_var(&mut |name, index, sort| {
                key = Some((name.clone(), index, sort.clone()));
            });
            if let Some((name, index, sort)) = key {
                let index = u32::try_from(index).map_err(|_| {
                    KernelError::TypeVariableIndexOutOfRange { name: name.clone(), index }
                })?;
                size_height =
                    known.get(&TypeVarId::new(name, index, sort)).copied().unwrap_or((1, 1));
            }
        }
        nodes = nodes.saturating_add(size_height.0);
        depth = depth.max(level.saturating_add(size_height.1 - 1));
        check_candidate_budget("type", "nodes", nodes, MAX_CANDIDATE_NODES)?;
        check_candidate_budget("type", "depth", depth, MAX_CANDIDATE_DEPTH)?;
    }
    Ok((nodes, depth))
}

// Reject expensive type substitutions before validation constructs substituted
// key and replacement types. The later pass checks the fully expanded environment.
fn check_proposed_term_budget(
    rule: &[InstEntry],
    state: &[InstEntry],
    type_sizes: &BTreeMap<TypeVarId, (usize, usize)>,
) -> Result<(), KernelError> {
    let mut total_nodes = 0usize;
    let mut total_annotations = 0usize;
    for entry in rule.iter().chain(state) {
        let cost =
            estimate_term_expansion(entry.replacement().term(), &BTreeMap::new(), type_sizes)?;
        let (key_annotations, _) = estimate_type_expansion(entry.var_ty(), type_sizes)?;
        total_nodes = total_nodes.saturating_add(cost.nodes);
        total_annotations =
            total_annotations.saturating_add(cost.annotations).saturating_add(key_annotations);
        check_candidate_budget("term", "total nodes", total_nodes, MAX_CANDIDATE_NODES)?;
        check_candidate_budget("term type", "total nodes", total_annotations, MAX_CANDIDATE_NODES)?;
    }
    Ok(())
}

fn collect_term_keys(term: &Term) -> BTreeSet<TermKey> {
    let mut variables = ProofVariables::default();
    variables.visit_term(term);
    variables.vars
}

fn collect_type_keys(ty: &Ty) -> Result<BTreeSet<TypeVarId>, KernelError> {
    let mut keys = BTreeSet::new();
    let mut error = None;
    ty.for_each_type_var(&mut |name, index, sort| match u32::try_from(index) {
        Ok(index) => {
            keys.insert(TypeVarId::new(name.clone(), index, sort.clone()));
        },
        Err(_) => {
            error = Some(KernelError::TypeVariableIndexOutOfRange { name: name.clone(), index })
        },
    });
    if let Some(error) = error {
        return Err(error);
    }
    Ok(keys)
}

pub(super) fn normalize_types(
    context: &ProofContext,
    proposed: &TypeInstantiation,
) -> Result<TypeInstantiation, KernelError> {
    context.validate_type_instantiation(proposed)?;
    check_candidate_budget(
        "type",
        "assignments",
        proposed.iter().count(),
        MAX_CANDIDATE_ASSIGNMENTS,
    )?;
    let mut remaining: BTreeMap<_, _> =
        proposed.iter().map(|(key, replacement)| (key.clone(), replacement.clone())).collect();
    let mut normalized: BTreeMap<TypeVarId, Ty> = BTreeMap::new();
    let mut known_sizes = BTreeMap::new();
    let mut total_nodes = 0usize;
    while !remaining.is_empty() {
        let mut next = None;
        for (key, replacement) in &remaining {
            let dependencies = collect_type_keys(replacement)?;
            if dependencies.iter().all(|dep| !remaining.contains_key(dep)) {
                next = Some(key.clone());
                break;
            }
        }
        let next = next.ok_or(BoundProofError::RecursiveAssignment { kind: "type" })?;
        let source =
            remaining.remove(&next).ok_or(BoundProofError::RecursiveAssignment { kind: "type" })?;
        let (size, depth) = estimate_type_expansion(&source, &known_sizes)?;
        total_nodes = total_nodes.saturating_add(size);
        check_candidate_budget("type", "total nodes", total_nodes, MAX_CANDIDATE_NODES)?;
        let needed = collect_type_keys(&source)?;
        let known = TypeInstantiation::try_new(
            normalized
                .iter()
                .filter(|(key, _)| needed.contains(*key))
                .map(|(key, ty)| (key.clone(), ty.clone()))
                .collect(),
        )?;
        let replacement = source.subst_type_vars(&known)?;
        known_sizes.insert(next.clone(), (size, depth));
        normalized.insert(next, replacement);
    }
    TypeInstantiation::try_new(normalized)
}

fn prepare_term_assignments(
    context: &ProofContext,
    types: &TypeInstantiation,
    rule: &[InstEntry],
    state: &[InstEntry],
) -> Result<BTreeMap<TermKey, Term>, KernelError> {
    let mut assignments = BTreeMap::new();
    for entry in rule.iter().chain(state) {
        context.validate_cterm(entry.replacement())?;
        let key = (entry.name().clone(), entry.index(), entry.var_ty().clone());
        let replacement = entry.replacement().term().clone();
        let expected = key.2.subst_type_vars(types)?;
        let actual = replacement.ty().subst_type_vars(types)?;
        if actual != expected {
            return Err(KernelError::TypeMismatch { expected, actual });
        }
        if let Some(previous) = assignments.insert(key.clone(), replacement.clone())
            && previous != replacement
        {
            return Err(KernelError::DuplicateSubstitution { name: key.0, index: key.1 });
        }
    }
    Ok(assignments)
}

pub(super) fn normalize_terms(
    context: &ProofContext,
    types: &TypeInstantiation,
    rule: &[InstEntry],
    state: &[InstEntry],
) -> Result<Vec<InstEntry>, KernelError> {
    check_candidate_budget(
        "term",
        "assignments",
        rule.len().saturating_add(state.len()),
        MAX_CANDIDATE_ASSIGNMENTS,
    )?;
    let type_sizes = types
        .iter()
        .map(|(key, replacement)| {
            Ok((key.clone(), estimate_type_expansion(replacement, &BTreeMap::new())?))
        })
        .collect::<Result<BTreeMap<_, _>, KernelError>>()?;
    check_proposed_term_budget(rule, state, &type_sizes)?;
    let mut remaining = prepare_term_assignments(context, types, rule, state)?;
    let mut normalized = Vec::with_capacity(remaining.len());
    let mut known_sizes = BTreeMap::new();
    let (mut total_nodes, mut total_annotations) = (0usize, 0usize);
    while !remaining.is_empty() {
        let next = remaining
            .iter()
            .find_map(|(key, replacement)| {
                let dependencies = collect_term_keys(replacement);
                dependencies.iter().all(|dep| !remaining.contains_key(dep)).then(|| key.clone())
            })
            .ok_or(BoundProofError::RecursiveAssignment { kind: "term" })?;
        let source =
            remaining.remove(&next).ok_or(BoundProofError::RecursiveAssignment { kind: "term" })?;
        let cost = estimate_term_expansion(&source, &known_sizes, &type_sizes)?;
        total_nodes = total_nodes.saturating_add(cost.nodes);
        total_annotations = total_annotations.saturating_add(cost.annotations);
        check_candidate_budget("term", "total nodes", total_nodes, MAX_CANDIDATE_NODES)?;
        check_candidate_budget("term type", "total nodes", total_annotations, MAX_CANDIDATE_NODES)?;
        let replacement = source.instantiate_vars(&normalized);
        let term = CTerm::from_certified_subterm(replacement, context.stamp());
        known_sizes.insert(next.clone(), cost);
        normalized.push(InstEntry::new(next.0, next.1, next.2, term));
    }
    normalized
        .into_iter()
        .map(|entry| {
            let replacement = entry.replacement().term().instantiate_types(types)?;
            let term = CTerm::from_certified_subterm(replacement, context.stamp());
            context.validate_cterm(&term)?;
            Ok(InstEntry::new(entry.name().clone(), entry.index(), entry.var_ty().clone(), term))
        })
        .collect()
}
