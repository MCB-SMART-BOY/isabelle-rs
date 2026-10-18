use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use crate::{InstEntry, KernelError, KernelThm, Name, Term, TrustedTheory, Ty, TypeInstantiation};

use super::{BoundProofError, LeafInstance, Node, Proof, inspect::ProofVariables, terms};

type TermMap<'a> = dyn FnMut(&Term, usize) -> Result<Term, KernelError> + 'a;
type TypeMap<'a> = dyn FnMut(&Ty) -> Result<Ty, KernelError> + 'a;

#[derive(Clone, Copy)]
pub(super) struct ProofScope {
    pub term_depth: usize,
    pub hypothesis_depth: usize,
    pub is_source_normalization: bool,
}

// Keep all constructors together: every bound annotation and leaf-local
// instance must receive a transformation. Only the explicitly checked
// rebinding operation changes authorized occurrence slots. This exhaustive
// constructor dispatch is intentionally kept in one place for review.
pub(super) fn map_proof_with_leaves(
    proof: &Proof,
    scope: ProofScope,
    term: &mut TermMap<'_>,
    ty: &mut TypeMap<'_>,
    leaf: &mut dyn FnMut(LeafInstance, usize, bool) -> Result<Node, KernelError>,
    flex: &mut dyn FnMut(usize, usize) -> Result<Proof, KernelError>,
) -> Result<Proof, KernelError> {
    let ProofScope { term_depth: depth, hypothesis_depth: hyp_depth, is_source_normalization } =
        scope;
    let result = match proof.as_ref() {
        Node::Hyp(slot) => Node::Hyp(*slot),
        Node::EqFlex(slot) => return flex(*slot, depth),
        Node::ImpliesIntro { assumption, body } => Node::ImpliesIntro {
            assumption: term(assumption, depth)?,
            body: map_proof_with_leaves(
                body,
                ProofScope { hypothesis_depth: terms::next_depth(hyp_depth)?, ..scope },
                term,
                ty,
                leaf,
                flex,
            )?,
        },
        Node::ImpliesElim(left, right) => Node::ImpliesElim(
            map_proof_with_leaves(left, scope, term, ty, leaf, flex)?,
            map_proof_with_leaves(right, scope, term, ty, leaf, flex)?,
        ),
        Node::ForallIntro { name, ty: parameter, body } => Node::ForallIntro {
            name: name.clone(),
            ty: ty(parameter)?,
            body: map_proof_with_leaves(
                body,
                ProofScope { term_depth: terms::next_depth(depth)?, ..scope },
                term,
                ty,
                leaf,
                flex,
            )?,
        },
        Node::EqAbs { name, ty: parameter, body } => Node::EqAbs {
            name: name.clone(),
            ty: ty(parameter)?,
            body: map_proof_with_leaves(
                body,
                ProofScope { term_depth: terms::next_depth(depth)?, ..scope },
                term,
                ty,
                leaf,
                flex,
            )?,
        },
        Node::ForallElim { premise, argument } => Node::ForallElim {
            premise: map_proof_with_leaves(premise, scope, term, ty, leaf, flex)?,
            argument: term(argument, depth)?,
        },
        Node::EqSym(premise) => {
            Node::EqSym(map_proof_with_leaves(premise, scope, term, ty, leaf, flex)?)
        },
        Node::Binary { rule, left, right } => Node::Binary {
            rule: *rule,
            left: map_proof_with_leaves(left, scope, term, ty, leaf, flex)?,
            right: map_proof_with_leaves(right, scope, term, ty, leaf, flex)?,
        },
        Node::Reflexive(value) => Node::Reflexive(term(value, depth)?),
        Node::Beta(value) => {
            let mapped = term(value, depth)?;
            if is_source_normalization { Node::Reflexive(mapped) } else { Node::Beta(mapped) }
        },
        Node::Eta(value) => {
            let mapped = term(value, depth)?;
            if is_source_normalization && crate::rules::contract_eta(&mapped).is_err() {
                let reduced = crate::rules::contract_eta(value)?;
                if !mapped.alpha_eq(&term(&reduced, depth)?) {
                    return Err(BoundProofError::StatementMismatch.into());
                }
                Node::Reflexive(mapped)
            } else {
                Node::Eta(mapped)
            }
        },
        Node::AuthorizedLeaf(instance) | Node::ClosedExportTransport(instance) => {
            let is_transport = matches!(proof.as_ref(), Node::ClosedExportTransport(_));
            leaf(
                LeafInstance {
                    source: instance.source,
                    types: instance
                        .types
                        .iter()
                        .map(|(key, value)| Ok((key.clone(), ty(value)?)))
                        .collect::<Result<_, KernelError>>()?,
                    terms: instance
                        .terms
                        .iter()
                        .map(|(key, value)| Ok((key.clone(), term(value, depth)?)))
                        .collect::<Result<_, KernelError>>()?,
                },
                hyp_depth,
                is_transport,
            )?
        },
        Node::ExportHead(view) => Node::ExportHead(super::LeafExportView {
            instance: LeafInstance {
                source: view.instance.source,
                types: view
                    .instance
                    .types
                    .iter()
                    .map(|(key, value)| Ok((key.clone(), ty(value)?)))
                    .collect::<Result<_, KernelError>>()?,
                terms: view
                    .instance
                    .terms
                    .iter()
                    .map(|(key, value)| Ok((key.clone(), term(value, depth)?)))
                    .collect::<Result<_, KernelError>>()?,
            },
            slots: view.slots.clone(),
        }),
    };
    Ok(Arc::new(result))
}

fn map_proof(
    proof: &Proof,
    depth: usize,
    term: &mut TermMap<'_>,
    ty: &mut TypeMap<'_>,
) -> Result<Proof, KernelError> {
    map_proof_with_leaves(
        proof,
        ProofScope { term_depth: depth, hypothesis_depth: 0, is_source_normalization: false },
        term,
        ty,
        &mut |instance, _, is_transport| {
            Ok(if is_transport {
                Node::ClosedExportTransport(instance)
            } else {
                Node::AuthorizedLeaf(instance)
            })
        },
        &mut |slot, _| Ok(Arc::new(Node::EqFlex(slot))),
    )
}

pub(super) fn rebind_sources(proof: &Proof, occurrences: &[usize]) -> Result<Proof, KernelError> {
    map_proof_with_leaves(
        proof,
        ProofScope { term_depth: 0, hypothesis_depth: 0, is_source_normalization: false },
        &mut |term, _| Ok(term.clone()),
        &mut |ty| Ok(ty.clone()),
        &mut |mut instance, _, is_transport| {
            instance.source = occurrences
                .get(instance.source)
                .copied()
                .ok_or(BoundProofError::UnauthorizedLeaf { leaf: instance.source })?;
            Ok(if is_transport {
                Node::ClosedExportTransport(instance)
            } else {
                Node::AuthorizedLeaf(instance)
            })
        },
        &mut |slot, _| Ok(Arc::new(Node::EqFlex(slot))),
    )
}
pub(super) fn map_export_proof(
    root: &Proof,
    owner: &TrustedTheory,
    sources: &super::Sources<'_>,
    plan: &super::export::ExportPlan,
) -> Result<Proof, KernelError> {
    map_proof_with_leaves(
        root,
        ProofScope { term_depth: 0, hypothesis_depth: 0, is_source_normalization: false },
        &mut |term, depth| {
            terms::rewrite_term(term, depth, &mut |_, _| Ok(None), &mut |ty| {
                terms::replace_type_atoms(ty, &plan.replacements)
            })
        },
        &mut |ty| terms::replace_type_atoms(ty, &plan.replacements),
        &mut |instance, hyp_depth, is_transport| {
            if is_transport {
                return Ok(Node::ClosedExportTransport(instance));
            }
            let source = sources
                .leaves
                .get(instance.source)
                .ok_or(BoundProofError::UnauthorizedLeaf { leaf: instance.source })?;
            let slots = plan.collect_leaf_slots(owner, source, &instance.types)?;
            let mut node = Node::ExportHead(super::LeafExportView {
                instance,
                slots: slots.iter().copied().collect(),
            });
            for slot in slots {
                let distance = plan
                    .premises
                    .len()
                    .checked_sub(slot + 1)
                    .ok_or(BoundProofError::IndexOverflow)?
                    .checked_add(hyp_depth)
                    .ok_or(BoundProofError::IndexOverflow)?;
                node = Node::ImpliesElim(Arc::new(node), Arc::new(Node::Hyp(distance)));
            }
            Ok(node)
        },
        &mut |slot, _| Ok(Arc::new(Node::EqFlex(slot))),
    )
}

pub(super) fn bind_free(proof: Proof, name: &Name, ty: &Ty) -> Result<Proof, KernelError> {
    map_proof(
        &proof,
        0,
        &mut |term, depth| {
            terms::rewrite_term(
                term,
                depth,
                &mut |node, depth| match node {
                    Term::Free { name: actual, ty: actual_ty }
                        if actual == name && actual_ty == ty =>
                    {
                        Ok(Some(Term::Bound { index: depth, ty: ty.clone() }))
                    },
                    Term::Bound { index, ty } if *index >= depth => {
                        Ok(Some(Term::Bound { index: terms::next_depth(*index)?, ty: ty.clone() }))
                    },
                    _ => Ok(None),
                },
                &mut |ty| Ok(ty.clone()),
            )
        },
        &mut |ty| Ok(ty.clone()),
    )
}

pub(super) fn generalize(
    proof: Proof,
    type_names: &BTreeSet<Name>,
    term_names: &BTreeSet<Name>,
    index: usize,
) -> Result<Proof, KernelError> {
    if type_names.is_empty() && term_names.is_empty() {
        return Ok(proof);
    }
    map_proof(
        &proof,
        0,
        &mut |term, _| term.generalize_vars(type_names, term_names, index),
        &mut |ty| ty.generalize_type(type_names, index),
    )
}

pub(super) fn instantiate(
    proof: Proof,
    types: &TypeInstantiation,
    substitutions: &[InstEntry],
) -> Result<Proof, KernelError> {
    let typed = map_proof(&proof, 0, &mut |term, _| term.instantiate_types(types), &mut |ty| {
        ty.subst_type_vars(types)
    })?;
    let entries = substitutions
        .iter()
        .map(|entry| ((entry.name(), entry.index(), entry.var_ty()), entry.replacement().term()))
        .collect();
    map_proof(&typed, 0, &mut |term, _| terms::instantiate_term(term, &entries), &mut |ty| {
        Ok(ty.clone())
    })
}

pub(super) fn instantiate_source_order(
    proof: Proof,
    types: &TypeInstantiation,
    substitutions: &[InstEntry],
) -> Result<Proof, KernelError> {
    map_proof_with_leaves(
        &proof,
        ProofScope { term_depth: 0, hypothesis_depth: 0, is_source_normalization: true },
        &mut |term, depth| terms::instantiate_source_order(term, depth, types, substitutions),
        &mut |ty| ty.subst_type_vars(types),
        &mut |instance, _, is_transport| {
            Ok(if is_transport {
                Node::ClosedExportTransport(instance)
            } else {
                Node::AuthorizedLeaf(instance)
            })
        },
        &mut |slot, _| Ok(Arc::new(Node::EqFlex(slot))),
    )
}

pub(super) fn rename_source_indices(
    proof: Proof,
    types: &TypeInstantiation,
    substitutions: &[InstEntry],
) -> Result<Proof, KernelError> {
    map_proof(
        &proof,
        0,
        &mut |term, depth| terms::instantiate_source_order_raw(term, depth, types, substitutions),
        &mut |ty| ty.subst_type_vars(types),
    )
}

pub(super) fn replace_proof_only_types_checked(
    proof: Proof,
    theorem: &KernelThm,
    owner: &TrustedTheory,
    representatives: &BTreeSet<crate::Sort>,
) -> Result<Proof, KernelError> {
    let present = super::collect_present_atoms(theorem);
    let variables = ProofVariables::collect(&proof);
    let mut max_index = variables.max_index.max(theorem.max_var_index());
    let mut dummies: BTreeMap<crate::Sort, Ty> = BTreeMap::new();
    let mut replacements = BTreeMap::new();
    for atom in variables.atoms.difference(&present) {
        let sort = atom.atomic_sort().ok_or(BoundProofError::UnsupportedSortExportVariant {
            operation: "non-atomic proof-only type",
        })?;
        let replacement =
            if let Some(witness) = crate::class_proof::find_class_witness(owner, sort, &present) {
                witness
            } else {
                let representative = representatives
                    .iter()
                    .find(|candidate| owner.signature().is_sort_le(candidate, sort))
                    .ok_or(BoundProofError::UnsupportedSortExportVariant {
                        operation: "proof-only sort without checked representative",
                    })?;
                if let Some(dummy) = dummies.get(representative) {
                    dummy.clone()
                } else {
                    let next_index = max_index.map_or(Ok(0), terms::next_depth)?;
                    let dummy = Ty::tvar("__strip_extra", next_index, representative.clone());
                    max_index = Some(next_index);
                    dummies.insert(representative.clone(), dummy.clone());
                    dummy
                }
            };
        replacements.insert(atom.clone(), replacement);
    }
    let proof = generalize_proof_only_frees(proof, theorem, &variables)?;
    if replacements.is_empty() {
        return Ok(proof);
    }
    map_proof(
        &proof,
        0,
        &mut |term, _| {
            terms::rewrite_term(term, 0, &mut |_, _| Ok(None), &mut |ty| {
                terms::replace_type_atoms(ty, &replacements)
            })
        },
        &mut |ty| terms::replace_type_atoms(ty, &replacements),
    )
}

fn generalize_proof_only_frees(
    proof: Proof,
    theorem: &KernelThm,
    variables: &ProofVariables,
) -> Result<Proof, KernelError> {
    let term_names: BTreeSet<Name> = variables
        .frees
        .iter()
        .filter(|(name, _)| !super::source_parameters::has_statement_free_name(theorem, name))
        .map(|(name, _)| name.clone())
        .collect();
    if term_names.is_empty() {
        return Ok(proof);
    }
    let start = variables.max_index.map_or(Ok(0), terms::next_depth)?;
    // Freshen proof-only parameters before a non-injective type map can merge
    // their identities. The theorem's statement and context remain unchanged.
    generalize(proof, &BTreeSet::new(), &term_names, start)
}
