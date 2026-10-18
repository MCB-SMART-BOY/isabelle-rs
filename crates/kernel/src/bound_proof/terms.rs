use std::collections::BTreeMap;

use crate::{InstEntry, KernelError, Name, Term, Ty, TypeInstantiation, TypeVarId};

use super::{BoundProofError, composition_env};

type LeafRewrite<'a> = dyn FnMut(&Term, usize) -> Result<Option<Term>, KernelError> + 'a;
type TypeRewrite<'a> = dyn FnMut(&Ty) -> Result<Ty, KernelError> + 'a;

// The single constructor table preserves every annotation, including cached
// application/equality types. A replacement is deliberately not traversed again.
pub(super) fn rewrite_term(
    term: &Term,
    depth: usize,
    leaf: &mut LeafRewrite<'_>,
    types: &mut TypeRewrite<'_>,
) -> Result<Term, KernelError> {
    if let Some(replacement) = leaf(term, depth)? {
        return Ok(replacement);
    }
    Ok(match term {
        Term::Const { name, ty } => Term::Const { name: name.clone(), ty: types(ty)? },
        Term::Free { name, ty } => Term::Free { name: name.clone(), ty: types(ty)? },
        Term::Var { name, index, ty } => {
            Term::Var { name: name.clone(), index: *index, ty: types(ty)? }
        },
        Term::Bound { index, ty } => Term::Bound { index: *index, ty: types(ty)? },
        Term::Abs { name, param_ty, body, ty } => Term::Abs {
            name: name.clone(),
            param_ty: types(param_ty)?,
            ty: types(ty)?,
            body: Box::new(rewrite_term(body, next_depth(depth)?, leaf, types)?),
        },
        Term::Forall { name, param_ty, body } => Term::Forall {
            name: name.clone(),
            param_ty: types(param_ty)?,
            body: Box::new(rewrite_term(body, next_depth(depth)?, leaf, types)?),
        },
        Term::App { func, arg, ty } => Term::App {
            func: Box::new(rewrite_term(func, depth, leaf, types)?),
            arg: Box::new(rewrite_term(arg, depth, leaf, types)?),
            ty: types(ty)?,
        },
        Term::Eq { object_ty, lhs, rhs } => Term::Eq {
            object_ty: types(object_ty)?,
            lhs: Box::new(rewrite_term(lhs, depth, leaf, types)?),
            rhs: Box::new(rewrite_term(rhs, depth, leaf, types)?),
        },
        Term::Imp { premise, conclusion } => Term::Imp {
            premise: Box::new(rewrite_term(premise, depth, leaf, types)?),
            conclusion: Box::new(rewrite_term(conclusion, depth, leaf, types)?),
        },
    })
}

/// Match the *original* typed Var key before applying the type environment.
/// Non-injective type substitutions therefore cannot conflate source binders.
pub(super) fn instantiate_source_order_raw(
    term: &Term,
    depth: usize,
    types: &TypeInstantiation,
    substitutions: &[InstEntry],
) -> Result<Term, KernelError> {
    check_source_rewrite_budget(term, types, substitutions)?;
    rewrite_term(
        term,
        depth,
        &mut |node, _| {
            let Term::Var { name, index, ty } = node else { return Ok(None) };
            Ok(substitutions
                .iter()
                .find(|entry| {
                    entry.name() == name && entry.index() == *index && entry.var_ty() == ty
                })
                .map(|entry| entry.replacement().term().clone()))
        },
        &mut |ty| ty.subst_type_vars(types),
    )
}

fn check_source_rewrite_budget(
    source: &Term,
    types: &TypeInstantiation,
    substitutions: &[InstEntry],
) -> Result<(), KernelError> {
    let type_sizes = types
        .iter()
        .map(|(key, replacement)| {
            Ok((
                key.clone(),
                composition_env::estimate_type_expansion(replacement, &BTreeMap::new())?,
            ))
        })
        .collect::<Result<BTreeMap<TypeVarId, (usize, usize)>, KernelError>>()?;
    let mut replacement_sizes = BTreeMap::new();
    for entry in substitutions {
        let size = composition_env::estimate_term_expansion(
            entry.replacement().term(),
            &BTreeMap::new(),
            &BTreeMap::new(),
        )?;
        replacement_sizes
            .insert((entry.name().clone(), entry.index(), entry.var_ty().clone()), size);
    }
    composition_env::estimate_term_expansion(source, &replacement_sizes, &type_sizes)?;
    Ok(())
}

/// The finite typed source substitution is one-shot; only its resulting term
/// is reduced, including redexes underneath binders and logical constructors.
pub(super) fn instantiate_source_order(
    term: &Term,
    depth: usize,
    types: &TypeInstantiation,
    substitutions: &[InstEntry],
) -> Result<Term, KernelError> {
    normalize_beta(instantiate_source_order_raw(term, depth, types, substitutions)?)
}

pub(super) fn normalize_beta(mut term: Term) -> Result<Term, KernelError> {
    let mut work = 0;
    normalize_beta_in_place(&mut term, &mut work)?;
    Ok(term)
}

fn normalize_beta_in_place(term: &mut Term, work: &mut usize) -> Result<(), KernelError> {
    *work = work.saturating_add(1);
    composition_env::check_candidate_budget(
        "beta normalization",
        "work",
        *work,
        composition_env::MAX_CANDIDATE_NODES,
    )?;
    match term {
        Term::App { func, arg, .. } => {
            normalize_beta_in_place(func, work)?;
            normalize_beta_in_place(arg, work)?;
            let Term::Abs { param_ty, body, .. } = func.as_ref() else {
                return Ok(());
            };
            if *param_ty != arg.ty() {
                return Err(KernelError::TypeMismatch {
                    expected: param_ty.clone(),
                    actual: arg.ty(),
                });
            }
            check_beta_reduction_budget(body, arg, work)?;
            let reduced = Term::instantiate_bound0(body, arg);
            *term = reduced;
            normalize_beta_in_place(term, work)
        },
        Term::Abs { body, .. } | Term::Forall { body, .. } => normalize_beta_in_place(body, work),
        Term::Eq { lhs, rhs, .. } => {
            normalize_beta_in_place(lhs, work)?;
            normalize_beta_in_place(rhs, work)
        },
        Term::Imp { premise, conclusion } => {
            normalize_beta_in_place(premise, work)?;
            normalize_beta_in_place(conclusion, work)
        },
        Term::Const { .. } | Term::Free { .. } | Term::Var { .. } | Term::Bound { .. } => Ok(()),
    }
}

pub(super) fn check_beta_reduction_budget(
    body: &Term,
    argument: &Term,
    work: &mut usize,
) -> Result<(), KernelError> {
    let empty = BTreeMap::new();
    let body_size = composition_env::estimate_term_expansion(body, &empty, &BTreeMap::new())?;
    let argument_size =
        composition_env::estimate_term_expansion(argument, &empty, &BTreeMap::new())?;
    let mut nodes = body_size.nodes;
    let mut annotations = body_size.annotations;
    let mut stack = vec![(body, 0usize)];
    while let Some((current, depth)) = stack.pop() {
        match current {
            Term::Bound { index, ty } if *index == depth => {
                let (bound_annotation, _) =
                    composition_env::estimate_type_expansion(ty, &BTreeMap::new())?;
                nodes = nodes.saturating_add(argument_size.nodes.saturating_sub(1));
                annotations = annotations
                    .saturating_sub(bound_annotation)
                    .saturating_add(argument_size.annotations);
            },
            Term::Abs { body, .. } | Term::Forall { body, .. } => {
                stack.push((body, depth.saturating_add(1)))
            },
            Term::App { func, arg, .. } => {
                stack.extend([(func.as_ref(), depth), (arg.as_ref(), depth)])
            },
            Term::Eq { lhs, rhs, .. } => {
                stack.extend([(lhs.as_ref(), depth), (rhs.as_ref(), depth)])
            },
            Term::Imp { premise, conclusion } => {
                stack.extend([(premise.as_ref(), depth), (conclusion.as_ref(), depth)])
            },
            _ => {},
        }
        composition_env::check_candidate_budget(
            "beta normalization",
            "nodes",
            nodes,
            composition_env::MAX_CANDIDATE_NODES,
        )?;
        composition_env::check_candidate_budget(
            "beta normalization",
            "type nodes",
            annotations,
            composition_env::MAX_CANDIDATE_NODES,
        )?;
    }
    *work = work.saturating_add(nodes);
    composition_env::check_candidate_budget(
        "beta normalization",
        "work",
        *work,
        composition_env::MAX_CANDIDATE_NODES,
    )
}

pub(super) fn next_depth(depth: usize) -> Result<usize, KernelError> {
    depth.checked_add(1).ok_or_else(|| BoundProofError::IndexOverflow.into())
}

pub(super) fn lift_term(term: &Term, amount: usize) -> Result<Term, KernelError> {
    if amount == 0 {
        return Ok(term.clone());
    }
    rewrite_term(
        term,
        0,
        &mut |node, depth| {
            let Term::Bound { index, ty } = node else { return Ok(None) };
            if *index < depth {
                return Ok(None);
            }
            let index = index.checked_add(amount).ok_or(BoundProofError::IndexOverflow)?;
            Ok(Some(Term::Bound { index, ty: ty.clone() }))
        },
        &mut |ty| Ok(ty.clone()),
    )
}

pub(super) fn replace_type_atoms(
    ty: &Ty,
    replacements: &BTreeMap<Ty, Ty>,
) -> Result<Ty, KernelError> {
    if let Some(replacement) = replacements.get(ty) {
        return Ok(replacement.clone());
    }
    let Some((name, arguments)) = ty.dest_type() else { return Ok(ty.clone()) };
    let arguments = arguments
        .iter()
        .map(|argument| replace_type_atoms(argument, replacements))
        .collect::<Result<_, _>>()?;
    Ty::apply(name.clone(), arguments)
}

pub(super) fn instantiate_term(
    term: &Term,
    entries: &BTreeMap<(&Name, usize, &Ty), &Term>,
) -> Result<Term, KernelError> {
    rewrite_term(
        term,
        0,
        &mut |node, depth| {
            let Term::Var { name, index, ty } = node else { return Ok(None) };
            match entries.get(&(name, *index, ty)) {
                Some(replacement) => Ok(Some(lift_term(replacement, depth)?)),
                None => Ok(None),
            }
        },
        &mut |ty| Ok(ty.clone()),
    )
}

pub(super) fn collect_type_atoms(term: &Term, atoms: &mut std::collections::BTreeSet<Ty>) {
    term.for_each_type_annotation(&mut |ty| {
        ty.for_each_type_atom(&mut |name, index, sort| {
            atoms.insert(match index {
                Some(index) => Ty::tvar(name.clone(), index, sort.clone()),
                None => Ty::tfree(name.clone(), sort.clone()),
            });
        });
    });
}

pub(crate) fn visit_free_variables<'a>(term: &'a Term, visit: &mut impl FnMut(&'a Name, &'a Ty)) {
    match term {
        Term::Free { name, ty } => visit(name, ty),
        Term::Abs { body, .. } | Term::Forall { body, .. } => visit_free_variables(body, visit),
        Term::App { func: left, arg: right, .. }
        | Term::Eq { lhs: left, rhs: right, .. }
        | Term::Imp { premise: left, conclusion: right } => {
            visit_free_variables(left, visit);
            visit_free_variables(right, visit);
        },
        Term::Const { .. } | Term::Var { .. } | Term::Bound { .. } => {},
    }
}
