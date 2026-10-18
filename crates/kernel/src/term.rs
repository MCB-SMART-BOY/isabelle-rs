use std::collections::BTreeSet;

use super::{
    CProp, CTerm, InstEntry, KernelError, Name, ProofContext, Ty, identity::CanonicalEncoder,
};

/// Raw term accepted at the edge of the strict kernel.
///
/// Raw terms may carry type annotations, but those annotations are not trusted
/// until checked against a `Signature` / `ProofContext`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RawTerm {
    Const { name: Name, ty: Ty },
    Free { name: Name, ty: Ty },
    Var { name: Name, index: usize, ty: Ty },
    Bound(usize),
    Abs { name: Name, ty: Ty, body: Box<RawTerm> },
    Forall { name: Name, param_ty: Ty, body: Box<RawTerm> },
    App { func: Box<RawTerm>, arg: Box<RawTerm> },
    Eq { lhs: Box<RawTerm>, rhs: Box<RawTerm> },
    Imp { premise: Box<RawTerm>, conclusion: Box<RawTerm> },
}

impl RawTerm {
    pub fn const_(name: impl Into<Name>, ty: Ty) -> Self {
        RawTerm::Const { name: name.into(), ty }
    }

    pub fn free(name: impl Into<Name>, ty: Ty) -> Self {
        RawTerm::Free { name: name.into(), ty }
    }

    pub fn var(name: impl Into<Name>, index: usize, ty: Ty) -> Self {
        RawTerm::Var { name: name.into(), index, ty }
    }

    pub fn bound(index: usize) -> Self {
        RawTerm::Bound(index)
    }

    pub fn abs(name: impl Into<Name>, ty: Ty, body: RawTerm) -> Self {
        RawTerm::Abs { name: name.into(), ty, body: Box::new(body) }
    }

    pub fn app(func: RawTerm, arg: RawTerm) -> Self {
        RawTerm::App { func: Box::new(func), arg: Box::new(arg) }
    }

    pub fn eq(lhs: RawTerm, rhs: RawTerm) -> Self {
        RawTerm::Eq { lhs: Box::new(lhs), rhs: Box::new(rhs) }
    }

    pub fn forall(name: impl Into<Name>, param_ty: Ty, body: RawTerm) -> Self {
        RawTerm::Forall { name: name.into(), param_ty, body: Box::new(body) }
    }

    pub fn imp(premise: RawTerm, conclusion: RawTerm) -> Self {
        RawTerm::Imp { premise: Box::new(premise), conclusion: Box::new(conclusion) }
    }

    /// Check if this term contains any free variables (`RawTerm::Free`).
    pub fn has_free_vars(&self) -> bool {
        let mut stack = vec![self];
        while let Some(t) = stack.pop() {
            match t {
                RawTerm::Free { .. } | RawTerm::Var { .. } => return true,
                RawTerm::Abs { body, .. } | RawTerm::Forall { body, .. } => stack.push(body),
                RawTerm::App { func, arg } => {
                    stack.push(arg);
                    stack.push(func);
                },
                RawTerm::Eq { lhs, rhs } | RawTerm::Imp { premise: lhs, conclusion: rhs } => {
                    stack.push(rhs);
                    stack.push(lhs);
                },
                RawTerm::Const { .. } | RawTerm::Bound(_) => {},
            }
        }
        false
    }

    pub(crate) fn write_canonical(&self, encoder: &mut CanonicalEncoder) {
        match self {
            RawTerm::Const { name, ty } => {
                encoder.write_u8(0);
                encoder.write_name(name);
                ty.write_canonical(encoder);
            },
            RawTerm::Free { name, ty } => {
                encoder.write_u8(1);
                encoder.write_name(name);
                ty.write_canonical(encoder);
            },
            RawTerm::Var { name, index, ty } => {
                encoder.write_u8(2);
                encoder.write_name(name);
                encoder.write_u64(*index as u64);
                ty.write_canonical(encoder);
            },
            RawTerm::Bound(i) => {
                encoder.write_u8(3);
                encoder.write_u64(*i as u64);
            },
            RawTerm::Abs { name, ty, body } => {
                encoder.write_u8(4);
                encoder.write_name(name);
                ty.write_canonical(encoder);
                body.write_canonical(encoder);
            },
            RawTerm::Forall { name, param_ty, body } => {
                encoder.write_u8(5);
                encoder.write_name(name);
                param_ty.write_canonical(encoder);
                body.write_canonical(encoder);
            },
            RawTerm::App { func, arg } => {
                encoder.write_u8(6);
                func.write_canonical(encoder);
                arg.write_canonical(encoder);
            },
            RawTerm::Eq { lhs, rhs } => {
                encoder.write_u8(7);
                lhs.write_canonical(encoder);
                rhs.write_canonical(encoder);
            },
            RawTerm::Imp { premise, conclusion } => {
                encoder.write_u8(8);
                premise.write_canonical(encoder);
                conclusion.write_canonical(encoder);
            },
        }
    }

    /// Check if this raw term mentions a specific constant name.
    pub fn mentions_const(&self, name: &Name) -> bool {
        let mut stack = vec![self];
        while let Some(t) = stack.pop() {
            match t {
                RawTerm::Const { name: n, .. } if n == name => return true,
                RawTerm::Abs { body, .. } | RawTerm::Forall { body, .. } => stack.push(body),
                RawTerm::App { func, arg } => {
                    stack.push(arg);
                    stack.push(func);
                },
                RawTerm::Eq { lhs, rhs } | RawTerm::Imp { premise: lhs, conclusion: rhs } => {
                    stack.push(rhs);
                    stack.push(lhs);
                },
                _ => {},
            }
        }
        false
    }
    pub(crate) fn referenced_consts(&self, names: &mut std::collections::BTreeSet<Name>) {
        match self {
            Self::Const { name, .. } => {
                names.insert(name.clone());
            },
            Self::Abs { body, .. } | Self::Forall { body, .. } => body.referenced_consts(names),
            Self::App { func, arg } => {
                func.referenced_consts(names);
                arg.referenced_consts(names);
            },
            Self::Eq { lhs, rhs } | Self::Imp { premise: lhs, conclusion: rhs } => {
                lhs.referenced_consts(names);
                rhs.referenced_consts(names);
            },
            _ => {},
        }
    }
    pub(crate) fn for_each_annotation(&self, f: &mut impl FnMut(&Ty)) {
        match self {
            Self::Const { ty, .. } | Self::Free { ty, .. } | Self::Var { ty, .. } => f(ty),
            Self::Abs { ty, body, .. } | Self::Forall { param_ty: ty, body, .. } => {
                f(ty);
                body.for_each_annotation(f);
            },
            Self::App { func, arg } => {
                func.for_each_annotation(f);
                arg.for_each_annotation(f);
            },
            Self::Eq { lhs, rhs } | Self::Imp { premise: lhs, conclusion: rhs } => {
                lhs.for_each_annotation(f);
                rhs.for_each_annotation(f);
            },
            Self::Bound(_) => {},
        }
    }
}

pub(crate) fn abstract_definition_frees(
    raw: RawTerm,
    parameters: &[(Name, Ty)],
    depth: usize,
) -> Result<RawTerm, KernelError> {
    let recurse = |raw, depth| abstract_definition_frees(raw, parameters, depth);
    Ok(match raw {
        RawTerm::Free { name, ty } => {
            let position = parameters
                .iter()
                .position(|(parameter, _)| *parameter == name)
                .ok_or_else(|| KernelError::UndeclaredFree(name.clone()))?;
            let declared = &parameters[position].1;
            if declared != &ty {
                return Err(KernelError::TypeMismatch { expected: declared.clone(), actual: ty });
            }
            let index = depth
                .checked_add(parameters.len() - position - 1)
                .ok_or_else(|| KernelError::Invariant("definition binder index overflow".into()))?;
            RawTerm::Bound(index)
        },
        RawTerm::Bound(index) if index >= depth => return Err(KernelError::UnboundBound(index)),
        RawTerm::Bound(index) => RawTerm::Bound(index),
        RawTerm::Abs { name, ty, body } => RawTerm::abs(name, ty, recurse(*body, depth + 1)?),
        RawTerm::Forall { name, param_ty, body } => {
            RawTerm::forall(name, param_ty, recurse(*body, depth + 1)?)
        },
        RawTerm::App { func, arg } => RawTerm::app(recurse(*func, depth)?, recurse(*arg, depth)?),
        RawTerm::Eq { lhs, rhs } => RawTerm::eq(recurse(*lhs, depth)?, recurse(*rhs, depth)?),
        RawTerm::Imp { premise, conclusion } => {
            RawTerm::imp(recurse(*premise, depth)?, recurse(*conclusion, depth)?)
        },
        other => other,
    })
}

/// Apply type substitution to a RawTerm with validation.
/// Rejects missing, extra, and duplicate inst entries.
pub fn subst_types(
    raw: &RawTerm,
    type_inst: &crate::logic::TypeInstantiation,
) -> Result<RawTerm, KernelError> {
    // An occurrence is identified by name, index and exact sort.
    let mut type_vars: Vec<(Name, usize, crate::Sort)> = Vec::new();
    collect_type_vars(raw, &mut type_vars);
    let mut seen: std::collections::BTreeMap<(Name, usize), crate::Sort> =
        std::collections::BTreeMap::new();
    for (name, index, sort) in &type_vars {
        if let Some(previous_sort) = seen.insert((name.clone(), *index), sort.clone())
            && previous_sort != *sort
        {
            return Err(KernelError::Invariant(format!(
                "schematic type variable `{name}` at index {index} has conflicting sorts"
            )));
        }
        let index = u32::try_from(*index).map_err(|_| {
            KernelError::TypeVariableIndexOutOfRange { name: name.clone(), index: *index }
        })?;
        let id = crate::logic::TypeVarId::new(name.clone(), index, sort.clone());
        if type_inst.get(&id).is_none() {
            return Err(KernelError::Invariant(format!(
                "unresolved schematic type variable {id:?} in schema"
            )));
        }
    }
    for (id, _) in type_inst.iter() {
        if !type_vars.iter().any(|(name, index, sort)| {
            name == &id.name && *index == id.index as usize && sort == &id.sort
        }) {
            return Err(KernelError::Invariant(format!(
                "type instantiation {id:?} not present in schema"
            )));
        }
    }
    apply_type_subst(raw, type_inst)
}

fn collect_type_vars(raw: &RawTerm, out: &mut Vec<(Name, usize, crate::Sort)>) {
    let push = |ty: &Ty, out: &mut Vec<(Name, usize, crate::Sort)>| {
        ty.for_each_type_var(&mut |name, index, sort| {
            if !out.iter().any(|(n, i, s)| n == name && *i == index && s == sort) {
                out.push((name.clone(), index, sort.clone()));
            }
        });
    };
    match raw {
        RawTerm::Const { ty, .. } | RawTerm::Free { ty, .. } | RawTerm::Var { ty, .. } => {
            push(ty, out);
        },
        RawTerm::Abs { ty, body, .. } => {
            push(ty, out);
            collect_type_vars(body, out);
        },
        RawTerm::Forall { param_ty, body, .. } => {
            push(param_ty, out);
            collect_type_vars(body, out);
        },
        RawTerm::App { func, arg } => {
            collect_type_vars(func, out);
            collect_type_vars(arg, out);
        },
        RawTerm::Eq { lhs, rhs } | RawTerm::Imp { premise: lhs, conclusion: rhs } => {
            collect_type_vars(lhs, out);
            collect_type_vars(rhs, out);
        },
        RawTerm::Bound(_) => {},
    }
}

fn apply_type_subst(
    raw: &RawTerm,
    inst: &crate::logic::TypeInstantiation,
) -> Result<RawTerm, KernelError> {
    let subst = |ty: &Ty| ty.subst_type_vars(inst);
    Ok(match raw {
        RawTerm::Const { name, ty } => RawTerm::Const { name: name.clone(), ty: subst(ty)? },
        RawTerm::Free { name, ty } => RawTerm::Free { name: name.clone(), ty: subst(ty)? },
        RawTerm::Var { name, index, ty } => {
            RawTerm::Var { name: name.clone(), index: *index, ty: subst(ty)? }
        },
        RawTerm::Bound(i) => RawTerm::Bound(*i),
        RawTerm::Abs { name, ty, body } => RawTerm::Abs {
            name: name.clone(),
            ty: subst(ty)?,
            body: Box::new(apply_type_subst(body, inst)?),
        },
        RawTerm::Forall { name, param_ty, body } => RawTerm::Forall {
            name: name.clone(),
            param_ty: subst(param_ty)?,
            body: Box::new(apply_type_subst(body, inst)?),
        },
        RawTerm::App { func, arg } => RawTerm::App {
            func: Box::new(apply_type_subst(func, inst)?),
            arg: Box::new(apply_type_subst(arg, inst)?),
        },
        RawTerm::Eq { lhs, rhs } => RawTerm::Eq {
            lhs: Box::new(apply_type_subst(lhs, inst)?),
            rhs: Box::new(apply_type_subst(rhs, inst)?),
        },
        RawTerm::Imp { premise, conclusion } => RawTerm::Imp {
            premise: Box::new(apply_type_subst(premise, inst)?),
            conclusion: Box::new(apply_type_subst(conclusion, inst)?),
        },
    })
}

#[allow(dead_code)] // TODO: use in source elaboration for axiom schema
pub(crate) fn strip_schema_foralls(raw: &RawTerm) -> RawTerm {
    match raw {
        RawTerm::Forall { body, .. } => strip_schema_foralls(body),
        other => other.clone(),
    }
}

/// Apply term substitution to a RawTerm with de Bruijn-aware capture avoidance.
///
/// Each `(name, index, replacement)` entry replaces `Var { name, index, .. }`.
/// Bound variable indices are lifted when crossing `Abs`/`Forall` binders.
pub fn subst_terms(raw: &RawTerm, term_inst: &[(Name, CTerm)]) -> Result<RawTerm, KernelError> {
    subst_terms_depth(raw, term_inst, 0)
}

fn subst_terms_depth(
    raw: &RawTerm,
    inst: &[(Name, CTerm)],
    depth: usize,
) -> Result<RawTerm, KernelError> {
    match raw {
        RawTerm::Var { name, .. } => {
            for (inst_name, replacement) in inst {
                if name == inst_name {
                    return Ok(lift_raw(replacement.term(), depth));
                }
            }
            Ok(raw.clone())
        },
        RawTerm::Abs { name, ty, body } => {
            let body = subst_terms_depth(body, inst, depth + 1)?;
            Ok(RawTerm::Abs { name: name.clone(), ty: ty.clone(), body: Box::new(body) })
        },
        RawTerm::Forall { name, param_ty, body } => {
            let body = subst_terms_depth(body, inst, depth + 1)?;
            Ok(RawTerm::Forall {
                name: name.clone(),
                param_ty: param_ty.clone(),
                body: Box::new(body),
            })
        },
        RawTerm::Bound(i) => Ok(RawTerm::Bound(*i)),
        RawTerm::Const { .. } | RawTerm::Free { .. } => Ok(raw.clone()),
        RawTerm::App { func, arg } => Ok(RawTerm::App {
            func: Box::new(subst_terms_depth(func, inst, depth)?),
            arg: Box::new(subst_terms_depth(arg, inst, depth)?),
        }),
        RawTerm::Eq { lhs, rhs } => Ok(RawTerm::Eq {
            lhs: Box::new(subst_terms_depth(lhs, inst, depth)?),
            rhs: Box::new(subst_terms_depth(rhs, inst, depth)?),
        }),
        RawTerm::Imp { premise, conclusion } => Ok(RawTerm::Imp {
            premise: Box::new(subst_terms_depth(premise, inst, depth)?),
            conclusion: Box::new(subst_terms_depth(conclusion, inst, depth)?),
        }),
    }
}

/// Lift a certified Term by `n` levels — increase all free de Bruijn indices by `n`.
fn lift_raw(term: &Term, n: usize) -> RawTerm {
    lift_raw_depth(term, n, 0)
}

fn lift_raw_depth(term: &Term, n: usize, depth: usize) -> RawTerm {
    match term {
        Term::Const { name, ty } => RawTerm::Const { name: name.clone(), ty: ty.clone() },
        Term::Free { name, ty } => RawTerm::Free { name: name.clone(), ty: ty.clone() },
        Term::Var { name, index, ty } => {
            RawTerm::Var { name: name.clone(), index: *index, ty: ty.clone() }
        },
        Term::Bound { index, ty: _ } => {
            if *index >= depth {
                RawTerm::Bound(index + n)
            } else {
                RawTerm::Bound(*index)
            }
        },
        Term::Abs { name, param_ty, body, ty: _ } => RawTerm::Abs {
            name: name.clone(),
            ty: param_ty.clone(),
            body: Box::new(lift_raw_depth(body, n, depth + 1)),
        },
        Term::Forall { name, param_ty, body } => RawTerm::Forall {
            name: name.clone(),
            param_ty: param_ty.clone(),
            body: Box::new(lift_raw_depth(body, n, depth + 1)),
        },
        Term::App { func, arg, ty: _ } => RawTerm::App {
            func: Box::new(lift_raw_depth(func, n, depth)),
            arg: Box::new(lift_raw_depth(arg, n, depth)),
        },
        Term::Eq { object_ty, lhs, rhs } => {
            let _ = object_ty;
            RawTerm::Eq {
                lhs: Box::new(lift_raw_depth(lhs, n, depth)),
                rhs: Box::new(lift_raw_depth(rhs, n, depth)),
            }
        },
        Term::Imp { premise, conclusion } => RawTerm::Imp {
            premise: Box::new(lift_raw_depth(premise, n, depth)),
            conclusion: Box::new(lift_raw_depth(conclusion, n, depth)),
        },
    }
}

/// Instantiate the outermost Forall binders of an axiom schema in order.
///
/// Each Forall binder declares one schematic variable (used as Bound(0) in the
/// body). `term_inst` provides replacements in the order the binders appear.
/// For each entry, the outermost Forall is consumed, Bound(0) is
/// substituted with the replacement, and all other Bound indices are lowered.
pub fn instantiate_schema_binders(
    context: &ProofContext,
    schema: RawTerm,
    term_inst: &[CTerm],
) -> Result<CProp, KernelError> {
    // Check the whole type pass before a vacuous binder can erase its annotations.
    let mut proposition = context.certify_prop(schema)?;
    for replacement in term_inst {
        context.validate_cterm(replacement)?;
    }
    for replacement in term_inst {
        proposition = consume_forall(context, &proposition, replacement)?;
    }
    if proposition.term().dest_forall().is_some() {
        return Err(KernelError::Invariant(
            "uninstantiated Forall binders remain in schema".into(),
        ));
    }
    Ok(proposition)
}

/// Consume the outermost Forall binder, substituting Bound(0).
fn consume_forall(
    context: &ProofContext,
    proposition: &CProp,
    replacement: &CTerm,
) -> Result<CProp, KernelError> {
    let (_, param_ty, body) = proposition.term().dest_forall().ok_or_else(|| {
        KernelError::Invariant("expected Forall binder for term instantiation".into())
    })?;
    if replacement.ty() != *param_ty {
        return Err(KernelError::TypeMismatch {
            expected: param_ty.clone(),
            actual: replacement.ty(),
        });
    }
    let result = CProp::new(Term::instantiate_bound0(body, replacement.term()), context.stamp())?;
    context.validate_cprop(&result)?;
    Ok(result)
}

/// Isabelle Name.clean_index removes each trailing internal-name underscore.
fn clean_generalize_name(name: &Name, index: usize) -> Result<(Name, usize), KernelError> {
    let clean = name.as_str().trim_end_matches('_');
    let offset = name.as_str().len() - clean.len();
    let index =
        index.checked_add(offset).ok_or(KernelError::GeneralizeIndexOverflow { index, offset })?;
    if offset == 0 {
        return Ok((name.clone(), index));
    }
    Ok((Name::from(clean), index))
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    Const { name: Name, ty: Ty },
    Free { name: Name, ty: Ty },
    Var { name: Name, index: usize, ty: Ty },
    Bound { index: usize, ty: Ty },
    Abs { name: Name, param_ty: Ty, body: Box<Term>, ty: Ty },
    Forall { name: Name, param_ty: Ty, body: Box<Term> },
    App { func: Box<Term>, arg: Box<Term>, ty: Ty },
    Eq { object_ty: Ty, lhs: Box<Term>, rhs: Box<Term> },
    Imp { premise: Box<Term>, conclusion: Box<Term> },
}

impl Term {
    /// Map every original annotation once; substitution RHS types are not traversed.
    pub(crate) fn instantiate_types(
        &self,
        instance: &crate::logic::TypeInstantiation,
    ) -> Result<Self, KernelError> {
        let map_type = |ty: &Ty| ty.subst_type_vars(instance);
        let map_term = |term: &Self| term.instantiate_types(instance).map(Box::new);
        Ok(match self {
            Self::Const { name, ty } => Self::Const { name: name.clone(), ty: map_type(ty)? },
            Self::Free { name, ty } => Self::Free { name: name.clone(), ty: map_type(ty)? },
            Self::Var { name, index, ty } => {
                Self::Var { name: name.clone(), index: *index, ty: map_type(ty)? }
            },
            Self::Bound { index, ty } => Self::Bound { index: *index, ty: map_type(ty)? },
            Self::Abs { name, param_ty, body, ty } => Self::Abs {
                name: name.clone(),
                param_ty: map_type(param_ty)?,
                body: map_term(body)?,
                ty: map_type(ty)?,
            },
            Self::Forall { name, param_ty, body } => Self::Forall {
                name: name.clone(),
                param_ty: map_type(param_ty)?,
                body: map_term(body)?,
            },
            Self::App { func, arg, ty } => {
                Self::App { func: map_term(func)?, arg: map_term(arg)?, ty: map_type(ty)? }
            },
            Self::Eq { object_ty, lhs, rhs } => Self::Eq {
                object_ty: map_type(object_ty)?,
                lhs: map_term(lhs)?,
                rhs: map_term(rhs)?,
            },
            Self::Imp { premise, conclusion } => {
                Self::Imp { premise: map_term(premise)?, conclusion: map_term(conclusion)? }
            },
        })
    }

    pub fn ty(&self) -> Ty {
        match self {
            Term::Const { ty, .. }
            | Term::Free { ty, .. }
            | Term::Var { ty, .. }
            | Term::Bound { ty, .. }
            | Term::Abs { ty, .. }
            | Term::App { ty, .. } => ty.clone(),
            Term::Eq { .. } | Term::Imp { .. } | Term::Forall { .. } => Ty::prop(),
        }
    }
    pub(crate) fn for_each_type_annotation<'a>(&'a self, f: &mut impl FnMut(&'a Ty)) {
        match self {
            Term::Const { ty, .. }
            | Term::Free { ty, .. }
            | Term::Var { ty, .. }
            | Term::Bound { ty, .. } => f(ty),
            Term::Abs { param_ty, body, ty, .. } => {
                f(param_ty);
                f(ty);
                body.for_each_type_annotation(f);
            },
            Term::Forall { param_ty, body, .. } => {
                f(param_ty);
                body.for_each_type_annotation(f);
            },
            Term::App { func, arg, ty } => {
                f(ty);
                func.for_each_type_annotation(f);
                arg.for_each_type_annotation(f);
            },
            Term::Eq { object_ty, lhs, rhs } => {
                f(object_ty);
                lhs.for_each_type_annotation(f);
                rhs.for_each_type_annotation(f);
            },
            Term::Imp { premise, conclusion } => {
                premise.for_each_type_annotation(f);
                conclusion.for_each_type_annotation(f);
            },
        }
    }
    /// Visit every physical constant occurrence, including duplicates below binders.
    pub(crate) fn visit_const_occurrences(
        &self,
        f: &mut impl FnMut(&Name, &Ty) -> Result<(), KernelError>,
    ) -> Result<(), KernelError> {
        match self {
            Self::Const { name, ty } => f(name, ty),
            Self::Free { .. } | Self::Var { .. } | Self::Bound { .. } => Ok(()),
            Self::Abs { body, .. } | Self::Forall { body, .. } => body.visit_const_occurrences(f),
            Self::App { func, arg, .. } => {
                func.visit_const_occurrences(f)?;
                arg.visit_const_occurrences(f)
            },
            Self::Eq { lhs, rhs, .. } => {
                lhs.visit_const_occurrences(f)?;
                rhs.visit_const_occurrences(f)
            },
            Self::Imp { premise, conclusion } => {
                premise.visit_const_occurrences(f)?;
                conclusion.visit_const_occurrences(f)
            },
        }
    }

    pub fn mk_eq(lhs: Term, rhs: Term) -> Result<Term, KernelError> {
        if lhs.ty() != rhs.ty() {
            return Err(KernelError::TypeMismatch { expected: lhs.ty(), actual: rhs.ty() });
        }
        Ok(Term::Eq { object_ty: lhs.ty(), lhs: Box::new(lhs), rhs: Box::new(rhs) })
    }

    pub fn mk_imp(premise: Term, conclusion: Term) -> Result<Term, KernelError> {
        if !premise.ty().is_prop() {
            return Err(KernelError::NotProposition(premise.ty().clone()));
        }
        if !conclusion.ty().is_prop() {
            return Err(KernelError::NotProposition(conclusion.ty().clone()));
        }
        Ok(Term::Imp { premise: Box::new(premise), conclusion: Box::new(conclusion) })
    }

    pub fn dest_eq(&self) -> Option<(&Ty, &Term, &Term)> {
        match self {
            Term::Eq { object_ty, lhs, rhs } => Some((object_ty, lhs, rhs)),
            _ => None,
        }
    }

    pub fn dest_imp(&self) -> Option<(&Term, &Term)> {
        match self {
            Term::Imp { premise, conclusion } => Some((premise, conclusion)),
            _ => None,
        }
    }

    pub fn dest_app(&self) -> Option<(&Term, &Term)> {
        match self {
            Term::App { func, arg, .. } => Some((func, arg)),
            _ => None,
        }
    }

    pub fn dest_abs(&self) -> Option<(&Name, &Ty, &Term)> {
        match self {
            Term::Abs { name, param_ty, body, .. } => Some((name, param_ty, body)),
            _ => None,
        }
    }

    pub fn dest_forall(&self) -> Option<(&Name, &Ty, &Term)> {
        match self {
            Term::Forall { name, param_ty, body } => Some((name, param_ty, body)),
            _ => None,
        }
    }

    /// Check whether `Free(name, ty)` occurs anywhere in this term.
    pub fn free_in(&self, name: &Name, ty: &Ty) -> bool {
        let mut stack = vec![self];
        while let Some(term) = stack.pop() {
            match term {
                Term::Free { name: n, ty: t } if n == name && t == ty => return true,
                Term::Abs { body, .. } | Term::Forall { body, .. } => stack.push(body),
                Term::App { func, arg, .. } => {
                    stack.push(arg);
                    stack.push(func);
                },
                Term::Eq { lhs, rhs, .. } => {
                    stack.push(rhs);
                    stack.push(lhs);
                },
                Term::Imp { premise, conclusion } => {
                    stack.push(conclusion);
                    stack.push(premise);
                },
                _ => {},
            }
        }
        false
    }

    /// Abstract a free variable, turning it into the outermost bound variable.
    ///
    /// Replaces every occurrence of `Free(name, ty)` with `Bound(depth, ty)`
    /// where `depth` counts the number of enclosing binders (Abs / Forall).
    /// Existing `Bound` indices are left unchanged—they already refer to the
    /// correct binder in their local context.
    ///
    /// This is the de Bruijn abstraction operation; it is the inverse of
    /// `instantiate_bound0` when the substituted argument is that free variable.
    pub fn abstract_over(name: &Name, ty: &Ty, term: &Term) -> Term {
        enum Frame {
            Process { term: Term, depth: usize },
            BuildAbs { name: Name, param_ty: Ty, abs_ty: Ty },
            BuildForall { name: Name, param_ty: Ty },
            BuildApp { ty: Ty },
            BuildEq { object_ty: Ty },
            BuildImp,
        }

        let mut stack = vec![Frame::Process { term: term.clone(), depth: 0 }];
        let mut results: Vec<Term> = vec![];

        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Process { term, depth } => match term {
                    Term::Free { name: n, ty: t } if &n == name && &t == ty => {
                        results.push(Term::Bound { index: depth, ty: ty.clone() });
                    },
                    Term::Abs { name, param_ty, body, ty } => {
                        stack.push(Frame::BuildAbs { name, param_ty, abs_ty: ty });
                        stack.push(Frame::Process { term: *body, depth: depth + 1 });
                    },
                    Term::Forall { name, param_ty, body } => {
                        stack.push(Frame::BuildForall { name, param_ty });
                        stack.push(Frame::Process { term: *body, depth: depth + 1 });
                    },
                    Term::App { func, arg, ty } => {
                        stack.push(Frame::BuildApp { ty });
                        stack.push(Frame::Process { term: *arg, depth });
                        stack.push(Frame::Process { term: *func, depth });
                    },
                    Term::Eq { object_ty, lhs, rhs } => {
                        stack.push(Frame::BuildEq { object_ty });
                        stack.push(Frame::Process { term: *rhs, depth });
                        stack.push(Frame::Process { term: *lhs, depth });
                    },
                    Term::Imp { premise, conclusion } => {
                        stack.push(Frame::BuildImp);
                        stack.push(Frame::Process { term: *conclusion, depth });
                        stack.push(Frame::Process { term: *premise, depth });
                    },
                    other => results.push(other),
                },
                Frame::BuildAbs { name, param_ty, abs_ty } => {
                    let body = Box::new(results.pop().unwrap());
                    results.push(Term::Abs { name, param_ty, body, ty: abs_ty });
                },
                Frame::BuildForall { name, param_ty } => {
                    let body = Box::new(results.pop().unwrap());
                    results.push(Term::Forall { name, param_ty, body });
                },
                Frame::BuildApp { ty } => {
                    let arg = Box::new(results.pop().unwrap());
                    let func = Box::new(results.pop().unwrap());
                    results.push(Term::App { func, arg, ty });
                },
                Frame::BuildEq { object_ty } => {
                    let rhs = Box::new(results.pop().unwrap());
                    let lhs = Box::new(results.pop().unwrap());
                    results.push(Term::Eq { object_ty, lhs, rhs });
                },
                Frame::BuildImp => {
                    let conclusion = Box::new(results.pop().unwrap());
                    let premise = Box::new(results.pop().unwrap());
                    results.push(Term::Imp { premise, conclusion });
                },
            }
        }
        results.pop().unwrap()
    }

    /// Substitute `arg` for the outermost `Bound(0)`. Local binders keep their
    /// indices; references outside the removed binder decrement by exactly one.
    ///
    /// For `(Abs { body: body', .. })(arg)`, this computes `body'[arg/x]`
    /// where `x` is represented as `Bound(0, param_ty)` in `body'`.
    /// The exhaustive substitution/lift tables stay together so every term
    /// constructor is handled identically in the two capture-avoiding walks.
    pub(crate) fn instantiate_bound0(body: &Term, arg: &Term) -> Term {
        fn subst(term: &Term, args: &[Term]) -> Term {
            match term {
                Term::Bound { index, ty } => {
                    if *index < args.len() {
                        lift(&args[*index], 0, 0)
                    } else {
                        Term::Bound { index: index - 1, ty: ty.clone() }
                    }
                },
                Term::Abs { name, param_ty, body: inner, ty } => {
                    let mut inner_args = vec![Term::Bound { index: 0, ty: param_ty.clone() }];
                    inner_args.extend(args.iter().map(|a| lift(a, 0, 1)));
                    Term::Abs {
                        name: name.clone(),
                        param_ty: param_ty.clone(),
                        body: Box::new(subst(inner, &inner_args)),
                        ty: ty.clone(),
                    }
                },
                Term::App { func, arg: fn_arg, ty } => Term::App {
                    func: Box::new(subst(func, args)),
                    arg: Box::new(subst(fn_arg, args)),
                    ty: ty.clone(),
                },
                Term::Eq { object_ty, lhs, rhs } => Term::Eq {
                    object_ty: object_ty.clone(),
                    lhs: Box::new(subst(lhs, args)),
                    rhs: Box::new(subst(rhs, args)),
                },
                Term::Forall { name, param_ty, body } => {
                    let mut inner_args = vec![Term::Bound { index: 0, ty: param_ty.clone() }];
                    inner_args.extend(args.iter().map(|a| lift(a, 0, 1)));
                    Term::Forall {
                        name: name.clone(),
                        param_ty: param_ty.clone(),
                        body: Box::new(subst(body, &inner_args)),
                    }
                },
                Term::Imp { premise, conclusion } => Term::Imp {
                    premise: Box::new(subst(premise, args)),
                    conclusion: Box::new(subst(conclusion, args)),
                },
                other => other.clone(),
            }
        }

        fn lift(term: &Term, cutoff: usize, n: usize) -> Term {
            match term {
                Term::Bound { index, ty } => {
                    if *index >= cutoff {
                        Term::Bound { index: index + n, ty: ty.clone() }
                    } else {
                        Term::Bound { index: *index, ty: ty.clone() }
                    }
                },
                Term::Abs { name, param_ty, body, ty } => Term::Abs {
                    name: name.clone(),
                    param_ty: param_ty.clone(),
                    body: Box::new(lift(body, cutoff + 1, n)),
                    ty: ty.clone(),
                },
                Term::Forall { name, param_ty, body } => Term::Forall {
                    name: name.clone(),
                    param_ty: param_ty.clone(),
                    body: Box::new(lift(body, cutoff + 1, n)),
                },
                Term::App { func, arg, ty } => Term::App {
                    func: Box::new(lift(func, cutoff, n)),
                    arg: Box::new(lift(arg, cutoff, n)),
                    ty: ty.clone(),
                },
                Term::Eq { object_ty, lhs, rhs } => Term::Eq {
                    object_ty: object_ty.clone(),
                    lhs: Box::new(lift(lhs, cutoff, n)),
                    rhs: Box::new(lift(rhs, cutoff, n)),
                },
                Term::Imp { premise, conclusion } => Term::Imp {
                    premise: Box::new(lift(premise, cutoff, n)),
                    conclusion: Box::new(lift(conclusion, cutoff, n)),
                },
                other => other.clone(),
            }
        }

        subst(body, std::slice::from_ref(arg))
    }

    pub fn alpha_eq(&self, other: &Term) -> bool {
        match (self, other) {
            (Term::Const { name: left, ty: lty }, Term::Const { name: right, ty: rty }) => {
                left == right && lty == rty
            },
            (Term::Free { name: left, ty: lty }, Term::Free { name: right, ty: rty }) => {
                left == right && lty == rty
            },
            (
                Term::Var { name: left, index: li, ty: lty },
                Term::Var { name: right, index: ri, ty: rty },
            ) => left == right && li == ri && lty == rty,
            (Term::Bound { index: left, ty: lty }, Term::Bound { index: right, ty: rty }) => {
                left == right && lty == rty
            },
            (
                Term::Abs { param_ty: lty, body: lbody, .. },
                Term::Abs { param_ty: rty, body: rbody, .. },
            ) => lty == rty && lbody.alpha_eq(rbody),
            (
                Term::Forall { param_ty: lty, body: lbody, .. },
                Term::Forall { param_ty: rty, body: rbody, .. },
            ) => lty == rty && lbody.alpha_eq(rbody),
            (
                Term::App { func: lf, arg: la, ty: lty },
                Term::App { func: rf, arg: ra, ty: rty },
            ) => lty == rty && lf.alpha_eq(rf) && la.alpha_eq(ra),
            (
                Term::Eq { object_ty: lty, lhs: ll, rhs: lr },
                Term::Eq { object_ty: rty, lhs: rl, rhs: rr },
            ) => lty == rty && ll.alpha_eq(rl) && lr.alpha_eq(rr),
            (
                Term::Imp { premise: lp, conclusion: lc },
                Term::Imp { premise: rp, conclusion: rc },
            ) => lp.alpha_eq(rp) && lc.alpha_eq(rc),
            _ => false,
        }
    }

    /// Canonical semantic encoding used by accepted-theorem identities.
    ///
    /// Binder labels and cached result types are omitted: the former are not
    /// logical data, and the latter are revalidated before this encoder runs.
    pub(crate) fn write_theorem_canonical(&self, encoder: &mut CanonicalEncoder) {
        match self {
            Term::Const { name, ty } => {
                encoder.write_u8(0);
                encoder.write_name(name);
                ty.write_canonical(encoder);
            },
            Term::Free { name, ty } => {
                encoder.write_u8(1);
                encoder.write_name(name);
                ty.write_canonical(encoder);
            },
            Term::Var { name, index, ty } => {
                encoder.write_u8(2);
                encoder.write_name(name);
                encoder.write_u64(*index as u64);
                ty.write_canonical(encoder);
            },
            Term::Bound { index, ty } => {
                encoder.write_u8(3);
                encoder.write_u64(*index as u64);
                ty.write_canonical(encoder);
            },
            Term::Abs { param_ty, body, .. } => {
                encoder.write_u8(4);
                param_ty.write_canonical(encoder);
                body.write_theorem_canonical(encoder);
            },
            Term::Forall { param_ty, body, .. } => {
                encoder.write_u8(5);
                param_ty.write_canonical(encoder);
                body.write_theorem_canonical(encoder);
            },
            Term::App { func, arg, .. } => {
                encoder.write_u8(6);
                func.write_theorem_canonical(encoder);
                arg.write_theorem_canonical(encoder);
            },
            Term::Eq { object_ty, lhs, rhs } => {
                encoder.write_u8(7);
                object_ty.write_canonical(encoder);
                lhs.write_theorem_canonical(encoder);
                rhs.write_theorem_canonical(encoder);
            },
            Term::Imp { premise, conclusion } => {
                encoder.write_u8(8);
                premise.write_theorem_canonical(encoder);
                conclusion.write_theorem_canonical(encoder);
            },
        }
    }

    pub(crate) fn has_schematic_hypothesis(&self) -> bool {
        let mut stack = vec![self];
        while let Some(term) = stack.pop() {
            match term {
                Term::Var { .. } => return true,
                Term::Const { ty, .. } | Term::Free { ty, .. } | Term::Bound { ty, .. } => {
                    if ty.has_type_vars() {
                        return true;
                    }
                },
                Term::Abs { param_ty, body, ty, .. } => {
                    if param_ty.has_type_vars() || ty.has_type_vars() {
                        return true;
                    }
                    stack.push(body);
                },
                Term::Forall { param_ty, body, .. } => {
                    if param_ty.has_type_vars() {
                        return true;
                    }
                    stack.push(body);
                },
                Term::App { func, arg, ty } => {
                    if ty.has_type_vars() {
                        return true;
                    }
                    stack.push(arg);
                    stack.push(func);
                },
                Term::Eq { object_ty, lhs, rhs } => {
                    if object_ty.has_type_vars() {
                        return true;
                    }
                    stack.push(rhs);
                    stack.push(lhs);
                },
                Term::Imp { premise, conclusion } => {
                    stack.push(conclusion);
                    stack.push(premise);
                },
            }
        }
        false
    }

    /// Return the highest `Var` index in the term, or `None` if there are no
    /// schematic variables.
    pub fn max_var_index(&self) -> Option<usize> {
        let mut max: Option<usize> = None;
        let mut stack = vec![self];
        while let Some(term) = stack.pop() {
            match term {
                Term::Var { index, .. } => {
                    max = Some(max.map_or(*index, |m| m.max(*index)));
                },
                Term::Abs { body, .. } | Term::Forall { body, .. } => stack.push(body),
                Term::App { func, arg, .. } => {
                    stack.push(arg);
                    stack.push(func);
                },
                Term::Eq { lhs, rhs, .. } => {
                    stack.push(rhs);
                    stack.push(lhs);
                },
                Term::Imp { premise, conclusion } => {
                    stack.push(conclusion);
                    stack.push(premise);
                },
                _ => {},
            }
        }
        max
    }

    /// Generalize selected fixed type and term names at a shared index.
    ///
    /// Selected `Free` names lose trailing underscores, increasing their own
    /// schematic index by one per underscore. The caller checks freshness for
    /// the complete certified object before transforming its components.
    pub fn generalize_vars(
        &self,
        type_names: &BTreeSet<Name>,
        term_names: &BTreeSet<Name>,
        index: usize,
    ) -> Result<Term, KernelError> {
        if type_names.is_empty() && term_names.is_empty() {
            return Ok(self.clone());
        }
        let map_type = |ty: &Ty| ty.generalize_type(type_names, index);
        let map_term =
            |term: &Self| term.generalize_vars(type_names, term_names, index).map(Box::new);
        Ok(match self {
            Self::Const { name, ty } => Self::Const { name: name.clone(), ty: map_type(ty)? },
            Self::Free { name, ty } if term_names.contains(name) => {
                let (name, index) = clean_generalize_name(name, index)?;
                Self::Var { name, index, ty: map_type(ty)? }
            },
            Self::Free { name, ty } => Self::Free { name: name.clone(), ty: map_type(ty)? },
            Self::Var { name, index, ty } => {
                Self::Var { name: name.clone(), index: *index, ty: map_type(ty)? }
            },
            Self::Bound { index, ty } => Self::Bound { index: *index, ty: map_type(ty)? },
            Self::Abs { name, param_ty, body, ty } => Self::Abs {
                name: name.clone(),
                param_ty: map_type(param_ty)?,
                body: map_term(body)?,
                ty: map_type(ty)?,
            },
            Self::Forall { name, param_ty, body } => Self::Forall {
                name: name.clone(),
                param_ty: map_type(param_ty)?,
                body: map_term(body)?,
            },
            Self::App { func, arg, ty } => {
                Self::App { func: map_term(func)?, arg: map_term(arg)?, ty: map_type(ty)? }
            },
            Self::Eq { object_ty, lhs, rhs } => Self::Eq {
                object_ty: map_type(object_ty)?,
                lhs: map_term(lhs)?,
                rhs: map_term(rhs)?,
            },
            Self::Imp { premise, conclusion } => {
                Self::Imp { premise: map_term(premise)?, conclusion: map_term(conclusion)? }
            },
        })
    }

    /// Replace each matching `Var(name, idx, ty)` with its corresponding
    /// replacement term. Vars not listed in the substitution are preserved.
    ///
    /// This is the inverse of `generalize_vars`.
    pub fn instantiate_vars(&self, subst: &[InstEntry]) -> Term {
        enum Frame {
            Process(Term),
            BuildAbs { name: Name, param_ty: Ty, abs_ty: Ty },
            BuildForall { name: Name, param_ty: Ty },
            BuildApp { ty: Ty },
            BuildEq { object_ty: Ty },
            BuildImp,
        }

        let mut stack = vec![Frame::Process(self.clone())];
        let mut results: Vec<Term> = vec![];

        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Process(term) => match term {
                    Term::Var { name, index, ty } => {
                        if let Some(entry) = subst
                            .iter()
                            .find(|e| e.name() == &name && e.index() == index && e.var_ty() == &ty)
                        {
                            results.push(entry.replacement().term().clone());
                        } else {
                            results.push(Term::Var { name, index, ty });
                        }
                    },
                    Term::Abs { name, param_ty, body, ty } => {
                        stack.push(Frame::BuildAbs { name, param_ty, abs_ty: ty });
                        stack.push(Frame::Process(*body));
                    },
                    Term::Forall { name, param_ty, body } => {
                        stack.push(Frame::BuildForall { name, param_ty });
                        stack.push(Frame::Process(*body));
                    },
                    Term::App { func, arg, ty } => {
                        stack.push(Frame::BuildApp { ty });
                        stack.push(Frame::Process(*arg));
                        stack.push(Frame::Process(*func));
                    },
                    Term::Eq { object_ty, lhs, rhs } => {
                        stack.push(Frame::BuildEq { object_ty });
                        stack.push(Frame::Process(*rhs));
                        stack.push(Frame::Process(*lhs));
                    },
                    Term::Imp { premise, conclusion } => {
                        stack.push(Frame::BuildImp);
                        stack.push(Frame::Process(*conclusion));
                        stack.push(Frame::Process(*premise));
                    },
                    other => results.push(other),
                },
                Frame::BuildAbs { name, param_ty, abs_ty } => {
                    let body = Box::new(results.pop().unwrap());
                    results.push(Term::Abs { name, param_ty, body, ty: abs_ty });
                },
                Frame::BuildForall { name, param_ty } => {
                    let body = Box::new(results.pop().unwrap());
                    results.push(Term::Forall { name, param_ty, body });
                },
                Frame::BuildApp { ty } => {
                    let arg = Box::new(results.pop().unwrap());
                    let func = Box::new(results.pop().unwrap());
                    results.push(Term::App { func, arg, ty });
                },
                Frame::BuildEq { object_ty } => {
                    let rhs = Box::new(results.pop().unwrap());
                    let lhs = Box::new(results.pop().unwrap());
                    results.push(Term::Eq { object_ty, lhs, rhs });
                },
                Frame::BuildImp => {
                    let conclusion = Box::new(results.pop().unwrap());
                    let premise = Box::new(results.pop().unwrap());
                    results.push(Term::Imp { premise, conclusion });
                },
            }
        }
        results.pop().unwrap()
    }

    /// Check capture freedom while allowing bound variables within their own binders.
    pub(crate) fn validate_closed_bounds(&self) -> Result<(), KernelError> {
        let mut pending = vec![(self, 0_usize)];
        while let Some((term, depth)) = pending.pop() {
            match term {
                Self::Bound { index, .. } if *index >= depth => {
                    return Err(KernelError::BoundInSubstitution);
                },
                Self::Abs { body, .. } | Self::Forall { body, .. } => {
                    let nested = depth.checked_add(1).ok_or_else(|| {
                        KernelError::Invariant("substitution binder depth overflow".into())
                    })?;
                    pending.push((body, nested));
                },
                Self::App { func, arg, .. } => {
                    pending.extend([(func.as_ref(), depth), (arg.as_ref(), depth)]);
                },
                Self::Eq { lhs, rhs, .. } => {
                    pending.extend([(lhs.as_ref(), depth), (rhs.as_ref(), depth)]);
                },
                Self::Imp { premise, conclusion } => {
                    pending.extend([(premise.as_ref(), depth), (conclusion.as_ref(), depth)]);
                },
                _ => {},
            }
        }
        Ok(())
    }

    /// Check whether any `Bound` node occurs anywhere in this term.
    pub fn contains_bound(&self) -> bool {
        let mut stack = vec![self];
        while let Some(term) = stack.pop() {
            match term {
                Term::Bound { .. } => return true,
                Term::Abs { body, .. } | Term::Forall { body, .. } => stack.push(body),
                Term::App { func, arg, .. } => {
                    stack.push(arg);
                    stack.push(func);
                },
                Term::Eq { lhs, rhs, .. } => {
                    stack.push(rhs);
                    stack.push(lhs);
                },
                Term::Imp { premise, conclusion } => {
                    stack.push(conclusion);
                    stack.push(premise);
                },
                _ => {},
            }
        }
        false
    }

    /// Decompose a proposition into its implication-chain premises and conclusion.
    ///
    /// `A ==> B ==> C` returns `(vec![A, B], C)`.
    /// A non-implication `C` returns `(vec![], C)`.
    ///
    /// This is the fundamental decomposition for goal states and rules in the
    /// resolution family. The returned premises are in left-to-right order:
    /// the first element is the outermost antecedent.
    pub fn dest_imp_chain(&self) -> (Vec<Term>, &Term) {
        let mut prems = Vec::new();
        let mut current = self;
        while let Term::Imp { premise, conclusion } = current {
            prems.push((**premise).clone());
            current = conclusion;
        }
        (prems, current)
    }

    /// Build an implication chain from premises and a conclusion.
    ///
    /// `mk_imp_chain(&[A, B], &C)` returns `A ==> B ==> C`.
    /// `mk_imp_chain(&[], &C)` returns `C`.
    ///
    /// Premises are nested right-to-left: the last premise is the innermost
    /// antecedent. Returns an error if any premise is not a proposition.
    pub fn mk_imp_chain(prems: &[Term], conclusion: &Term) -> Result<Term, KernelError> {
        if !conclusion.ty().is_prop() {
            return Err(KernelError::NotProposition(conclusion.ty()));
        }
        let mut result = conclusion.clone();
        for prem in prems.iter().rev() {
            if !prem.ty().is_prop() {
                return Err(KernelError::NotProposition(prem.ty()));
            }
            result = Term::Imp { premise: Box::new(prem.clone()), conclusion: Box::new(result) };
        }
        Ok(result)
    }

    /// Count the number of premises (subgoals) in a goal state.
    ///
    /// `nprems(A ==> B ==> C)` returns `2`.
    /// `nprems(C)` returns `0`.
    pub fn nprems(&self) -> usize {
        let (prems, _) = self.dest_imp_chain();
        prems.len()
    }

    /// Select the i-th subgoal (0-indexed) from a goal state.
    ///
    /// `select_subgoal(A ==> B ==> C, 0)` returns `Some(A)`.
    /// `select_subgoal(A ==> B ==> C, 1)` returns `Some(B)`.
    /// `select_subgoal(C, 0)` returns `None` (it is the conclusion, not a subgoal).
    ///
    /// Returns `None` if the index points at or past the conclusion.
    pub fn select_subgoal(&self, i: usize) -> Option<Term> {
        let (prems, _) = self.dest_imp_chain();
        prems.get(i).cloned()
    }

    /// Replace the i-th subgoal with a list of new premises.
    ///
    /// `replace_subgoal_with_premises(A ==> C, 0, &[P, Q])` returns `Ok(P ==> Q ==> C)`.
    /// `replace_subgoal_with_premises(A ==> C, 0, &[])` returns `Ok(C)` (subgoal removed).
    ///
    /// Returns `SubgoalIndexOutOfRange` if `i >= nprems`.
    pub fn replace_subgoal_with_premises(
        &self,
        i: usize,
        new_prems: &[Term],
    ) -> Result<Term, KernelError> {
        let (prems, conclusion) = self.dest_imp_chain();
        let n = prems.len();
        if i >= n {
            return Err(KernelError::SubgoalIndexOutOfRange { index: i, nprems: n });
        }
        let mut new_chain: Vec<Term> = Vec::with_capacity(n - 1 + new_prems.len());
        new_chain.extend(prems[..i].iter().cloned());
        new_chain.extend(new_prems.iter().cloned());
        new_chain.extend(prems[i + 1..].iter().cloned());
        Term::mk_imp_chain(&new_chain, conclusion)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logic::{TypeInstantiation, TypeVarId};
    use crate::{Sort, Ty};

    #[test]
    fn subst_types_allows_same_name_different_index() {
        // Two type variables with same name 'a but different indices: 'a.0 and 'a.1
        // should be treated as distinct variables, not rejected as ambiguous.
        let raw = RawTerm::const_(
            "f",
            Ty::arrow(
                Ty::tvar("'a", 0, Sort::hol_type()),
                Ty::arrow(Ty::tvar("'a", 1, Sort::hol_type()), Ty::prop()),
            ),
        );

        let mut bindings = std::collections::BTreeMap::new();
        bindings.insert(TypeVarId::new("'a", 0, Sort::hol_type()), Ty::base("bool").unwrap());
        bindings.insert(TypeVarId::new("'a", 1, Sort::hol_type()), Ty::base("nat").unwrap());
        let inst = TypeInstantiation::try_new(bindings).unwrap();

        let result = subst_types(&raw, &inst);
        assert!(result.is_ok(), "same-name-different-index must be allowed, got: {result:?}");
    }
    #[test]
    fn generalize_vars_shared_index_cleans_names_and_all_annotations() {
        let fixed = Ty::tfree("a", Sort::empty());
        let function = Ty::arrow(fixed.clone(), fixed.clone());
        let source = Term::Forall {
            name: "z".into(),
            param_ty: fixed.clone(),
            body: Box::new(Term::Eq {
                object_ty: fixed.clone(),
                lhs: Box::new(Term::App {
                    func: Box::new(Term::Free { name: "x__".into(), ty: function }),
                    arg: Box::new(Term::Bound { index: 0, ty: fixed.clone() }),
                    ty: fixed.clone(),
                }),
                rhs: Box::new(Term::Free { name: "x__".into(), ty: fixed }),
            }),
        };
        let type_names = BTreeSet::from(["a".into()]);
        let term_names = BTreeSet::from(["x__".into()]);
        let generalized = source.generalize_vars(&type_names, &term_names, 0).unwrap();
        let schematic = Ty::tvar("a", 0, Sort::empty());
        let expected = Term::Forall {
            name: "z".into(),
            param_ty: schematic.clone(),
            body: Box::new(Term::Eq {
                object_ty: schematic.clone(),
                lhs: Box::new(Term::App {
                    func: Box::new(Term::Var {
                        name: "x".into(),
                        index: 2,
                        ty: Ty::arrow(schematic.clone(), schematic.clone()),
                    }),
                    arg: Box::new(Term::Bound { index: 0, ty: schematic.clone() }),
                    ty: schematic.clone(),
                }),
                rhs: Box::new(Term::Var { name: "x".into(), index: 2, ty: schematic }),
            }),
        };
        assert_eq!(generalized, expected);
        assert_eq!(
            source.generalize_vars(&BTreeSet::new(), &BTreeSet::new(), usize::MAX),
            Ok(source)
        );
    }

    #[test]
    fn generalize_vars_clean_index_overflow_rejects() {
        let term = Term::Free { name: "x__".into(), ty: Ty::prop() };
        assert_eq!(
            term.generalize_vars(&BTreeSet::new(), &BTreeSet::from(["x__".into()]), usize::MAX),
            Err(KernelError::GeneralizeIndexOverflow { index: usize::MAX, offset: 2 }),
        );
    }
}
