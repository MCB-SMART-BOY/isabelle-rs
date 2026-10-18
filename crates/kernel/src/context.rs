use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::{Sort, TypeInstantiation};

use super::{
    CProp, CTerm, CType, ContextStamp, KernelError, Name, RawTerm, Signature, Term, TheorySnapshot,
    Ty,
};

/// Proof context for strict term certification.
#[derive(Clone, Debug)]
pub struct ProofContext {
    theory: TheorySnapshot,
    frees: HashMap<Name, Ty>,
    type_frees: HashMap<Name, Sort>,
    local_stamp: Option<ContextStamp>,
    // Present only in a private replay view passed to the bound checker.
    // Public declarations remain single-name; this table never enters a capsule.
    replay_permissions: Option<BTreeSet<(Name, Ty)>>,
}

/// Kernel-issued snapshot of one proof context's local declarations.
/// No public constructor or deserialization can grant a local scope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofScope {
    stamp: ContextStamp,
    type_frees: BTreeMap<Name, Sort>,
    frees: BTreeMap<Name, Ty>,
}

impl ProofScope {
    pub(crate) fn stamp(&self) -> ContextStamp {
        self.stamp
    }

    pub(crate) fn type_frees(&self) -> &BTreeMap<Name, Sort> {
        &self.type_frees
    }

    pub(crate) fn frees(&self) -> &BTreeMap<Name, Ty> {
        &self.frees
    }

    /// Restore only in the exact owner world. Retain the original local stamp:
    /// allocating a new scope would not authenticate existing certified operands.
    pub(crate) fn restore(&self, theory: &TheorySnapshot) -> Result<ProofContext, KernelError> {
        let owner = theory.stamp();
        if self.stamp.theory() != owner.theory()
            || self.stamp.signature() != owner.signature()
            || self.stamp.logic_basis() != owner.logic_basis()
            || self.stamp.has_local_type_scope() != !self.type_frees.is_empty()
        {
            return Err(KernelError::MixedContext {
                expected: Box::new(owner),
                actual: Box::new(self.stamp),
            });
        }
        let mut context = ProofContext::new(theory.clone());
        for (name, sort) in &self.type_frees {
            context.signature().validate_type(&Ty::tfree(name.clone(), sort.clone()))?;
            if context.type_frees.insert(name.clone(), sort.clone()).is_some() {
                return Err(KernelError::DuplicateDeclaration { name: name.clone() });
            }
        }
        for (name, ty) in &self.frees {
            context.validate_type(ty)?;
            if context.frees.insert(name.clone(), ty.clone()).is_some() {
                return Err(KernelError::DuplicateDeclaration { name: name.clone() });
            }
        }
        if self.stamp != owner {
            context.local_stamp = Some(self.stamp);
        }
        Ok(context)
    }
}

impl ProofContext {
    pub fn new(theory: TheorySnapshot) -> Self {
        ProofContext {
            theory,
            frees: HashMap::new(),
            type_frees: HashMap::new(),
            local_stamp: None,
            replay_permissions: None,
        }
    }

    pub fn signature(&self) -> &Signature {
        self.theory.signature()
    }

    pub fn theory(&self) -> &TheorySnapshot {
        &self.theory
    }

    pub fn stamp(&self) -> ContextStamp {
        self.local_stamp.unwrap_or_else(|| self.theory.stamp())
    }

    pub(crate) fn snapshot_scope(&self) -> ProofScope {
        ProofScope {
            stamp: self.stamp(),
            type_frees: self
                .type_frees
                .iter()
                .map(|(name, sort)| (name.clone(), sort.clone()))
                .collect(),
            frees: self.frees.iter().map(|(name, ty)| (name.clone(), ty.clone())).collect(),
        }
    }

    pub(crate) fn replay_frees(&self) -> BTreeSet<(Name, Ty)> {
        self.replay_permissions.clone().unwrap_or_else(|| {
            self.frees.iter().map(|(name, ty)| (name.clone(), ty.clone())).collect()
        })
    }

    pub(crate) fn has_same_type_scope(&self, other: &Self) -> bool {
        self.stamp() == other.stamp() && self.type_frees == other.type_frees
    }

    /// Bridge already-validated lexical grants to existing bound-proof validators.
    /// No public caller or target theorem field can construct this view.
    pub(crate) fn for_replay<'a>(
        &'a self,
        grants: BTreeSet<(Name, Ty)>,
    ) -> std::borrow::Cow<'a, Self> {
        let is_same = self.replay_permissions.as_ref().map_or_else(
            || {
                self.frees.len() == grants.len()
                    && grants.iter().all(|(name, ty)| self.frees.get(name) == Some(ty))
            },
            |permissions| permissions == &grants,
        );
        if is_same {
            return std::borrow::Cow::Borrowed(self);
        }
        let mut view = self.clone();
        view.replay_permissions = Some(grants);
        std::borrow::Cow::Owned(view)
    }

    pub fn declare_free(&mut self, name: impl Into<Name>, ty: Ty) {
        self.frees.insert(name.into(), ty);
    }

    pub fn free_type(&self, name: &Name) -> Option<&Ty> {
        self.frees.get(name)
    }

    /// Introduce a fixed parameter valid only in this proof context and its clones.
    pub fn declare_type_free(
        &mut self,
        name: impl Into<Name>,
        sort: Sort,
    ) -> Result<Ty, KernelError> {
        let name = name.into();
        let fixed = Ty::tfree(name.clone(), sort.clone());
        self.signature().validate_type(&fixed)?;
        if let Some(existing) = self.type_frees.get(&name) {
            return Err(if existing == &sort {
                KernelError::DuplicateDeclaration { name }
            } else {
                KernelError::TypeIdentityMismatch {
                    name,
                    index: None,
                    expected: existing.clone(),
                    actual: sort,
                }
            });
        }
        let local_stamp = self.stamp().fresh_local_type_scope(&name)?;
        self.type_frees.insert(name, sort);
        self.local_stamp = Some(local_stamp);
        Ok(fixed)
    }

    /// Check substitutions before even an erased term binder can hide a fixed type.
    pub(crate) fn validate_type_instantiation(
        &self,
        instance: &TypeInstantiation,
    ) -> Result<(), KernelError> {
        self.signature().validate_type_instantiation(instance)?;
        for (_, replacement) in instance.iter() {
            self.validate_type(replacement)?;
        }
        Ok(())
    }

    pub(crate) fn validate_type(&self, ty: &Ty) -> Result<(), KernelError> {
        self.signature().validate_type(ty)?;
        let mut error = None;
        ty.for_each_type_free(&mut |name, sort| {
            if error.is_some() {
                return;
            }
            error = match self.type_frees.get(name) {
                Some(expected) if expected == sort => None,
                Some(expected) => Some(KernelError::TypeIdentityMismatch {
                    name: name.clone(),
                    index: None,
                    expected: expected.clone(),
                    actual: sort.clone(),
                }),
                None => {
                    Some(KernelError::UndeclaredTypeFree { name: name.clone(), sort: sort.clone() })
                },
            };
        });
        error.map_or(Ok(()), Err)
    }

    pub fn certify_type(&self, ty: Ty) -> Result<CType, KernelError> {
        self.validate_type(&ty)?;
        let mut identities = crate::typ::TypeIdentityMap::default();
        identities.validate(&ty)?;
        Ok(CType::new(ty, self.stamp()))
    }

    /// Generalize fixed types in a certified type without granting theorem authority.
    pub fn generalize_type(
        &self,
        source: &CType,
        names: &BTreeSet<Name>,
        index: usize,
    ) -> Result<CType, KernelError> {
        self.require_stamp(source.context())?;
        self.validate_type(source.ty())?;
        let mut identities = crate::typ::TypeIdentityMap::default();
        identities.validate(source.ty())?;
        crate::typ::check_generalize_index(names.is_empty(), index, source.max_var_index())?;
        if names.is_empty() {
            return Ok(source.clone());
        }
        let ty = source.ty().generalize_type(names, index)?;
        self.validate_type(&ty)?;
        let mut identities = crate::typ::TypeIdentityMap::default();
        identities.validate(&ty)?;
        Ok(CType::with_max_index(ty, self.stamp(), source.max_var_index().max(Some(index))))
    }

    pub fn certify_term(&self, raw: RawTerm) -> Result<CTerm, KernelError> {
        let term = self.certify_raw(raw, &[])?;
        Self::validate_type_identities(&term)?;
        Ok(CTerm::new(term, self.stamp()))
    }

    /// Generalize a certified term and derive a context for any remaining Free
    /// names whose types changed. The original context is never modified.
    pub fn generalize_term(
        &self,
        source: &CTerm,
        type_names: &BTreeSet<Name>,
        term_names: &BTreeSet<Name>,
        index: usize,
    ) -> Result<(ProofContext, CTerm), KernelError> {
        self.validate_cterm(source)?;
        let is_empty = type_names.is_empty() && term_names.is_empty();
        crate::typ::check_generalize_index(is_empty, index, source.max_var_index())?;
        if is_empty {
            return Ok((self.clone(), source.clone()));
        }
        let term = source.term().generalize_vars(type_names, term_names, index)?;
        let mut derived = self.clone();
        if !type_names.is_empty() {
            for ty in derived.frees.values_mut() {
                *ty = ty.generalize_type(type_names, index)?;
            }
        }
        let certified =
            CTerm::with_max_index(term, derived.stamp(), source.max_var_index().max(Some(index)));
        derived.validate_cterm(&certified)?;
        Ok((derived, certified))
    }

    pub fn certify_prop(&self, raw: RawTerm) -> Result<CProp, KernelError> {
        let term = self.certify_raw(raw, &[])?;
        Self::validate_type_identities(&term)?;
        CProp::new(term, self.stamp())
    }

    /// Validate a schema without exporting a certified proposition or proof authority.
    pub(crate) fn validate_axiom_schema(&self, raw: RawTerm) -> Result<(), KernelError> {
        let term = self.certify_raw(raw, &[])?;
        Self::validate_type_identities(&term)?;
        if !term.ty().is_prop() {
            return Err(KernelError::NotProposition(term.ty()));
        }
        Ok(())
    }

    /// Revalidate a certified term against this exact proof context without
    /// normalizing or rebuilding it.
    pub(crate) fn validate_cterm(&self, term: &CTerm) -> Result<(), KernelError> {
        self.require_stamp(term.context())?;
        Self::validate_type_identities(term.term())?;
        let mut bounds = Vec::new();
        self.validate_checked(term.term(), &mut bounds)?;
        Ok(())
    }

    /// Replay-only Free authorization is an exact typed-key set. The public
    /// declaration map is not consulted for an ungranted typed occurrence.
    pub(crate) fn validate_replay_cterm(
        &self,
        term: &CTerm,
        certify_free: &mut dyn FnMut(&Name, &Ty) -> Result<(), KernelError>,
    ) -> Result<(), KernelError> {
        self.require_stamp(term.context())?;
        Self::validate_type_identities(term.term())?;
        let mut bounds = Vec::new();
        self.validate_checked_with(
            term.term(),
            &mut bounds,
            &mut |name, ty| self.signature().certify_const_instance(name, ty).map(|_| ()),
            certify_free,
        )?;
        Ok(())
    }

    /// Revalidate a certified proposition against this exact proof context.
    pub(crate) fn validate_cprop(&self, prop: &CProp) -> Result<(), KernelError> {
        self.require_stamp(prop.context())?;
        Self::validate_type_identities(prop.term())?;
        let mut bounds = Vec::new();
        let ty = self.validate_checked(prop.term(), &mut bounds)?;
        if !ty.is_prop() {
            return Err(KernelError::NotProposition(ty));
        }
        Ok(())
    }

    /// Check the full term structure of an exported proposition. Only
    /// polymorphic instances transported by a replayed export may bypass the
    /// ordinary scheme check; monomorphic declarations are always exact.
    pub(crate) fn validate_sort_erased_cprop(&self, prop: &CProp) -> Result<(), KernelError> {
        self.require_stamp(prop.context())?;
        let mut bounds = Vec::new();
        let ty =
            self.validate_sort_erased_term(prop.term(), &mut bounds, &mut |name, ty| match self
                .signature()
                .get_const(name)
            {
                Some(crate::ConstScheme::Monomorphic(_)) => {
                    self.signature().certify_const_instance(name, ty)?;
                    Ok(())
                },
                Some(crate::ConstScheme::Polymorphic(_)) => Ok(()),
                None => Err(KernelError::UndeclaredConst(name.clone())),
            })?;
        if !ty.is_prop() {
            return Err(KernelError::NotProposition(ty));
        }
        Ok(())
    }

    pub(crate) fn validate_replay_cprop(
        &self,
        prop: &CProp,
        certify_free: &mut dyn FnMut(&Name, &Ty) -> Result<(), KernelError>,
        is_sort_erased: bool,
    ) -> Result<(), KernelError> {
        self.require_stamp(prop.context())?;
        Self::validate_type_identities(prop.term())?;
        let mut bounds = Vec::new();
        let mut certify_const = |name: &Name, ty: &Ty| {
            if is_sort_erased {
                match self.signature().get_const(name) {
                    Some(crate::ConstScheme::Polymorphic(_)) => return Ok(()),
                    Some(crate::ConstScheme::Monomorphic(_)) => {},
                    None => return Err(KernelError::UndeclaredConst(name.clone())),
                }
            }
            self.signature().certify_const_instance(name, ty).map(|_| ())
        };
        let ty =
            self.validate_checked_with(prop.term(), &mut bounds, &mut certify_const, certify_free)?;
        if !ty.is_prop() {
            return Err(KernelError::NotProposition(ty));
        }
        Ok(())
    }

    pub(crate) fn validate_theorem_type_identities(
        prop: &CProp,
        hyps: &[CProp],
        flex_pairs: &[(CTerm, CTerm)],
    ) -> Result<(), KernelError> {
        let mut identities = crate::typ::TypeIdentityMap::default();
        identities.validate_term(prop.term())?;
        for hyp in hyps {
            identities.validate_term(hyp.term())?;
        }
        for (left, right) in flex_pairs {
            identities.validate_term(left.term())?;
            identities.validate_term(right.term())?;
        }
        Ok(())
    }

    /// Proof-local sort export retains ordinary term/binder/type checking.
    /// The supplied checker certifies each erased constant occurrence.
    pub(crate) fn validate_sort_erased_term(
        &self,
        term: &Term,
        bounds: &mut Vec<Ty>,
        certify_const: &mut dyn FnMut(&Name, &Ty) -> Result<(), KernelError>,
    ) -> Result<Ty, KernelError> {
        Self::validate_type_identities(term)?;
        self.validate_checked_with(term, bounds, certify_const, &mut |name, ty| {
            self.check_declared_free(name, ty)
        })
    }

    /// Re-certify an already checked proposition under this context's immutable
    /// theory/signature owner.
    pub(crate) fn recertify_prop(&self, prop: &CProp) -> Result<CProp, KernelError> {
        if prop.context().has_local_type_scope() && prop.context() != self.stamp() {
            return Err(KernelError::MixedContext {
                expected: Box::new(self.stamp()),
                actual: Box::new(prop.context()),
            });
        }
        Self::validate_type_identities(prop.term())?;
        let mut bounds = Vec::new();
        let ty = self.validate_checked(prop.term(), &mut bounds)?;
        if !ty.is_prop() {
            return Err(KernelError::NotProposition(ty));
        }
        CProp::new(prop.term().clone(), self.stamp())
    }

    fn validate_type_identities(term: &Term) -> Result<(), KernelError> {
        let mut identities = crate::typ::TypeIdentityMap::default();
        let mut result = Ok(());
        term.for_each_type_annotation(&mut |ty| {
            if result.is_ok() {
                result = identities.validate(ty);
            }
        });
        result
    }

    fn require_stamp(&self, actual: ContextStamp) -> Result<(), KernelError> {
        let expected = self.stamp();
        if expected != actual {
            return Err(KernelError::MixedContext {
                expected: Box::new(expected),
                actual: Box::new(actual),
            });
        }
        Ok(())
    }

    fn check_declared_free(&self, name: &Name, ty: &Ty) -> Result<(), KernelError> {
        if let Some(grants) = &self.replay_permissions {
            return Self::require_replay_free(grants, name, ty);
        }
        let declared =
            self.frees.get(name).ok_or_else(|| KernelError::UndeclaredFree(name.clone()))?;
        if declared != ty {
            return Err(KernelError::TypeMismatch {
                expected: declared.clone(),
                actual: ty.clone(),
            });
        }
        Ok(())
    }

    fn require_replay_free(
        replay_frees: &BTreeSet<(Name, Ty)>,
        name: &Name,
        ty: &Ty,
    ) -> Result<(), KernelError> {
        if replay_frees
            .iter()
            .any(|(granted_name, granted_ty)| granted_name == name && granted_ty == ty)
        {
            return Ok(());
        }
        Err(KernelError::UndeclaredFree(name.clone()))
    }

    /// Validate an already-certified term — used during replay.
    fn validate_checked(&self, term: &Term, bounds: &mut Vec<Ty>) -> Result<Ty, KernelError> {
        self.validate_checked_with(
            term,
            bounds,
            &mut |name, ty| self.signature().certify_const_instance(name, ty).map(|_| ()),
            &mut |name, ty| self.check_declared_free(name, ty),
        )
    }

    /// Kept as one exhaustive constructor table so replay checks remain auditable.
    fn validate_checked_with(
        &self,
        term: &Term,
        bounds: &mut Vec<Ty>,
        certify_const: &mut dyn FnMut(&Name, &Ty) -> Result<(), KernelError>,
        certify_free: &mut dyn FnMut(&Name, &Ty) -> Result<(), KernelError>,
    ) -> Result<Ty, KernelError> {
        self.validate_checked_annotations(term)?;
        match term {
            Term::Const { name, ty } => {
                certify_const(name, ty)?;
                Ok(ty.clone())
            },
            Term::Free { name, ty } => {
                certify_free(name, ty)?;
                Ok(ty.clone())
            },
            Term::Var { ty, .. } => Ok(ty.clone()),
            Term::Bound { index, ty } => {
                let distance = index.checked_add(1).ok_or(KernelError::UnboundBound(*index))?;
                let expected = bounds
                    .len()
                    .checked_sub(distance)
                    .and_then(|position| bounds.get(position))
                    .cloned()
                    .ok_or(KernelError::UnboundBound(*index))?;
                if expected != *ty {
                    return Err(KernelError::TypeMismatch { expected, actual: ty.clone() });
                }
                Ok(ty.clone())
            },
            Term::Abs { param_ty, body, ty, .. } => {
                bounds.push(param_ty.clone());
                let body_ty =
                    self.validate_checked_with(body, bounds, certify_const, certify_free)?;
                bounds.pop();
                let expected = Ty::arrow(param_ty.clone(), body_ty);
                if expected != *ty {
                    return Err(KernelError::TypeMismatch { expected, actual: ty.clone() });
                }
                Ok(ty.clone())
            },
            Term::Forall { param_ty, body, .. } => {
                bounds.push(param_ty.clone());
                let body_ty =
                    self.validate_checked_with(body, bounds, certify_const, certify_free)?;
                bounds.pop();
                if !body_ty.is_prop() {
                    return Err(KernelError::NotProposition(body_ty));
                }
                Ok(Ty::prop())
            },
            Term::App { func, arg, ty } => {
                let func_ty =
                    self.validate_checked_with(func, bounds, certify_const, certify_free)?;
                let arg_ty =
                    self.validate_checked_with(arg, bounds, certify_const, certify_free)?;
                let (expected_arg, expected_result) = func_ty
                    .dest_arrow()
                    .map(|(from, to)| (from.clone(), to.clone()))
                    .ok_or_else(|| KernelError::NotFunctionType(func_ty.clone()))?;
                if expected_arg != arg_ty {
                    return Err(KernelError::TypeMismatch {
                        expected: expected_arg,
                        actual: arg_ty,
                    });
                }
                if expected_result != *ty {
                    return Err(KernelError::TypeMismatch {
                        expected: expected_result,
                        actual: ty.clone(),
                    });
                }
                Ok(ty.clone())
            },
            Term::Eq { object_ty, lhs, rhs } => {
                let lhs_ty =
                    self.validate_checked_with(lhs, bounds, certify_const, certify_free)?;
                let rhs_ty =
                    self.validate_checked_with(rhs, bounds, certify_const, certify_free)?;
                if lhs_ty != *object_ty {
                    return Err(KernelError::TypeMismatch {
                        expected: object_ty.clone(),
                        actual: lhs_ty,
                    });
                }
                if rhs_ty != *object_ty {
                    return Err(KernelError::TypeMismatch {
                        expected: object_ty.clone(),
                        actual: rhs_ty,
                    });
                }
                Ok(Ty::prop())
            },
            Term::Imp { premise, conclusion } => {
                let premise_ty =
                    self.validate_checked_with(premise, bounds, certify_const, certify_free)?;
                if !premise_ty.is_prop() {
                    return Err(KernelError::NotProposition(premise_ty));
                }
                let conclusion_ty =
                    self.validate_checked_with(conclusion, bounds, certify_const, certify_free)?;
                if !conclusion_ty.is_prop() {
                    return Err(KernelError::NotProposition(conclusion_ty));
                }
                Ok(Ty::prop())
            },
        }
    }

    // One exhaustive constructor table keeps public and schema checks identical.
    fn certify_raw(&self, raw: RawTerm, bounds: &[Ty]) -> Result<Term, KernelError> {
        self.validate_raw_annotation(&raw)?;
        match raw {
            RawTerm::Const { name, ty } => {
                self.signature().certify_const_instance(&name, &ty)?;
                self.validate_type(&ty)?;
                Ok(Term::Const { name, ty })
            },
            RawTerm::Free { name, ty } => {
                self.check_declared_free(&name, &ty)?;
                Ok(Term::Free { name, ty })
            },
            RawTerm::Var { name, index, ty } => Ok(Term::Var { name, index, ty }),
            RawTerm::Bound(index) => {
                let ty = bounds.get(index).cloned().ok_or(KernelError::UnboundBound(index))?;
                Ok(Term::Bound { index, ty })
            },
            RawTerm::Abs { name, ty, body } => {
                let mut scoped = Vec::with_capacity(bounds.len() + 1);
                scoped.push(ty.clone());
                scoped.extend_from_slice(bounds);
                let body = self.certify_raw(*body, &scoped)?;
                let abs_ty = Ty::arrow(ty.clone(), body.ty());
                Ok(Term::Abs { name, param_ty: ty, body: Box::new(body), ty: abs_ty })
            },
            RawTerm::Forall { name, param_ty, body } => {
                let mut scoped = Vec::with_capacity(bounds.len() + 1);
                scoped.push(param_ty.clone());
                scoped.extend_from_slice(bounds);
                let body = self.certify_raw(*body, &scoped)?;
                if !body.ty().is_prop() {
                    return Err(KernelError::NotProposition(body.ty()));
                }
                Ok(Term::Forall { name, param_ty, body: Box::new(body) })
            },
            RawTerm::App { func, arg } => {
                let func = self.certify_raw(*func, bounds)?;
                let arg = self.certify_raw(*arg, bounds)?;
                let (expected_arg, result_ty) = func
                    .ty()
                    .dest_arrow()
                    .map(|(from, to)| (from.clone(), to.clone()))
                    .ok_or_else(|| KernelError::NotFunctionType(func.ty().clone()))?;
                if expected_arg != arg.ty() {
                    return Err(KernelError::TypeMismatch {
                        expected: expected_arg,
                        actual: arg.ty(),
                    });
                }
                Ok(Term::App { func: Box::new(func), arg: Box::new(arg), ty: result_ty })
            },
            RawTerm::Eq { lhs, rhs } => {
                let lhs = self.certify_raw(*lhs, bounds)?;
                let rhs = self.certify_raw(*rhs, bounds)?;
                Term::mk_eq(lhs, rhs)
            },
            RawTerm::Imp { premise, conclusion } => {
                let premise = self.certify_raw(*premise, bounds)?;
                let conclusion = self.certify_raw(*conclusion, bounds)?;
                Term::mk_imp(premise, conclusion)
            },
        }
    }

    fn validate_raw_annotation(&self, raw: &RawTerm) -> Result<(), KernelError> {
        match raw {
            RawTerm::Const { ty, .. }
            | RawTerm::Free { ty, .. }
            | RawTerm::Var { ty, .. }
            | RawTerm::Abs { ty, .. } => self.validate_type(ty),
            RawTerm::Forall { param_ty, .. } => self.validate_type(param_ty),
            _ => Ok(()),
        }
    }

    fn validate_checked_annotations(&self, term: &Term) -> Result<(), KernelError> {
        match term {
            Term::Const { ty, .. }
            | Term::Free { ty, .. }
            | Term::Var { ty, .. }
            | Term::Bound { ty, .. }
            | Term::App { ty, .. } => self.validate_type(ty),
            Term::Abs { param_ty, ty, .. } => {
                self.validate_type(param_ty)?;
                self.validate_type(ty)
            },
            Term::Forall { param_ty, .. } => self.validate_type(param_ty),
            Term::Eq { object_ty, .. } => self.validate_type(object_ty),
            Term::Imp { .. } => Ok(()),
        }
    }
}

/// A proof obligation is not a theorem.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofObligation {
    goal: CProp,
}

impl ProofObligation {
    pub fn new(context: &ProofContext, raw_goal: RawTerm) -> Result<Self, KernelError> {
        Ok(ProofObligation { goal: context.certify_prop(raw_goal)? })
    }

    pub fn goal(&self) -> &CProp {
        &self.goal
    }
}

#[cfg(test)]
pub(crate) fn validate_checked_for_test(
    ctx: &ProofContext,
    term: &Term,
) -> Result<Ty, KernelError> {
    let mut bounds = Vec::new();
    ProofContext::validate_type_identities(term)?;
    ctx.validate_checked(term, &mut bounds)
}

#[cfg(test)]
mod type_identity_tests {
    use super::*;

    #[test]
    fn certify_prop_same_schematic_identity_different_sort_rejects() {
        let context = ProofContext::new(TheorySnapshot::root(
            "T",
            Signature::new().install_empty_class(crate::EmptyClassDeclCert::hol_type()).unwrap(),
        ));
        let left_ty = Ty::tvar("a", 0, crate::Sort::empty());
        let right_ty = Ty::tvar("a", 0, crate::Sort::hol_type());
        let proposition = RawTerm::imp(
            RawTerm::eq(RawTerm::var("x", 0, left_ty.clone()), RawTerm::var("x", 0, left_ty)),
            RawTerm::eq(RawTerm::var("y", 0, right_ty.clone()), RawTerm::var("y", 0, right_ty)),
        );
        assert!(matches!(
            context.certify_prop(proposition),
            Err(KernelError::TypeIdentityMismatch { name, index: Some(0), .. })
                if name.as_str() == "a"
        ));
    }
}
