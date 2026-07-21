use std::collections::HashMap;

use super::{
    CProp, CTerm, ContextStamp, KernelError, Name, RawTerm, Signature, Term, TheorySnapshot, Ty,
};

/// Proof context for strict term certification.
#[derive(Clone, Debug)]
pub struct ProofContext {
    theory: TheorySnapshot,
    frees: HashMap<Name, Ty>,
}

impl ProofContext {
    pub fn new(theory: TheorySnapshot) -> Self {
        ProofContext { theory, frees: HashMap::new() }
    }

    pub fn signature(&self) -> &Signature {
        self.theory.signature()
    }

    pub fn theory(&self) -> &TheorySnapshot {
        &self.theory
    }

    pub fn stamp(&self) -> ContextStamp {
        self.theory.stamp()
    }

    pub fn declare_free(&mut self, name: impl Into<Name>, ty: Ty) {
        self.frees.insert(name.into(), ty);
    }

    pub fn free_type(&self, name: &Name) -> Option<&Ty> {
        self.frees.get(name)
    }

    pub fn certify_term(&self, raw: RawTerm) -> Result<CTerm, KernelError> {
        let term = self.certify_raw(raw, &[])?;
        Ok(CTerm::new(term, self.stamp()))
    }

    pub fn certify_prop(&self, raw: RawTerm) -> Result<CProp, KernelError> {
        let term = self.certify_raw(raw, &[])?;
        CProp::new(term, self.stamp())
    }

    /// Revalidate a certified term against this exact proof context without
    /// normalizing or rebuilding it.
    pub(crate) fn validate_cterm(&self, term: &CTerm) -> Result<(), KernelError> {
        self.require_stamp(term.context())?;
        let mut bounds = Vec::new();
        self.validate_checked(term.term(), &mut bounds)?;
        Ok(())
    }

    /// Revalidate a certified proposition against this exact proof context.
    pub(crate) fn validate_cprop(&self, prop: &CProp) -> Result<(), KernelError> {
        self.require_stamp(prop.context())?;
        let mut bounds = Vec::new();
        let ty = self.validate_checked(prop.term(), &mut bounds)?;
        if !ty.is_prop() {
            return Err(KernelError::NotProposition(ty));
        }
        Ok(())
    }

    /// Re-certify an already checked proposition under this context's immutable
    /// theory/signature owner.
    pub(crate) fn recertify_prop(&self, prop: &CProp) -> Result<CProp, KernelError> {
        let mut bounds = Vec::new();
        let ty = self.validate_checked(prop.term(), &mut bounds)?;
        if !ty.is_prop() {
            return Err(KernelError::NotProposition(ty));
        }
        CProp::new(prop.term().clone(), self.stamp())
    }

    fn require_stamp(&self, actual: ContextStamp) -> Result<(), KernelError> {
        let expected = self.stamp();
        if expected != actual {
            return Err(KernelError::MixedContext { expected, actual });
        }
        Ok(())
    }

    fn validate_checked(&self, term: &Term, bounds: &mut Vec<Ty>) -> Result<Ty, KernelError> {
        match term {
            Term::Const { name, ty } => {
                let _inst = self.signature().certify_const_instance(name, ty)?;
                Ok(ty.clone())
            },
            Term::Free { name, ty } => {
                let declared = self
                    .frees
                    .get(name)
                    .ok_or_else(|| KernelError::UndeclaredFree(name.clone()))?;
                if declared != ty {
                    return Err(KernelError::TypeMismatch {
                        expected: declared.clone(),
                        actual: ty.clone(),
                    });
                }
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
                let body_ty = self.validate_checked(body, bounds)?;
                bounds.pop();
                let expected = Ty::arrow(param_ty.clone(), body_ty);
                if expected != *ty {
                    return Err(KernelError::TypeMismatch { expected, actual: ty.clone() });
                }
                Ok(ty.clone())
            },
            Term::Forall { param_ty, body, .. } => {
                bounds.push(param_ty.clone());
                let body_ty = self.validate_checked(body, bounds)?;
                bounds.pop();
                if !body_ty.is_prop() {
                    return Err(KernelError::NotProposition(body_ty));
                }
                Ok(Ty::prop())
            },
            Term::App { func, arg, ty } => {
                let func_ty = self.validate_checked(func, bounds)?;
                let arg_ty = self.validate_checked(arg, bounds)?;
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
                let lhs_ty = self.validate_checked(lhs, bounds)?;
                let rhs_ty = self.validate_checked(rhs, bounds)?;
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
                let premise_ty = self.validate_checked(premise, bounds)?;
                if !premise_ty.is_prop() {
                    return Err(KernelError::NotProposition(premise_ty));
                }
                let conclusion_ty = self.validate_checked(conclusion, bounds)?;
                if !conclusion_ty.is_prop() {
                    return Err(KernelError::NotProposition(conclusion_ty));
                }
                Ok(Ty::prop())
            },
        }
    }

    fn certify_raw(&self, raw: RawTerm, bounds: &[Ty]) -> Result<Term, KernelError> {
        match raw {
            RawTerm::Const { name, ty } => {
                let _inst = self.signature().certify_const_instance(&name, &ty)?;
                Ok(Term::Const { name, ty })
            },
            RawTerm::Free { name, ty } => {
                let declared = self
                    .frees
                    .get(&name)
                    .ok_or_else(|| KernelError::UndeclaredFree(name.clone()))?;
                if declared != &ty {
                    return Err(KernelError::TypeMismatch {
                        expected: declared.clone(),
                        actual: ty,
                    });
                }
                Ok(Term::Free { name, ty: declared.clone() })
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
