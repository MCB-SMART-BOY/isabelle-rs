use std::collections::HashMap;

use super::{CProp, CTerm, KernelError, Name, RawTerm, Signature, Term, Ty};

/// Proof context for strict term certification.
#[derive(Clone, Debug)]
pub struct ProofContext {
    signature: Signature,
    frees: HashMap<Name, Ty>,
}

impl ProofContext {
    pub fn new(signature: Signature) -> Self {
        ProofContext { signature, frees: HashMap::new() }
    }

    pub fn signature(&self) -> &Signature {
        &self.signature
    }

    pub fn declare_free(&mut self, name: impl Into<Name>, ty: Ty) {
        self.frees.insert(name.into(), ty);
    }

    pub fn free_type(&self, name: &Name) -> Option<&Ty> {
        self.frees.get(name)
    }

    pub fn certify_term(&self, raw: RawTerm) -> Result<CTerm, KernelError> {
        let term = self.certify_raw(raw, &[])?;
        Ok(CTerm::new(term))
    }

    pub fn certify_prop(&self, raw: RawTerm) -> Result<CProp, KernelError> {
        let term = self.certify_raw(raw, &[])?;
        CProp::new(term)
    }

    fn certify_raw(&self, raw: RawTerm, bounds: &[Ty]) -> Result<Term, KernelError> {
        match raw {
            RawTerm::Const { name, ty } => {
                let declared = self
                    .signature
                    .const_type(&name)
                    .ok_or_else(|| KernelError::UndeclaredConst(name.clone()))?;
                if declared != &ty {
                    return Err(KernelError::TypeMismatch {
                        expected: declared.clone(),
                        actual: ty,
                    });
                }
                Ok(Term::Const { name, ty: declared.clone() })
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
