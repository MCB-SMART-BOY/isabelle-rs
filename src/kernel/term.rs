use super::{InstEntry, KernelError, Name, Ty};

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
}

/// Certified typed term used by the strict kernel.
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

    /// Substitute `arg` for the outermost `Bound(0)`, decrementing all other
    /// Bound indices by 1. This is the core operation of beta reduction.
    ///
    /// For `(Abs { body: body', .. })(arg)`, this computes `body'[arg/x]`
    /// where `x` is represented as `Bound(0, param_ty)` in `body'`.
    pub(in crate::kernel) fn instantiate_bound0(body: &Term, arg: &Term) -> Term {
        fn subst(term: &Term, args: &[Term]) -> Term {
            match term {
                Term::Bound { index, ty } => {
                    if *index < args.len() {
                        lift(&args[*index], 0, 0)
                    } else {
                        Term::Bound { index: index - args.len(), ty: ty.clone() }
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

        subst(body, &[arg.clone()])
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

    /// Replace each listed `Free(name, ty)` with a `Var(name, start + i, ty)`
    /// where `i` is the position in the `frees` list.
    ///
    /// Unmatched entries in `frees` are silently ignored (no-op). The caller is
    /// responsible for setting `start` to avoid collisions with existing `Var`
    /// indices — typically `start = max_var_index() + 1`.
    pub fn generalize_to_vars(&self, frees: &[(Name, Ty)], start: usize) -> Term {
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
                    Term::Free { name, ty } => {
                        if let Some(i) = frees.iter().position(|(n, t)| n == &name && t == &ty) {
                            results.push(Term::Var { name, index: start + i, ty });
                        } else {
                            results.push(Term::Free { name, ty });
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

    /// Replace each matching `Var(name, idx, ty)` with its corresponding
    /// replacement term. Vars not listed in the substitution are preserved.
    ///
    /// This is the inverse of `generalize_to_vars`.
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
        loop {
            match current {
                Term::Imp { premise, conclusion } => {
                    prems.push((**premise).clone());
                    current = conclusion;
                },
                _ => break,
            }
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
