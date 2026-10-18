use std::{
    borrow::Cow,
    collections::{BTreeSet, HashSet},
};

use super::{
    CProp, CTerm, ClosedThm, ContextStamp, DependencySet, Derivation, InstEntry, KernelError,
    KernelThm, Name, OpenThm, ProofContext, Term, TrustedTheorem, TrustedTheory, Ty,
    obligations::ProofPayload,
    thm::{prop_from_term, remove_hyp, union_hyps},
    unify,
};

fn require_same_context(expected: ContextStamp, actual: ContextStamp) -> Result<(), KernelError> {
    if expected != actual {
        return Err(KernelError::MixedContext {
            expected: Box::new(expected),
            actual: Box::new(actual),
        });
    }
    Ok(())
}

pub(crate) fn validate_instantiation_entries(
    context: ContextStamp,
    validator: Option<&ProofContext>,
    subst: &[InstEntry],
) -> Result<(), KernelError> {
    let mut identities = HashSet::with_capacity(subst.len());
    for entry in subst {
        require_same_context(context, entry.replacement().context())?;
        if !identities.insert((entry.name(), entry.index(), entry.var_ty())) {
            return Err(KernelError::DuplicateSubstitution {
                name: entry.name().clone(),
                index: entry.index(),
            });
        }
        if entry.replacement().ty() != *entry.var_ty() {
            return Err(KernelError::TypeMismatch {
                expected: entry.var_ty().clone(),
                actual: entry.replacement().ty(),
            });
        }
        entry.replacement().term().validate_closed_bounds()?;
        if let Some(validator) = validator {
            validator.validate_cterm(entry.replacement())?;
        }
    }
    Ok(())
}

// Only accepting replay supplies a validator; structural diagnostics cannot seal a token.
pub(crate) fn replay_instantiation(
    validator: Option<&ProofContext>,
    thm: &KernelThm,
    type_inst: &crate::logic::TypeInstantiation,
    subst: &[InstEntry],
) -> Result<KernelThm, KernelError> {
    if thm.hyps().iter().any(|hyp| hyp.term().has_schematic_hypothesis()) {
        return Err(KernelError::SchematicHypothesis);
    }
    let is_erased = matches!(thm.payload().mode(), crate::obligations::ProofMode::SortErased);
    if let Some(context) = validator {
        require_same_context(context.stamp(), thm.context())?;
        context.validate_type_instantiation(type_inst)?;
        validate_instantiated_prop(context, thm.prop(), is_erased)?;
        for hyp in thm.hyps() {
            context.validate_cprop(hyp)?;
        }
    }
    validate_instantiation_entries(thm.context(), validator, subst)?;
    let typed = if type_inst.iter().next().is_none() {
        Cow::Borrowed(thm.prop())
    } else {
        Cow::Owned(CProp::new(thm.prop().term().instantiate_types(type_inst)?, thm.context())?)
    };
    if let Some(context) = validator {
        validate_instantiated_prop(context, &typed, is_erased)?;
    }
    let prop = if subst.is_empty() {
        typed.into_owned()
    } else {
        CProp::new(typed.term().instantiate_vars(subst), thm.context())?
    };
    if let Some(context) = validator {
        validate_instantiated_prop(context, &prop, is_erased)?;
    }
    let payload = ProofPayload::instantiate(thm.payload(), type_inst, subst, thm.hyps(), &prop)?;
    if validator.is_some() {
        ProofContext::validate_theorem_type_identities(&prop, thm.hyps(), payload.flex_pairs())?;
    }
    Ok(KernelThm::new_with_payload(
        thm.hyps().to_vec(),
        prop,
        payload,
        Derivation::Instantiate {
            type_inst: type_inst.clone(),
            subst: subst.to_vec(),
            premise: Box::new(thm.clone()),
        },
    ))
}

fn validate_instantiated_prop(
    context: &ProofContext,
    prop: &CProp,
    is_erased: bool,
) -> Result<(), KernelError> {
    if is_erased { context.validate_sort_erased_cprop(prop) } else { context.validate_cprop(prop) }
}

pub(crate) fn transfer_with_dependencies(
    owner: &TrustedTheory,
    theorem: &KernelThm,
) -> Result<(KernelThm, DependencySet), KernelError> {
    if theorem.context().has_local_type_scope() {
        return Err(KernelError::LocalTypeScopeEscape { context: Box::new(theorem.context()) });
    }
    let origin = owner
        .find_ancestor_by_id(theorem.proved_in())
        .ok_or(KernelError::UnknownTheoremDependency)?;
    require_same_context(origin.stamp(), theorem.context())?;
    let original_context = ProofContext::new(origin.snapshot().clone());
    let mut dependencies = DependencySet::empty();
    crate::invariant::replay_source_in(&origin, &original_context, theorem, &mut dependencies)?;
    if origin.id() == owner.id() {
        return Ok((theorem.clone(), dependencies));
    }
    let target = ProofContext::new(owner.snapshot().clone());
    let prop = if matches!(theorem.payload().mode(), crate::obligations::ProofMode::SortErased) {
        let prop = prop_from_term(theorem.prop().term().clone(), target.stamp());
        target.validate_sort_erased_cprop(&prop)?;
        prop
    } else {
        target.recertify_prop(theorem.prop())?
    };
    let hyps = theorem
        .hyps()
        .iter()
        .map(|hyp| target.recertify_prop(hyp))
        .collect::<Result<Vec<_>, _>>()?;
    let payload = theorem.payload().transfer_to(&target)?;
    Ok((
        KernelThm::new_with_payload(
            hyps,
            prop,
            payload,
            Derivation::Transfer { premise: Box::new(theorem.clone()) },
        ),
        dependencies,
    ))
}

pub(crate) fn export_scope_with_dependencies(
    owner: &TrustedTheory,
    source_context: &ProofContext,
    theorem: &KernelThm,
    dependencies: &mut DependencySet,
) -> Result<KernelThm, KernelError> {
    require_same_context(owner.stamp(), source_context.theory().stamp())?;
    require_same_context(source_context.stamp(), theorem.context())?;
    let source =
        crate::invariant::replay_scoped_source_in(owner, source_context, theorem, dependencies)?;
    let target = ProofContext::new(owner.snapshot().clone());
    let prop = prop_from_term(source.prop().term().clone(), target.stamp());
    validate_instantiated_prop(
        &target,
        &prop,
        matches!(source.payload().mode(), crate::obligations::ProofMode::SortErased),
    )?;
    let hyps = source
        .hyps()
        .iter()
        .map(|hyp| {
            let hyp = prop_from_term(hyp.term().clone(), target.stamp());
            target.validate_cprop(&hyp)?;
            Ok(hyp)
        })
        .collect::<Result<Vec<_>, KernelError>>()?;
    let payload = source.payload().transfer_to(&target)?;
    Ok(KernelThm::new_with_payload(
        hyps,
        prop,
        payload,
        Derivation::ExportScope {
            scope: source_context.snapshot_scope(),
            premise: Box::new(source),
        },
    ))
}

/// Primitive inference rules of the strict kernel nucleus.
pub struct KernelRules;

impl KernelRules {
    /// Import one replay-accepted ancestor theorem into the current immutable
    /// theory context.
    pub fn theorem_ref(
        theory: &TrustedTheory,
        theorem: &TrustedTheorem,
    ) -> Result<ClosedThm, KernelError> {
        let theorem =
            theory.find_accepted_theorem(theorem).ok_or(KernelError::UnknownTheoremDependency)?;
        let context = ProofContext::new(theory.snapshot().clone());
        let prop = if matches!(
            theorem.as_kernel().payload().mode(),
            crate::obligations::ProofMode::SortErased,
        ) {
            crate::thm::prop_from_term(theorem.prop().term().clone(), context.stamp())
        } else {
            context.recertify_prop(theorem.prop())?
        };
        Ok(ClosedThm::new(KernelThm::new(
            Vec::new(),
            prop,
            Derivation::TheoremRef { theorem: theorem.clone() },
        )))
    }

    /// Re-certify a complete, replayed open or closed proof from a committed
    /// ancestor into this owner. A sibling or locally scoped proof is not an
    /// implicit theorem reference.
    pub fn transfer(owner: &TrustedTheory, theorem: &KernelThm) -> Result<KernelThm, KernelError> {
        Ok(transfer_with_dependencies(owner, theorem)?.0)
    }

    /// Export a fully replayed local proof without publishing local declarations.
    /// Remaining fixed parameters or outstanding obligations are never erased.
    pub fn export_scope(
        owner: &TrustedTheory,
        source_context: &ProofContext,
        theorem: &KernelThm,
    ) -> Result<KernelThm, KernelError> {
        export_scope_with_dependencies(owner, source_context, theorem, &mut DependencySet::empty())
    }

    pub fn assume(prop: CProp) -> Result<OpenThm, KernelError> {
        if prop.term().has_schematic_hypothesis() {
            return Err(KernelError::SchematicHypothesis);
        }
        let thm = KernelThm::new(vec![prop.clone()], prop.clone(), Derivation::Assume { prop });
        Ok(OpenThm::new(thm))
    }
    /// Add a certified, schematic-free real hypothesis without discharging the source.
    pub fn weaken(assumption: &CProp, thm: &KernelThm) -> Result<KernelThm, KernelError> {
        require_same_context(thm.context(), assumption.context())?;
        if assumption.term().has_schematic_hypothesis() {
            return Err(KernelError::SchematicHypothesis);
        }
        let hyps = union_hyps(thm.hyps(), std::slice::from_ref(assumption));
        Ok(KernelThm::new(
            hyps,
            thm.prop().clone(),
            Derivation::Weaken { assumption: assumption.clone(), premise: Box::new(thm.clone()) },
        ))
    }

    pub fn reflexive(term: CTerm) -> ClosedThm {
        let prop = prop_from_term(
            Term::mk_eq(term.term().clone(), term.term().clone())
                .expect("reflexive uses one typed term"),
            term.context(),
        );
        let thm = KernelThm::new(vec![], prop, Derivation::Reflexive { term });
        ClosedThm::new(thm)
    }

    pub fn symmetric(thm: &KernelThm) -> Result<KernelThm, KernelError> {
        let (_, lhs, rhs) = thm.prop().term().dest_eq().ok_or(KernelError::NotEquality)?;
        let prop = prop_from_term(Term::mk_eq(rhs.clone(), lhs.clone())?, thm.context());
        Ok(KernelThm::new(
            thm.hyps().to_vec(),
            prop,
            Derivation::Symmetric { premise: Box::new(thm.clone()) },
        ))
    }

    pub fn transitive(left: &KernelThm, right: &KernelThm) -> Result<KernelThm, KernelError> {
        require_same_context(left.context(), right.context())?;
        let (left_ty, lhs, left_mid) =
            left.prop().term().dest_eq().ok_or(KernelError::NotEquality)?;
        let (right_ty, right_mid, rhs) =
            right.prop().term().dest_eq().ok_or(KernelError::NotEquality)?;
        if left_ty != right_ty {
            return Err(KernelError::TypeMismatch {
                expected: left_ty.clone(),
                actual: right_ty.clone(),
            });
        }
        if !left_mid.alpha_eq(right_mid) {
            return Err(KernelError::MiddleMismatch);
        }
        let prop = prop_from_term(Term::mk_eq(lhs.clone(), rhs.clone())?, left.context());
        Ok(KernelThm::new(
            union_hyps(left.hyps(), right.hyps()),
            prop,
            Derivation::Transitive { left: Box::new(left.clone()), right: Box::new(right.clone()) },
        ))
    }

    pub fn beta_conversion(redex: CTerm) -> Result<ClosedThm, KernelError> {
        let (abs, arg) =
            redex.term().dest_app().ok_or(KernelError::BetaRedexExpected(redex.ty()))?;
        let (_, param_ty, body) =
            abs.dest_abs().ok_or(KernelError::BetaRedexExpected(redex.ty()))?;

        // The argument's type must match the binder's parameter type.
        if arg.ty() != *param_ty {
            return Err(KernelError::TypeMismatch { expected: param_ty.clone(), actual: arg.ty() });
        }

        let reduced = Term::instantiate_bound0(body, arg);

        let prop = prop_from_term(
            Term::mk_eq(
                Term::App {
                    func: Box::new(abs.clone()),
                    arg: Box::new(arg.clone()),
                    ty: body.ty(),
                },
                reduced,
            )?,
            redex.context(),
        );
        let thm = KernelThm::new(vec![], prop, Derivation::BetaConversion { redex: redex.clone() });
        Ok(ClosedThm::new(thm))
    }
    /// The exact Pure eta redex `λx. f x == f`, not arbitrary eta normalization.
    pub fn eta_conversion(redex: CTerm) -> Result<ClosedThm, KernelError> {
        redex.term().validate_closed_bounds()?;
        let contracted = contract_eta(redex.term())?;
        let prop = prop_from_term(Term::mk_eq(redex.term().clone(), contracted)?, redex.context());
        Ok(ClosedThm::new(KernelThm::new(vec![], prop, Derivation::EtaConversion { redex })))
    }

    pub fn implies_intr(assumption: &CProp, thm: &KernelThm) -> Result<KernelThm, KernelError> {
        require_same_context(thm.context(), assumption.context())?;
        let hyps = remove_hyp(thm.hyps(), assumption);
        let prop = prop_from_term(
            Term::mk_imp(assumption.term().clone(), thm.prop().term().clone())?,
            thm.context(),
        );
        Ok(KernelThm::new(
            hyps,
            prop,
            Derivation::ImpliesIntr {
                assumption: assumption.clone(),
                premise: Box::new(thm.clone()),
            },
        ))
    }

    pub fn implies_elim(major: &KernelThm, minor: &KernelThm) -> Result<KernelThm, KernelError> {
        require_same_context(major.context(), minor.context())?;
        let (antecedent, consequent) =
            major.prop().term().dest_imp().ok_or(KernelError::NotImplication)?;
        if !antecedent.alpha_eq(minor.prop().term()) {
            return Err(KernelError::AntecedentMismatch);
        }
        Ok(KernelThm::new(
            union_hyps(major.hyps(), minor.hyps()),
            prop_from_term(consequent.clone(), major.context()),
            Derivation::ImpliesElim {
                major: Box::new(major.clone()),
                minor: Box::new(minor.clone()),
            },
        ))
    }

    /// `∀`-introduction (universal generalisation).
    ///
    /// ```text
    /// input:  Γ |- P
    ///         x : Free(name, τ)
    /// output: Γ |- ⋀x:τ. P'    where P' = P[x → Bound(0)]
    /// side:   x ∉ FV(Γ)
    /// ```
    ///
    /// The variable `x` is abstracted from the conclusion and replaced with
    /// `Bound(0)` inside the new `Forall` binder. Free-variable-in-hypotheses
    /// is enforced: `x` must not appear in any hypothesis of the input theorem.
    pub fn forall_intr(variable: &CTerm, thm: &KernelThm) -> Result<KernelThm, KernelError> {
        require_same_context(thm.context(), variable.context())?;
        // 1. Extract the free variable to abstract.
        let (free_name, free_ty) = match variable.term() {
            Term::Free { name, ty } => (name.clone(), ty.clone()),
            Term::Var { .. } => {
                // Schematic variable abstraction is not supported yet.
                return Err(KernelError::NotAbstractable(variable.ty()));
            },
            _ => return Err(KernelError::NotAbstractable(variable.ty())),
        };

        // 2. Side condition: x must not be free in any hypothesis.
        for hyp in thm.hyps() {
            if hyp.term().free_in(&free_name, &free_ty) {
                return Err(KernelError::FreeVarInHypotheses { name: free_name });
            }
        }
        if thm.payload().has_free_in_flex_pairs(&free_name, &free_ty) {
            return Err(KernelError::FreeVarInHypotheses { name: free_name });
        }

        // 3. Abstract the variable from the conclusion.
        let abstracted = Term::abstract_over(&free_name, &free_ty, thm.prop().term());
        let forall_prop =
            Term::Forall { name: free_name, param_ty: free_ty, body: Box::new(abstracted) };

        // 4. Preserve hypotheses; wrap result.
        Ok(KernelThm::new(
            thm.hyps().to_vec(),
            prop_from_term(forall_prop, thm.context()),
            Derivation::ForallIntr { variable: variable.clone(), premise: Box::new(thm.clone()) },
        ))
    }

    /// Congruence of equality (function-congruence).
    ///
    /// ```text
    /// input:  Γ |- f == g        (f, g : τ → σ)
    ///         Δ |- x == y        (x, y : τ)
    /// output: Γ ∪ Δ |- f x == g y
    /// ```
    ///
    /// Side conditions:
    /// - Both premises must be equality propositions.
    /// - `f` and `g` must be function types whose domain matches the argument
    ///   types of `x` and `y`.
    /// - The result `f x` and `g y` share the codomain `σ`.
    ///
    /// Propagation:
    /// - Hypotheses are unioned modulo strict alpha-equivalence.
    pub fn combination(th_f: &KernelThm, th_x: &KernelThm) -> Result<KernelThm, KernelError> {
        require_same_context(th_f.context(), th_x.context())?;
        // 1. Destructure both premises as equality.
        let (fn_ty, f, g) = th_f.prop().term().dest_eq().ok_or(KernelError::NotEquality)?;
        let (arg_ty, x, y) = th_x.prop().term().dest_eq().ok_or(KernelError::NotEquality)?;

        // 2. f/g must be function types.
        let (domain, codomain) =
            fn_ty.dest_arrow().ok_or(KernelError::NotFunctionType(fn_ty.clone()))?;

        // 3. x/y types must match the function domain.
        if *domain != *arg_ty {
            return Err(KernelError::TypeMismatch {
                expected: domain.clone(),
                actual: arg_ty.clone(),
            });
        }

        // 4. Build f x and g y then wrap as equality.
        let fx =
            Term::App { func: Box::new(f.clone()), arg: Box::new(x.clone()), ty: codomain.clone() };
        let gy =
            Term::App { func: Box::new(g.clone()), arg: Box::new(y.clone()), ty: codomain.clone() };
        let prop = prop_from_term(Term::mk_eq(fx, gy)?, th_f.context());

        // 5. Union hypotheses; wrap result.
        Ok(KernelThm::new(
            union_hyps(th_f.hyps(), th_x.hyps()),
            prop,
            Derivation::Combination {
                function: Box::new(th_f.clone()),
                argument: Box::new(th_x.clone()),
            },
        ))
    }

    /// `∀`-elimination (universal instantiation).
    ///
    /// ```text
    /// input:  Γ |- ⋀x:τ. P(x)
    ///         t : CTerm  with type τ
    /// output: Γ |- P(t)
    /// ```
    ///
    /// The outermost `Forall` binder is stripped and `Bound(0)` in the body is
    /// replaced with the argument term via `instantiate_bound0`. This is the
    /// de Bruijn inverse of `forall_intr`.
    ///
    /// Side conditions:
    /// - The theorem proposition must be a `Forall`.
    /// - The argument type must match the binder parameter type.
    pub fn forall_elim(thm: &KernelThm, arg: &CTerm) -> Result<KernelThm, KernelError> {
        require_same_context(thm.context(), arg.context())?;
        // 1. Destructure the forall proposition.
        let (_, param_ty, body) = thm.prop().term().dest_forall().ok_or(KernelError::NotForall)?;

        // 2. Type check: argument type must match binder type.
        if arg.ty() != *param_ty {
            return Err(KernelError::ForallBinderMismatch {
                expected: param_ty.clone(),
                actual: arg.ty(),
            });
        }

        // 3. Substitute argument for Bound(0) in the body.
        let instantiated = Term::instantiate_bound0(body, arg.term());

        // 4. Preserve hypotheses; wrap result.
        Ok(KernelThm::new(
            thm.hyps().to_vec(),
            prop_from_term(instantiated, thm.context()),
            Derivation::ForallElim { forall: Box::new(thm.clone()), arg: arg.clone() },
        ))
    }

    /// Abstraction: introduce lambda binders on both sides of an equality.
    ///
    /// ```text
    /// input:  Γ |- t == u              (t, u : β)
    ///         variable name x, type α
    /// output: Γ |- (λx:α. t[x→Bound(0)]) == (λx:α. u[x→Bound(0)])   (λx..., λx... : α → β)
    /// ```
    ///
    /// Side conditions:
    /// - Premise proposition must be equality.
    /// - `x` must not be free in any hypothesis in Γ.
    ///
    /// Propagation:
    /// - Hypotheses are preserved.
    pub fn abstraction(
        var_name: Name,
        var_ty: Ty,
        thm: &KernelThm,
    ) -> Result<KernelThm, KernelError> {
        // 1. Destructure premise as equality.
        let (eq_ty, t, u) = thm.prop().term().dest_eq().ok_or(KernelError::NotEquality)?;

        // 2. Side condition: x must not be free in any hypothesis.
        for hyp in thm.hyps() {
            if hyp.term().free_in(&var_name, &var_ty) {
                return Err(KernelError::FreeVarInHypotheses { name: var_name.clone() });
            }
        }
        if thm.payload().has_free_in_flex_pairs(&var_name, &var_ty) {
            return Err(KernelError::FreeVarInHypotheses { name: var_name.clone() });
        }

        // 3. Abstract the variable from both sides of the equality.
        //    This replaces Free(x, τ) with Bound(0, τ) at depth 0,
        //    converting external free references into de Bruijn indices
        //    bound by the new λ-binder.
        let lhs_body = Term::abstract_over(&var_name, &var_ty, t);
        let rhs_body = Term::abstract_over(&var_name, &var_ty, u);
        let fn_ty = Ty::arrow(var_ty.clone(), eq_ty.clone());
        let lhs = Term::Abs {
            name: var_name.clone(),
            param_ty: var_ty.clone(),
            body: Box::new(lhs_body),
            ty: fn_ty.clone(),
        };
        let rhs = Term::Abs {
            name: var_name.clone(),
            param_ty: var_ty.clone(),
            body: Box::new(rhs_body),
            ty: fn_ty.clone(),
        };
        let prop = prop_from_term(Term::mk_eq(lhs, rhs)?, thm.context());

        Ok(KernelThm::new(
            thm.hyps().to_vec(),
            prop,
            Derivation::Abstraction {
                variable_name: var_name,
                variable_type: var_ty,
                premise: Box::new(thm.clone()),
            },
        ))
    }

    /// Equality introduction: two mutual implications yield a propositional equality.
    ///
    /// ```text
    /// input:  Γ |- A ==> B
    ///         Δ |- B ==> A
    /// output: Γ ∪ Δ |- A == B
    /// ```
    ///
    /// Side conditions:
    /// - Both premises must be implication propositions.
    /// - The antecedent of the first must equal the consequent of the second
    ///   (strict alpha-equivalent), and vice versa.
    ///
    /// Propagation:
    /// - Hypotheses are unioned modulo strict alpha-equivalence.
    pub fn equal_intr(left: &KernelThm, right: &KernelThm) -> Result<KernelThm, KernelError> {
        require_same_context(left.context(), right.context())?;
        let (a1, b1) = left.prop().term().dest_imp().ok_or(KernelError::NotImplication)?;
        let (b2, a2) = right.prop().term().dest_imp().ok_or(KernelError::NotImplication)?;

        if !a1.alpha_eq(a2) {
            return Err(KernelError::AntecedentMismatch);
        }
        if !b1.alpha_eq(b2) {
            return Err(KernelError::AntecedentMismatch);
        }

        let prop = prop_from_term(Term::mk_eq(a1.clone(), b1.clone())?, left.context());
        Ok(KernelThm::new(
            union_hyps(left.hyps(), right.hyps()),
            prop,
            Derivation::EqualIntr { left: Box::new(left.clone()), right: Box::new(right.clone()) },
        ))
    }

    /// Equality elimination: from `A == B` and `A`, derive `B`.
    ///
    /// ```text
    /// input:  Γ |- A == B
    ///         Δ |- A
    /// output: Γ ∪ Δ |- B
    /// ```
    ///
    /// Side conditions:
    /// - Major premise must be an equality proposition.
    /// - Minor premise must be strict alpha-equivalent to the left-hand side
    ///   of the equality.
    ///
    /// Propagation:
    /// - Hypotheses are unioned modulo strict alpha-equivalence.
    pub fn equal_elim(equality: &KernelThm, minor: &KernelThm) -> Result<KernelThm, KernelError> {
        require_same_context(equality.context(), minor.context())?;
        let (object_ty, a, b) = equality.prop().term().dest_eq().ok_or(KernelError::NotEquality)?;

        // equal_elim requires propositional equality (A == B where A,B : prop),
        // not object equality (x == y where x,y : nat).
        if !object_ty.is_prop() {
            return Err(KernelError::NotProposition(object_ty.clone()));
        }

        if !a.alpha_eq(minor.prop().term()) {
            return Err(KernelError::AntecedentMismatch);
        }

        Ok(KernelThm::new(
            union_hyps(equality.hyps(), minor.hyps()),
            prop_from_term(b.clone(), equality.context()),
            Derivation::EqualElim {
                equality: Box::new(equality.clone()),
                minor: Box::new(minor.clone()),
            },
        ))
    }

    /// Conservative premise rewriting for goal states.
    ///
    /// ```text
    /// input:  Γ |- A == B      where A, B : prop
    ///         Δ |- G₁ ==> ... ==> A ==> ... ==> Gₘ ==> R
    /// output: Γ ∪ Δ |- G₁ ==> ... ==> B ==> ... ==> Gₘ ==> R
    /// ```
    ///
    /// First-version restrictions:
    /// - propositional equality only;
    /// - fixed lhs -> rhs direction;
    /// - selected goal subgoal must be strict alpha-equivalent to lhs;
    /// - no symmetric rewrite, object equality rewrite, unification, lifting,
    ///   freshening, or flex-flex handling.
    pub fn subst_premise(
        equality: &KernelThm,
        goal_state: &KernelThm,
        selected_subgoal_index: usize,
    ) -> Result<KernelThm, KernelError> {
        require_same_context(equality.context(), goal_state.context())?;
        let (object_ty, lhs, rhs) =
            equality.prop().term().dest_eq().ok_or(KernelError::NotEquality)?;

        if !object_ty.is_prop() {
            return Err(KernelError::NotProposition(object_ty.clone()));
        }
        if !lhs.ty().is_prop() {
            return Err(KernelError::NotProposition(lhs.ty()));
        }
        if !rhs.ty().is_prop() {
            return Err(KernelError::NotProposition(rhs.ty()));
        }

        let (goal_prems, _) = goal_state.prop().term().dest_imp_chain();
        let n_goal_prems = goal_prems.len();
        let selected_subgoal =
            goal_state.prop().term().select_subgoal(selected_subgoal_index).ok_or(
                KernelError::SubgoalIndexOutOfRange {
                    index: selected_subgoal_index,
                    nprems: n_goal_prems,
                },
            )?;

        if !selected_subgoal.alpha_eq(lhs) {
            return Err(KernelError::AntecedentMismatch);
        }

        let result_prop = prop_from_term(
            goal_state
                .prop()
                .term()
                .replace_subgoal_with_premises(selected_subgoal_index, std::slice::from_ref(rhs))?,
            goal_state.context(),
        );

        Ok(KernelThm::new(
            union_hyps(equality.hyps(), goal_state.hyps()),
            result_prop,
            Derivation::SubstPremise {
                equality: Box::new(equality.clone()),
                goal_state: Box::new(goal_state.clone()),
                selected_subgoal_index,
            },
        ))
    }

    /// Set Isabelle's maxidx to the requested bound, clamped to every
    /// schematic index still present in the theorem's complete payload.
    /// A larger bound is metadata only: it never certifies new variables.
    pub fn adjust_max_index(thm: &KernelThm, requested: Option<usize>) -> KernelThm {
        KernelThm::new_with_payload(
            thm.hyps().to_vec(),
            thm.prop().clone(),
            thm.payload().clone(),
            Derivation::AdjustMaxIndex { premise: Box::new(thm.clone()), requested },
        )
    }

    /// Generalize selected fixed types and terms at one fresh schematic index.
    /// Real hypotheses are unchanged and cannot mention selected parameters.
    pub fn generalize(
        thm: &KernelThm,
        type_names: &BTreeSet<Name>,
        term_names: &BTreeSet<Name>,
        index: usize,
    ) -> Result<KernelThm, KernelError> {
        if type_names.is_empty() && term_names.is_empty() {
            return Ok(thm.clone());
        }
        crate::typ::check_generalize_index(false, index, thm.max_var_index())?;
        validate_generalize_hypotheses(thm, type_names, term_names)?;
        let prop = prop_from_term(
            thm.prop().term().generalize_vars(type_names, term_names, index)?,
            thm.context(),
        );
        let source_frees = crate::bound_proof::collect_lexical_frees(thm)
            .into_iter()
            .filter(|(name, _)| term_names.contains(name))
            .collect();
        Ok(KernelThm::new_with_payload(
            thm.hyps().to_vec(),
            prop,
            thm.payload().generalize(type_names, term_names, index)?,
            Derivation::Generalize {
                type_names: type_names.clone(),
                term_names: term_names.clone(),
                index,
                source_frees,
                premise: Box::new(thm.clone()),
            },
        ))
    }

    /// Apply finite, simultaneous type substitution, then term substitution to P.
    /// Real hypotheses are fixed and cannot contain Var or TVar.
    ///
    /// # Trust boundary
    ///
    /// Every replacement must be a certified `CTerm` (via `InstEntry`), enforcing
    /// the kernel certification boundary: `RawTerm → CTerm certification →
    /// KernelRules`. Bare `Term` values cannot be passed as replacements.
    ///
    /// Side conditions:
    /// - Term keys match `(name, index, type)` after the complete type pass.
    /// - `replacement.ty() == var_ty` for every entry → `TypeMismatch`.
    /// - No duplicate `(name, index, type)` entries → `DuplicateSubstitution`.
    /// - No loose `Bound` in any replacement → `BoundInSubstitution`.
    /// - Partial substitution is valid: unmatched Vars remain unchanged.
    ///
    /// # Substitution semantics
    ///
    /// Substitution is **simultaneous**: Var nodes inside replacement terms are
    /// NOT substituted even if they match another entry. The replacement is a
    /// single-pass traversal.
    ///
    /// Duplicate detection uses the complete typed key after the type pass.
    /// Equal names and indices at distinct types remain distinct substitutions.
    ///
    /// The real hypotheses are preserved exactly.
    pub fn instantiate(
        context: &ProofContext,
        thm: &KernelThm,
        type_inst: &crate::logic::TypeInstantiation,
        subst: &[InstEntry],
    ) -> Result<KernelThm, KernelError> {
        replay_instantiation(Some(context), thm, type_inst, subst)
    }

    /// Internal certified-origin matcher for resolution rules.
    ///
    /// Calls the structural `unify::match_terms` and wraps each raw
    /// `MatchBinding` into a certified `InstEntry` via
    /// `CTerm::from_certified_subterm`.
    ///
    /// # Trust boundary
    ///
    /// This function is `pub(crate)` — only `src/kernel/` modules
    /// may call it. Legacy `src/core/`, `src/isar/`, `src/tools/`, and
    /// other upper-layer modules MUST NOT call this directly.
    ///
    /// The caller (currently only the resolution family in `KernelRules`)
    /// is responsible for ensuring that `pattern` and `target` are subterms
    /// extracted from certified `CProp`/`KernelThm` propositions
    /// (certified-by-origin).
    ///
    /// There is intentionally NO public API that accepts bare `&Term`
    /// and returns `InstEntry`.  External code must go through
    /// `ProofContext::certify_term` to construct `CTerm` values.
    ///
    /// # Constraints
    ///
    /// - Only pattern-side `Var` nodes are matched.
    /// - Exact type match required.
    /// - Repeated `Var` assignments must be consistent.
    /// - Replacements must not contain `Bound` variables.
    pub(crate) fn match_terms_certified(
        pattern: &Term,
        target: &Term,
        context: ContextStamp,
    ) -> Result<Vec<InstEntry>, KernelError> {
        let bindings = unify::match_terms(pattern, target)?;
        let mut entries = Vec::with_capacity(bindings.len());
        for b in bindings {
            let cterm = CTerm::from_certified_subterm(b.replacement, context);
            if cterm.ty() != b.var_ty {
                return Err(KernelError::TypeMismatch { expected: b.var_ty, actual: cterm.ty() });
            }
            entries.push(InstEntry::new(b.name, b.index, b.var_ty, cterm));
        }
        Ok(entries)
    }

    /// Minimal backward resolution: match the rule conclusion against a
    /// selected subgoal of the goal state, then replace that subgoal with
    /// the rule premises under the matching substitution.
    ///
    /// # Contract
    ///
    /// ```text
    /// rule:      Γ |- A₁ ==> ... ==> Aₙ ==> C
    /// goal:      Δ |- G₁ ==> ... ==> Gᵢ ==> ... ==> Gₘ ==> R
    /// match:     σ(C) = σ(Gᵢ)    (one-way matching, pattern Vars in C)
    /// result:    Γσ ∪ Δσ |-
    ///              G₁σ ==> ... ==> Gᵢ₋₁σ ==> A₁σ ==> ... ==> Aₙσ ==>
    ///              Gᵢ₊₁σ ==> ... ==> Gₘσ ==> Rσ
    /// ```
    ///
    /// # Constraints (first version)
    ///
    /// - One-way matching only (pattern-side Vars in rule conclusion `C`).
    /// - No lifting/freshening — returns `RequiresLifting` if rule and goal
    ///   have overlapping free variable names or schematic Var `(name, index)`
    ///   pairs.
    /// - No full unification. No flex-flex pairs.
    /// - Substitution is applied simultaneously to all components.
    ///
    /// # Errors
    ///
    /// - `SubgoalIndexOutOfRange` if `selected_subgoal_index >= nprems(goal)`.
    /// - `RequiresLifting` if rule and goal have overlapping free variable names
    ///   or schematic Var `(name, index)` pairs.
    /// - Match errors propagated from `match_terms_certified`.
    /// - Type errors propagated from term construction.
    pub fn resolve1_match(
        rule: &KernelThm,
        goal_state: &KernelThm,
        selected_subgoal_index: usize,
    ) -> Result<KernelThm, KernelError> {
        require_same_context(rule.context(), goal_state.context())?;
        // 1. Decompose rule into premises and conclusion.
        let (rule_prems, rule_concl) = rule.prop().term().dest_imp_chain();
        let rule_concl = rule_concl.clone();

        // 2. Decompose goal state to count selectable subgoals.
        let (goal_prems, _) = goal_state.prop().term().dest_imp_chain();
        let n_goal_prems = goal_prems.len();

        // 3. Select the target subgoal.
        let selected_subgoal =
            goal_state.prop().term().select_subgoal(selected_subgoal_index).ok_or(
                KernelError::SubgoalIndexOutOfRange {
                    index: selected_subgoal_index,
                    nprems: n_goal_prems,
                },
            )?;

        // 4. Match rule conclusion against the selected subgoal.
        let subst = Self::match_terms_certified(&rule_concl, &selected_subgoal, rule.context())?;

        // 5. Detect variable collision between rule and goal.
        Self::detect_collision(rule, goal_state)?;

        // 6. Apply substitution to rule premises.
        let rule_prems_sigma: Vec<Term> =
            rule_prems.iter().map(|p| p.instantiate_vars(&subst)).collect();

        // 7. Apply substitution to the goal state, then splice through the
        // same helper used by the implication-chain foundation tests. Keeping
        // all resolution-family rules on one subgoal replacement primitive
        // avoids subtly different premise ordering semantics.
        let goal_prop_sigma = goal_state.prop().term().instantiate_vars(&subst);
        let result_prop = prop_from_term(
            goal_prop_sigma
                .replace_subgoal_with_premises(selected_subgoal_index, &rule_prems_sigma)?,
            goal_state.context(),
        );

        // 8. Apply substitution to hypotheses and union.
        let rule_hyps_sigma: Vec<CProp> = rule
            .hyps()
            .iter()
            .map(|h| CProp::from_checked_term(h.term().instantiate_vars(&subst), rule.context()))
            .collect();
        let goal_hyps_sigma: Vec<CProp> = goal_state
            .hyps()
            .iter()
            .map(|h| {
                CProp::from_checked_term(h.term().instantiate_vars(&subst), goal_state.context())
            })
            .collect();
        let all_hyps = union_hyps(&rule_hyps_sigma, &goal_hyps_sigma);

        let payload = ProofPayload::resolve_match(
            rule.payload(),
            goal_state.payload(),
            &subst,
            &all_hyps,
            &result_prop,
        )?;
        Ok(KernelThm::new_with_payload(
            all_hyps,
            result_prop,
            payload,
            Derivation::Resolve1Match {
                rule: Box::new(rule.clone()),
                goal_state: Box::new(goal_state.clone()),
                selected_subgoal_index,
                subst,
            },
        ))
    }

    /// Conservative collision detection: return `RequiresLifting` if rule
    /// and goal share any free variable name or schematic Var `(name, index)`.
    ///
    /// This is intentionally conservative — it may reject valid cases, but
    /// it will never silently produce an incorrect theorem. As lifting is
    /// implemented, the rejection set will shrink.
    fn detect_collision(rule: &KernelThm, goal: &KernelThm) -> Result<(), KernelError> {
        let mut rule_frees = HashSet::new();
        for hyp in rule.hyps() {
            collect_free_names(hyp.term(), &mut rule_frees);
        }
        collect_free_names(rule.prop().term(), &mut rule_frees);

        let mut goal_frees = HashSet::new();
        for hyp in goal.hyps() {
            collect_free_names(hyp.term(), &mut goal_frees);
        }
        collect_free_names(goal.prop().term(), &mut goal_frees);

        for name in &rule_frees {
            if goal_frees.contains(name) {
                return Err(KernelError::RequiresLifting {
                    rule_var: name.clone(),
                    goal_var: name.clone(),
                });
            }
        }

        let mut rule_vars = HashSet::new();
        for hyp in rule.hyps() {
            collect_var_keys(hyp.term(), &mut rule_vars);
        }
        collect_var_keys(rule.prop().term(), &mut rule_vars);

        let mut goal_vars = HashSet::new();
        for hyp in goal.hyps() {
            collect_var_keys(hyp.term(), &mut goal_vars);
        }
        collect_var_keys(goal.prop().term(), &mut goal_vars);

        for (name, index) in &rule_vars {
            if goal_vars.contains(&(name.clone(), *index)) {
                return Err(KernelError::RequiresLifting {
                    rule_var: name.clone(),
                    goal_var: name.clone(),
                });
            }
        }
        Ok(())
    }
}

fn validate_generalize_hypotheses(
    theorem: &KernelThm,
    type_names: &BTreeSet<Name>,
    term_names: &BTreeSet<Name>,
) -> Result<(), KernelError> {
    for hyp in theorem.hyps() {
        if hyp.term().has_schematic_hypothesis() {
            return Err(KernelError::SchematicHypothesis);
        }
        let mut names = HashSet::new();
        collect_free_names(hyp.term(), &mut names);
        if let Some(name) = names.iter().filter(|name| term_names.contains(*name)).min() {
            return Err(KernelError::FreeVarInHypotheses { name: name.clone() });
        }
        let mut selected = BTreeSet::new();
        hyp.term().for_each_type_annotation(&mut |ty| {
            ty.for_each_type_free(&mut |name, _| {
                if type_names.contains(name) {
                    selected.insert(name.clone());
                }
            });
        });
        if let Some(name) = selected.into_iter().next() {
            return Err(KernelError::TypeFreeInHypotheses { name });
        }
    }
    Ok(())
}

/// Check the binder's typed application and lower only indices outside that binder.
pub(crate) fn contract_eta(redex: &Term) -> Result<Term, KernelError> {
    let (_, param_ty, body) =
        redex.dest_abs().ok_or_else(|| KernelError::EtaRedexExpected(redex.ty()))?;
    let (function, argument) =
        body.dest_app().ok_or_else(|| KernelError::EtaRedexExpected(redex.ty()))?;
    if !matches!(argument, Term::Bound { index: 0, ty } if ty == param_ty)
        || mentions_eta_binder(function, 0)
    {
        return Err(KernelError::EtaRedexExpected(redex.ty()));
    }
    let function_type = function.ty();
    let (domain, range) = function_type
        .dest_arrow()
        .ok_or_else(|| KernelError::NotFunctionType(function_type.clone()))?;
    if domain != param_ty {
        return Err(KernelError::TypeMismatch {
            expected: param_ty.clone(),
            actual: domain.clone(),
        });
    }
    if body.ty() != *range || redex.ty() != function_type {
        return Err(KernelError::TypeMismatch { expected: range.clone(), actual: body.ty() });
    }
    Ok(Term::instantiate_bound0(function, argument))
}

fn mentions_eta_binder(term: &Term, depth: usize) -> bool {
    match term {
        Term::Bound { index, .. } => *index == depth,
        Term::Abs { body, .. } | Term::Forall { body, .. } => mentions_eta_binder(body, depth + 1),
        Term::App { func, arg, .. }
        | Term::Eq { lhs: func, rhs: arg, .. }
        | Term::Imp { premise: func, conclusion: arg } => {
            mentions_eta_binder(func, depth) || mentions_eta_binder(arg, depth)
        },
        _ => false,
    }
}

/// Collect free variable names from a `Term`.
fn collect_free_names(term: &Term, names: &mut HashSet<Name>) {
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        match t {
            Term::Free { name, .. } => {
                names.insert(name.clone());
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
            Term::Const { .. } | Term::Var { .. } | Term::Bound { .. } => {},
        }
    }
}

/// Collect schematic variable `(name, index)` pairs from a `Term`.
fn collect_var_keys(term: &Term, vars: &mut HashSet<(Name, usize)>) {
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        match t {
            Term::Var { name, index, .. } => {
                vars.insert((name.clone(), *index));
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
            Term::Const { .. } | Term::Free { .. } | Term::Bound { .. } => {},
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::{KernelError, Name, ProofContext, Signature, Term, TheorySnapshot, Ty};
    use super::*;

    fn ty(name: &str) -> Ty {
        Ty::base(name).unwrap()
    }

    fn ctx_with_props(names: &[&str]) -> ProofContext {
        let mut sig = Signature::new();
        for name in names {
            sig = sig.extend_const(*name, Ty::prop()).unwrap();
        }
        ProofContext::new(TheorySnapshot::root("Test", sig))
    }

    fn prop_term(ctx: &ProofContext, name: &str) -> Term {
        use super::super::RawTerm;
        ctx.certify_prop(RawTerm::const_(name, Ty::prop())).unwrap().term().clone()
    }

    #[test]
    fn match_terms_certified_basic_var() {
        let ctx = ctx_with_props(&["A"]);
        let a_term = prop_term(&ctx, "A");
        let pattern = Term::Var { name: Name::from("P"), index: 0, ty: Ty::prop() };
        let entries = KernelRules::match_terms_certified(&pattern, &a_term, ctx.stamp()).unwrap();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].name().as_str(), "P");
        assert_eq!(entries[0].index(), 0);
        assert_eq!(entries[0].replacement().term(), &a_term);
    }

    #[test]
    fn match_terms_certified_repeated_var_consistent() {
        let ctx = ctx_with_props(&["A"]);
        let a = prop_term(&ctx, "A");
        let var_p = Term::Var { name: Name::from("P"), index: 0, ty: Ty::prop() };
        let pattern = Term::Imp { premise: Box::new(var_p.clone()), conclusion: Box::new(var_p) };
        let target = Term::Imp { premise: Box::new(a.clone()), conclusion: Box::new(a.clone()) };
        let entries = KernelRules::match_terms_certified(&pattern, &target, ctx.stamp()).unwrap();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].replacement().term(), &a);
    }

    #[test]
    fn match_terms_certified_repeated_var_inconsistent() {
        let ctx = ctx_with_props(&["A", "B"]);
        let a = prop_term(&ctx, "A");
        let b = prop_term(&ctx, "B");
        let var_p = Term::Var { name: Name::from("P"), index: 0, ty: Ty::prop() };
        let pattern = Term::Imp { premise: Box::new(var_p.clone()), conclusion: Box::new(var_p) };
        let target = Term::Imp { premise: Box::new(a), conclusion: Box::new(b) };
        let err = KernelRules::match_terms_certified(&pattern, &target, ctx.stamp()).unwrap_err();
        assert!(format!("{err}").contains("inconsistent"));
    }

    #[test]
    fn match_terms_certified_type_mismatch() {
        let mut sig = Signature::new();
        sig = sig.extend_type_constructor("nat", 0).unwrap();
        sig = sig.extend_const("a", ty("nat")).unwrap();
        let ctx = ProofContext::new(TheorySnapshot::root("Test", sig));
        let a_nat = ctx.certify_term(super::super::RawTerm::const_("a", ty("nat"))).unwrap();
        let pattern = Term::Var { name: Name::from("P"), index: 0, ty: Ty::prop() };
        let err =
            KernelRules::match_terms_certified(&pattern, a_nat.term(), ctx.stamp()).unwrap_err();
        assert!(format!("{err}").contains("type mismatch"));
    }

    #[test]
    fn match_terms_certified_const_mismatch() {
        let ctx = ctx_with_props(&["A", "B"]);
        let a = prop_term(&ctx, "A");
        let b = prop_term(&ctx, "B");
        let err = KernelRules::match_terms_certified(&a, &b, ctx.stamp()).unwrap_err();
        assert!(format!("{err}").contains("Const mismatch"));
    }

    #[test]
    fn match_terms_certified_nested_app() {
        let mut sig = Signature::new();
        sig = sig.extend_type_constructor("nat", 0).unwrap();
        sig = sig.extend_const("f", Ty::arrow(ty("nat"), Ty::prop())).unwrap();
        sig = sig.extend_const("a", ty("nat")).unwrap();
        let ctx = ProofContext::new(TheorySnapshot::root("Test", sig));
        let f_cterm = ctx
            .certify_term(super::super::RawTerm::const_("f", Ty::arrow(ty("nat"), Ty::prop())))
            .unwrap();
        let a_cterm = ctx.certify_term(super::super::RawTerm::const_("a", ty("nat"))).unwrap();
        let target = Term::App {
            func: Box::new(f_cterm.term().clone()),
            arg: Box::new(a_cterm.term().clone()),
            ty: Ty::prop(),
        };
        let p_var =
            Term::Var { name: Name::from("P"), index: 0, ty: Ty::arrow(ty("nat"), Ty::prop()) };
        let x_var = Term::Var { name: Name::from("x"), index: 0, ty: ty("nat") };
        let pattern = Term::App { func: Box::new(p_var), arg: Box::new(x_var), ty: Ty::prop() };
        let entries = KernelRules::match_terms_certified(&pattern, &target, ctx.stamp()).unwrap();
        assert_eq!(entries.len(), 2);
        let p_entry = entries.iter().find(|e| e.name().as_str() == "P").unwrap();
        assert_eq!(p_entry.replacement().term(), f_cterm.term());
        let x_entry = entries.iter().find(|e| e.name().as_str() == "x").unwrap();
        assert_eq!(x_entry.replacement().term(), a_cterm.term());
    }

    #[test]
    fn match_terms_certified_rejects_bound() {
        let ctx = ctx_with_props(&[]);
        let pattern = Term::Var { name: Name::from("P"), index: 0, ty: Ty::prop() };
        let target = Term::Bound { index: 0, ty: Ty::prop() };
        let err = KernelRules::match_terms_certified(&pattern, &target, ctx.stamp()).unwrap_err();
        assert!(format!("{err}").contains("Bound"));
    }

    #[test]
    fn match_terms_certified_no_vars_empty() {
        let ctx = ctx_with_props(&["A"]);
        let a = prop_term(&ctx, "A");
        let entries = KernelRules::match_terms_certified(&a, &a, ctx.stamp()).unwrap();
        assert!(entries.is_empty());
    }

    #[test]
    fn match_terms_certified_multiple_distinct_vars() {
        let ctx = ctx_with_props(&["A", "B"]);
        let a = prop_term(&ctx, "A");
        let b = prop_term(&ctx, "B");
        let p_var = Term::Var { name: Name::from("P"), index: 0, ty: Ty::prop() };
        let q_var = Term::Var { name: Name::from("Q"), index: 1, ty: Ty::prop() };
        let pattern = Term::Imp { premise: Box::new(p_var), conclusion: Box::new(q_var) };
        let target = Term::Imp { premise: Box::new(a.clone()), conclusion: Box::new(b.clone()) };
        let entries = KernelRules::match_terms_certified(&pattern, &target, ctx.stamp()).unwrap();
        assert_eq!(entries.len(), 2);
        let pb = entries.iter().find(|e| e.name().as_str() == "P").unwrap();
        assert_eq!(pb.replacement().term(), &a);
        let qb = entries.iter().find(|e| e.name().as_str() == "Q").unwrap();
        assert_eq!(qb.replacement().term(), &b);
    }

    #[test]
    fn match_terms_certified_multiple_distinct_vars_are_sorted() {
        let ctx = ctx_with_props(&["A", "B"]);
        let a = prop_term(&ctx, "A");
        let b = prop_term(&ctx, "B");
        let q_var = Term::Var { name: Name::from("Q"), index: 1, ty: Ty::prop() };
        let p_var = Term::Var { name: Name::from("P"), index: 0, ty: Ty::prop() };
        let pattern = Term::Imp { premise: Box::new(q_var), conclusion: Box::new(p_var) };
        let target = Term::Imp { premise: Box::new(b), conclusion: Box::new(a) };

        let entries = KernelRules::match_terms_certified(&pattern, &target, ctx.stamp()).unwrap();
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].name().as_str(), "P");
        assert_eq!(entries[0].index(), 0);
        assert_eq!(entries[1].name().as_str(), "Q");
        assert_eq!(entries[1].index(), 1);
    }

    // ── resolution-family test helpers ──

    fn imp_chain(ctx: &ProofContext, names: &[&str]) -> Term {
        assert!(!names.is_empty());
        let mut terms: Vec<Term> = names.iter().map(|n| prop_term(ctx, n)).collect();
        let conclusion = terms.pop().unwrap();
        let mut current = conclusion;
        for prem in terms.into_iter().rev() {
            current = Term::Imp { premise: Box::new(prem), conclusion: Box::new(current) };
        }
        current
    }

    fn certify_prop_term(ctx: &ProofContext, term: &Term) -> CProp {
        CProp::from_checked_term(term.clone(), ctx.stamp())
    }

    #[test]
    fn implies_intr_unused_assumption_preserves_closed_proof() {
        let ctx = ctx_with_props(&["A", "B"]);
        let reflexive = KernelRules::reflexive(
            ctx.certify_term(super::super::RawTerm::const_("A", Ty::prop())).unwrap(),
        );
        let assumption = ctx.certify_prop(super::super::RawTerm::const_("B", Ty::prop())).unwrap();
        let introduced = KernelRules::implies_intr(&assumption, reflexive.as_kernel()).unwrap();
        assert!(introduced.hyps().is_empty());
        let (antecedent, consequent) = introduced.prop().term().dest_imp().unwrap();
        assert!(antecedent.alpha_eq(assumption.term()));
        assert!(consequent.alpha_eq(reflexive.as_kernel().prop().term()));
        super::super::invariant::check_kernel_thm(&introduced).unwrap();
    }

    /// Create a theorem `[P] |- P` via assume. The conclusion is P (no imp chain).
    fn assume_thm(ctx: &ProofContext, name: &str) -> KernelThm {
        let cprop = certify_prop_term(ctx, &prop_term(ctx, name));
        KernelRules::assume(cprop).unwrap().into_kernel()
    }

    fn assumed_eq(ctx: &ProofContext, lhs: &str, rhs: &str) -> KernelThm {
        let eq = Term::mk_eq(prop_term(ctx, lhs), prop_term(ctx, rhs)).unwrap();
        KernelRules::assume(certify_prop_term(ctx, &eq)).unwrap().into_kernel()
    }

    fn assumed_goal(ctx: &ProofContext, names: &[&str]) -> KernelThm {
        KernelRules::assume(certify_prop_term(ctx, &imp_chain(ctx, names))).unwrap().into_kernel()
    }

    fn resolution_ctx(names: &[&str]) -> ProofContext {
        let mut ctx = ctx_with_props(names);
        for name in ["P", "Q", "G"] {
            ctx.declare_free(name, Ty::prop());
        }
        ctx
    }

    fn schematic_identity_rule(ctx: &ProofContext) -> KernelThm {
        let p = ctx.certify_prop(super::super::RawTerm::free("P", Ty::prop())).unwrap();
        let assumed = KernelRules::assume(p.clone()).unwrap();
        let discharged = KernelRules::implies_intr(&p, assumed.as_kernel()).unwrap();
        KernelRules::generalize(&discharged, &BTreeSet::new(), &BTreeSet::from(["P".into()]), 0)
            .unwrap()
    }

    fn schematic_eq_rule(ctx: &ProofContext) -> KernelThm {
        let p = ctx.certify_prop(super::super::RawTerm::free("P", Ty::prop())).unwrap();
        let q = ctx.certify_prop(super::super::RawTerm::free("Q", Ty::prop())).unwrap();
        let eq = certify_prop_term(ctx, &Term::mk_eq(p.term().clone(), q.term().clone()).unwrap());
        let assumed = KernelRules::assume(eq.clone()).unwrap();
        let discharged_eq = KernelRules::implies_intr(&eq, assumed.as_kernel()).unwrap();
        let discharged_p = KernelRules::implies_intr(&p, &discharged_eq).unwrap();
        KernelRules::generalize(
            &discharged_p,
            &BTreeSet::new(),
            &BTreeSet::from(["P".into(), "Q".into()]),
            0,
        )
        .unwrap()
    }

    fn schematic_reflexive_rule(ctx: &ProofContext) -> KernelThm {
        let variable = ctx.certify_term(super::super::RawTerm::var("P", 0, Ty::prop())).unwrap();
        KernelRules::reflexive(variable).into_kernel()
    }

    fn goal_with_schematic_premise(
        ctx: &ProofContext,
        name: &str,
        index: usize,
        remaining: &[&str],
    ) -> KernelThm {
        let conclusion = remaining.last().unwrap();
        let mut goal = assume_thm(ctx, conclusion);
        for premise in remaining[..remaining.len() - 1].iter().rev() {
            goal =
                KernelRules::implies_intr(&certify_prop_term(ctx, &prop_term(ctx, premise)), &goal)
                    .unwrap();
        }
        let free = ctx.certify_term(super::super::RawTerm::free("G", Ty::prop())).unwrap();
        goal = KernelRules::implies_intr(&certify_prop_term(ctx, free.term()), &goal).unwrap();
        let quantified = KernelRules::forall_intr(&free, &goal).unwrap();
        let var = ctx.certify_term(super::super::RawTerm::var(name, index, Ty::prop())).unwrap();
        KernelRules::forall_elim(&quantified, &var).unwrap()
    }

    fn rule_with_rigid_hypothesis(ctx: &ProofContext) -> KernelThm {
        let h = certify_prop_term(ctx, &prop_term(ctx, "H"));
        let conditional = KernelRules::implies_intr(&h, &schematic_reflexive_rule(ctx)).unwrap();
        let assumed = KernelRules::assume(h).unwrap();
        KernelRules::implies_elim(&conditional, assumed.as_kernel()).unwrap()
    }

    // ── subst_premise tests ──

    #[test]
    fn subst_premise_basic() {
        let ctx = ctx_with_props(&["A", "B", "R"]);
        let eq = assumed_eq(&ctx, "A", "B");
        let goal = assumed_goal(&ctx, &["A", "R"]);

        let result = KernelRules::subst_premise(&eq, &goal, 0).unwrap();

        let expected = imp_chain(&ctx, &["B", "R"]);
        assert_eq!(result.prop(), &certify_prop_term(&ctx, &expected));
    }

    #[test]
    fn subst_premise_rejects_object_equality() {
        let mut sig = Signature::new();
        sig = sig.extend_type_constructor("nat", 0).unwrap();
        sig = sig.extend_const("x", ty("nat")).unwrap();
        sig = sig.extend_const("y", ty("nat")).unwrap();
        sig = sig.extend_const("A", Ty::prop()).unwrap();
        sig = sig.extend_const("R", Ty::prop()).unwrap();
        let ctx = ProofContext::new(TheorySnapshot::root("Test", sig));

        let x =
            ctx.certify_term(super::super::RawTerm::const_("x", ty("nat"))).unwrap().term().clone();
        let y =
            ctx.certify_term(super::super::RawTerm::const_("y", ty("nat"))).unwrap().term().clone();
        let object_eq = Term::mk_eq(x, y).unwrap();
        let eq = KernelRules::assume(certify_prop_term(&ctx, &object_eq)).unwrap().into_kernel();
        let goal = assumed_goal(&ctx, &["A", "R"]);

        let err = KernelRules::subst_premise(&eq, &goal, 0).unwrap_err();
        assert!(matches!(err, KernelError::NotProposition(_)));
    }

    #[test]
    fn subst_premise_rejects_out_of_range() {
        let ctx = ctx_with_props(&["A", "B", "R"]);
        let eq = assumed_eq(&ctx, "A", "B");
        let goal = assumed_goal(&ctx, &["A", "R"]);

        let err = KernelRules::subst_premise(&eq, &goal, 1).unwrap_err();
        assert!(matches!(err, KernelError::SubgoalIndexOutOfRange { index: 1, nprems: 1 }));
    }

    #[test]
    fn subst_premise_rejects_mismatch() {
        let ctx = ctx_with_props(&["A", "B", "C", "R"]);
        let eq = assumed_eq(&ctx, "A", "B");
        let goal = assumed_goal(&ctx, &["C", "R"]);

        let err = KernelRules::subst_premise(&eq, &goal, 0).unwrap_err();
        assert!(matches!(err, KernelError::AntecedentMismatch));
    }

    #[test]
    fn subst_premise_rejects_symmetric_direction() {
        let ctx = ctx_with_props(&["A", "B", "R"]);
        let eq = assumed_eq(&ctx, "A", "B");
        let goal = assumed_goal(&ctx, &["B", "R"]);

        let err = KernelRules::subst_premise(&eq, &goal, 0).unwrap_err();
        assert!(matches!(err, KernelError::AntecedentMismatch));
    }

    #[test]
    fn subst_premise_selected_index_is_goal_subgoal() {
        let ctx = ctx_with_props(&["A", "C", "D", "R"]);
        let eq = assumed_eq(&ctx, "C", "D");
        let goal = assumed_goal(&ctx, &["A", "C", "R"]);

        let wrong_index = KernelRules::subst_premise(&eq, &goal, 0).unwrap_err();
        assert!(matches!(wrong_index, KernelError::AntecedentMismatch));

        let result = KernelRules::subst_premise(&eq, &goal, 1).unwrap();
        let expected = imp_chain(&ctx, &["A", "D", "R"]);
        assert_eq!(result.prop(), &certify_prop_term(&ctx, &expected));
    }

    #[test]
    fn subst_premise_preserves_other_subgoals() {
        let ctx = ctx_with_props(&["H", "A", "B", "C", "R"]);
        let eq = assumed_eq(&ctx, "A", "B");
        let goal = assumed_goal(&ctx, &["H", "A", "C", "R"]);

        let result = KernelRules::subst_premise(&eq, &goal, 1).unwrap();

        let expected = imp_chain(&ctx, &["H", "B", "C", "R"]);
        assert_eq!(result.prop(), &certify_prop_term(&ctx, &expected));
    }

    #[test]
    fn subst_premise_preserves_hypotheses() {
        let ctx = ctx_with_props(&["H", "A", "B", "R"]);
        let eq = assumed_eq(&ctx, "A", "B");
        let goal = assumed_goal(&ctx, &["H", "A", "R"]);

        let result = KernelRules::subst_premise(&eq, &goal, 1).unwrap();

        assert_eq!(result.hyps().len(), 2);
        assert!(result.hyps().iter().any(|h| h.term().alpha_eq(eq.prop().term())));
        assert!(result.hyps().iter().any(|h| h.term().alpha_eq(goal.prop().term())));
    }

    #[test]
    fn subst_premise_invariant_check_passes() {
        let ctx = ctx_with_props(&["H", "A", "B", "R"]);
        let eq = assumed_eq(&ctx, "A", "B");
        let goal = assumed_goal(&ctx, &["H", "A", "R"]);

        let result = KernelRules::subst_premise(&eq, &goal, 1).unwrap();

        super::super::invariant::check_kernel_thm(&result).unwrap();
    }

    #[test]
    fn subst_premise_tampered_result_rejected() {
        use super::super::thm::prop_from_term;

        let ctx = ctx_with_props(&["A", "B", "R", "WRONG"]);
        let eq = assumed_eq(&ctx, "A", "B");
        let goal = assumed_goal(&ctx, &["A", "R"]);
        let result = KernelRules::subst_premise(&eq, &goal, 0).unwrap();

        let tampered_prop = prop_from_term(imp_chain(&ctx, &["B", "WRONG"]), ctx.stamp());
        let tampered =
            KernelThm::new(result.hyps().to_vec(), tampered_prop, result.derivation().clone());

        let check = super::super::invariant::check_kernel_thm(&tampered);
        assert!(check.is_err(), "tampered theorem should fail invariant check");
    }

    // ── resolve1_match tests ──

    #[test]
    fn resolve1_basic_no_vars() {
        // Rule: [A] |- A  (conclusion A, 0 premises)
        // Goal: [A ==> B] |- A ==> B  (subgoal 0 = A, conclusion B)
        // Match: A matches A (no Vars)
        // Result: hyps union, subgoal A removed, result prop = B
        let ctx = ctx_with_props(&["A", "B"]);
        let rule = assume_thm(&ctx, "A"); // [A] |- A

        let goal_imp = imp_chain(&ctx, &["A", "B"]);
        let goal_prop = certify_prop_term(&ctx, &goal_imp);
        let goal = KernelRules::assume(goal_prop).unwrap().into_kernel(); // [A==>B] |- A==>B

        let result = KernelRules::resolve1_match(&rule, &goal, 0).unwrap();
        // Rule concl A matches subgoal A; rule has 0 premises → subgoal removed
        assert_eq!(result.prop(), &certify_prop_term(&ctx, &prop_term(&ctx, "B")));
        // hyps: [A] ∪ [A==>B] → 2 (alpha-inequivalent: A ≠ A==>B)
        assert_eq!(result.hyps().len(), 2);
    }

    #[test]
    fn resolve1_basic_with_match() {
        let ctx = ctx_with_props(&["A", "B"]);
        let rule = schematic_reflexive_rule(&ctx);
        let eq = Term::mk_eq(prop_term(&ctx, "A"), prop_term(&ctx, "A")).unwrap();
        let goal_term = Term::mk_imp(eq, prop_term(&ctx, "B")).unwrap();
        let goal = KernelRules::assume(certify_prop_term(&ctx, &goal_term)).unwrap();

        let result = KernelRules::resolve1_match(&rule, goal.as_kernel(), 0).unwrap();
        assert_eq!(result.prop(), &certify_prop_term(&ctx, &prop_term(&ctx, "B")));
        assert_eq!(result.hyps(), goal.as_kernel().hyps());
        super::super::invariant::check_kernel_thm(&result).unwrap();
    }

    #[test]
    fn resolve1_rejects_match_failure() {
        // Rule conclusion A does not match selected goal subgoal B.
        let ctx = ctx_with_props(&["A", "B", "R"]);
        let rule = assume_thm(&ctx, "A");

        let goal_imp = imp_chain(&ctx, &["B", "R"]);
        let goal = KernelRules::assume(certify_prop_term(&ctx, &goal_imp)).unwrap().into_kernel();

        let err = KernelRules::resolve1_match(&rule, &goal, 0).unwrap_err();
        assert!(matches!(err, KernelError::Invariant(_)), "expected match failure, got {err:?}");
    }

    #[test]
    fn resolve1_empty_rule_premises_tamper_kept_subgoal_rejected() {
        let ctx = ctx_with_props(&["A", "B"]);
        let rule = schematic_reflexive_rule(&ctx);
        let eq = Term::mk_eq(prop_term(&ctx, "A"), prop_term(&ctx, "A")).unwrap();
        let goal_term = Term::mk_imp(eq, prop_term(&ctx, "B")).unwrap();
        let goal = KernelRules::assume(certify_prop_term(&ctx, &goal_term)).unwrap();
        let result = KernelRules::resolve1_match(&rule, goal.as_kernel(), 0).unwrap();
        assert_eq!(result.prop(), &certify_prop_term(&ctx, &prop_term(&ctx, "B")));

        let tampered = KernelThm::new(
            result.hyps().to_vec(),
            certify_prop_term(&ctx, &goal_term),
            result.derivation().clone(),
        );
        assert!(super::super::invariant::check_kernel_thm(&tampered).is_err());
    }

    #[test]
    fn resolve1_applies_substitution_to_rule_premises() {
        let ctx = resolution_ctx(&["H", "A", "B", "R"]);
        let rule = schematic_eq_rule(&ctx);
        let eq = Term::mk_eq(prop_term(&ctx, "A"), prop_term(&ctx, "B")).unwrap();
        let goal_term =
            Term::mk_imp_chain(&[prop_term(&ctx, "H"), eq.clone()], &prop_term(&ctx, "R")).unwrap();
        let goal = KernelRules::assume(certify_prop_term(&ctx, &goal_term)).unwrap();

        let result = KernelRules::resolve1_match(&rule, goal.as_kernel(), 1).unwrap();
        let expected = Term::mk_imp_chain(
            &[prop_term(&ctx, "H"), prop_term(&ctx, "A"), eq],
            &prop_term(&ctx, "R"),
        )
        .unwrap();
        assert_eq!(result.prop(), &certify_prop_term(&ctx, &expected));
        super::super::invariant::check_kernel_thm(&result).unwrap();
    }

    #[test]
    fn resolve1_rejects_goal_var_namespace_collision_without_lifting() {
        let ctx = resolution_ctx(&["A", "R"]);
        let rule = schematic_identity_rule(&ctx);
        let goal = goal_with_schematic_premise(&ctx, "P", 0, &["A", "R"]);

        let err = KernelRules::resolve1_match(&rule, &goal, 1).unwrap_err();
        assert!(matches!(err, KernelError::RequiresLifting { .. }), "got {err:?}");
        super::super::invariant::check_kernel_thm(&goal).unwrap();
    }

    #[test]
    fn resolve1_preserves_rigid_hypotheses_after_matching() {
        let ctx = ctx_with_props(&["H", "A", "R"]);
        let rule = rule_with_rigid_hypothesis(&ctx);
        let eq = Term::mk_eq(prop_term(&ctx, "A"), prop_term(&ctx, "A")).unwrap();
        let goal = KernelRules::assume(certify_prop_term(
            &ctx,
            &Term::mk_imp(eq, prop_term(&ctx, "R")).unwrap(),
        ))
        .unwrap();
        let result = KernelRules::resolve1_match(&rule, goal.as_kernel(), 0).unwrap();

        assert_eq!(result.prop(), &certify_prop_term(&ctx, &prop_term(&ctx, "R")));
        assert!(result.hyps().contains(&certify_prop_term(&ctx, &prop_term(&ctx, "H"))));
        assert!(result.hyps().contains(goal.as_kernel().prop()));
        assert!(result.hyps().iter().all(|hyp| !hyp.term().has_schematic_hypothesis()));
        super::super::invariant::check_kernel_thm(&result).unwrap();
    }

    #[test]
    fn resolve1_selected_index_is_goal_subgoal_not_rule_premise() {
        // Rule: [A ==> C] |- A ==> C  (rule premise index 0 is A, conclusion C)
        // Goal: [B ==> C ==> R] |- B ==> C ==> R
        //
        // selected_subgoal_index indexes the GOAL chain. Index 0 selects B and
        // must fail; index 1 selects C and succeeds.
        let ctx = ctx_with_props(&["A", "B", "C", "R"]);
        let rule_term = imp_chain(&ctx, &["A", "C"]);
        let rule = KernelRules::assume(certify_prop_term(&ctx, &rule_term)).unwrap().into_kernel();

        let goal_term = imp_chain(&ctx, &["B", "C", "R"]);
        let goal = KernelRules::assume(certify_prop_term(&ctx, &goal_term)).unwrap().into_kernel();

        let wrong_index = KernelRules::resolve1_match(&rule, &goal, 0).unwrap_err();
        assert!(
            matches!(wrong_index, KernelError::Invariant(_)),
            "index 0 should select goal subgoal B and fail, got {wrong_index:?}"
        );

        let result = KernelRules::resolve1_match(&rule, &goal, 1).unwrap();
        let expected = imp_chain(&ctx, &["B", "A", "R"]);
        assert_eq!(result.prop(), &certify_prop_term(&ctx, &expected));
    }

    #[test]
    fn resolve1_replaces_selected_subgoal() {
        // Rule: [B ==> C] |- B ==> C  (conclusion C, premises [B])
        // Goal: [A ==> C ==> R] |- A ==> C ==> R  (subgoals [A, C], conclusion R)
        // Select subgoal 1 = C
        // Match: C matches C ✅
        // Result: A ==> B ==> R
        let ctx = ctx_with_props(&["A", "B", "C", "R"]);
        let rule_imp = imp_chain(&ctx, &["B", "C"]);
        let rule_prop = certify_prop_term(&ctx, &rule_imp);
        let rule = KernelRules::assume(rule_prop).unwrap().into_kernel();

        let goal_imp = imp_chain(&ctx, &["A", "C", "R"]);
        let goal_prop = certify_prop_term(&ctx, &goal_imp);
        let goal = KernelRules::assume(goal_prop).unwrap().into_kernel();

        let result = KernelRules::resolve1_match(&rule, &goal, 1).unwrap();
        let expected_imp = imp_chain(&ctx, &["A", "B", "R"]);
        assert_eq!(result.prop(), &certify_prop_term(&ctx, &expected_imp));
    }

    #[test]
    fn resolve1_preserves_other_subgoals() {
        // Rule: [B] |- B  (conclusion B, 0 premises)
        // Goal: [A ==> B ==> R] |- A ==> B ==> R
        // Select subgoal 1 = B
        // Result: A ==> R (subgoal B removed, A and R preserved)
        let ctx = ctx_with_props(&["A", "B", "R"]);
        let rule = assume_thm(&ctx, "B");

        let goal_imp = imp_chain(&ctx, &["A", "B", "R"]);
        let goal_prop = certify_prop_term(&ctx, &goal_imp);
        let goal = KernelRules::assume(goal_prop).unwrap().into_kernel();

        let result = KernelRules::resolve1_match(&rule, &goal, 1).unwrap();
        let expected_imp = imp_chain(&ctx, &["A", "R"]);
        assert_eq!(result.prop(), &certify_prop_term(&ctx, &expected_imp));
    }

    #[test]
    fn resolve1_rejects_out_of_range() {
        let ctx = ctx_with_props(&["A", "B"]);
        let rule = assume_thm(&ctx, "B");
        let goal_imp = imp_chain(&ctx, &["A", "B"]);
        let goal_prop = certify_prop_term(&ctx, &goal_imp);
        let goal = KernelRules::assume(goal_prop).unwrap().into_kernel();

        // Goal has 1 subgoal (A), index 1 ≥ nprems → out of range.
        let err = KernelRules::resolve1_match(&rule, &goal, 1).unwrap_err();
        assert!(format!("{err}").contains("out of range"));
    }

    #[test]
    fn resolve1_rejects_empty_goal_subgoals() {
        let ctx = ctx_with_props(&["R"]);
        let rule = assume_thm(&ctx, "R");
        let r_prop = certify_prop_term(&ctx, &prop_term(&ctx, "R"));
        let goal = KernelRules::assume(r_prop).unwrap().into_kernel();

        let err = KernelRules::resolve1_match(&rule, &goal, 0).unwrap_err();
        assert!(format!("{err}").contains("out of range"));
    }

    #[test]
    fn resolve1_rejects_variable_collision_without_lifting() {
        let mut sig = Signature::new();
        sig = sig.extend_type_constructor("nat", 0).unwrap();
        sig = sig.extend_const("R", Ty::prop()).unwrap();
        let mut ctx = ProofContext::new(TheorySnapshot::root("Test", sig));
        ctx.declare_free("x", ty("nat"));

        let x_cterm = ctx.certify_term(super::super::RawTerm::free("x", ty("nat"))).unwrap();
        let x_term = x_cterm.term().clone();

        // Rule: reflexive(x) → |- x == x (contains Free "x")
        let rule = KernelRules::reflexive(x_cterm).into_kernel();

        // Build x == x term
        let eq_term = super::super::Term::mk_eq(x_term.clone(), x_term).unwrap();

        // Goal: assume((x == x) ==> R) → 1 subgoal = (x == x)
        let r_term = prop_term(&ctx, "R");
        let goal_imp = Term::Imp { premise: Box::new(eq_term), conclusion: Box::new(r_term) };
        let goal_prop = certify_prop_term(&ctx, &goal_imp);
        let goal = KernelRules::assume(goal_prop).unwrap().into_kernel();

        // Rule conclusion (x == x) matches subgoal 0 (x == x) → OK
        // But both rule and goal contain Free("x") → RequiresLifting
        let err = KernelRules::resolve1_match(&rule, &goal, 0).unwrap_err();
        assert!(format!("{err}").contains("lifting"), "expected RequiresLifting, got: {err}");
    }

    #[test]
    fn resolve1_invariant_check_passes() {
        let ctx = ctx_with_props(&["A", "B", "C", "R"]);
        // Rule: [B ==> C] |- B ==> C
        let rule_imp = imp_chain(&ctx, &["B", "C"]);
        let rule_prop = certify_prop_term(&ctx, &rule_imp);
        let rule = KernelRules::assume(rule_prop).unwrap().into_kernel();

        // Goal: [A ==> C ==> R] |- A ==> C ==> R  (2 subgoals: A, C)
        let goal_imp = imp_chain(&ctx, &["A", "C", "R"]);
        let goal_prop = certify_prop_term(&ctx, &goal_imp);
        let goal = KernelRules::assume(goal_prop).unwrap().into_kernel();

        let result = KernelRules::resolve1_match(&rule, &goal, 1).unwrap();
        super::super::invariant::check_kernel_thm(&result).unwrap();
    }

    #[test]
    fn resolve1_invariant_with_multiple_bindings_is_deterministic() {
        let ctx = resolution_ctx(&["A", "B", "R"]);
        let rule = schematic_eq_rule(&ctx);
        let eq = Term::mk_eq(prop_term(&ctx, "A"), prop_term(&ctx, "B")).unwrap();
        let goal_term = Term::mk_imp(eq.clone(), prop_term(&ctx, "R")).unwrap();
        let goal = KernelRules::assume(certify_prop_term(&ctx, &goal_term)).unwrap();
        let result = KernelRules::resolve1_match(&rule, goal.as_kernel(), 0).unwrap();
        let expected =
            Term::mk_imp_chain(&[prop_term(&ctx, "A"), eq], &prop_term(&ctx, "R")).unwrap();
        assert_eq!(result.prop(), &certify_prop_term(&ctx, &expected));
        super::super::invariant::check_kernel_thm(&result).unwrap();

        let Derivation::Resolve1Match { rule, goal_state, selected_subgoal_index, mut subst } =
            result.derivation().clone()
        else {
            panic!("resolution must record matching bindings");
        };
        assert_eq!(subst.len(), 2);
        subst.reverse();
        let tampered = KernelThm::new(
            result.hyps().to_vec(),
            result.prop().clone(),
            Derivation::Resolve1Match { rule, goal_state, selected_subgoal_index, subst },
        );
        assert!(super::super::invariant::check_kernel_thm(&tampered).is_err());
    }

    #[test]
    fn resolve1_tampered_result_rejected() {
        use super::super::thm::prop_from_term;

        let ctx = ctx_with_props(&["A", "B", "C", "R", "WRONG"]);
        let rule_imp = imp_chain(&ctx, &["B", "C"]);
        let rule_prop = certify_prop_term(&ctx, &rule_imp);
        let rule = KernelRules::assume(rule_prop).unwrap().into_kernel();

        let goal_imp = imp_chain(&ctx, &["A", "C", "R"]);
        let goal_prop = certify_prop_term(&ctx, &goal_imp);
        let goal = KernelRules::assume(goal_prop).unwrap().into_kernel();

        let result = KernelRules::resolve1_match(&rule, &goal, 1).unwrap();

        // Tamper with the proposition and re-wrap.
        let tampered_prop = prop_from_term(imp_chain(&ctx, &["A", "B", "WRONG"]), ctx.stamp());
        let tampered =
            KernelThm::new(result.hyps().to_vec(), tampered_prop, result.derivation().clone());
        let check = super::super::invariant::check_kernel_thm(&tampered);
        assert!(check.is_err(), "tampered theorem should fail invariant check");
    }

    #[test]
    fn resolve1_preserves_hypotheses() {
        // Rule: [B ==> A] |- B ==> A  (premises [B], conclusion A)
        // Goal: [H ==> A ==> R] |- H ==> A ==> R  (subgoals [H, A])
        // Select subgoal 1 = A
        // Match: rule concl A matches subgoal A ✅
        // Result: H ==> B ==> R
        let ctx = ctx_with_props(&["H", "A", "B", "R"]);
        let rule_imp = imp_chain(&ctx, &["B", "A"]);
        let rule_prop = certify_prop_term(&ctx, &rule_imp);
        let rule = KernelRules::assume(rule_prop).unwrap().into_kernel();

        let goal_imp = imp_chain(&ctx, &["H", "A", "R"]);
        let goal_prop = certify_prop_term(&ctx, &goal_imp);
        let goal = KernelRules::assume(goal_prop).unwrap().into_kernel();

        let result = KernelRules::resolve1_match(&rule, &goal, 1).unwrap();
        // Rule hyps: [B ==> A], Goal hyps: [H ==> A ==> R] → union
        assert_eq!(result.hyps().len(), 2, "both hypotheses should be preserved");
    }

    #[test]
    fn resolve1_single_subgoal_with_vars() {
        let ctx = resolution_ctx(&["A", "R"]);
        let rule = schematic_identity_rule(&ctx);
        let goal = assumed_goal(&ctx, &["A", "R"]);

        let result = KernelRules::resolve1_match(&rule, &goal, 0).unwrap();
        assert_eq!(result.prop(), &certify_prop_term(&ctx, &imp_chain(&ctx, &["A", "R"])));
        assert_eq!(result.hyps(), goal.hyps());
        super::super::invariant::check_kernel_thm(&result).unwrap();
    }

    #[test]
    fn resolve1_mutiple_rule_premises() {
        // Rule: [P ==> Q ==> R] |- P ==> Q ==> R  (2 premises, conclusion R)
        // Goal: [A ==> R ==> S] |- A ==> R ==> S  (subgoals [A, R])
        // Select subgoal 1 = R
        // Match: R matches R ✅
        // Result: A ==> P ==> Q ==> S
        let ctx = ctx_with_props(&["A", "P", "Q", "R", "S"]);
        let rule_imp = imp_chain(&ctx, &["P", "Q", "R"]);
        let rule_prop = certify_prop_term(&ctx, &rule_imp);
        let rule = KernelRules::assume(rule_prop).unwrap().into_kernel();

        let goal_imp = imp_chain(&ctx, &["A", "R", "S"]);
        let goal_prop = certify_prop_term(&ctx, &goal_imp);
        let goal = KernelRules::assume(goal_prop).unwrap().into_kernel();

        let result = KernelRules::resolve1_match(&rule, &goal, 1).unwrap();
        let expected_imp = imp_chain(&ctx, &["A", "P", "Q", "S"]);
        assert_eq!(result.prop(), &certify_prop_term(&ctx, &expected_imp));
    }

    #[test]
    fn resolve1_multiple_bindings_preserve_subgoal_order() {
        let ctx = resolution_ctx(&["A", "B", "C", "S"]);
        let rule = schematic_eq_rule(&ctx);
        let eq = Term::mk_eq(prop_term(&ctx, "B"), prop_term(&ctx, "C")).unwrap();
        let goal_term =
            Term::mk_imp_chain(&[prop_term(&ctx, "A"), eq.clone()], &prop_term(&ctx, "S")).unwrap();
        let goal = KernelRules::assume(certify_prop_term(&ctx, &goal_term)).unwrap();

        let result = KernelRules::resolve1_match(&rule, goal.as_kernel(), 1).unwrap();
        let expected = Term::mk_imp_chain(
            &[prop_term(&ctx, "A"), prop_term(&ctx, "B"), eq],
            &prop_term(&ctx, "S"),
        )
        .unwrap();
        assert_eq!(result.prop(), &certify_prop_term(&ctx, &expected));
        super::super::invariant::check_kernel_thm(&result).unwrap();
    }
}
