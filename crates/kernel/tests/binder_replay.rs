use std::collections::{BTreeMap, BTreeSet};

use isabelle_kernel::{
    CTerm, InstEntry, KernelError, KernelRules, KernelThm, Name, ProofContext, RawTerm, Signature,
    Sort, TrustedTheory, Ty, TypeInstantiation, TypeVarId, accept_closed_theorem,
};

fn names(selected: &[&str]) -> BTreeSet<Name> {
    selected.iter().map(|name| Name::from(*name)).collect()
}

#[test]
fn generalize_inside_binder_preserves_outer_operand_authority_and_accepts() {
    let owner = TrustedTheory::root("OuterBinderGeneralize", Signature::new());
    let mut context = ProofContext::new(owner.snapshot().clone());
    context.declare_free("x", Ty::prop());
    let variable = context.certify_term(RawTerm::free("x", Ty::prop())).unwrap();
    let source = KernelRules::reflexive(variable.clone());
    let generalized =
        KernelRules::generalize(source.as_kernel(), &names(&[]), &names(&["x"]), 0).unwrap();
    let assumption = context
        .certify_prop(RawTerm::eq(RawTerm::free("x", Ty::prop()), RawTerm::free("x", Ty::prop())))
        .unwrap();
    let discharged = KernelRules::implies_intr(&assumption, &generalized).unwrap();
    let quantified = KernelRules::forall_intr(&variable, &discharged).unwrap();
    let expected = ProofContext::new(owner.snapshot().clone())
        .certify_prop(RawTerm::forall(
            "x",
            Ty::prop(),
            RawTerm::imp(
                RawTerm::eq(RawTerm::bound(0), RawTerm::bound(0)),
                RawTerm::eq(RawTerm::var("x", 0, Ty::prop()), RawTerm::var("x", 0, Ty::prop())),
            ),
        ))
        .unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "quantified_generalize", quantified.try_close().unwrap())
            .unwrap();
    assert_eq!(token.prop(), &expected);
    assert_eq!(token.dependencies().len(), 0);
}

#[test]
fn instantiate_simultaneous_type_map_preserves_term_rhs_free_and_accepts() {
    let owner = TrustedTheory::root("RhsTypeSubstitution", Signature::new());
    let mut context = ProofContext::new(owner.snapshot().clone());
    let alpha = Ty::tvar("a", 0, Sort::empty());
    let beta = Ty::tvar("b", 0, Sort::empty());
    context.declare_free("y", beta.clone());
    let source = KernelRules::reflexive(context.certify_term(RawTerm::var("X", 0, alpha)).unwrap());
    let types = TypeInstantiation::try_new(BTreeMap::from([
        (TypeVarId::new("a", 0, Sort::empty()), beta.clone()),
        (TypeVarId::new("b", 0, Sort::empty()), Ty::prop()),
    ]))
    .unwrap();
    let replacement = context.certify_term(RawTerm::free("y", beta.clone())).unwrap();
    let instantiated = KernelRules::instantiate(
        &context,
        source.as_kernel(),
        &types,
        &[InstEntry::new("X", 0, beta.clone(), replacement)],
    )
    .unwrap();
    let generalized =
        KernelRules::generalize(&instantiated, &names(&[]), &names(&["y"]), 1).unwrap();
    let exported = KernelRules::export_scope(&owner, &context, &generalized).unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "simultaneous_rhs", exported.try_close().unwrap()).unwrap();
    let expected = context
        .certify_prop(RawTerm::eq(RawTerm::var("y", 1, beta.clone()), RawTerm::var("y", 1, beta)))
        .unwrap();
    assert_eq!(token.prop(), &expected);
    assert_eq!(token.dependencies().len(), 0);
}

fn create_transformed_binder_operand() -> (TrustedTheory, KernelThm, CTerm) {
    let owner = TrustedTheory::root(
        "BinderTypeEscape",
        Signature::new().extend_const("P", Ty::prop()).unwrap(),
    );
    let mut context = ProofContext::new(owner.snapshot().clone());
    let alpha = Ty::tvar("a", 0, Sort::empty());
    context.declare_free("x", alpha.clone());
    context.declare_free("z", Ty::prop());
    let x = context.certify_term(RawTerm::free("x", alpha)).unwrap();
    let z = context.certify_term(RawTerm::free("z", Ty::prop())).unwrap();
    let source =
        KernelRules::reflexive(context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap());
    let types = TypeInstantiation::try_new(BTreeMap::from([(
        TypeVarId::new("a", 0, Sort::empty()),
        Ty::prop(),
    )]))
    .unwrap();
    let instantiated = KernelRules::instantiate(&context, source.as_kernel(), &types, &[]).unwrap();
    let first = KernelRules::forall_intr(&x, &instantiated).unwrap();
    let second = KernelRules::forall_intr(&z, &first).unwrap();
    let mut alternate = context.clone();
    alternate.declare_free("x", Ty::prop());
    let escaped = alternate.certify_term(RawTerm::free("x", Ty::prop())).unwrap();
    let eliminated = KernelRules::forall_elim(&second, &escaped).unwrap();
    (owner, eliminated, escaped)
}

#[test]
fn instantiate_inside_binder_rejects_transformed_authority_escape() {
    let (owner, eliminated, _) = create_transformed_binder_operand();
    let result = accept_closed_theorem(&owner, "escaped_operand", eliminated.try_close().unwrap());
    assert!(
        matches!(
            &result, Err(KernelError::UndeclaredFree(name)) if name == &Name::from("x"),
        ),
        "{result:?}"
    );
}

#[test]
fn instantiate_converging_binder_grants_preserves_independent_outer_authority() {
    let (owner, eliminated, outer_variable) = create_transformed_binder_operand();
    let quantified = KernelRules::forall_intr(&outer_variable, &eliminated).unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "independent_outer", quantified.try_close().unwrap())
            .unwrap();
    let context = ProofContext::new(owner.snapshot().clone());
    let p = RawTerm::const_("P", Ty::prop());
    let expected = context
        .certify_prop(RawTerm::forall(
            "outer",
            Ty::prop(),
            RawTerm::forall("inner", Ty::tvar("a", 0, Sort::empty()), RawTerm::eq(p.clone(), p)),
        ))
        .unwrap();
    assert!(token.prop().term().alpha_eq(expected.term()));
    assert_eq!(token.prop().context(), expected.context());
    assert_eq!(token.dependencies().len(), 0);
}

#[test]
fn instantiate_rhs_inside_binder_rejects_copied_authority_escape() {
    let owner = TrustedTheory::root(
        "BinderRhsEscape",
        Signature::new().extend_const("P", Ty::prop()).unwrap(),
    );
    let mut context = ProofContext::new(owner.snapshot().clone());
    context.declare_free("x", Ty::prop());
    context.declare_free("z", Ty::prop());
    let x = context.certify_term(RawTerm::free("x", Ty::prop())).unwrap();
    let z = context.certify_term(RawTerm::free("z", Ty::prop())).unwrap();
    let source =
        KernelRules::reflexive(context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap());
    let instantiated = KernelRules::instantiate(
        &context,
        source.as_kernel(),
        &TypeInstantiation::empty(),
        &[InstEntry::new("unused", 0, Ty::prop(), x.clone())],
    )
    .unwrap();
    let first = KernelRules::forall_intr(&x, &instantiated).unwrap();
    let second = KernelRules::forall_intr(&z, &first).unwrap();
    let eliminated = KernelRules::forall_elim(&second, &x).unwrap();
    let result = accept_closed_theorem(&owner, "rhs_escape", eliminated.try_close().unwrap());
    assert!(
        matches!(
            &result, Err(KernelError::UndeclaredFree(name)) if name == &Name::from("x"),
        ),
        "{result:?}"
    );
}

#[test]
fn abstraction_same_name_distinct_types_preserves_both_bindings() {
    let owner = TrustedTheory::root("TypedAbstraction", Signature::new());
    let mut context = ProofContext::new(owner.snapshot().clone());
    let function_ty = Ty::arrow(Ty::prop(), Ty::prop());
    context.declare_free("x", function_ty.clone());
    let function = context.certify_term(RawTerm::free("x", function_ty.clone())).unwrap();
    context.declare_free("x", Ty::prop());
    let argument = context.certify_term(RawTerm::free("x", Ty::prop())).unwrap();
    let application = KernelRules::combination(
        KernelRules::reflexive(function).as_kernel(),
        KernelRules::reflexive(argument).as_kernel(),
    )
    .unwrap();
    let inner = KernelRules::abstraction("x".into(), Ty::prop(), &application).unwrap();
    let outer = KernelRules::abstraction("x".into(), function_ty.clone(), &inner).unwrap();
    let (accepted_owner, token) =
        accept_closed_theorem(&owner, "typed_bindings", outer.try_close().unwrap()).unwrap();
    let function = RawTerm::abs(
        "function",
        function_ty,
        RawTerm::abs("argument", Ty::prop(), RawTerm::app(RawTerm::bound(1), RawTerm::bound(0))),
    );
    let expected = ProofContext::new(owner.snapshot().clone())
        .certify_prop(RawTerm::eq(function.clone(), function))
        .unwrap();
    assert!(token.prop().term().alpha_eq(expected.term()));
    assert_eq!(token.prop().context(), expected.context());
    assert!(token.dependencies().is_empty());
    assert!(matches!(
        ProofContext::new(accepted_owner.snapshot().clone())
            .certify_term(RawTerm::free("x", Ty::prop())),
        Err(KernelError::UndeclaredFree(_))
    ));
}
