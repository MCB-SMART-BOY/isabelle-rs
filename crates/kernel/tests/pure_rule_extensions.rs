use std::collections::BTreeMap;

use isabelle_kernel::{
    AxiomSchema, InstEntry, KernelError, KernelRules, LogicBasis, ProofContext, RawTerm, Signature,
    Sort, TrustedTheory, Ty, TypeInstantiation, TypeVarId, accept_closed_theorem, theorem_builder,
};

fn make_owner() -> (TrustedTheory, ProofContext) {
    let signature = Signature::new()
        .extend_const("A", Ty::prop())
        .unwrap()
        .extend_const("P", Ty::prop())
        .unwrap()
        .extend_const("f", Ty::arrow(Ty::prop(), Ty::prop()))
        .unwrap();
    let owner = TrustedTheory::root("PureRules", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    (owner, context)
}

fn eta_redex(function: RawTerm) -> RawTerm {
    RawTerm::abs("x", Ty::prop(), RawTerm::app(function, RawTerm::bound(0)))
}

#[test]
fn weaken_real_hypothesis_requires_discharge_before_acceptance() {
    let (owner, context) = make_owner();
    let assumption = context.certify_prop(RawTerm::const_("A", Ty::prop())).unwrap();
    let term = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let original = KernelRules::reflexive(term).into_kernel();
    let weakened = KernelRules::weaken(&assumption, &original).unwrap();
    assert_eq!(weakened.prop(), original.prop());
    assert_eq!(weakened.hyps(), std::slice::from_ref(&assumption));
    assert!(weakened.clone().try_close().is_err());
    let repeated = KernelRules::weaken(&assumption, &weakened).unwrap();
    assert_eq!(repeated.hyps(), weakened.hyps());
    let stripped = KernelRules::strip_shyps(&owner, &context, &weakened).unwrap();
    assert_eq!(stripped.hyps(), std::slice::from_ref(&assumption));
    let discharged = KernelRules::implies_intr(&assumption, &stripped).unwrap();
    let (_, accepted) =
        accept_closed_theorem(&owner, "weaken_discharge", discharged.try_close().unwrap()).unwrap();
    let expected = context
        .certify_prop(RawTerm::imp(
            RawTerm::const_("A", Ty::prop()),
            RawTerm::eq(RawTerm::const_("P", Ty::prop()), RawTerm::const_("P", Ty::prop())),
        ))
        .unwrap();
    assert_eq!(accepted.prop(), &expected);
}

#[test]
fn weaken_schematic_hypothesis_and_wrong_owner_reject() {
    let (owner, context) = make_owner();
    let theorem =
        KernelRules::reflexive(context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap());
    let schematic = context.certify_prop(RawTerm::var("Q", 0, Ty::prop())).unwrap();
    assert!(matches!(
        KernelRules::weaken(&schematic, theorem.as_kernel()),
        Err(KernelError::SchematicHypothesis)
    ));
    let schematic_type = Ty::tvar("t", 0, Sort::empty());
    let typed_term = RawTerm::abs("x", schematic_type, RawTerm::const_("P", Ty::prop()));
    let typed = context.certify_prop(RawTerm::eq(typed_term.clone(), typed_term)).unwrap();
    assert!(matches!(
        KernelRules::weaken(&typed, theorem.as_kernel()),
        Err(KernelError::SchematicHypothesis)
    ));
    let other = TrustedTheory::root("Other", owner.signature().clone());
    let foreign = ProofContext::new(other.snapshot().clone())
        .certify_prop(RawTerm::const_("A", Ty::prop()))
        .unwrap();
    assert!(matches!(
        KernelRules::weaken(&foreign, theorem.as_kernel()),
        Err(KernelError::MixedContext { .. })
    ));
}

#[test]
fn eta_conversion_accepts_exact_pure_equality_after_strip() {
    let (owner, context) = make_owner();
    let function = RawTerm::const_("f", Ty::arrow(Ty::prop(), Ty::prop()));
    let redex = context.certify_term(eta_redex(function.clone())).unwrap();
    let converted = KernelRules::eta_conversion(redex).unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, converted.as_kernel()).unwrap();
    let (_, accepted) =
        accept_closed_theorem(&owner, "eta", stripped.try_close().unwrap()).unwrap();
    let expected =
        context.certify_prop(RawTerm::eq(eta_redex(function.clone()), function)).unwrap();
    assert_eq!(accepted.prop(), &expected);
    assert!(accepted.dependencies().is_empty());
}

#[test]
fn eta_conversion_under_forall_binder_shifts_outer_bound_safely() {
    let (owner, mut context) = make_owner();
    let function_type = Ty::arrow(Ty::prop(), Ty::prop());
    context.declare_free("g", function_type.clone());
    let function = RawTerm::free("g", function_type.clone());
    let redex = context.certify_term(eta_redex(function.clone())).unwrap();
    let eta = KernelRules::eta_conversion(redex).unwrap();
    let variable = context.certify_term(function.clone()).unwrap();
    let quantified = KernelRules::forall_intr(&variable, eta.as_kernel()).unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &quantified).unwrap();
    let (_, accepted) =
        accept_closed_theorem(&owner, "eta_under_binder", stripped.try_close().unwrap()).unwrap();
    let expected = context
        .certify_prop(RawTerm::forall(
            "g",
            function_type,
            RawTerm::eq(
                RawTerm::abs("x", Ty::prop(), RawTerm::app(RawTerm::bound(1), RawTerm::bound(0))),
                RawTerm::bound(0),
            ),
        ))
        .unwrap();
    assert_eq!(accepted.prop(), &expected);
}

#[test]
fn eta_conversion_rejects_captured_variable_and_non_redex() {
    let (_, context) = make_owner();
    let captured =
        context.certify_term(eta_redex(RawTerm::abs("y", Ty::prop(), RawTerm::bound(1)))).unwrap();
    assert!(matches!(KernelRules::eta_conversion(captured), Err(KernelError::EtaRedexExpected(_))));
    let non_redex = context.certify_term(RawTerm::abs("x", Ty::prop(), RawTerm::bound(0))).unwrap();
    assert!(matches!(
        KernelRules::eta_conversion(non_redex),
        Err(KernelError::EtaRedexExpected(_))
    ));
    let wrong_argument = context
        .certify_term(RawTerm::abs(
            "x",
            Ty::prop(),
            RawTerm::app(
                RawTerm::const_("f", Ty::arrow(Ty::prop(), Ty::prop())),
                RawTerm::const_("P", Ty::prop()),
            ),
        ))
        .unwrap();
    assert!(matches!(
        KernelRules::eta_conversion(wrong_argument),
        Err(KernelError::EtaRedexExpected(_))
    ));
    let wrong_type = RawTerm::abs(
        "x",
        Ty::arrow(Ty::prop(), Ty::prop()),
        RawTerm::app(RawTerm::const_("f", Ty::arrow(Ty::prop(), Ty::prop())), RawTerm::bound(0)),
    );
    assert!(context.certify_term(wrong_type).is_err());
    assert!(context.certify_term(eta_redex(RawTerm::bound(1))).is_err());
}

#[test]
fn eta_conversion_strip_removes_only_disappeared_empty_sort() {
    let (owner, context) = make_owner();
    let hidden = Ty::tvar("hidden", 0, Sort::empty());
    let function_type = Ty::arrow(hidden.clone(), hidden.clone());
    let source = context
        .certify_term(RawTerm::abs(
            "x",
            hidden,
            RawTerm::app(RawTerm::var("F", 0, function_type), RawTerm::bound(0)),
        ))
        .unwrap();
    let source = KernelRules::eta_conversion(source).unwrap();
    let types = TypeInstantiation::try_new(BTreeMap::from([(
        TypeVarId::new("hidden", 0, Sort::empty()),
        Ty::prop(),
    )]))
    .unwrap();
    let function =
        context.certify_term(RawTerm::const_("f", Ty::arrow(Ty::prop(), Ty::prop()))).unwrap();
    let instantiated = KernelRules::instantiate(
        &context,
        source.as_kernel(),
        &types,
        &[InstEntry::new("F", 0, Ty::arrow(Ty::prop(), Ty::prop()), function)],
    )
    .unwrap();
    assert!(instantiated.clone().try_close().is_err());
    let stripped = KernelRules::strip_shyps(&owner, &context, &instantiated).unwrap();
    let (_, accepted) =
        accept_closed_theorem(&owner, "eta_stripped_sort", stripped.try_close().unwrap()).unwrap();
    assert_eq!(accepted.prop(), instantiated.prop());
}

#[test]
fn weaken_strip_preserves_axiom_dependency() {
    let (base_owner, _) = make_owner();
    let signature = base_owner.signature().clone();
    let original = RawTerm::eq(RawTerm::const_("P", Ty::prop()), RawTerm::const_("P", Ty::prop()));
    let basis = LogicBasis::try_new(
        vec![],
        vec![AxiomSchema { name: "refl_P".into(), prop: original.clone() }],
    )
    .unwrap();
    let owner = TrustedTheory::with_basis("PureDependency", signature, &basis).unwrap();
    let context = ProofContext::new(owner.snapshot().clone());
    let axiom = theorem_builder::axiom_theorem(
        &context,
        &basis,
        "refl_P".into(),
        TypeInstantiation::empty(),
        vec![],
        original.clone(),
    )
    .unwrap();
    let assumption = context.certify_prop(RawTerm::const_("A", Ty::prop())).unwrap();
    let weakened = KernelRules::weaken(&assumption, &axiom).unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &weakened).unwrap();
    let closed = KernelRules::implies_intr(&assumption, &stripped).unwrap().try_close().unwrap();
    let (_, accepted) = accept_closed_theorem(&owner, "weakened_axiom", closed).unwrap();
    assert_eq!(accepted.dependencies().len(), 1);
    let expected =
        context.certify_prop(RawTerm::imp(RawTerm::const_("A", Ty::prop()), original)).unwrap();
    assert_eq!(accepted.prop(), &expected);
}
