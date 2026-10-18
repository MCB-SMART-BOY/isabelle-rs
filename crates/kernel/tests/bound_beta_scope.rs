use isabelle_kernel::{
    KernelRules, ProofContext, RawTerm, Signature, TrustedTheory, Ty, accept_closed_theorem,
};

#[test]
fn beta_under_outer_forall_preserves_reference_through_inner_lambda() {
    let signature = Signature::new().extend_const("P", Ty::prop()).unwrap();
    let owner = TrustedTheory::root("NestedBeta", signature);
    let mut context = ProofContext::new(owner.snapshot().clone());
    context.declare_free("z", Ty::prop());
    let free = context.certify_term(RawTerm::free("z", Ty::prop())).unwrap();
    let redex = context
        .certify_term(RawTerm::app(
            RawTerm::abs(
                "x",
                Ty::prop(),
                RawTerm::abs("y", Ty::prop(), RawTerm::free("z", Ty::prop())),
            ),
            RawTerm::const_("P", Ty::prop()),
        ))
        .unwrap();
    let converted = KernelRules::beta_conversion(redex).unwrap();
    let quantified = KernelRules::forall_intr(&free, converted.as_kernel()).unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &quantified).unwrap();
    let expected = context
        .certify_prop(RawTerm::forall(
            "z",
            Ty::prop(),
            RawTerm::eq(
                RawTerm::app(
                    RawTerm::abs("x", Ty::prop(), RawTerm::abs("y", Ty::prop(), RawTerm::bound(2))),
                    RawTerm::const_("P", Ty::prop()),
                ),
                RawTerm::abs("y", Ty::prop(), RawTerm::bound(1)),
            ),
        ))
        .unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "outer_parameter", stripped.try_close().unwrap()).unwrap();
    assert_eq!(token.prop(), &expected);
}

#[test]
fn forall_elimination_under_outer_binder_preserves_inner_quantifier_scope() {
    let signature = Signature::new().extend_const("P", Ty::prop()).unwrap();
    let owner = TrustedTheory::root("NestedForall", signature);
    let mut context = ProofContext::new(owner.snapshot().clone());
    let mut frees = Vec::new();
    for name in ["x", "y", "z"] {
        context.declare_free(name, Ty::prop());
        frees.push(context.certify_term(RawTerm::free(name, Ty::prop())).unwrap());
    }
    let [x, y, z] = frees.as_slice() else { unreachable!() };
    let reflexive = KernelRules::reflexive(z.clone()).into_kernel();
    let inner = KernelRules::forall_intr(y, &reflexive).unwrap();
    let outer = KernelRules::forall_intr(x, &inner).unwrap();
    let argument = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let applied = KernelRules::forall_elim(&outer, &argument).unwrap();
    let quantified = KernelRules::forall_intr(z, &applied).unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &quantified).unwrap();
    let expected = context
        .certify_prop(RawTerm::forall(
            "z",
            Ty::prop(),
            RawTerm::forall("y", Ty::prop(), RawTerm::eq(RawTerm::bound(1), RawTerm::bound(1))),
        ))
        .unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "outer_parameter", stripped.try_close().unwrap()).unwrap();
    assert_eq!(token.prop(), &expected);
}

#[test]
fn eta_nested_function_preserves_outer_binder_without_capture() {
    let owner = TrustedTheory::root("NestedEta", Signature::new());
    let mut context = ProofContext::new(owner.snapshot().clone());
    context.declare_free("z", Ty::prop());
    let z = context.certify_term(RawTerm::free("z", Ty::prop())).unwrap();
    let function = RawTerm::abs("y", Ty::prop(), RawTerm::free("z", Ty::prop()));
    let redex = context
        .certify_term(RawTerm::abs("x", Ty::prop(), RawTerm::app(function, RawTerm::bound(0))))
        .unwrap();
    let eta = KernelRules::eta_conversion(redex).unwrap();
    let quantified = KernelRules::forall_intr(&z, eta.as_kernel()).unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &quantified).unwrap();
    let expected = context
        .certify_prop(RawTerm::forall(
            "z",
            Ty::prop(),
            RawTerm::eq(
                RawTerm::abs(
                    "x",
                    Ty::prop(),
                    RawTerm::app(
                        RawTerm::abs("y", Ty::prop(), RawTerm::bound(2)),
                        RawTerm::bound(0),
                    ),
                ),
                RawTerm::abs("y", Ty::prop(), RawTerm::bound(1)),
            ),
        ))
        .unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "outer_parameter", stripped.try_close().unwrap()).unwrap();
    assert_eq!(token.prop(), &expected);
}
