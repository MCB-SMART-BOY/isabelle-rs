use isabelle_kernel::{
    AxiomSchema, EmptyClassDeclCert, KernelError, KernelRules, LogicBasis, Name, PolyType,
    PolyTypeParam, ProofContext, RawTerm, Signature, Sort, TrustedTheory, Ty, TypeVarId,
    accept_closed_theorem,
};

fn owner() -> TrustedTheory {
    TrustedTheory::root(
        "FixedTypeScope",
        Signature::new().install_empty_class(EmptyClassDeclCert::hol_type()).unwrap(),
    )
}

fn fixed_proposition(name: &str, ty: Ty) -> RawTerm {
    let value = RawTerm::free(name, ty);
    RawTerm::eq(value.clone(), value)
}

#[test]
fn certify_undeclared_fixed_type_in_annotation_rejects() {
    let context = ProofContext::new(owner().snapshot().clone());
    let fixed = Ty::tfree("a", Sort::empty());
    assert!(matches!(
        context.certify_term(RawTerm::abs("x", fixed.clone(), RawTerm::bound(0))),
        Err(KernelError::UndeclaredTypeFree { name, .. }) if name == Name::from("a")
    ));
    assert!(matches!(
        context.certify_prop(RawTerm::forall(
            "x",
            fixed,
            RawTerm::eq(RawTerm::bound(0), RawTerm::bound(0),)
        )),
        Err(KernelError::UndeclaredTypeFree { .. })
    ));
}

#[test]
fn certify_declared_fixed_type_supports_local_open_proof() {
    let owner = owner();
    let mut context = ProofContext::new(owner.snapshot().clone());
    let fixed = context.declare_type_free("a", Sort::empty()).unwrap();
    context.declare_free("x", fixed.clone());
    let term = context.certify_term(RawTerm::free("x", fixed.clone())).unwrap();
    let prop = context.certify_prop(fixed_proposition("x", fixed)).unwrap();
    let assumed = KernelRules::assume(prop.clone()).unwrap();
    assert_eq!(assumed.context(), context.stamp());
    assert_eq!(KernelRules::reflexive(term).context(), context.stamp());
    let discharged = KernelRules::implies_intr(&prop, assumed.as_kernel()).unwrap();
    assert!(discharged.hyps().is_empty());
    assert!(matches!(discharged.try_close(), Err(KernelError::LocalTypeScopeEscape { .. })));
}

#[test]
fn fixed_scope_clone_reuses_identity_but_independent_declarations_do_not() {
    let owner = owner();
    assert_eq!(ProofContext::new(owner.snapshot().clone()).stamp(), owner.stamp());
    let mut left = ProofContext::new(owner.snapshot().clone());
    let fixed = left.declare_type_free("a", Sort::empty()).unwrap();
    left.declare_free("x", fixed.clone());
    let mut copied = left.clone();
    copied.declare_free("y", fixed.clone());
    let left_prop = left.certify_prop(fixed_proposition("x", fixed.clone())).unwrap();
    let assumption = KernelRules::assume(left_prop.clone()).unwrap();
    let cloned_prop = copied.certify_prop(fixed_proposition("x", fixed.clone())).unwrap();
    assert_eq!(left.stamp(), copied.stamp());
    assert!(KernelRules::implies_intr(&cloned_prop, assumption.as_kernel()).is_ok());

    let mut independent = ProofContext::new(owner.snapshot().clone());
    let other = independent.declare_type_free("a", Sort::empty()).unwrap();
    independent.declare_free("x", other.clone());
    let other_prop = independent.certify_prop(fixed_proposition("x", other)).unwrap();
    assert_ne!(left.stamp(), independent.stamp());
    assert!(matches!(
        KernelRules::implies_intr(&other_prop, assumption.as_kernel()),
        Err(KernelError::MixedContext { .. })
    ));
    let forall = left
        .certify_prop(RawTerm::forall(
            "y",
            fixed.clone(),
            RawTerm::eq(RawTerm::bound(0), RawTerm::bound(0)),
        ))
        .unwrap();
    let forall_proof = KernelRules::assume(forall).unwrap();
    let foreign_term = independent.certify_term(RawTerm::free("x", fixed.clone())).unwrap();
    assert!(matches!(
        KernelRules::forall_elim(forall_proof.as_kernel(), &foreign_term),
        Err(KernelError::MixedContext { .. })
    ));
    let mut extended = left.clone();
    extended.declare_type_free("b", Sort::empty()).unwrap();
    assert_eq!(left.stamp(), copied.stamp());
    assert_ne!(left.stamp(), extended.stamp());
    assert!(matches!(
        KernelRules::implies_intr(
            &left_prop,
            KernelRules::assume(extended.certify_prop(fixed_proposition("x", fixed)).unwrap(),)
                .unwrap()
                .as_kernel()
        ),
        Err(KernelError::MixedContext { .. })
    ));
}

#[test]
fn certify_polymorphic_constant_requires_local_type_scope() {
    let alpha = Ty::tvar("a", 0, Sort::empty());
    let scheme = PolyType::new(
        vec![PolyTypeParam { id: TypeVarId::new("a", 0, Sort::empty()) }],
        Ty::arrow(alpha.clone(), alpha),
    )
    .unwrap();
    let signature = Signature::new().extend_const_scheme("id", scheme).unwrap();
    let owner = TrustedTheory::root("FixedConstant", signature);
    let mut context = ProofContext::new(owner.snapshot().clone());
    let fixed = Ty::tfree("a", Sort::empty());
    let raw = RawTerm::const_("id", Ty::arrow(fixed.clone(), fixed.clone()));
    assert!(matches!(
        context.certify_term(raw.clone()),
        Err(KernelError::UndeclaredTypeFree { .. })
    ));
    context.declare_type_free("a", Sort::empty()).unwrap();
    assert_eq!(context.certify_term(raw).unwrap().ty(), Ty::arrow(fixed.clone(), fixed));
}

#[test]
fn declare_fixed_type_sort_conflict_and_invalid_sort_reject() {
    let mut context = ProofContext::new(owner().snapshot().clone());
    context.declare_type_free("a", Sort::empty()).unwrap();
    let stamp = context.stamp();
    assert!(matches!(
        context.declare_type_free("a", Sort::empty()),
        Err(KernelError::DuplicateDeclaration { .. })
    ));
    assert!(matches!(
        context.declare_type_free("a", Sort::hol_type()),
        Err(KernelError::TypeIdentityMismatch { .. })
    ));
    assert_eq!(context.stamp(), stamp);
    assert!(matches!(
        context.certify_term(RawTerm::abs(
            "x",
            Ty::tfree("a", Sort::hol_type()),
            RawTerm::bound(0),
        )),
        Err(KernelError::TypeIdentityMismatch { .. })
    ));
    assert!(matches!(
        context.declare_type_free("b", Sort::new(vec!["Unknown.class".into()])),
        Err(KernelError::UnsupportedTypeSort { .. })
    ));
    assert_eq!(context.stamp(), stamp);
}

#[test]
fn signature_and_axiom_reject_permanent_fixed_type() {
    let fixed = Ty::tfree("a", Sort::empty());
    assert!(matches!(
        Signature::new().extend_const("bad", Ty::arrow(fixed.clone(), fixed.clone())),
        Err(KernelError::LocalTypeInSignature { .. })
    ));
    let scheme = PolyType::new(vec![], fixed.clone()).unwrap();
    assert!(matches!(
        Signature::new().extend_const_scheme("bad_scheme", scheme),
        Err(KernelError::LocalTypeInSignature { .. })
    ));
    let signature = Signature::new().extend_const("P", Ty::prop()).unwrap();
    let basis = LogicBasis::try_new(
        vec![],
        vec![AxiomSchema {
            name: Name::from("bad_axiom"),
            prop: RawTerm::forall("x", fixed, RawTerm::const_("P", Ty::prop())),
        }],
    )
    .unwrap();
    assert!(matches!(
        TrustedTheory::with_basis("BadFixed", signature, &basis),
        Err(KernelError::InvalidAxiomSchema { .. })
    ));
}

#[test]
fn accept_closed_local_reflexivity_rejects_scope_escape() {
    let owner = owner();
    let mut context = ProofContext::new(owner.snapshot().clone());
    let fixed = context.declare_type_free("a", Sort::empty()).unwrap();
    context.declare_free("x", fixed.clone());
    let term = context.certify_term(RawTerm::free("x", fixed)).unwrap();
    // Reflexivity already has an empty hypothesis set and a ClosedThm handle.
    let closed = KernelRules::reflexive(term);
    assert!(matches!(
        accept_closed_theorem(&owner, "escaped", closed),
        Err(KernelError::MixedContext { .. })
    ));
}
