use isabelle_kernel::{
    EmptyClassDeclCert, KernelError, KernelRules, Name, ProofContext, RawTerm, Signature, Sort,
    TrustedTheory, Ty, accept_closed_theorem,
};

fn accept_reflexivity(
    owner: &TrustedTheory,
    name: &str,
) -> (TrustedTheory, isabelle_kernel::TrustedTheorem) {
    let context = ProofContext::new(owner.snapshot().clone());
    let a = context.certify_term(RawTerm::const_("A", Ty::prop())).unwrap();
    accept_closed_theorem(owner, name, KernelRules::reflexive(a)).unwrap()
}

#[test]
fn merge_parents_diamond_retains_order_shared_fact_and_exact_tokens() {
    let root = TrustedTheory::root("Root", Signature::new().extend_const("A", Ty::prop()).unwrap());
    let (common, token_common) = accept_reflexivity(&root, "shared");
    let (left, token_left) = accept_reflexivity(&common.begin_child("L"), "left");
    let (right, token_right) = accept_reflexivity(&common.begin_child("R"), "right");
    assert!(matches!(
        KernelRules::theorem_ref(&right, &token_left),
        Err(KernelError::UnknownTheoremDependency)
    ));
    let forward =
        TrustedTheory::merge_parents("Merge", &[common.clone(), left.clone(), right.clone()])
            .unwrap();
    let reverse = TrustedTheory::merge_parents("Merge", &[right.clone(), left.clone()]).unwrap();
    assert_eq!(
        forward.parents().iter().map(TrustedTheory::id).collect::<Vec<_>>(),
        vec![left.id(), right.id()]
    );
    assert_eq!(
        reverse.parents().iter().map(TrustedTheory::id).collect::<Vec<_>>(),
        vec![right.id(), left.id()]
    );
    assert_ne!(forward.id(), reverse.id());
    assert_eq!(forward.len(), 3);
    for token in [&token_common, &token_left, &token_right] {
        assert!(KernelRules::theorem_ref(&forward, token).is_ok());
    }
    let (child, _) = accept_reflexivity(&forward, "after_merge");
    assert_eq!(child.len(), 4);
    assert!(matches!(TrustedTheory::merge_parents("Empty", &[]), Err(KernelError::Invariant(_))));
}

#[test]
fn merge_parents_conflicting_declarations_and_definitions_reject() {
    let root = TrustedTheory::root("Root", Signature::new().extend_const("A", Ty::prop()).unwrap());
    let left = root.begin_child("L").extend_const("other", Ty::prop()).unwrap();
    let right = root.begin_child("R").extend_const("other", Ty::prop()).unwrap();
    assert!(matches!(TrustedTheory::merge_parents("Collision", &[left, right]),
        Err(KernelError::DuplicateDeclaration { name }) if name == Name::from("other")));

    let root = TrustedTheory::root(
        "Definitions",
        Signature::new()
            .extend_const("c", Ty::prop())
            .unwrap()
            .extend_const("d", Ty::prop())
            .unwrap(),
    );
    let (left, _) =
        root.begin_child("L").define_const("c", RawTerm::const_("d", Ty::prop())).unwrap();
    let (right, _) =
        root.begin_child("R").define_const("d", RawTerm::const_("c", Ty::prop())).unwrap();
    assert!(matches!(
        TrustedTheory::merge_parents("Cycle", &[left, right]),
        Err(KernelError::DefinitionCertificate(_))
    ));
    assert!(root.get(&Name::from("c_def")).is_none());
}

#[test]
fn define_const_polymorphic_parameter_closure_replays_without_hidden_type_vars() {
    let signature = Signature::new().install_empty_class(EmptyClassDeclCert::hol_type()).unwrap();
    let root = TrustedTheory::root("Definitions", signature);
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let (owner, theorem) = root
        .define_const_with_args(
            "id",
            vec![(Name::from("x"), alpha.clone())],
            RawTerm::free("x", alpha.clone()),
        )
        .unwrap();
    assert!(
        owner
            .signature()
            .certify_const_instance(&Name::from("id"), &Ty::arrow(alpha.clone(), alpha.clone()))
            .is_ok()
    );
    assert!(KernelRules::theorem_ref(&owner, &theorem).is_ok());
    let hidden = Ty::tvar("b", 0, Sort::hol_type());
    let wrong = RawTerm::abs(
        "x",
        alpha,
        RawTerm::forall("hidden", hidden, RawTerm::eq(RawTerm::bound(1), RawTerm::bound(1))),
    );
    assert!(matches!(
        root.define_const("bad", wrong),
        Err(KernelError::DefinitionCertificate(
            isabelle_kernel::DefinitionCertificateError::RhsContainsTypeVariables { .. }
        ))
    ));
    assert!(root.signature().get_const(&Name::from("bad")).is_none());
    assert!(matches!(
        root.define_const_with_args("bad", vec![], RawTerm::free("unbound", Ty::prop())),
        Err(KernelError::UndeclaredFree(_))
    ));
}

#[test]
fn certify_type_hol_class_requires_declared_class_and_matching_owner_scope() {
    let undecided =
        ProofContext::new(TrustedTheory::root("Pure", Signature::new()).snapshot().clone());
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    assert!(matches!(
        undecided.certify_type(alpha.clone()),
        Err(KernelError::UnsupportedTypeSort { .. })
    ));
    let root = TrustedTheory::root(
        "HOL",
        Signature::new().install_empty_class(EmptyClassDeclCert::hol_type()).unwrap(),
    );
    let mut context = ProofContext::new(root.snapshot().clone());
    let certified = context.certify_type(alpha).unwrap();
    assert_eq!(certified.ty(), &Ty::tvar("a", 0, Sort::hol_type()));
    assert_eq!(certified.context(), context.stamp());
    let fixed = Ty::tfree("a", Sort::hol_type());
    assert!(matches!(
        context.certify_type(fixed.clone()),
        Err(KernelError::UndeclaredTypeFree { .. })
    ));
    assert_eq!(context.declare_type_free("a", Sort::hol_type()).unwrap(), fixed);
    assert_eq!(context.certify_type(fixed).unwrap().context(), context.stamp());
    assert_ne!(certified.context(), context.stamp());
}

#[test]
fn define_const_predeclared_matching_type_allows_tautological_prior_fact() {
    let root = TrustedTheory::root(
        "Root",
        Signature::new()
            .extend_const("existing", Ty::prop())
            .unwrap()
            .extend_const("P", Ty::prop())
            .unwrap(),
    );
    let context = ProofContext::new(root.snapshot().clone());
    let term = context.certify_term(RawTerm::const_("existing", Ty::prop())).unwrap();
    let (with_fact, _) =
        accept_closed_theorem(&root, "used", KernelRules::reflexive(term)).unwrap();
    let (defined, definition) =
        with_fact.define_const("existing", RawTerm::const_("P", Ty::prop())).unwrap();
    assert_eq!(root.signature().const_type(&Name::from("existing")), Some(&Ty::prop()));
    assert!(KernelRules::theorem_ref(&defined, &definition).is_ok());
    assert!(with_fact.get(&Name::from("existing_def")).is_none());
}
