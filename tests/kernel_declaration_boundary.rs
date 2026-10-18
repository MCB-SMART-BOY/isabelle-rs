use isabelle_rs::hol::hol_basis::{hol_basis, hol_signature};
use isabelle_rs::kernel::{
    AxiomSchema, BasisDeclaration, DefinitionCertificateError, EmptyClassDeclCert, KernelError,
    LogicBasis, Name, PolyType, ProofContext, RawTerm, Signature, Sort, TheorySnapshot,
    TrustedTheory, Ty,
};

fn make_context(signature: Signature) -> ProofContext {
    ProofContext::new(TheorySnapshot::root("Declarations", signature))
}

#[test]
fn declare_constant_unknown_type_rejects_without_changing_signature() {
    let signature = Signature::new();
    let identity = signature.id();
    assert!(matches!(
        signature.extend_const("x", Ty::base("nat").unwrap()),
        Err(KernelError::UndeclaredTypeConstructor(name)) if name.as_str() == "nat"
    ));
    assert_eq!(signature.id(), identity);
    assert!(signature.get_const(&Name::from("x")).is_none());
}

#[test]
fn certify_unused_binder_wrong_arity_rejects() {
    let signature = Signature::new().extend_type_constructor("bool", 0).unwrap();
    let context = make_context(signature);
    let malformed = Ty::apply("bool", vec![Ty::prop()]).unwrap();
    let body = RawTerm::eq(
        RawTerm::abs("p", Ty::prop(), RawTerm::bound(0)),
        RawTerm::abs("p", Ty::prop(), RawTerm::bound(0)),
    );
    assert!(matches!(
        context.certify_prop(RawTerm::Forall {
            name: Name::from("unused"),
            param_ty: malformed,
            body: Box::new(body),
        }),
        Err(KernelError::TypeConstructorArityMismatch { expected: 0, actual: 1, .. })
    ));
}

#[test]
fn certify_free_and_schematic_unknown_annotations_rejects() {
    let mut context = make_context(Signature::new());
    let unknown = Ty::base("unknown").unwrap();
    context.declare_free("x", unknown.clone());
    assert!(matches!(
        context.certify_term(RawTerm::free("x", unknown.clone())),
        Err(KernelError::UndeclaredTypeConstructor(_))
    ));
    assert!(matches!(
        context.certify_term(RawTerm::Var { name: Name::from("x"), index: 0, ty: unknown }),
        Err(KernelError::UndeclaredTypeConstructor(_))
    ));
}

#[test]
fn certify_declared_constructor_application_succeeds() {
    let signature = Signature::new().extend_type_constructor("box", 1).unwrap();
    let boxed = Ty::apply("box", vec![Ty::prop()]).unwrap();
    let signature = signature.extend_const("value", boxed.clone()).unwrap();
    let context = make_context(signature);
    assert_eq!(context.certify_term(RawTerm::const_("value", boxed.clone())).unwrap().ty(), boxed);
    assert!(context.signature().validate_type(&Ty::arrow(Ty::prop(), Ty::prop())).is_ok());
}

#[test]
fn signature_type_arity_affects_identity_and_order_does_not() {
    let first = Signature::new()
        .extend_type_constructor("t", 0)
        .unwrap()
        .extend_type_constructor("u", 1)
        .unwrap();
    let reordered = Signature::new()
        .extend_type_constructor("u", 1)
        .unwrap()
        .extend_type_constructor("t", 0)
        .unwrap();
    let different = Signature::new()
        .extend_type_constructor("t", 1)
        .unwrap()
        .extend_type_constructor("u", 1)
        .unwrap();
    assert_eq!(first.id(), reordered.id());
    assert_ne!(first.id(), different.id());
    assert!(matches!(
        first.extend_type_constructor("t", 0),
        Err(KernelError::DuplicateDeclaration { .. })
    ));
    assert!(first.extend_const("t", Ty::prop()).is_ok());
}

#[test]
fn snapshot_missing_or_changed_type_declarations_rejects() {
    let signature = Signature::new().extend_type_constructor("t", 1).unwrap();
    assert_eq!(
        Signature::from_untrusted_snapshot(
            signature.id().to_bytes(),
            vec![(Name::from("t"), 1)],
            vec![]
        )
        .unwrap(),
        signature,
    );
    assert!(matches!(
        Signature::from_untrusted_snapshot(signature.id().to_bytes(), vec![], vec![]),
        Err(KernelError::SignatureDigestMismatch)
    ));
    assert!(matches!(
        Signature::from_untrusted_snapshot(
            signature.id().to_bytes(),
            vec![(Name::from("t"), 0)],
            vec![]
        ),
        Err(KernelError::SignatureDigestMismatch)
    ));
}

#[test]
fn certify_type_variable_index_overflow_rejects() {
    let Some(index) = (u32::MAX as usize).checked_add(1) else { return };
    let context =
        make_context(Signature::new().install_empty_class(EmptyClassDeclCert::hol_type()).unwrap());
    let invalid = Ty::tvar("a", index, Sort::hol_type());
    assert!(matches!(
        context.certify_term(RawTerm::Var { name: Name::from("x"), index: 0, ty: invalid }),
        Err(KernelError::TypeVariableIndexOutOfRange { .. })
    ));
}

fn basis_with_axiom(name: &str, prop: RawTerm) -> LogicBasis {
    LogicBasis::try_new(vec![], vec![AxiomSchema { name: name.into(), prop }]).unwrap()
}

#[test]
fn with_basis_undeclared_axiom_rejects_before_later_definition() {
    let signature = Signature::new();
    let basis = basis_with_axiom("bad_P", RawTerm::const_("P", Ty::prop()));
    assert!(matches!(
        TrustedTheory::with_basis("Root", signature.clone(), &basis),
        Err(KernelError::InvalidAxiomSchema { name, source })
            if name.as_str() == "bad_P"
                && matches!(source.as_ref(), KernelError::UndeclaredConst(constant) if constant.as_str() == "P")
    ));
    let root = TrustedTheory::root("Root", signature.extend_const("A", Ty::prop()).unwrap());
    let (defined, theorem) = root.define_const("P", RawTerm::const_("A", Ty::prop())).unwrap();
    assert!(defined.logic_basis().is_none());
    assert_eq!(theorem.name().as_str(), "P_def");
}

#[test]
fn with_basis_hol_refl_copied_signature_rejected_without_owner_history() {
    let basis = hol_basis();
    assert!(matches!(
        TrustedTheory::with_basis("HOL", hol_signature().unwrap(), &basis),
        Err(KernelError::InvalidLogicBasisOrigin { .. })
    ));
}

#[test]
fn with_basis_inconsistent_polymorphic_schema_rejects() {
    let alpha = Ty::tvar("'alpha", 0, Sort::hol_type());
    let beta = Ty::tvar("'beta", 0, Sort::hol_type());
    let bool_ty = Ty::base("bool").unwrap();
    let malformed_eq_ty = Ty::arrow(alpha.clone(), Ty::arrow(beta.clone(), bool_ty.clone()));
    let proposition = RawTerm::forall(
        "x",
        alpha,
        RawTerm::forall(
            "y",
            beta,
            RawTerm::app(
                RawTerm::const_("HOL.Trueprop", Ty::arrow(bool_ty, Ty::prop())),
                RawTerm::app(
                    RawTerm::app(RawTerm::const_("HOL.eq", malformed_eq_ty), RawTerm::bound(1)),
                    RawTerm::bound(0),
                ),
            ),
        ),
    );
    let basis = LogicBasis::try_new(
        hol_basis().declarations().to_vec(),
        vec![AxiomSchema { name: "bad_eq".into(), prop: proposition }],
    )
    .unwrap();
    assert!(matches!(
        TrustedTheory::with_basis("HOL", hol_signature().unwrap(), &basis),
        Err(KernelError::InvalidAxiomSchema { name, source })
            if name.as_str() == "bad_eq"
                && matches!(*source, KernelError::TypeMismatch { .. })
    ));
}

#[test]
fn with_basis_type_declaration_must_match_signature_arity() {
    let basis = LogicBasis::try_new(
        vec![BasisDeclaration::TypeConstructor { name: "box".into(), arity: 1 }],
        vec![],
    )
    .unwrap();
    assert!(matches!(
        TrustedTheory::with_basis("Root", Signature::new(), &basis),
        Err(KernelError::UndeclaredTypeConstructor(name)) if name.as_str() == "box"
    ));
    let signature = Signature::new().extend_type_constructor("box", 0).unwrap();
    assert!(matches!(
        TrustedTheory::with_basis("Root", signature, &basis),
        Err(KernelError::TypeConstructorArityMismatch { name, expected, actual })
            if name.as_str() == "box"
                && ((expected == 0 && actual == 1) || (expected == 1 && actual == 0))
    ));
}

#[test]
fn with_basis_shared_type_and_constant_name_are_distinct() {
    let ty = Ty::base("shared").unwrap();
    let signature = Signature::new()
        .extend_type_constructor("shared", 0)
        .unwrap()
        .extend_const("shared", ty.clone())
        .unwrap();
    let basis = LogicBasis::try_new(
        vec![
            BasisDeclaration::TypeConstructor { name: "shared".into(), arity: 0 },
            BasisDeclaration::Constant {
                name: "shared".into(),
                scheme: PolyType::new(vec![], ty).unwrap(),
            },
        ],
        vec![],
    )
    .unwrap();
    assert!(TrustedTheory::with_basis("Root", signature, &basis).is_ok());
}

#[test]
fn with_basis_invalid_axiom_scope_or_result_rejects() {
    for (axiom_name, proposition) in [
        ("dangling", RawTerm::bound(0)),
        ("free", RawTerm::free("x", Ty::prop())),
        ("not_prop", RawTerm::const_("value", Ty::base("bool").unwrap())),
    ] {
        let signature = Signature::new()
            .extend_type_constructor("bool", 0)
            .unwrap()
            .extend_const("value", Ty::base("bool").unwrap())
            .unwrap();
        let basis = basis_with_axiom(axiom_name, proposition);
        let expected = match axiom_name {
            "dangling" => KernelError::UnboundBound(0),
            "free" => KernelError::UndeclaredFree("x".into()),
            _ => KernelError::NotProposition(Ty::base("bool").unwrap()),
        };
        assert!(matches!(
            TrustedTheory::with_basis("Root", signature, &basis),
            Err(KernelError::InvalidAxiomSchema { name, source })
                if name.as_str() == axiom_name && *source == expected
        ));
    }
}

#[test]
fn define_const_hidden_type_variables_rejects_without_extension() {
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const("P", Ty::prop())
        .unwrap();
    let root = TrustedTheory::root("Root", signature);
    let alpha = Ty::tvar("'alpha", 0, Sort::hol_type());
    let proposition = RawTerm::const_("P", Ty::prop());
    for (name, rhs) in [
        (
            "bound",
            RawTerm::forall("x", alpha.clone(), RawTerm::eq(RawTerm::bound(0), RawTerm::bound(0))),
        ),
        ("unused", RawTerm::forall("x", alpha.clone(), proposition)),
    ] {
        assert!(matches!(
            root.define_const(name, rhs),
            Err(KernelError::DefinitionCertificate(
                DefinitionCertificateError::RhsContainsTypeVariables { name: invalid, ty }
            )) if invalid.as_str() == name && ty == alpha
        ));
        assert!(root.signature().get_const(&Name::from(name)).is_none());
        assert!(root.get(&Name::from(format!("{name}_def"))).is_none());
    }
}

#[test]
fn define_const_monomorphic_rhs_accepts_definition_dependency() {
    let signature = Signature::new().extend_const("P", Ty::prop()).unwrap();
    let root = TrustedTheory::root("Root", signature);
    let (child, definition) = root.define_const("alias", RawTerm::const_("P", Ty::prop())).unwrap();
    assert_eq!(child.signature().const_type(&Name::from("alias")), Some(&Ty::prop()));
    assert_eq!(child.get(&Name::from("alias_def")).unwrap().id(), definition.id());
    assert_eq!(definition.dependencies().len(), 1);
    assert_eq!(definition.proved_in(), child.parents()[0].id());
    assert_eq!(child.parents()[0].parents()[0].id(), root.id());
}
