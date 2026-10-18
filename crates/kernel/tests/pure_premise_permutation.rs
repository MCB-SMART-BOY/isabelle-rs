use std::collections::BTreeSet;

use isabelle_kernel::{
    EmptyClassDeclCert, KernelError, KernelRules, PolyType, PolyTypeParam, ProofContext, RawTerm,
    Signature, Sort, TrustedTheory, Ty, TypeVarId, accept_closed_theorem,
};

fn prepare_owner() -> (TrustedTheory, ProofContext) {
    let signature =
        ["A", "B", "C", "Tail"].into_iter().fold(Signature::new(), |signature, name| {
            signature.extend_const(name, Ty::prop()).unwrap()
        });
    let owner = TrustedTheory::root("Permutations", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    (owner, context)
}

fn proposition(name: &str) -> RawTerm {
    RawTerm::const_(name, Ty::prop())
}

fn prove_identity(context: &ProofContext, antecedents: &[&str]) -> isabelle_kernel::KernelThm {
    let a = context.certify_prop(proposition("A")).unwrap();
    let mut theorem = KernelRules::assume(a).unwrap().into_kernel();
    for name in antecedents.iter().rev() {
        let premise = context.certify_prop(proposition(name)).unwrap();
        theorem = KernelRules::implies_intr(&premise, &theorem).unwrap();
    }
    theorem
}

#[test]
fn permute_tail_negative_rotation_preserves_order_and_accepts() {
    let (owner, context) = prepare_owner();
    let source = prove_identity(&context, &["A", "B", "C"]);
    let moved = KernelRules::permute_prems(&owner, &context, &source, 1, -1).unwrap();
    let expected = context
        .certify_prop(RawTerm::imp(
            proposition("A"),
            RawTerm::imp(proposition("C"), RawTerm::imp(proposition("B"), proposition("A"))),
        ))
        .unwrap();
    assert_eq!(moved.prop(), &expected);
    let (updated, accepted) =
        accept_closed_theorem(&owner, "permuted", moved.try_close().unwrap()).unwrap();
    let replayed = KernelRules::theorem_ref(&updated, &accepted).unwrap();
    assert_eq!(replayed.as_kernel().prop().term(), expected.term());
    assert_eq!(replayed.context(), updated.snapshot().stamp());
}

#[test]
fn permute_tail_duplicate_slots_remain_distinct() {
    let (owner, context) = prepare_owner();
    let source = prove_identity(&context, &["A", "B", "A"]);
    let moved = KernelRules::permute_prems(&owner, &context, &source, 0, 1).unwrap();
    let expected = context
        .certify_prop(RawTerm::imp(
            proposition("B"),
            RawTerm::imp(proposition("A"), RawTerm::imp(proposition("A"), proposition("A"))),
        ))
        .unwrap();
    assert_eq!(moved.prop(), &expected);
    assert!(accept_closed_theorem(&owner, "duplicates", moved.try_close().unwrap()).is_ok());
}

#[test]
fn permute_tail_identity_and_out_of_range_are_explicit() {
    let (owner, context) = prepare_owner();
    let source = prove_identity(&context, &["A", "B"]);
    for rotation in [0, 2, -2] {
        let moved = KernelRules::permute_prems(&owner, &context, &source, 0, rotation).unwrap();
        assert_eq!(moved.prop(), source.prop());
    }
    assert!(matches!(
        KernelRules::permute_prems(&owner, &context, &source, 3, 0),
        Err(KernelError::BoundProof(_))
    ));
    assert!(matches!(
        KernelRules::permute_prems(&owner, &context, &source, 0, -3),
        Err(KernelError::BoundProof(_))
    ));
}

#[test]
fn rotate_selected_nested_forall_preserves_outer_tail() {
    let (owner, context) = prepare_owner();
    let inner = RawTerm::forall(
        "x",
        Ty::prop(),
        RawTerm::imp(proposition("A"), RawTerm::imp(proposition("B"), proposition("A"))),
    );
    let c = context.certify_prop(proposition("C")).unwrap();
    let mut theorem = KernelRules::assume(c.clone()).unwrap().into_kernel();
    for premise in [proposition("C"), proposition("Tail"), inner.clone()] {
        theorem =
            KernelRules::implies_intr(&context.certify_prop(premise).unwrap(), &theorem).unwrap();
    }
    let rotated = KernelRules::rotate_rule(&owner, &context, &theorem, 0, 1).unwrap();
    let expected_inner = RawTerm::forall(
        "x",
        Ty::prop(),
        RawTerm::imp(proposition("B"), RawTerm::imp(proposition("A"), proposition("A"))),
    );
    let expected = context
        .certify_prop(RawTerm::imp(
            expected_inner,
            RawTerm::imp(proposition("Tail"), RawTerm::imp(proposition("C"), proposition("C"))),
        ))
        .unwrap();
    assert_eq!(rotated.prop(), &expected);
    assert!(accept_closed_theorem(&owner, "rotated", rotated.try_close().unwrap()).is_ok());
    assert!(matches!(
        KernelRules::rotate_rule(&owner, &context, &theorem, 3, 1),
        Err(KernelError::BoundProof(_))
    ));
}

#[test]
fn permute_prems_open_hypothesis_preserves_payload_and_rejects_foreign_owner() {
    let (owner, context) = prepare_owner();
    let source = prove_identity(&context, &["A", "B"]);
    let hypothesis = context.certify_prop(proposition("Tail")).unwrap();
    let open = KernelRules::weaken(&hypothesis, &source).unwrap();
    let moved = KernelRules::permute_prems(&owner, &context, &open, 0, 1).unwrap();
    assert_eq!(moved.hyps(), open.hyps());
    assert_eq!(moved.max_var_index(), open.max_var_index());
    assert!(moved.try_close().is_err());
    let foreign = TrustedTheory::root("Foreign", owner.signature().clone());
    assert!(KernelRules::permute_prems(&foreign, &context, &open, 0, 1).is_err());
}

#[test]
fn permute_exported_sorted_premises_accepts_identity_and_swap() {
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let beta = Ty::tvar("b", 0, Sort::hol_type());
    let function_ty = Ty::arrow(alpha, beta);
    let scheme = PolyType::new(
        vec![
            PolyTypeParam { id: TypeVarId::new("a", 0, Sort::hol_type()) },
            PolyTypeParam { id: TypeVarId::new("b", 0, Sort::hol_type()) },
        ],
        function_ty.clone(),
    )
    .unwrap();
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const_scheme("F", scheme)
        .unwrap();
    let owner = TrustedTheory::root("ExportPermute", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    let function = context.certify_term(RawTerm::const_("F", function_ty)).unwrap();
    let exported =
        KernelRules::unconstrain_t(&owner, &context, KernelRules::reflexive(function).as_kernel())
            .unwrap();
    assert_eq!(exported.prop().term().nprems(), 2);
    for rotation in [0, 1] {
        let permuted =
            KernelRules::permute_prems(&owner, &context, &exported, 0, rotation).unwrap();
        let (_, token) = accept_closed_theorem(
            &owner,
            format!("export_permutation_{rotation}"),
            permuted.try_close().unwrap(),
        )
        .unwrap();
        assert_eq!(token.prop().term().nprems(), 2);
    }
}

#[test]
fn permute_exported_sorted_constant_then_strip_and_export_accepts() {
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let function_ty = Ty::arrow(alpha.clone(), alpha);
    let scheme = PolyType::new(
        vec![PolyTypeParam { id: TypeVarId::new("a", 0, Sort::hol_type()) }],
        function_ty.clone(),
    )
    .unwrap();
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const_scheme("F", scheme)
        .unwrap();
    let owner = TrustedTheory::root("ExportStripPermute", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    let term = context.certify_term(RawTerm::const_("F", function_ty)).unwrap();
    let reflexive = KernelRules::reflexive(term);
    let assumption = reflexive.as_kernel().prop().clone();
    let source = KernelRules::implies_intr(&assumption, reflexive.as_kernel()).unwrap();
    let exported = KernelRules::unconstrain_t(&owner, &context, &source).unwrap();
    let permuted = KernelRules::permute_prems(&owner, &context, &exported, 0, 1).unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &permuted).unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "permuted_stripped", stripped.try_close().unwrap()).unwrap();
    assert_eq!(token.prop(), permuted.prop());
    let twice = KernelRules::unconstrain_t(&owner, &context, &permuted).unwrap();
    let (_, twice_token) =
        accept_closed_theorem(&owner, "permuted_reexported", twice.try_close().unwrap()).unwrap();
    assert_eq!(twice_token.prop().term().nprems(), permuted.prop().term().nprems());
}

#[test]
fn strip_user_generalized_permuted_exported_sort_accepts() {
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let function_ty = Ty::arrow(alpha.clone(), alpha);
    let scheme = PolyType::new(
        vec![PolyTypeParam { id: TypeVarId::new("a", 0, Sort::hol_type()) }],
        function_ty.clone(),
    )
    .unwrap();
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const_scheme("F", scheme)
        .unwrap();
    let owner = TrustedTheory::root("ExportGeneralizeStrip", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    let mut local = context.clone();
    local.declare_free("q", Ty::prop());
    let f = local.certify_term(RawTerm::const_("F", function_ty)).unwrap();
    let q = local.certify_term(RawTerm::free("q", Ty::prop())).unwrap();
    let premise = KernelRules::reflexive(f).as_kernel().prop().clone();
    let body = KernelRules::reflexive(q);
    let source = KernelRules::implies_intr(&premise, body.as_kernel()).unwrap();
    let exported = KernelRules::unconstrain_t(&owner, &local, &source).unwrap();
    let permuted = KernelRules::permute_prems(&owner, &local, &exported, 0, 1).unwrap();
    let index = permuted
        .max_var_index()
        .map_or(Ok(0), |value| {
            value
                .checked_add(1)
                .ok_or(KernelError::GeneralizeIndexOverflow { index: value, offset: 1 })
        })
        .unwrap();
    let generalized =
        KernelRules::generalize(&permuted, &BTreeSet::new(), &BTreeSet::from(["q".into()]), index)
            .unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &generalized).unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "user_generalized_export", stripped.try_close().unwrap())
            .unwrap();
    assert_eq!(token.prop(), generalized.prop());
}

#[test]
fn rotate_exported_sorted_subgoal_accepts_identity_and_nonidentity() {
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let function_ty = Ty::arrow(alpha.clone(), alpha.clone());
    let scheme = PolyType::new(
        vec![PolyTypeParam { id: TypeVarId::new("a", 0, Sort::hol_type()) }],
        function_ty.clone(),
    )
    .unwrap();
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const("P", Ty::prop())
        .unwrap()
        .extend_const_scheme("F", scheme)
        .unwrap();
    let owner = TrustedTheory::root("ExportRotate", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    let assertion =
        RawTerm::eq(RawTerm::const_("F", function_ty.clone()), RawTerm::const_("F", function_ty));
    let inner = RawTerm::imp(assertion.clone(), RawTerm::imp(proposition("P"), assertion));
    let premise = context.certify_prop(inner).unwrap();
    let term =
        context.certify_term(RawTerm::var("x", 0, Ty::tvar("a", 0, Sort::hol_type()))).unwrap();
    let body = KernelRules::reflexive(term);
    let closed = KernelRules::implies_intr(&premise, body.as_kernel()).unwrap();
    let exported = KernelRules::unconstrain_t(&owner, &context, &closed).unwrap();
    assert_eq!(exported.prop().term().nprems(), 2);
    for rotation in [0, 1] {
        let rotated = KernelRules::rotate_rule(&owner, &context, &exported, 1, rotation).unwrap();
        let (_, token) = accept_closed_theorem(
            &owner,
            format!("export_rotation_{rotation}"),
            rotated.try_close().unwrap(),
        )
        .unwrap();
        assert_eq!(token.prop().term().nprems(), 2);
    }
}

#[test]
fn rotate_exported_sorted_constant_then_strip_accepts() {
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let function_ty = Ty::arrow(alpha.clone(), alpha);
    let scheme = PolyType::new(
        vec![PolyTypeParam { id: TypeVarId::new("a", 0, Sort::hol_type()) }],
        function_ty.clone(),
    )
    .unwrap();
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const("P", Ty::prop())
        .unwrap()
        .extend_const_scheme("F", scheme)
        .unwrap();
    let owner = TrustedTheory::root("ExportStripRotate", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    let assertion =
        RawTerm::eq(RawTerm::const_("F", function_ty.clone()), RawTerm::const_("F", function_ty));
    let inner = RawTerm::imp(assertion.clone(), RawTerm::imp(proposition("P"), assertion));
    let premise = context.certify_prop(inner).unwrap();
    let term =
        context.certify_term(RawTerm::var("x", 0, Ty::tvar("a", 0, Sort::hol_type()))).unwrap();
    let closed =
        KernelRules::implies_intr(&premise, KernelRules::reflexive(term).as_kernel()).unwrap();
    let exported = KernelRules::unconstrain_t(&owner, &context, &closed).unwrap();
    let rotated = KernelRules::rotate_rule(&owner, &context, &exported, 1, 1).unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &rotated).unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "rotated_stripped", stripped.try_close().unwrap()).unwrap();
    assert_eq!(token.prop(), rotated.prop());
}
