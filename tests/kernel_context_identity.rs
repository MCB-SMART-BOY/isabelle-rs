use isabelle_rs::kernel::{
    KernelError, KernelRules, ProofContext, RawTerm, Signature, TheorySnapshot, Ty,
};

fn ty(name: &str) -> Ty {
    Ty::base(name).unwrap()
}

fn signature_with_a() -> Signature {
    Signature::new().extend_const("A", Ty::prop()).unwrap()
}

fn context(theory: TheorySnapshot) -> ProofContext {
    ProofContext::new(theory)
}

fn certified_a(ctx: &ProofContext) -> isabelle_rs::kernel::CProp {
    ctx.certify_prop(RawTerm::const_("A", Ty::prop())).unwrap()
}

#[test]
fn signature_id_is_deterministic_and_order_independent() {
    let first = Signature::new()
        .extend_const("A", Ty::prop())
        .unwrap()
        .extend_const("n", ty("nat"))
        .unwrap();
    let second = Signature::new()
        .extend_const("n", ty("nat"))
        .unwrap()
        .extend_const("A", Ty::prop())
        .unwrap();

    assert_eq!(first.id(), second.id());
    assert_eq!(first, second);

    let changed = Signature::new()
        .extend_const("A", Ty::prop())
        .unwrap()
        .extend_const("n", ty("bool"))
        .unwrap();
    assert_ne!(first.id(), changed.id());
}

#[test]
fn signature_extension_is_immutable_and_duplicates_fail_closed() {
    let parent = signature_with_a();
    let parent_id = parent.id();
    let child = parent.extend_const("B", Ty::prop()).unwrap();

    assert_eq!(parent.id(), parent_id);
    assert_eq!(parent.len(), 1);
    assert!(parent.const_type(&"B".into()).is_none());
    assert_eq!(child.len(), 2);
    assert!(child.const_type(&"B".into()).is_some());

    for duplicate_ty in [Ty::prop(), ty("nat")] {
        let error = parent.extend_const("A", duplicate_ty).unwrap_err();
        assert!(matches!(error, KernelError::DuplicateDeclaration { .. }));
        assert_eq!(parent.id(), parent_id);
        assert_eq!(parent.len(), 1);
    }
}

#[test]
fn untrusted_signature_snapshot_recomputes_and_checks_digest() {
    let expected = Signature::new()
        .extend_const("n", ty("nat"))
        .unwrap()
        .extend_const("A", Ty::prop())
        .unwrap();
    let declarations = vec![("A".into(), Ty::prop()), ("n".into(), ty("nat"))];

    let rebuilt =
        Signature::from_untrusted_snapshot(expected.id().to_bytes(), declarations.clone()).unwrap();
    assert_eq!(rebuilt.id(), expected.id());

    let mut forged_digest = expected.id().to_bytes();
    forged_digest[0] ^= 0xff;
    assert!(matches!(
        Signature::from_untrusted_snapshot(forged_digest, declarations),
        Err(KernelError::SignatureDigestMismatch)
    ));

    assert!(matches!(
        Signature::from_untrusted_snapshot(
            expected.id().to_bytes(),
            vec![("A".into(), Ty::prop()), ("A".into(), Ty::prop())],
        ),
        Err(KernelError::DuplicateDeclaration { .. })
    ));
}

#[test]
fn theory_id_is_deterministic_ancestry_sensitive_and_domain_separated() {
    let signature = signature_with_a();
    let root_a = TheorySnapshot::root("Root", signature.clone());
    let root_b = TheorySnapshot::root("Root", signature.clone());
    assert_eq!(root_a.id(), root_b.id());
    assert_eq!(root_a.stamp(), root_b.stamp());

    let child = root_a.begin_child("Child");
    let independently_rebuilt_child = root_b.begin_child("Child");
    assert_eq!(child.id(), independently_rebuilt_child.id());
    assert_ne!(child.id(), root_a.id());
    assert_eq!(child.signature().id(), root_a.signature().id());
    assert_ne!(signature.id().to_bytes(), root_a.id().to_bytes());

    let other_child = root_a.begin_child("OtherChild");
    assert_ne!(child.id(), other_child.id());
    assert!(root_a.is_ancestor_of(&child));
    assert!(!child.is_ancestor_of(&root_a));
}

#[test]
fn theory_id_commits_to_extension_history_even_when_signatures_match() {
    let root = TheorySnapshot::root("Root", Signature::new());
    let a_then_b =
        root.extend_const("A", Ty::prop()).unwrap().extend_const("B", Ty::prop()).unwrap();
    let b_then_a =
        root.extend_const("B", Ty::prop()).unwrap().extend_const("A", Ty::prop()).unwrap();

    assert_eq!(a_then_b.signature().id(), b_then_a.signature().id());
    assert_ne!(a_then_b.id(), b_then_a.id());
}

#[test]
fn failed_theory_extension_preserves_parent_identity_and_signature() {
    let parent = TheorySnapshot::root("Root", signature_with_a());
    let parent_id = parent.id();
    let signature_id = parent.signature().id();

    let error = parent.extend_const("A", ty("nat")).unwrap_err();

    assert!(matches!(error, KernelError::DuplicateDeclaration { .. }));
    assert_eq!(parent.id(), parent_id);
    assert_eq!(parent.signature().id(), signature_id);
    assert_eq!(parent.signature().const_type(&"A".into()), Some(&Ty::prop()));
}

#[test]
fn sibling_theory_extensions_are_isolated() {
    let parent = TheorySnapshot::root("Root", signature_with_a());
    let left = parent.extend_const("L", Ty::prop()).unwrap();
    let right = parent.extend_const("R", Ty::prop()).unwrap();

    assert_ne!(left.id(), right.id());
    assert!(parent.signature().const_type(&"L".into()).is_none());
    assert!(parent.signature().const_type(&"R".into()).is_none());
    assert!(left.signature().const_type(&"L".into()).is_some());
    assert!(left.signature().const_type(&"R".into()).is_none());
    assert!(right.signature().const_type(&"L".into()).is_none());
    assert!(right.signature().const_type(&"R".into()).is_some());
}

#[test]
fn same_signature_in_distinct_sibling_theories_has_distinct_contexts() {
    let parent = TheorySnapshot::root("Root", signature_with_a());
    let left = parent.begin_child("Left");
    let right = parent.begin_child("Right");

    assert_eq!(left.signature().id(), right.signature().id());
    assert_ne!(left.id(), right.id());
    assert_ne!(left.stamp(), right.stamp());
}

#[test]
fn independently_rebuilt_identical_contexts_interoperate() {
    let left_ctx = context(TheorySnapshot::root("Root", signature_with_a()));
    let right_ctx = context(TheorySnapshot::root("Root", signature_with_a()));
    let left_a = certified_a(&left_ctx);
    let right_assumption = KernelRules::assume(certified_a(&right_ctx)).into_kernel();

    let identity = KernelRules::implies_intr(&left_a, &right_assumption).unwrap();
    assert!(identity.hyps().is_empty());
    assert_eq!(identity.context(), left_ctx.stamp());
}

#[test]
fn same_text_under_wrong_signature_is_rejected_before_logical_matching() {
    let narrow = signature_with_a();
    let wide = narrow.extend_const("B", Ty::prop()).unwrap();
    let narrow_ctx = context(TheorySnapshot::root("Root", narrow));
    let wide_ctx = context(TheorySnapshot::root("Root", wide));
    let narrow_a = KernelRules::assume(certified_a(&narrow_ctx)).into_kernel();
    let wide_a = KernelRules::assume(certified_a(&wide_ctx)).into_kernel();

    let error = KernelRules::transitive(&narrow_a, &wide_a).unwrap_err();
    assert!(matches!(error, KernelError::MixedContext { .. }));
}

#[test]
fn same_text_under_different_theory_ancestry_is_rejected() {
    let root = TheorySnapshot::root("Root", signature_with_a());
    let left_ctx = context(root.begin_child("Left"));
    let right_ctx = context(root.begin_child("Right"));
    let left_a = KernelRules::assume(certified_a(&left_ctx)).into_kernel();
    let right_a = KernelRules::assume(certified_a(&right_ctx)).into_kernel();

    let error = KernelRules::implies_elim(&left_a, &right_a).unwrap_err();
    assert!(matches!(error, KernelError::MixedContext { .. }));
}

#[test]
fn mixed_context_substitution_is_rejected_before_rule_shape_checks() {
    let root = TheorySnapshot::root("Root", signature_with_a());
    let left_ctx = context(root.begin_child("Left"));
    let right_ctx = context(root.begin_child("Right"));
    let alleged_equality = KernelRules::assume(certified_a(&left_ctx)).into_kernel();
    let goal = KernelRules::assume(certified_a(&right_ctx)).into_kernel();

    let error = KernelRules::subst_premise(&alleged_equality, &goal, 0).unwrap_err();
    assert!(matches!(error, KernelError::MixedContext { .. }));
}

#[test]
fn stale_parent_certified_object_is_rejected_in_child_context() {
    let parent_theory = TheorySnapshot::root("Root", signature_with_a());
    let parent_ctx = context(parent_theory.clone());
    let stale_parent_a = certified_a(&parent_ctx);

    let child_ctx = context(parent_theory.begin_child("Child"));
    let child_assumption = KernelRules::assume(certified_a(&child_ctx)).into_kernel();
    let error = KernelRules::implies_intr(&stale_parent_a, &child_assumption).unwrap_err();

    assert!(matches!(error, KernelError::MixedContext { .. }));
}

#[test]
fn closed_theorem_records_exact_proved_in_theory() {
    let parent = TheorySnapshot::root("Root", signature_with_a());
    let ctx = context(parent.clone());
    let a = certified_a(&ctx);
    let assumed = KernelRules::assume(a.clone()).into_kernel();
    let identity = KernelRules::implies_intr(&a, &assumed).unwrap();
    let closed = identity.try_close().unwrap();

    assert_eq!(closed.as_kernel().proved_in(), parent.id());
    assert_eq!(closed.context(), parent.stamp());

    let child = parent.begin_child("LaterExtension");
    assert_ne!(closed.as_kernel().proved_in(), child.id());
    assert_eq!(closed.as_kernel().proved_in(), parent.id());
}
