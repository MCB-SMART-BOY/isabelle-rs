use std::collections::BTreeMap;

use isabelle_kernel::{
    CompositionFlags, CompositionOptions, InstEntry, KernelError, KernelRules, KernelThm, Name,
    PayloadError, ProofContext, RawTerm, Sort, TrustedTheory, Ty, TypeInstantiation, TypeVarId,
    accept_closed_theorem,
};

#[path = "../examples/native_thm/support.rs"]
mod support;

#[test]
fn native_thm_complete_public_consumer_accepts_and_references() -> Result<(), KernelError> {
    // The executable and this test run the same structural assertions at every step.
    support::run_closure()?;
    Ok(())
}

#[test]
fn native_thm_root_bound_rejects_certification() {
    let root = support::create_root().unwrap();
    let context = ProofContext::new(root.snapshot().clone());
    assert!(matches!(context.certify_term(RawTerm::bound(0)), Err(KernelError::UnboundBound(0))));
}

#[test]
fn native_thm_composed_transfer_retains_real_hypothesis_and_rejects_close() {
    let root = support::create_root().unwrap();
    let composed = support::derive_composed_symmetry(&root).unwrap();
    let (child, transferred) = support::transfer_to_child(&root, &composed).unwrap();
    let context = ProofContext::new(child.snapshot().clone());
    assert_eq!(transferred.hyps(), &[context.certify_prop(support::make_premise()).unwrap()]);
    assert_eq!(transferred.prop(), &context.certify_prop(support::make_conclusion()).unwrap());
    assert!(matches!(transferred.try_close(), Err(KernelError::Invariant(_))));
    assert!(child.is_empty());
}

#[test]
fn native_thm_composed_child_cannot_transfer_to_sibling() {
    let root = support::create_root().unwrap();
    let left = root.begin_child("Left");
    let right = root.begin_child("Right");
    let source = support::derive_composed_symmetry(&left).unwrap();
    assert_eq!(source.context(), left.stamp());
    assert!(matches!(
        KernelRules::transfer(&right, &source),
        Err(KernelError::UnknownTheoremDependency)
    ));
}

#[test]
fn native_thm_closed_child_cannot_be_accepted_by_parent() {
    let root = support::create_root().unwrap();
    let composed = support::derive_composed_symmetry(&root).unwrap();
    let (child, transferred) = support::transfer_to_child(&root, &composed).unwrap();
    let context = ProofContext::new(child.snapshot().clone());
    let premise = context.certify_prop(support::make_premise()).unwrap();
    let closed = KernelRules::implies_intr(&premise, &transferred).unwrap().try_close().unwrap();
    assert!(matches!(
        accept_closed_theorem(&root, "wrong_owner", closed),
        Err(KernelError::MixedContext { expected, actual })
            if *expected == root.stamp() && *actual == child.stamp()
    ));
    assert!(root.is_empty());
}

#[test]
fn native_thm_bicompose_flex_survives_transfer_and_hypothesis_discharge() {
    let root = support::create_root().unwrap();
    let context = ProofContext::new(root.snapshot().clone());
    let rule = support::derive_instantiated_congruence(&context).unwrap();
    let p = RawTerm::const_("p", Ty::prop());
    let state = KernelRules::implies_intr(
        &context.certify_prop(p.clone()).unwrap(),
        KernelRules::reflexive(context.certify_term(p.clone()).unwrap()).as_kernel(),
    )
    .unwrap();
    let mut candidate = support::create_empty_candidate();
    candidate.residual_pairs.push((
        context.certify_term(support::make_image_equality()).unwrap(),
        context.certify_term(p.clone()).unwrap(),
    ));
    let composed = KernelRules::bicompose_candidate(
        &root,
        &context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        &rule,
        &state,
        &candidate,
    )
    .unwrap();
    let (child, transferred) = support::transfer_to_child(&root, &composed).unwrap();
    let context = ProofContext::new(child.snapshot().clone());
    let premise = context.certify_prop(support::make_premise()).unwrap();
    let discharged = KernelRules::implies_intr(&premise, &transferred).unwrap();
    assert!(discharged.hyps().is_empty());
    assert_eq!(
        discharged.prop(),
        &context
            .certify_prop(RawTerm::imp(support::make_premise(), RawTerm::eq(p.clone(), p)))
            .unwrap()
    );
    assert!(matches!(
        discharged.try_close(),
        Err(KernelError::TheoremObligations(PayloadError::UnresolvedFlexPairs { pairs: 1 }))
    ));
}

#[test]
fn native_thm_extra_sort_survives_transfer_and_hypothesis_discharge() {
    let root = support::create_root().unwrap();
    let context = ProofContext::new(root.snapshot().clone());
    let variable = RawTerm::var("x", 0, Ty::tvar("a", 0, Sort::empty()));
    let source = KernelRules::reflexive(context.certify_term(variable).unwrap());
    let types = TypeInstantiation::try_new(BTreeMap::from([(
        TypeVarId::new("a", 0, Sort::empty()),
        Ty::prop(),
    )]))
    .unwrap();
    let p = context.certify_term(RawTerm::const_("p", Ty::prop())).unwrap();
    let instantiated = KernelRules::instantiate(
        &context,
        source.as_kernel(),
        &types,
        &[InstEntry::new("x", 0, Ty::prop(), p)],
    )
    .unwrap();
    let premise = context.certify_prop(support::make_premise()).unwrap();
    let weakened = KernelRules::weaken(&premise, &instantiated).unwrap();
    let (child, transferred) = support::transfer_to_child(&root, &weakened).unwrap();
    let context = ProofContext::new(child.snapshot().clone());
    let premise = context.certify_prop(support::make_premise()).unwrap();
    let discharged = KernelRules::implies_intr(&premise, &transferred).unwrap();
    assert!(discharged.hyps().is_empty());
    assert!(matches!(
        discharged.try_close(),
        Err(KernelError::TheoremObligations(PayloadError::ExtraSortHypotheses { sorts: 1 }))
    ));
}

#[test]
fn native_thm_foreign_instantiation_rhs_rejects_at_rule_boundary() {
    let root = support::create_root().unwrap();
    let context = ProofContext::new(root.snapshot().clone());
    let source = support::derive_schematic_congruence(&context).unwrap();
    let child = support::create_child(&root).unwrap();
    let foreign = ProofContext::new(child.snapshot().clone());
    let replacement =
        foreign.certify_term(RawTerm::const_("g", support::make_function_type())).unwrap();
    let entry = InstEntry::new("f", 0, support::make_function_type(), replacement);
    assert!(matches!(
        KernelRules::instantiate(&context, &source, &TypeInstantiation::empty(), &[entry]),
        Err(KernelError::MixedContext { expected, actual })
            if *expected == root.stamp() && *actual == child.stamp()
    ));
}

#[test]
fn native_thm_instantiated_local_free_rejects_at_accepting_replay() {
    let root = support::create_root().unwrap();
    let mut context = ProofContext::new(root.snapshot().clone());
    context.declare_free("local_function", support::make_function_type());
    let source = support::derive_schematic_congruence(&context).unwrap();
    let replacement = context
        .certify_term(RawTerm::free("local_function", support::make_function_type()))
        .unwrap();
    let instantiated = KernelRules::instantiate(
        &context,
        &source,
        &TypeInstantiation::empty(),
        &[InstEntry::new("f", 0, support::make_function_type(), replacement)],
    )
    .unwrap();
    let premise = context.certify_prop(support::make_premise()).unwrap();
    let discharged = KernelRules::implies_intr(&premise, &instantiated).unwrap();
    assert!(discharged.hyps().is_empty());
    assert!(matches!(
        accept_closed_theorem(&root, "unscoped", discharged.try_close().unwrap()),
        Err(KernelError::UndeclaredFree(name)) if name == Name::from("local_function")
    ));
    assert!(root.is_empty());
}

fn accept_exported_local(root: &TrustedTheory, theorem: KernelThm, expected: RawTerm) {
    let child = support::create_child(root).unwrap();
    let transferred = KernelRules::transfer(&child, &theorem).unwrap();
    assert!(transferred.hyps().is_empty());
    let (owner, token) =
        accept_closed_theorem(&child, "exported", transferred.try_close().unwrap()).unwrap();
    let fresh_context = ProofContext::new(owner.snapshot().clone());
    assert_eq!(token.prop().term(), fresh_context.certify_prop(expected).unwrap().term());
    assert!(matches!(
        fresh_context.certify_term(RawTerm::free("local", Ty::prop())),
        Err(KernelError::UndeclaredFree(name)) if name == Name::from("local")
    ));
    assert!(token.dependencies().is_empty());
}

#[test]
fn native_thm_forall_export_transfers_without_publishing_local_free() {
    let root = support::create_root().unwrap();
    let mut context = ProofContext::new(root.snapshot().clone());
    context.declare_free("local", Ty::prop());
    let local = context.certify_term(RawTerm::free("local", Ty::prop())).unwrap();
    let source = KernelRules::reflexive(local.clone());
    let exported = KernelRules::forall_intr(&local, source.as_kernel()).unwrap();
    let expected =
        RawTerm::forall("local", Ty::prop(), RawTerm::eq(RawTerm::bound(0), RawTerm::bound(0)));
    accept_exported_local(&root, exported, expected);
}

#[test]
fn native_thm_abstraction_export_transfers_without_publishing_local_free() {
    let root = support::create_root().unwrap();
    let mut context = ProofContext::new(root.snapshot().clone());
    context.declare_free("local", Ty::prop());
    let local = context.certify_term(RawTerm::free("local", Ty::prop())).unwrap();
    let source = KernelRules::reflexive(local);
    let exported =
        KernelRules::abstraction("local".into(), Ty::prop(), source.as_kernel()).unwrap();
    let identity = RawTerm::abs("local", Ty::prop(), RawTerm::bound(0));
    accept_exported_local(&root, exported, RawTerm::eq(identity.clone(), identity));
}
