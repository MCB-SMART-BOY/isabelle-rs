use std::collections::{BTreeMap, BTreeSet};

use isabelle_kernel::{
    AxiomSchema, CompositionCandidate, CompositionFlags, CompositionOptions, EmptyClassDeclCert,
    InstEntry, KernelError, KernelRules, LogicBasis, Name, PayloadError, ProofContext, RawTerm,
    SemanticArityCert, Signature, Sort, TrustedTheory, Ty, TypeInstantiation, TypeVarId,
    accept_closed_theorem,
};

fn create_owner() -> TrustedTheory {
    TrustedTheory::root(
        "ScopeExport",
        Signature::new().install_empty_class(EmptyClassDeclCert::hol_type()).unwrap(),
    )
}

fn selected(names: &[&str]) -> BTreeSet<Name> {
    names.iter().map(|name| Name::from(*name)).collect()
}

fn create_local_proof() -> (TrustedTheory, ProofContext, Ty) {
    let owner = create_owner();
    let mut context = ProofContext::new(owner.snapshot().clone());
    let fixed = context.declare_type_free("a", Sort::empty()).unwrap();
    context.declare_free("x", fixed.clone());
    (owner, context, fixed)
}

#[test]
fn export_scope_sequential_type_then_term_generalization_accepts() {
    let (owner, context, fixed) = create_local_proof();
    let source = KernelRules::reflexive(context.certify_term(RawTerm::free("x", fixed)).unwrap());
    let typed =
        KernelRules::generalize(source.as_kernel(), &selected(&["a"]), &selected(&[]), 0).unwrap();
    let generalized =
        KernelRules::generalize(&typed, &selected(&[]), &selected(&["x"]), 1).unwrap();
    assert_eq!(generalized.context(), context.stamp());
    assert!(matches!(
        generalized.clone().try_close(),
        Err(KernelError::LocalTypeScopeEscape { .. })
    ));
    let expected = RawTerm::eq(
        RawTerm::var("x", 1, Ty::tvar("a", 0, Sort::empty())),
        RawTerm::var("x", 1, Ty::tvar("a", 0, Sort::empty())),
    );
    assert_eq!(generalized.prop().term(), context.certify_prop(expected).unwrap().term());
    let exported = KernelRules::export_scope(&owner, &context, &generalized).unwrap();
    assert!(exported.hyps().is_empty());
    assert_eq!(exported.context(), owner.stamp());
    assert_eq!(exported.prop().term(), generalized.prop().term());
    let (_, accepted) =
        accept_closed_theorem(&owner, "sequential", exported.try_close().unwrap()).unwrap();
    assert!(accepted.dependencies().is_empty());
    assert_eq!(accepted.prop().term(), generalized.prop().term());
}

#[test]
fn export_scope_unbound_local_type_or_term_rejects() {
    let (owner, context, fixed) = create_local_proof();
    let source = KernelRules::reflexive(context.certify_term(RawTerm::free("x", fixed)).unwrap());
    let only_type =
        KernelRules::generalize(source.as_kernel(), &selected(&["a"]), &selected(&[]), 0).unwrap();
    assert!(matches!(
        KernelRules::export_scope(&owner, &context, &only_type),
        Err(KernelError::UndeclaredFree(name)) if name == Name::from("x"),
    ));
    let only_term =
        KernelRules::generalize(source.as_kernel(), &selected(&[]), &selected(&["x"]), 0).unwrap();
    assert!(matches!(
        KernelRules::export_scope(&owner, &context, &only_term),
        Err(KernelError::UndeclaredTypeFree { .. }),
    ));
}

#[test]
fn export_scope_independent_same_name_scope_rejects() {
    let (owner, left, fixed) = create_local_proof();
    let source = KernelRules::reflexive(left.certify_term(RawTerm::free("x", fixed)).unwrap());
    let mut right = ProofContext::new(owner.snapshot().clone());
    right.declare_type_free("a", Sort::empty()).unwrap();
    right.declare_free("x", Ty::tfree("a", Sort::empty()));
    assert_ne!(left.stamp(), right.stamp());
    assert!(matches!(
        KernelRules::export_scope(&owner, &right, source.as_kernel()),
        Err(KernelError::MixedContext { .. }),
    ));
}

fn create_proof_only_source(
    context: &ProofContext,
    fixed: Ty,
    basis: &LogicBasis,
) -> isabelle_kernel::KernelThm {
    let y = RawTerm::free("y", fixed.clone());
    let a = context.certify_prop(RawTerm::eq(y.clone(), y)).unwrap();
    let p = RawTerm::const_("P", Ty::prop());
    let b = context.certify_prop(RawTerm::eq(p.clone(), p.clone())).unwrap();
    let b_proof = isabelle_kernel::theorem_builder::axiom_theorem(
        context,
        basis,
        "closed_b".into(),
        TypeInstantiation::empty(),
        vec![],
        RawTerm::eq(p.clone(), p),
    )
    .unwrap();
    let weakened = KernelRules::weaken(&a, &b_proof).unwrap();
    let conditional = KernelRules::implies_intr(&a, &weakened).unwrap();
    let a_proof = KernelRules::reflexive(context.certify_term(RawTerm::free("y", fixed)).unwrap());
    let result = KernelRules::implies_elim(&conditional, a_proof.as_kernel()).unwrap();
    assert!(result.hyps().is_empty());
    assert_eq!(result.prop(), &b);
    result
}

#[test]
fn export_scope_proof_only_local_parameter_survives_index_transfer_and_composition() {
    let signature = Signature::new().extend_const("P", Ty::prop()).unwrap();
    let p = RawTerm::const_("P", Ty::prop());
    let basis = LogicBasis::try_new(
        vec![],
        vec![AxiomSchema { name: "closed_b".into(), prop: RawTerm::eq(p.clone(), p) }],
    )
    .unwrap();
    let root = TrustedTheory::with_basis("ProofOnlyExport", signature, &basis).unwrap();
    let mut local = ProofContext::new(root.snapshot().clone());
    let fixed = local.declare_type_free("a", Sort::empty()).unwrap();
    local.declare_free("y", fixed.clone());
    let source = create_proof_only_source(&local, fixed, &basis);
    let expected = source.prop().term().clone();
    assert!(matches!(source.clone().try_close(), Err(KernelError::LocalTypeScopeEscape { .. })));
    let exported = KernelRules::export_scope(&root, &local, &source).unwrap();
    let root_context = ProofContext::new(root.snapshot().clone());
    let renamed = KernelRules::incr_indexes(&root, &root_context, &exported, 2).unwrap();
    let child = root.begin_child("child");
    let transferred = KernelRules::transfer(&child, &renamed).unwrap();
    let child_context = ProofContext::new(child.snapshot().clone());
    let p = RawTerm::const_("P", Ty::prop());
    let premise = child_context.certify_prop(RawTerm::eq(p.clone(), p)).unwrap();
    let state = KernelRules::implies_intr(&premise, &transferred).unwrap();
    let candidate = CompositionCandidate {
        type_inst: TypeInstantiation::empty(),
        rule_subst: vec![],
        state_subst: vec![],
        residual_pairs: vec![],
        elimination_choice: None,
    };
    let composed = KernelRules::bicompose_candidate(
        &child,
        &child_context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        &transferred,
        &state,
        &candidate,
    )
    .unwrap();
    assert!(composed.hyps().is_empty());
    assert_eq!(composed.prop().term(), &expected);
    assert!(matches!(
        composed.clone().try_close(),
        Err(KernelError::TheoremObligations(PayloadError::ExtraSortHypotheses { sorts: 1 })),
    ));
    let stripped = KernelRules::strip_shyps(&child, &child_context, &composed).unwrap();
    let (_, accepted) =
        accept_closed_theorem(&child, "proof_only", stripped.try_close().unwrap()).unwrap();
    assert_eq!(accepted.dependencies().len(), 1);
    assert_eq!(accepted.prop().term(), &expected);
}

#[test]
fn export_scope_lawful_flex_survives_generalize_index_and_transfer() {
    let owner =
        TrustedTheory::root("FlexExport", Signature::new().extend_const("P", Ty::prop()).unwrap());
    let context = ProofContext::new(owner.snapshot().clone());
    let p = RawTerm::const_("P", Ty::prop());
    let eq = RawTerm::eq(p.clone(), p.clone());
    let assumption = context.certify_prop(p.clone()).unwrap();
    let rule = KernelRules::implies_intr(
        &assumption,
        KernelRules::assume(assumption.clone()).unwrap().as_kernel(),
    )
    .unwrap();
    let goal = context.certify_prop(RawTerm::imp(eq.clone(), eq.clone())).unwrap();
    let state = KernelRules::implies_intr(
        &goal,
        KernelRules::reflexive(context.certify_term(p.clone()).unwrap()).as_kernel(),
    )
    .unwrap();
    let candidate = CompositionCandidate {
        type_inst: TypeInstantiation::empty(),
        rule_subst: vec![],
        state_subst: vec![],
        residual_pairs: vec![(
            context.certify_term(p).unwrap(),
            context.certify_term(eq.clone()).unwrap(),
        )],
        elimination_choice: None,
    };
    let flex = KernelRules::bicompose_candidate(
        &owner,
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
    assert!(flex.hyps().is_empty());
    let generalized =
        KernelRules::generalize(&flex, &selected(&["absent"]), &selected(&[]), 0).unwrap();
    let exported = KernelRules::export_scope(&owner, &context, &generalized).unwrap();
    let indexed = KernelRules::incr_indexes(&owner, &context, &exported, 2).unwrap();
    let descendant = owner.begin_child("flex_child");
    let transferred = KernelRules::transfer(&descendant, &indexed).unwrap();
    let descendant_context = ProofContext::new(descendant.snapshot().clone());
    assert_eq!(transferred.prop().term(), descendant_context.certify_prop(eq).unwrap().term());
    assert!(transferred.hyps().is_empty());
    assert!(matches!(
        transferred.try_close(),
        Err(KernelError::TheoremObligations(PayloadError::UnresolvedFlexPairs { pairs: 1 })),
    ));
}

#[test]
fn export_scope_lawful_sort_constraint_survives_index_and_transfer() {
    let owner =
        create_owner().install_semantic_arity(SemanticArityCert::FunctionTypeArityCert).unwrap();
    let context = ProofContext::new(owner.snapshot().clone());
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let beta = Ty::tvar("b", 0, Sort::hol_type());
    let source = KernelRules::reflexive(context.certify_term(RawTerm::var("x", 0, alpha)).unwrap());
    let instantiated = KernelRules::instantiate(
        &context,
        source.as_kernel(),
        &TypeInstantiation::try_new(BTreeMap::from([(
            TypeVarId::new("a", 0, Sort::hol_type()),
            Ty::arrow(beta.clone(), beta),
        )]))
        .unwrap(),
        &[],
    )
    .unwrap();
    assert!(instantiated.hyps().is_empty());
    let generalized =
        KernelRules::generalize(&instantiated, &selected(&["absent"]), &selected(&[]), 1).unwrap();
    let exported = KernelRules::export_scope(&owner, &context, &generalized).unwrap();
    let indexed = KernelRules::incr_indexes(&owner, &context, &exported, 2).unwrap();
    let child = owner.begin_child("constraint_child");
    let transferred = KernelRules::transfer(&child, &indexed).unwrap();
    let child_context = ProofContext::new(child.snapshot().clone());
    let renamed_type = Ty::tvar("b", 2, Sort::hol_type());
    let renamed_x = RawTerm::var("x", 2, Ty::arrow(renamed_type.clone(), renamed_type));
    assert_eq!(
        transferred.prop().term(),
        child_context.certify_prop(RawTerm::eq(renamed_x.clone(), renamed_x)).unwrap().term()
    );
    assert!(transferred.hyps().is_empty());
    assert!(matches!(
        transferred.try_close(),
        Err(KernelError::TheoremObligations(PayloadError::UnresolvedSortConstraints {
            constraints: 1
        })),
    ));
}

#[test]
fn export_scope_lawful_extra_sort_survives_index_and_transfer() {
    let owner = create_owner().extend_const("P", Ty::prop()).unwrap();
    let context = ProofContext::new(owner.snapshot().clone());
    let alpha = Ty::tvar("a", 0, Sort::empty());
    let source = KernelRules::reflexive(context.certify_term(RawTerm::var("x", 0, alpha)).unwrap());
    let replacement = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let instantiated = KernelRules::instantiate(
        &context,
        source.as_kernel(),
        &TypeInstantiation::try_new(BTreeMap::from([(
            TypeVarId::new("a", 0, Sort::empty()),
            Ty::prop(),
        )]))
        .unwrap(),
        &[InstEntry::new("x", 0, Ty::prop(), replacement)],
    )
    .unwrap();
    assert!(instantiated.hyps().is_empty());
    let generalized =
        KernelRules::generalize(&instantiated, &selected(&["absent"]), &selected(&[]), 1).unwrap();
    let exported = KernelRules::export_scope(&owner, &context, &generalized).unwrap();
    let indexed = KernelRules::incr_indexes(&owner, &context, &exported, 2).unwrap();
    let child = owner.begin_child("sort_child");
    let transferred = KernelRules::transfer(&child, &indexed).unwrap();
    let child_context = ProofContext::new(child.snapshot().clone());
    let p = RawTerm::const_("P", Ty::prop());
    assert_eq!(
        transferred.prop().term(),
        child_context.certify_prop(RawTerm::eq(p.clone(), p)).unwrap().term()
    );
    assert!(transferred.hyps().is_empty());
    assert!(matches!(
        transferred.try_close(),
        Err(KernelError::TheoremObligations(PayloadError::ExtraSortHypotheses { sorts: 1 })),
    ));
}

#[test]
fn generalize_same_name_distinct_typed_lexical_binders_do_not_leak() {
    let owner = TrustedTheory::root(
        "LexicalNames",
        Signature::new().extend_const("P", Ty::prop()).unwrap(),
    );
    let mut context = ProofContext::new(owner.snapshot().clone());
    let p = RawTerm::const_("P", Ty::prop());
    let reflexive = KernelRules::reflexive(context.certify_term(p.clone()).unwrap());
    context.declare_free("x", Ty::prop());
    let first_binder = context.certify_term(RawTerm::free("x", Ty::prop())).unwrap();
    let first = KernelRules::forall_intr(&first_binder, reflexive.as_kernel()).unwrap();
    let first =
        KernelRules::forall_elim(&first, &context.certify_term(p.clone()).unwrap()).unwrap();
    let function_ty = Ty::arrow(Ty::prop(), Ty::prop());
    context.declare_free("x", function_ty.clone());
    let second_binder = context.certify_term(RawTerm::free("x", function_ty)).unwrap();
    let second = KernelRules::forall_intr(&second_binder, reflexive.as_kernel()).unwrap();
    let identity = context.certify_term(RawTerm::abs("z", Ty::prop(), RawTerm::bound(0))).unwrap();
    let second = KernelRules::forall_elim(&second, &identity).unwrap();
    let combined = KernelRules::transitive(&first, &second).unwrap();
    let expected = context.certify_prop(RawTerm::eq(p.clone(), p)).unwrap();
    assert_eq!(combined.prop(), &expected);
    let generalized =
        KernelRules::generalize(&combined, &selected(&[]), &selected(&["x"]), 0).unwrap();
    assert_eq!(generalized.prop(), &expected);
    let exported = KernelRules::export_scope(&owner, &context, &generalized).unwrap();
    let (_, accepted) =
        accept_closed_theorem(&owner, "lexical_binders", exported.try_close().unwrap()).unwrap();
    assert!(accepted.dependencies().is_empty());
    assert_eq!(accepted.prop().term(), expected.term());
}

#[test]
fn export_scope_local_type_only_in_sort_constraint_rejects() {
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const("P", Ty::prop())
        .unwrap();
    let owner = TrustedTheory::root("HiddenConstraintScope", signature);
    let mut context = ProofContext::new(owner.snapshot().clone());
    let local = context.declare_type_free("a", Sort::hol_type()).unwrap();
    let p = RawTerm::const_("P", Ty::prop());
    let source = KernelRules::reflexive(context.certify_term(p.clone()).unwrap());
    let instantiated = KernelRules::instantiate(
        &context,
        source.as_kernel(),
        &TypeInstantiation::try_new(BTreeMap::from([(
            TypeVarId::new("hidden", 0, Sort::hol_type()),
            local,
        )]))
        .unwrap(),
        &[],
    )
    .unwrap();
    assert!(instantiated.hyps().is_empty());
    assert_eq!(instantiated.prop().term(), source.as_kernel().prop().term());
    assert!(matches!(
        KernelRules::export_scope(&owner, &context, &instantiated),
        Err(KernelError::UndeclaredTypeFree { name, .. }) if name == Name::from("a"),
    ));
}
