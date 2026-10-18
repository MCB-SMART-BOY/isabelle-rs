use std::collections::{BTreeMap, BTreeSet};

use crate::{
    AxiomDependencyId, AxiomSchema, DependencyKind, Derivation, EmptyClassDeclCert, InstEntry,
    KernelError, KernelRules, KernelThm, LogicBasis, Name, ProofContext, RawTerm,
    SemanticArityCert, Signature, Sort, TrustedTheorem, TrustedTheory, Ty, TypeInstantiation,
    TypeVarId, accept_closed_theorem, obligations::ProofPayload, theory::DependencySet,
};

fn names(selected: &[&str]) -> BTreeSet<Name> {
    selected.iter().map(|name| Name::from(*name)).collect()
}

fn create_scope() -> (TrustedTheory, ProofContext, KernelThm) {
    let owner = TrustedTheory::root(
        "ReplayVariableAttacks",
        Signature::new().extend_const("P", Ty::prop()).unwrap(),
    );
    let mut context = ProofContext::new(owner.snapshot().clone());
    let fixed = context.declare_type_free("a", Sort::empty()).unwrap();
    context.declare_free("x", fixed.clone());
    let source = KernelRules::reflexive(context.certify_term(RawTerm::free("x", fixed)).unwrap());
    let typed =
        KernelRules::generalize(source.as_kernel(), &names(&["a"]), &names(&[]), 0).unwrap();
    let generalized = KernelRules::generalize(&typed, &names(&[]), &names(&["x"]), 1).unwrap();
    (owner, context, generalized)
}

fn replace_derivation(source: &KernelThm, derivation: Derivation) -> KernelThm {
    KernelThm::new_with_payload(
        source.hyps().to_vec(),
        source.prop().clone(),
        source.payload().clone(),
        derivation,
    )
}

fn accepts_replay(owner: &TrustedTheory, theorem: KernelThm) -> Result<(), KernelError> {
    accept_closed_theorem(owner, "tampered", theorem.try_close()?).map(|_| ())
}

#[test]
fn generalize_forged_source_frees_or_index_rejected_at_export() {
    let (owner, context, source) = create_scope();
    let Derivation::Generalize { type_names, term_names, index, source_frees, premise } =
        source.derivation()
    else {
        panic!("fixture must end with generalization");
    };
    let make_forged = |source_frees: Vec<(Name, Ty)>, index| {
        replace_derivation(
            &source,
            Derivation::Generalize {
                type_names: type_names.clone(),
                term_names: term_names.clone(),
                index,
                source_frees,
                premise: premise.clone(),
            },
        )
    };
    for forged_keys in [
        vec![],
        vec![("x".into(), Ty::prop())],
        vec![("extra".into(), Ty::prop()), ("x".into(), Ty::tvar("a", 0, Sort::empty()))],
    ] {
        assert_eq!(
            KernelRules::export_scope(&owner, &context, &make_forged(forged_keys, *index))
                .unwrap_err(),
            KernelError::AcceptanceReplayMismatch
        );
    }
    let changed_index = make_forged(source_frees.clone(), index + 1);
    assert_eq!(
        KernelRules::export_scope(&owner, &context, &changed_index).unwrap_err(),
        KernelError::AcceptanceReplayMismatch
    );
}

#[test]
fn export_scope_forged_capsule_or_source_rejected_at_acceptance() {
    let (owner, context, generalized) = create_scope();
    let exported = KernelRules::export_scope(&owner, &context, &generalized).unwrap();
    let mut independent = ProofContext::new(owner.snapshot().clone());
    independent.declare_type_free("a", Sort::empty()).unwrap();
    independent.declare_free("x", Ty::tfree("a", Sort::empty()));
    assert_ne!(context.stamp(), independent.stamp());
    let Derivation::ExportScope { premise, .. } = exported.derivation() else {
        panic!("fixture must end with export");
    };
    let forged = replace_derivation(
        &exported,
        Derivation::ExportScope { scope: independent.snapshot_scope(), premise: premise.clone() },
    );
    assert!(matches!(accepts_replay(&owner, forged), Err(KernelError::MixedContext { .. })));
    let alternate =
        KernelRules::reflexive(context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap());
    let forged = replace_derivation(
        &exported,
        Derivation::ExportScope {
            scope: context.snapshot_scope(),
            premise: Box::new(alternate.into_kernel()),
        },
    );
    assert_eq!(accepts_replay(&owner, forged).unwrap_err(), KernelError::AcceptanceReplayMismatch);
}

#[test]
fn generalize_tampered_statement_hypotheses_or_mode_rejected() {
    let (owner, context, source) = create_scope();
    let exported = KernelRules::export_scope(&owner, &context, &source).unwrap();
    let original = exported.derivation().clone();
    let owner_context = ProofContext::new(owner.snapshot().clone());
    let other_prop = owner_context.certify_prop(RawTerm::const_("P", Ty::prop())).unwrap();
    let altered_prop = owner_context
        .certify_prop(RawTerm::eq(
            RawTerm::var("different", 1, Ty::tvar("a", 0, Sort::empty())),
            RawTerm::var("different", 1, Ty::tvar("a", 0, Sort::empty())),
        ))
        .unwrap();
    let forged_prop = KernelThm::new_with_payload(
        vec![],
        altered_prop,
        exported.payload().clone(),
        original.clone(),
    );
    assert_eq!(
        accepts_replay(&owner, forged_prop).unwrap_err(),
        KernelError::AcceptanceReplayMismatch
    );
    let forged_hyp = KernelThm::new_with_payload(
        vec![other_prop],
        exported.prop().clone(),
        exported.payload().clone(),
        original.clone(),
    );
    let mut dependencies = DependencySet::empty();
    assert_eq!(
        super::replay_source_in(&owner, &owner_context, &forged_hyp, &mut dependencies)
            .unwrap_err(),
        KernelError::AcceptanceReplayMismatch
    );
    let forged_mode = ProofPayload::from_sort_export(exported.prop(), exported.payload()).unwrap();
    let forged_payload =
        KernelThm::new_with_payload(vec![], exported.prop().clone(), forged_mode, original);
    assert_eq!(
        accepts_replay(&owner, forged_payload).unwrap_err(),
        KernelError::AcceptanceReplayMismatch
    );
}

#[test]
fn export_scope_forged_flex_pairs_rejected() {
    let (owner, context, _) = create_scope();
    let source =
        KernelRules::reflexive(context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap())
            .into_kernel();
    let endpoint = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let flex_payload = ProofPayload::with_residual_flex(
        source.payload(),
        &[(endpoint.clone(), endpoint)],
        source.hyps(),
        source.prop(),
    );
    let forged_flex = KernelThm::new_with_payload(
        vec![],
        source.prop().clone(),
        flex_payload,
        source.derivation().clone(),
    );
    assert_eq!(
        KernelRules::export_scope(&owner, &context, &forged_flex).unwrap_err(),
        KernelError::AcceptanceReplayMismatch
    );
}

#[test]
fn export_scope_forged_sort_constraints_rejected() {
    let (owner, context, _) = create_scope();
    let source =
        KernelRules::reflexive(context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap())
            .into_kernel();

    let instantiation = TypeInstantiation::try_new(BTreeMap::from([(
        TypeVarId::new("z", 0, Sort::hol_type()),
        Ty::prop(),
    )]))
    .unwrap();
    let constraint_payload = ProofPayload::instantiate(
        source.payload(),
        &instantiation,
        &[],
        source.hyps(),
        source.prop(),
    )
    .unwrap();
    assert!(!constraint_payload.sort_obligations().is_empty());
    let forged_constraint = KernelThm::new_with_payload(
        vec![],
        source.prop().clone(),
        constraint_payload,
        source.derivation().clone(),
    );
    assert_eq!(
        KernelRules::export_scope(&owner, &context, &forged_constraint).unwrap_err(),
        KernelError::AcceptanceReplayMismatch
    );
}

#[test]
fn incr_indexes_forged_flex_pairs_rejected() {
    let (owner, context, generalized) = create_scope();

    let exported = KernelRules::export_scope(&owner, &context, &generalized).unwrap();
    let owner_context = ProofContext::new(owner.snapshot().clone());
    let corrupted = KernelThm::new_with_payload(
        vec![],
        exported.prop().clone(),
        ProofPayload::with_residual_flex(
            exported.payload(),
            &[(
                owner_context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap(),
                owner_context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap(),
            )],
            exported.hyps(),
            exported.prop(),
        ),
        exported.derivation().clone(),
    );
    assert_eq!(
        KernelRules::incr_indexes(&owner, &owner_context, &corrupted, 2).unwrap_err(),
        KernelError::AcceptanceReplayMismatch
    );
}

fn instantiate_in_branch(
    schema_owner: &TrustedTheory,
    generic: &TrustedTheorem,
    branch_name: &str,
    type_name: &str,
    constant_name: &str,
) -> TrustedTheorem {
    let branch_type = Ty::apply(type_name, vec![]).unwrap();
    let branch = schema_owner.extend_const(constant_name, branch_type.clone()).unwrap();
    let context = ProofContext::new(branch.snapshot().clone());
    let theorem_ref = KernelRules::theorem_ref(&branch, generic).unwrap();
    let value = context.certify_term(RawTerm::const_(constant_name, branch_type.clone())).unwrap();
    let instance = KernelRules::instantiate(
        &context,
        theorem_ref.as_kernel(),
        &TypeInstantiation::try_new(BTreeMap::from([(
            TypeVarId::new("a", 0, Sort::empty()),
            branch_type.clone(),
        )]))
        .unwrap(),
        &[InstEntry::new("x", 1, branch_type.clone(), value)],
    )
    .unwrap();
    let expected = context
        .certify_prop(RawTerm::eq(
            RawTerm::const_(constant_name, branch_type.clone()),
            RawTerm::const_(constant_name, branch_type),
        ))
        .unwrap();
    assert_eq!(instance.prop(), &expected);
    let closed =
        KernelRules::strip_shyps(&branch, &context, &instance).unwrap().try_close().unwrap();
    let (accepted_owner, token) = accept_closed_theorem(&branch, branch_name, closed).unwrap();
    assert_eq!(token.prop().term(), expected.term());
    assert_eq!(
        token.dependencies().as_sorted_entries(),
        vec![(DependencyKind::Theorem, generic.id().to_bytes())]
    );
    let referenced = KernelRules::theorem_ref(&accepted_owner, &token).unwrap();
    let (_, reaccepted) =
        accept_closed_theorem(&accepted_owner, format!("{branch_name}_again"), referenced).unwrap();
    assert_eq!(reaccepted.prop().term(), expected.term());
    assert_eq!(
        reaccepted.dependencies().as_sorted_entries(),
        vec![(DependencyKind::Theorem, token.id().to_bytes())]
    );
    token
}

#[test]
fn generic_export_two_type_instances_record_exact_direct_dependencies() {
    let signature = Signature::new()
        .extend_type_constructor("left_ty", 0)
        .unwrap()
        .extend_type_constructor("right_ty", 0)
        .unwrap();
    let root = TrustedTheory::root("TwoTypeReplayDependencies", signature);
    let mut context = ProofContext::new(root.snapshot().clone());
    let fixed = context.declare_type_free("a", Sort::empty()).unwrap();
    context.declare_free("x", fixed.clone());
    let source = KernelRules::reflexive(context.certify_term(RawTerm::free("x", fixed)).unwrap());
    let typed =
        KernelRules::generalize(source.as_kernel(), &names(&["a"]), &names(&[]), 0).unwrap();
    let generalized = KernelRules::generalize(&typed, &names(&[]), &names(&["x"]), 1).unwrap();
    let exported = KernelRules::export_scope(&root, &context, &generalized).unwrap();
    let (schema_owner, generic) =
        accept_closed_theorem(&root, "generic_identity", exported.try_close().unwrap()).unwrap();
    assert!(generic.dependencies().as_sorted_entries().is_empty());
    let left = instantiate_in_branch(&schema_owner, &generic, "left_identity", "left_ty", "p_left");
    let right =
        instantiate_in_branch(&schema_owner, &generic, "right_identity", "right_ty", "p_right");
    let left_owner =
        schema_owner.extend_const("p_left", Ty::apply("left_ty", vec![]).unwrap()).unwrap();
    let right_owner =
        schema_owner.extend_const("p_right", Ty::apply("right_ty", vec![]).unwrap()).unwrap();
    assert!(matches!(
        KernelRules::theorem_ref(&left_owner, &right),
        Err(KernelError::UnknownTheoremDependency)
    ));
    assert!(matches!(
        KernelRules::theorem_ref(&right_owner, &left),
        Err(KernelError::UnknownTheoremDependency)
    ));
}

#[test]
fn export_scope_proof_only_axiom_keeps_exact_dependency() {
    let p = RawTerm::const_("P", Ty::prop());
    let b = RawTerm::eq(p.clone(), p.clone());
    let schema = AxiomSchema { name: "b_axiom".into(), prop: b.clone() };
    let basis = LogicBasis::try_new(vec![], vec![schema.clone()]).unwrap();
    let owner = TrustedTheory::with_basis(
        "LocalAxiomDependency",
        Signature::new().extend_const("P", Ty::prop()).unwrap(),
        &basis,
    )
    .unwrap();
    let mut local = ProofContext::new(owner.snapshot().clone());
    let fixed = local.declare_type_free("a", Sort::empty()).unwrap();
    local.declare_free("y", fixed.clone());
    let y = RawTerm::free("y", fixed);
    let a = local.certify_prop(RawTerm::eq(y.clone(), y.clone())).unwrap();
    let b_proof = crate::theorem_builder::axiom_theorem(
        &local,
        &basis,
        "b_axiom".into(),
        TypeInstantiation::empty(),
        vec![],
        b.clone(),
    )
    .unwrap();
    let conditional =
        KernelRules::implies_intr(&a, &KernelRules::weaken(&a, &b_proof).unwrap()).unwrap();
    let premise = KernelRules::reflexive(local.certify_term(y).unwrap());
    let source = KernelRules::implies_elim(&conditional, premise.as_kernel()).unwrap();
    assert!(source.hyps().is_empty());
    let exported = KernelRules::export_scope(&owner, &local, &source).unwrap();
    let owner_context = ProofContext::new(owner.snapshot().clone());
    let indexed = KernelRules::incr_indexes(&owner, &owner_context, &exported, 2).unwrap();
    let descendant = owner.begin_child("downstream");
    let transferred = KernelRules::transfer(&descendant, &indexed).unwrap();
    let context = ProofContext::new(descendant.snapshot().clone());
    let stripped = KernelRules::strip_shyps(&descendant, &context, &transferred).unwrap();
    let (_, accepted) =
        accept_closed_theorem(&descendant, "axiom_export", stripped.try_close().unwrap()).unwrap();
    assert_eq!(accepted.prop().term(), context.certify_prop(b).unwrap().term());
    assert_eq!(
        accepted.dependencies().as_sorted_entries(),
        vec![(
            DependencyKind::Axiom,
            AxiomDependencyId::compute(basis.id(), schema.id()).to_bytes(),
        )]
    );
}

#[test]
fn export_scope_sorted_arity_retains_exact_installer_dependency() {
    let owner = TrustedTheory::root(
        "ArityVariableReplay",
        Signature::new().install_empty_class(EmptyClassDeclCert::hol_type()).unwrap(),
    )
    .install_semantic_arity(SemanticArityCert::FunctionTypeArityCert)
    .unwrap();
    let context = ProofContext::new(owner.snapshot().clone());
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let beta = Ty::tvar("b", 0, Sort::hol_type());
    let source = KernelRules::reflexive(context.certify_term(RawTerm::var("x", 0, alpha)).unwrap());
    let instance = KernelRules::instantiate(
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
    let exported = KernelRules::export_scope(&owner, &context, &instance).unwrap();
    let indexed = KernelRules::incr_indexes(&owner, &context, &exported, 2).unwrap();
    let child = owner.begin_child("arity_child");
    let transferred = KernelRules::transfer(&child, &indexed).unwrap();
    let solved = KernelRules::solve_constraints(&child, &transferred).unwrap();
    let child_context = ProofContext::new(child.snapshot().clone());
    let stripped = KernelRules::strip_shyps(&child, &child_context, &solved).unwrap();
    let (_, accepted) =
        accept_closed_theorem(&child, "arity_export", stripped.try_close().unwrap()).unwrap();
    let installer = child.find_arity_installation(&"fun".into(), &"HOL.type".into()).unwrap();
    assert_eq!(
        accepted.dependencies().as_sorted_entries(),
        vec![(DependencyKind::Class, installer.to_bytes())]
    );
}

#[test]
fn generalize_same_name_distinct_typed_frees_export_and_accept() {
    let owner = TrustedTheory::root("TypedFreeReplay", Signature::new());
    let mut local = ProofContext::new(owner.snapshot().clone());
    let fixed = local.declare_type_free("a", Sort::empty()).unwrap();
    local.declare_free("x", fixed.clone());
    let first = KernelRules::reflexive(local.certify_term(RawTerm::free("x", fixed)).unwrap());
    let mut alternate = local.clone();
    alternate.declare_free("x", Ty::prop());
    assert_eq!(local.stamp(), alternate.stamp());
    let second =
        KernelRules::reflexive(alternate.certify_term(RawTerm::free("x", Ty::prop())).unwrap());
    let antecedent = first.as_kernel().prop();
    let conditional = KernelRules::implies_intr(
        antecedent,
        &KernelRules::weaken(antecedent, second.as_kernel()).unwrap(),
    )
    .unwrap();
    let proof = KernelRules::implies_elim(&conditional, first.as_kernel()).unwrap();
    assert!(proof.hyps().is_empty());
    let typed = KernelRules::generalize(&proof, &names(&["a"]), &names(&[]), 0).unwrap();
    let generalized = KernelRules::generalize(&typed, &names(&[]), &names(&["x"]), 1).unwrap();
    let Derivation::Generalize { source_frees, .. } = generalized.derivation() else {
        panic!("fixture must retain the term generalization");
    };
    assert_eq!(
        source_frees,
        &vec![(Name::from("x"), Ty::prop()), (Name::from("x"), Ty::tfree("a", Sort::empty())),]
    );
    let expected = RawTerm::eq(RawTerm::var("x", 1, Ty::prop()), RawTerm::var("x", 1, Ty::prop()));
    assert_eq!(generalized.prop().term(), local.certify_prop(expected.clone()).unwrap().term());
    let exported = KernelRules::export_scope(&owner, &local, &generalized).unwrap();
    let owner_context = ProofContext::new(owner.snapshot().clone());
    let stripped = KernelRules::strip_shyps(&owner, &owner_context, &exported).unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "same_name_typed", stripped.try_close().unwrap()).unwrap();
    assert_eq!(token.prop().term(), owner_context.certify_prop(expected).unwrap().term());
    assert!(token.dependencies().is_empty());
}
