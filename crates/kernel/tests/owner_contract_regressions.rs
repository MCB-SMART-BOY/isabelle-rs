use isabelle_kernel::{
    AxiomSchema, KernelError, KernelRules, LogicBasis, Name, ProofContext, RawTerm, Signature,
    TrustedTheory, Ty, accept_closed_theorem,
};

fn create_predeclared_owner() -> TrustedTheory {
    let signature = ["P", "c", "d"].into_iter().fold(Signature::new(), |signature, name| {
        signature.extend_const(name, Ty::prop()).unwrap()
    });
    TrustedTheory::root("Definitions", signature)
}

#[test]
fn merge_parents_independent_declaration_and_definition_reject_origin_collision() {
    let root = TrustedTheory::root("Root", Signature::new().extend_const("P", Ty::prop()).unwrap());
    let left = root.begin_child("Left").extend_const("c", Ty::prop()).unwrap();
    let (right, _) =
        root.begin_child("Right").define_const("c", RawTerm::const_("P", Ty::prop())).unwrap();
    assert!(matches!(TrustedTheory::merge_parents("Merge", &[left, right]),
        Err(KernelError::DuplicateDeclaration { name }) if name == Name::from("c")));
}

#[test]
fn define_const_sequential_predeclared_definitions_preserve_both_tokens() {
    let root = create_predeclared_owner();
    let (first, c) = root.define_const("c", RawTerm::const_("P", Ty::prop())).unwrap();
    let (second, d) = first.define_const("d", RawTerm::const_("P", Ty::prop())).unwrap();
    let c_ref = KernelRules::theorem_ref(&second, &c).unwrap();
    let d_ref = KernelRules::theorem_ref(&second, &d).unwrap();
    assert_eq!(c_ref.as_kernel().prop().term(), c.prop().term());
    assert_eq!(d_ref.as_kernel().prop().term(), d.prop().term());
}

#[test]
fn define_const_unrelated_accepted_fact_allows_predeclared_definition() {
    let root = create_predeclared_owner();
    let context = ProofContext::new(root.snapshot().clone());
    let p = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let (with_fact, fact) =
        accept_closed_theorem(&root, "unrelated", KernelRules::reflexive(p)).unwrap();
    let (defined, definition) =
        with_fact.define_const("c", RawTerm::const_("P", Ty::prop())).unwrap();
    assert_eq!(
        KernelRules::theorem_ref(&defined, &fact).unwrap().as_kernel().prop().term(),
        fact.prop().term()
    );
    assert_eq!(
        KernelRules::theorem_ref(&defined, &definition).unwrap().as_kernel().prop().term(),
        definition.prop().term()
    );
}

#[test]
fn define_const_with_args_dangling_bound_rejects_in_original_scope() {
    let root = TrustedTheory::root("Root", Signature::new());
    assert!(matches!(
        root.define_const_with_args("bad", vec![("x".into(), Ty::prop())], RawTerm::bound(0)),
        Err(KernelError::UnboundBound(0))
    ));
}

#[test]
fn define_const_with_args_nested_dangling_bound_rejects_in_original_scope() {
    let root = TrustedTheory::root("Root", Signature::new());
    let rhs = RawTerm::abs("y", Ty::prop(), RawTerm::bound(1));
    assert!(matches!(
        root.define_const_with_args("bad", vec![("x".into(), Ty::prop())], rhs),
        Err(KernelError::UnboundBound(1))
    ));
}

fn create_nested_permutation() -> (TrustedTheory, isabelle_kernel::KernelThm) {
    let function_type = Ty::arrow(Ty::prop(), Ty::prop());
    let signature = Signature::new()
        .extend_const("f", function_type.clone())
        .unwrap()
        .extend_const("x", Ty::prop())
        .unwrap();
    let root = TrustedTheory::root("Nested", signature);
    let context = ProofContext::new(root.snapshot().clone());
    let function = context.certify_term(RawTerm::const_("f", function_type)).unwrap();
    let (owner, f) = accept_closed_theorem(&root, "F", KernelRules::reflexive(function)).unwrap();
    let context = ProofContext::new(owner.snapshot().clone());
    let argument = context.certify_term(RawTerm::const_("x", Ty::prop())).unwrap();
    let (owner, x) = accept_closed_theorem(&owner, "X", KernelRules::reflexive(argument)).unwrap();
    let context = ProofContext::new(owner.snapshot().clone());
    let f_ref = KernelRules::theorem_ref(&owner, &f).unwrap();
    let x_ref = KernelRules::theorem_ref(&owner, &x).unwrap();
    let permuted = KernelRules::permute_prems(&owner, &context, x_ref.as_kernel(), 0, 0).unwrap();
    let combined = KernelRules::combination(f_ref.as_kernel(), &permuted).unwrap();
    (owner, combined)
}

#[test]
fn permute_prems_nested_second_authorized_leaf_preserves_proposition() {
    let (owner, combined) = create_nested_permutation();
    let context = ProofContext::new(owner.snapshot().clone());
    let transformed = KernelRules::permute_prems(&owner, &context, &combined, 0, 0).unwrap();
    assert_eq!(transformed.prop(), combined.prop());
    let (_, accepted) =
        accept_closed_theorem(&owner, "NestedPermutation", transformed.try_close().unwrap())
            .unwrap();
    assert_eq!(accepted.prop().term(), combined.prop().term());
}

#[test]
fn define_const_with_args_original_nested_bound_remains_bound() {
    let root = TrustedTheory::root("Binders", Signature::new());
    let rhs = RawTerm::abs("y", Ty::prop(), RawTerm::bound(0));
    let (defined, theorem) =
        root.define_const_with_args("keep", vec![("x".into(), Ty::prop())], rhs).unwrap();
    assert_eq!(
        defined.signature().const_type(&Name::from("keep")),
        Some(&Ty::arrow(Ty::prop(), Ty::arrow(Ty::prop(), Ty::prop())))
    );
    assert!(KernelRules::theorem_ref(&defined, &theorem).is_ok());
}

#[test]
fn merge_parents_shared_predeclaration_completed_on_one_branch_retains_token() {
    let root = create_predeclared_owner();
    let (left, theorem) =
        root.begin_child("Left").define_const("c", RawTerm::const_("P", Ty::prop())).unwrap();
    let right = root.begin_child("Right").extend_const("other", Ty::prop()).unwrap();
    let merged = TrustedTheory::merge_parents("Merged", &[left, right]).unwrap();
    assert_eq!(merged.signature().const_type(&Name::from("c")), Some(&Ty::prop()));
    assert!(KernelRules::theorem_ref(&merged, &theorem).is_ok());
}

#[test]
fn merge_parents_shared_predeclaration_two_independent_definitions_reject() {
    let root = create_predeclared_owner();
    let (left, _) =
        root.begin_child("Left").define_const("c", RawTerm::const_("P", Ty::prop())).unwrap();
    let (right, _) =
        root.begin_child("Right").define_const("c", RawTerm::const_("P", Ty::prop())).unwrap();
    assert!(matches!(TrustedTheory::merge_parents("Conflict", &[left, right]),
        Err(KernelError::DuplicateDeclaration { name }) if name == Name::from("c")));
}

#[test]
fn define_const_sequential_dependency_cycle_rejects_without_new_fact() {
    let root = create_predeclared_owner();
    let (first, theorem) = root.define_const("c", RawTerm::const_("d", Ty::prop())).unwrap();
    assert!(matches!(
        first.define_const("d", RawTerm::const_("c", Ty::prop())),
        Err(KernelError::DefinitionCertificate(_))
    ));
    assert!(first.get(&Name::from("d_def")).is_none());
    assert!(KernelRules::theorem_ref(&first, &theorem).is_ok());
}

#[test]
fn merge_parents_layered_diamonds_keep_one_common_fact() {
    let root =
        TrustedTheory::root("Layered", Signature::new().extend_const("P", Ty::prop()).unwrap());
    let context = ProofContext::new(root.snapshot().clone());
    let p = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let (mut owner, shared) =
        accept_closed_theorem(&root, "shared", KernelRules::reflexive(p)).unwrap();
    for depth in 0..6 {
        let left = owner.begin_child(format!("L{depth}"));
        let right = owner.begin_child(format!("R{depth}"));
        owner = TrustedTheory::merge_parents(format!("M{depth}"), &[left, right]).unwrap();
    }
    assert_eq!(owner.len(), 1);
    assert!(KernelRules::theorem_ref(&owner, &shared).is_ok());
}

#[test]
fn rotate_rule_nested_nonfirst_leaf_survives_strip_and_outer_permutation() {
    let function_type = Ty::arrow(Ty::prop(), Ty::prop());
    let signature = Signature::new()
        .extend_const("f", function_type.clone())
        .unwrap()
        .extend_const("x", Ty::prop())
        .unwrap()
        .extend_const("P", Ty::prop())
        .unwrap();
    let root = TrustedTheory::root("Rotated", signature);
    let context = ProofContext::new(root.snapshot().clone());
    let function = context.certify_term(RawTerm::const_("f", function_type)).unwrap();
    let (owner, f) = accept_closed_theorem(&root, "F", KernelRules::reflexive(function)).unwrap();
    let context = ProofContext::new(owner.snapshot().clone());
    let argument = context.certify_term(RawTerm::const_("x", Ty::prop())).unwrap();
    let (owner, x) = accept_closed_theorem(&owner, "X", KernelRules::reflexive(argument)).unwrap();
    let context = ProofContext::new(owner.snapshot().clone());
    let p = context.certify_prop(RawTerm::const_("P", Ty::prop())).unwrap();
    let f_ref = KernelRules::theorem_ref(&owner, &f).unwrap();
    let x_ref = KernelRules::theorem_ref(&owner, &x).unwrap();
    let weakened = KernelRules::weaken(&p, x_ref.as_kernel()).unwrap();
    let conditional = KernelRules::implies_intr(&p, &weakened).unwrap();
    let rotated = KernelRules::rotate_rule(&owner, &context, &conditional, 0, 0).unwrap();
    let open = KernelRules::implies_elim(&rotated, &KernelRules::assume(p).unwrap().into_kernel())
        .unwrap();
    let combined = KernelRules::combination(f_ref.as_kernel(), &open).unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &combined).unwrap();
    assert_eq!(stripped.prop(), combined.prop());
    assert_eq!(stripped.hyps(), combined.hyps());
    let permuted = KernelRules::permute_prems(&owner, &context, &stripped, 0, 0).unwrap();
    assert_eq!(permuted.prop(), combined.prop());
    assert_eq!(permuted.hyps(), combined.hyps());
}

#[test]
fn define_const_predeclared_axiom_constraint_rejects_only_affected_origin() {
    let basis = LogicBasis::try_new(
        vec![],
        vec![AxiomSchema { name: "constraint".into(), prop: RawTerm::const_("c", Ty::prop()) }],
    )
    .unwrap();
    let root = TrustedTheory::with_basis(
        "Constrained",
        create_predeclared_owner().signature().clone(),
        &basis,
    )
    .unwrap();
    assert!(matches!(root.define_const("c", RawTerm::const_("P", Ty::prop())),
        Err(KernelError::DuplicateDeclaration { name }) if name == Name::from("c")));
    let (defined, theorem) = root.define_const("d", RawTerm::const_("P", Ty::prop())).unwrap();
    assert!(KernelRules::theorem_ref(&defined, &theorem).is_ok());
}
