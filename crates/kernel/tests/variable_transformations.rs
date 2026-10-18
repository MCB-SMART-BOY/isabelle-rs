use std::collections::{BTreeMap, BTreeSet};

use isabelle_kernel::{
    InstEntry, KernelError, KernelRules, Name, ProofContext, RawTerm, Signature, Sort, Term,
    TrustedTheory, Ty, TypeInstantiation, TypeVarId,
};

fn names(names: &[&str]) -> BTreeSet<Name> {
    names.iter().map(|name| Name::from(*name)).collect()
}

fn fixed_context() -> (TrustedTheory, ProofContext) {
    let owner = TrustedTheory::root("Variables", Signature::new());
    let mut context = ProofContext::new(owner.snapshot().clone());
    let fixed = context.declare_type_free("a", Sort::empty()).unwrap();
    context.declare_free("x", fixed.clone());
    context.declare_free("y", fixed);
    (owner, context)
}

#[test]
fn generalize_shared_index_cleans_trailing_underscores_and_preserves_unselected_free() {
    let (_owner, mut context) = fixed_context();
    let fixed = Ty::tfree("a", Sort::empty());
    context.declare_free("x__", fixed.clone());
    let term = context
        .certify_term(RawTerm::eq(
            RawTerm::free("x__", fixed.clone()),
            RawTerm::free("y", fixed.clone()),
        ))
        .unwrap();
    let theorem = KernelRules::reflexive(term).into_kernel();
    let generalized =
        KernelRules::generalize(&theorem, &names(&["a"]), &names(&["x__", "ghost"]), 4).unwrap();
    let variable_type = Ty::tvar("a", 4, Sort::empty());
    let inner = Term::mk_eq(
        Term::Var { name: "x".into(), index: 6, ty: variable_type.clone() },
        Term::Free { name: "y".into(), ty: variable_type },
    )
    .unwrap();
    assert_eq!(generalized.prop().term(), &Term::mk_eq(inner.clone(), inner).unwrap());
    assert_eq!(generalized.max_var_index(), Some(6));
    assert_eq!(generalized.hyps(), theorem.hyps());
}

#[test]
fn generalize_vars_selects_same_name_at_distinct_types() {
    let fixed_nat = Ty::base("nat").unwrap();
    let nat_equality = Term::mk_eq(
        Term::Free { name: "x".into(), ty: fixed_nat.clone() },
        Term::Free { name: "x".into(), ty: fixed_nat.clone() },
    )
    .unwrap();
    let prop_equality = Term::mk_eq(
        Term::Free { name: "x".into(), ty: Ty::prop() },
        Term::Free { name: "x".into(), ty: Ty::prop() },
    )
    .unwrap();
    let source = Term::mk_imp(nat_equality, prop_equality).unwrap();
    let transformed = source.generalize_vars(&names(&[]), &names(&["x", "x"]), 2).unwrap();
    let expected_nat = Term::mk_eq(
        Term::Var { name: "x".into(), index: 2, ty: fixed_nat.clone() },
        Term::Var { name: "x".into(), index: 2, ty: fixed_nat },
    )
    .unwrap();
    let expected_prop = Term::mk_eq(
        Term::Var { name: "x".into(), index: 2, ty: Ty::prop() },
        Term::Var { name: "x".into(), index: 2, ty: Ty::prop() },
    )
    .unwrap();
    assert_eq!(transformed, Term::mk_imp(expected_nat, expected_prop).unwrap());
}

#[test]
fn generalize_nonempty_unmatched_requires_fresh_index_but_empty_selection_is_identity() {
    let context =
        ProofContext::new(TrustedTheory::root("Fresh", Signature::new()).snapshot().clone());
    let term = context.certify_term(RawTerm::var("P", 3, Ty::prop())).unwrap();
    let theorem = KernelRules::reflexive(term).into_kernel();
    let unchanged =
        KernelRules::generalize(&theorem, &names(&[]), &names(&[]), usize::MAX).unwrap();
    assert_eq!(unchanged.prop(), theorem.prop());
    assert_eq!(unchanged.max_var_index(), Some(3));
    assert_eq!(
        KernelRules::generalize(&theorem, &names(&[]), &names(&["absent"]), 3).unwrap_err(),
        KernelError::GeneralizeIndexNotFresh { index: 3, max_index: 3 }
    );
    let unmatched = KernelRules::generalize(&theorem, &names(&["unused"]), &names(&[]), 4).unwrap();
    assert_eq!(unmatched.prop(), theorem.prop());
    assert_eq!(unmatched.max_var_index(), Some(3));
}

#[test]
fn generalize_recomputes_current_max_index_after_metadata_only_raise() {
    let owner = TrustedTheory::root("MaxReset", Signature::new());
    let mut context = ProofContext::new(owner.snapshot().clone());
    context.declare_free("x", Ty::prop());
    let theorem =
        KernelRules::reflexive(context.certify_term(RawTerm::free("x", Ty::prop())).unwrap())
            .into_kernel();
    let raised = KernelRules::adjust_max_index(&theorem, Some(17));
    assert_eq!(raised.max_var_index(), Some(17));
    let unmatched = KernelRules::generalize(&raised, &names(&[]), &names(&["absent"]), 18).unwrap();
    assert_eq!(unmatched.max_var_index(), None);
    let actual = KernelRules::generalize(&unmatched, &names(&[]), &names(&["x"]), 0).unwrap();
    assert_eq!(actual.max_var_index(), Some(0));
    assert_eq!(
        actual.prop().term(),
        context
            .certify_prop(RawTerm::eq(
                RawTerm::var("x", 0, Ty::prop()),
                RawTerm::var("x", 0, Ty::prop()),
            ))
            .unwrap()
            .term()
    );
}

#[test]
fn generalize_selected_term_or_type_in_hypotheses_rejects() {
    let (_owner, context) = fixed_context();
    let fixed = Ty::tfree("a", Sort::empty());
    let proposition = context
        .certify_prop(RawTerm::eq(RawTerm::free("x", fixed.clone()), RawTerm::free("y", fixed)))
        .unwrap();
    let theorem = KernelRules::assume(proposition).unwrap().into_kernel();
    assert!(matches!(
        KernelRules::generalize(&theorem, &names(&[]), &names(&["x"]), 0),
        Err(KernelError::FreeVarInHypotheses { name }) if name == Name::from("x")
    ));
    assert!(matches!(
        KernelRules::generalize(&theorem, &names(&["a"]), &names(&[]), 0),
        Err(KernelError::TypeFreeInHypotheses { name }) if name == Name::from("a")
    ));
}

#[test]
fn generalize_type_index_boundaries_and_term_cleanup_overflow_are_structured() {
    let (_owner, context) = fixed_context();
    let fixed = Ty::tfree("a", Sort::empty());
    let term = context.certify_term(RawTerm::free("x", fixed.clone())).unwrap();
    let theorem = KernelRules::reflexive(term).into_kernel();
    let max_type_index = u32::MAX as usize;
    let highest =
        KernelRules::generalize(&theorem, &names(&["a"]), &names(&[]), max_type_index).unwrap();
    assert_eq!(highest.max_var_index(), Some(max_type_index));
    if let Some(index) = max_type_index.checked_add(1) {
        assert_eq!(
            KernelRules::generalize(&theorem, &names(&["a"]), &names(&[]), index).unwrap_err(),
            KernelError::TypeVariableIndexOutOfRange { name: "a".into(), index }
        );
    }
    assert_eq!(
        Term::Free { name: "x_".into(), ty: fixed }.generalize_vars(
            &names(&[]),
            &names(&["x_"]),
            usize::MAX,
        ),
        Err(KernelError::GeneralizeIndexOverflow { index: usize::MAX, offset: 1 })
    );
}

#[test]
fn certified_generalize_empty_selection_preserves_index_metadata() {
    let (_owner, context) = fixed_context();
    let fixed = Ty::tfree("a", Sort::empty());
    let certified_type = context.certify_type(Ty::arrow(fixed.clone(), fixed.clone())).unwrap();
    let certified_term = context.certify_term(RawTerm::free("x", fixed)).unwrap();
    let unchanged_type = context.generalize_type(&certified_type, &names(&[]), usize::MAX).unwrap();
    let (unchanged_context, unchanged_term) =
        context.generalize_term(&certified_term, &names(&[]), &names(&[]), usize::MAX).unwrap();
    assert_eq!(unchanged_type, certified_type);
    assert_eq!(unchanged_term, certified_term);
    assert_eq!(unchanged_context.stamp(), context.stamp());
    assert_eq!(unchanged_type.max_var_index(), None);
    assert_eq!(unchanged_term.max_var_index(), None);
}

#[test]
fn certified_generalize_type_rewrites_arrow_and_tracks_index() {
    let (_owner, context) = fixed_context();
    let fixed = Ty::tfree("a", Sort::empty());
    let source = context.certify_type(Ty::arrow(fixed.clone(), fixed)).unwrap();
    let generalized = context.generalize_type(&source, &names(&["a"]), 5).unwrap();
    let variable = Ty::tvar("a", 5, Sort::empty());
    assert_eq!(generalized.ty(), &Ty::arrow(variable.clone(), variable));
    assert_eq!(generalized.max_var_index(), Some(5));
    assert_eq!(generalized.context(), source.context());
}

#[test]
fn certified_generalize_term_rewrites_bound_and_abstraction_annotations() {
    let (_owner, context) = fixed_context();
    let fixed = Ty::tfree("a", Sort::empty());
    let source = context.certify_term(RawTerm::abs("bound", fixed, RawTerm::bound(0))).unwrap();
    let (_, generalized) =
        context.generalize_term(&source, &names(&["a"]), &names(&[]), 2).unwrap();
    let variable = Ty::tvar("a", 2, Sort::empty());
    assert_eq!(
        generalized.term(),
        &Term::Abs {
            name: "bound".into(),
            param_ty: variable.clone(),
            body: Box::new(Term::Bound { index: 0, ty: variable.clone() }),
            ty: Ty::arrow(variable.clone(), variable),
        }
    );
    assert_eq!(generalized.max_var_index(), Some(2));
}

#[test]
fn certified_generalize_unmatched_selection_raises_cache_and_rejects_reused_index() {
    let (_owner, context) = fixed_context();
    let fixed = Ty::tfree("a", Sort::empty());
    let certified_type = context.certify_type(fixed.clone()).unwrap();
    let certified_term = context.certify_term(RawTerm::free("x", fixed)).unwrap();
    let generalized_type =
        context.generalize_type(&certified_type, &names(&["unused"]), 8).unwrap();
    let (next_context, generalized_term) =
        context.generalize_term(&certified_term, &names(&[]), &names(&["unused"]), 8).unwrap();
    assert_eq!(generalized_type.ty(), certified_type.ty());
    assert_eq!(generalized_term.term(), certified_term.term());
    assert_eq!(generalized_type.max_var_index(), Some(8));
    assert_eq!(generalized_term.max_var_index(), Some(8));
    assert_eq!(
        context.generalize_type(&generalized_type, &names(&["a"]), 8).unwrap_err(),
        KernelError::GeneralizeIndexNotFresh { index: 8, max_index: 8 }
    );
    assert_eq!(
        next_context
            .generalize_term(&generalized_term, &names(&[]), &names(&["x"]), 8)
            .unwrap_err(),
        KernelError::GeneralizeIndexNotFresh { index: 8, max_index: 8 }
    );
}

#[test]
fn certified_generalize_updates_unselected_free_type_in_derived_context() {
    let (_owner, context) = fixed_context();
    let fixed = Ty::tfree("a", Sort::empty());
    let source = context.certify_term(RawTerm::free("x", fixed.clone())).unwrap();
    let (derived, result) =
        context.generalize_term(&source, &names(&["a"]), &names(&[]), 0).unwrap();
    let schematic = Ty::tvar("a", 0, Sort::empty());
    assert_eq!(result.term(), &Term::Free { name: "x".into(), ty: schematic.clone() });
    assert_eq!(context.free_type(&"x".into()), Some(&fixed));
    assert_eq!(derived.free_type(&"x".into()), Some(&schematic));
    assert!(context.certify_term(RawTerm::free("x", schematic.clone())).is_err());
    let next = derived.certify_term(RawTerm::free("x", schematic)).unwrap();
    assert_eq!(next.term(), result.term());
}

#[test]
fn certified_generalize_cleaned_name_records_actual_max_index() {
    let (_owner, mut context) = fixed_context();
    let fixed = Ty::tfree("a", Sort::empty());
    context.declare_free("x__", fixed.clone());
    let source = context.certify_term(RawTerm::free("x__", fixed.clone())).unwrap();
    let (derived, result) =
        context.generalize_term(&source, &names(&["a"]), &names(&["x__"]), 2).unwrap();
    assert_eq!(result.max_var_index(), Some(4));
    assert_eq!(
        result.term(),
        &Term::Var { name: "x".into(), index: 4, ty: Ty::tvar("a", 2, Sort::empty()) }
    );
    assert_eq!(derived.stamp(), context.stamp());
}

#[test]
fn generalize_then_instantiate_types_and_terms_uses_post_type_keys_once() {
    let (_owner, context) = fixed_context();
    let fixed = Ty::tfree("a", Sort::empty());
    let source = context
        .certify_term(RawTerm::eq(RawTerm::free("x", fixed.clone()), RawTerm::free("y", fixed)))
        .unwrap();
    let theorem = KernelRules::reflexive(source).into_kernel();
    let schema = KernelRules::generalize(&theorem, &names(&["a"]), &names(&["x", "y"]), 0).unwrap();
    let types = TypeInstantiation::try_new(BTreeMap::from([(
        TypeVarId::new("a", 0, Sort::empty()),
        Ty::prop(),
    )]))
    .unwrap();
    let y = context.certify_term(RawTerm::var("y", 0, Ty::prop())).unwrap();
    // A second replacement refers to the first replacement's schematic variable.
    // Both keys are substituted against the original theorem, not sequentially.
    let replacement = context.certify_term(RawTerm::var("z", 0, Ty::prop())).unwrap();
    let instantiated = KernelRules::instantiate(
        &context,
        &schema,
        &types,
        &[InstEntry::new("x", 0, Ty::prop(), y), InstEntry::new("y", 0, Ty::prop(), replacement)],
    )
    .unwrap();
    let inner = Term::mk_eq(
        Term::Var { name: "y".into(), index: 0, ty: Ty::prop() },
        Term::Var { name: "z".into(), index: 0, ty: Ty::prop() },
    )
    .unwrap();
    assert_eq!(instantiated.prop().term(), &Term::mk_eq(inner.clone(), inner).unwrap());
}
