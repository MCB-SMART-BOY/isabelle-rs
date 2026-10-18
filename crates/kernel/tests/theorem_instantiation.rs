use std::collections::{BTreeMap, BTreeSet};

use isabelle_kernel::{
    CTerm, EmptyClassDeclCert, InstEntry, KernelError, KernelRules, KernelThm, ProofContext,
    RawTerm, Signature, Sort, TrustedTheory, Ty, TypeInstantiation, TypeVarId,
    accept_closed_theorem,
};

fn nat() -> Ty {
    Ty::base("nat").unwrap()
}

fn build_owner() -> (TrustedTheory, ProofContext) {
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_type_constructor("nat", 0)
        .unwrap()
        .extend_type_constructor("list", 1)
        .unwrap()
        .extend_const("a", nat())
        .unwrap()
        .extend_const("b", nat())
        .unwrap()
        .extend_const("P", Ty::prop())
        .unwrap()
        .extend_const("f", Ty::arrow(nat(), nat()))
        .unwrap()
        .extend_const("pair", Ty::arrow(nat(), Ty::arrow(nat(), nat())))
        .unwrap();
    let owner = TrustedTheory::root("Instantiation", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    (owner, context)
}

fn certify(context: &ProofContext, raw: RawTerm) -> CTerm {
    context.certify_term(raw).unwrap()
}

fn prove_refl(context: &ProofContext, raw: RawTerm) -> KernelThm {
    KernelRules::reflexive(certify(context, raw)).into_kernel()
}

fn make_pair(left: RawTerm, right: RawTerm) -> RawTerm {
    RawTerm::app(
        RawTerm::app(RawTerm::const_("pair", Ty::arrow(nat(), Ty::arrow(nat(), nat()))), left),
        right,
    )
}

fn assert_accepted_refl(owner: &TrustedTheory, theorem: KernelThm, expected: RawTerm) {
    let context = ProofContext::new(owner.snapshot().clone());
    let expected = context.certify_prop(RawTerm::eq(expected.clone(), expected)).unwrap();
    let theorem = KernelRules::strip_shyps(owner, &context, &theorem).unwrap();
    let (updated, token) =
        accept_closed_theorem(owner, "instantiated", theorem.try_close().unwrap()).unwrap();
    assert_eq!(token.prop().term(), expected.term());
    assert!(token.dependencies().is_empty());
    assert_eq!(
        KernelRules::theorem_ref(&updated, &token).unwrap().as_kernel().prop().term(),
        expected.term()
    );
}

fn make_types(bindings: Vec<(&str, Sort, Ty)>) -> TypeInstantiation {
    TypeInstantiation::try_new(
        bindings
            .into_iter()
            .map(|(name, sort, ty)| (TypeVarId::new(name, 0, sort), ty))
            .collect::<BTreeMap<_, _>>(),
    )
    .unwrap()
}

#[test]
fn instantiate_type_pass_matches_post_substitution_term_keys() {
    let (owner, context) = build_owner();
    let alpha = Ty::tvar("alpha", 0, Sort::empty());
    let theorem = prove_refl(&context, RawTerm::var("x", 0, alpha));
    let types = make_types(vec![("alpha", Sort::empty(), nat())]);
    let replacement = certify(&context, RawTerm::const_("a", nat()));
    let result = KernelRules::instantiate(
        &context,
        &theorem,
        &types,
        &[InstEntry::new("x", 0, nat(), replacement)],
    )
    .unwrap();
    assert_accepted_refl(&owner, result, RawTerm::const_("a", nat()));
}

#[test]
fn instantiate_type_rhs_cross_references_are_simultaneous() {
    let (owner, context) = build_owner();
    let alpha = Ty::tvar("alpha", 0, Sort::empty());
    let beta = Ty::tvar("beta", 0, Sort::empty());
    let theorem = prove_refl(&context, RawTerm::var("f", 0, Ty::arrow(alpha, beta.clone())));
    let types =
        make_types(vec![("alpha", Sort::empty(), beta.clone()), ("beta", Sort::empty(), nat())]);
    let result = KernelRules::instantiate(&context, &theorem, &types, &[]).unwrap();
    assert_accepted_refl(&owner, result, RawTerm::var("f", 0, Ty::arrow(beta, nat())));
}

#[test]
fn instantiate_type_rhs_self_occurrence_is_finite() {
    let (owner, context) = build_owner();
    let alpha = Ty::tvar("alpha", 0, Sort::empty());
    let theorem = prove_refl(&context, RawTerm::var("x", 0, alpha.clone()));
    let list = Ty::apply("list", vec![alpha]).unwrap();
    let types = make_types(vec![("alpha", Sort::empty(), list.clone())]);
    let result = KernelRules::instantiate(&context, &theorem, &types, &[]).unwrap();
    assert_accepted_refl(&owner, result, RawTerm::var("x", 0, list));
}

#[test]
fn instantiate_term_rhs_cross_references_are_simultaneous() {
    let (owner, context) = build_owner();
    let x = RawTerm::var("x", 0, nat());
    let y = RawTerm::var("y", 0, nat());
    let theorem = prove_refl(&context, make_pair(x, y.clone()));
    let result = KernelRules::instantiate(
        &context,
        &theorem,
        &TypeInstantiation::empty(),
        &[
            InstEntry::new("x", 0, nat(), certify(&context, y.clone())),
            InstEntry::new("y", 0, nat(), certify(&context, RawTerm::const_("a", nat()))),
        ],
    )
    .unwrap();
    assert_accepted_refl(&owner, result, make_pair(y, RawTerm::const_("a", nat())));
}

#[test]
fn instantiate_term_rhs_self_occurrence_is_finite() {
    let (owner, context) = build_owner();
    let x = RawTerm::var("x", 0, nat());
    let theorem = prove_refl(&context, x.clone());
    let replacement = RawTerm::app(RawTerm::const_("f", Ty::arrow(nat(), nat())), x);
    let result = KernelRules::instantiate(
        &context,
        &theorem,
        &TypeInstantiation::empty(),
        &[InstEntry::new("x", 0, nat(), certify(&context, replacement.clone()))],
    )
    .unwrap();
    assert_accepted_refl(&owner, result, replacement);
}

#[test]
fn instantiate_distinct_indexes_preserves_unmatched_occurrence() {
    let (owner, context) = build_owner();
    let theorem =
        prove_refl(&context, make_pair(RawTerm::var("x", 0, nat()), RawTerm::var("x", 1, nat())));
    let result = KernelRules::instantiate(
        &context,
        &theorem,
        &TypeInstantiation::empty(),
        &[InstEntry::new("x", 0, nat(), certify(&context, RawTerm::const_("a", nat())))],
    )
    .unwrap();
    assert_accepted_refl(
        &owner,
        result,
        make_pair(RawTerm::const_("a", nat()), RawTerm::var("x", 1, nat())),
    );
}

#[test]
fn instantiate_different_key_type_does_not_match() {
    let (owner, context) = build_owner();
    let theorem = prove_refl(&context, RawTerm::var("x", 0, nat()));
    let result = KernelRules::instantiate(
        &context,
        &theorem,
        &TypeInstantiation::empty(),
        &[InstEntry::new("x", 0, Ty::prop(), certify(&context, RawTerm::const_("P", Ty::prop())))],
    )
    .unwrap();
    assert_accepted_refl(&owner, result, RawTerm::var("x", 0, nat()));
}

#[test]
fn instantiate_replacement_type_mismatch_rejects() {
    let (_owner, context) = build_owner();
    let theorem = prove_refl(&context, RawTerm::var("x", 0, nat()));
    let result = KernelRules::instantiate(
        &context,
        &theorem,
        &TypeInstantiation::empty(),
        &[InstEntry::new("x", 0, nat(), certify(&context, RawTerm::const_("P", Ty::prop())))],
    );
    assert!(matches!(result, Err(KernelError::TypeMismatch { .. })));
}

#[test]
fn instantiate_duplicate_typed_identity_rejects() {
    let (_owner, context) = build_owner();
    let theorem = prove_refl(&context, RawTerm::var("x", 0, nat()));
    let result = KernelRules::instantiate(
        &context,
        &theorem,
        &TypeInstantiation::empty(),
        &[
            InstEntry::new("x", 0, nat(), certify(&context, RawTerm::const_("a", nat()))),
            InstEntry::new("x", 0, nat(), certify(&context, RawTerm::const_("b", nat()))),
        ],
    );
    assert!(matches!(result, Err(KernelError::DuplicateSubstitution { .. })));
}

#[test]
fn instantiate_same_index_different_typed_keys_both_apply() {
    let (owner, context) = build_owner();
    let prop = Ty::prop();
    let arrow = Ty::arrow(prop.clone(), prop.clone());
    let source =
        RawTerm::app(RawTerm::var("x", 0, arrow.clone()), RawTerm::var("x", 0, prop.clone()));
    let theorem = prove_refl(&context, source);
    let identity = RawTerm::abs("z", prop.clone(), RawTerm::bound(0));
    let constant = RawTerm::const_("P", prop.clone());
    let result = KernelRules::instantiate(
        &context,
        &theorem,
        &TypeInstantiation::empty(),
        &[
            InstEntry::new("x", 0, arrow, certify(&context, identity.clone())),
            InstEntry::new("x", 0, prop, certify(&context, constant.clone())),
        ],
    )
    .unwrap();
    assert_accepted_refl(&owner, result, RawTerm::app(identity, constant));
}

#[test]
fn instantiate_real_hypothesis_is_preserved_exactly() {
    let (_owner, context) = build_owner();
    let hypothesis = context
        .certify_prop(RawTerm::forall(
            "z",
            nat(),
            RawTerm::eq(RawTerm::bound(0), RawTerm::bound(0)),
        ))
        .unwrap();
    let assumption = KernelRules::assume(hypothesis.clone()).unwrap();
    let theorem = KernelRules::forall_elim(
        assumption.as_kernel(),
        &certify(&context, RawTerm::var("x", 0, nat())),
    )
    .unwrap();
    let result = KernelRules::instantiate(
        &context,
        &theorem,
        &TypeInstantiation::empty(),
        &[InstEntry::new("x", 0, nat(), certify(&context, RawTerm::const_("a", nat())))],
    )
    .unwrap();
    let expected = context
        .certify_prop(RawTerm::eq(RawTerm::const_("a", nat()), RawTerm::const_("a", nat())))
        .unwrap();
    assert_eq!(result.prop(), &expected);
    assert_eq!(result.hyps(), &[hypothesis]);
    assert!(result.try_close().is_err());
}

#[test]
fn instantiate_empty_maps_preserve_schema_and_accept() {
    let (owner, context) = build_owner();
    let variable = RawTerm::var("x", 7, Ty::tvar("alpha", 0, Sort::empty()));
    let theorem = prove_refl(&context, variable.clone());
    let result =
        KernelRules::instantiate(&context, &theorem, &TypeInstantiation::empty(), &[]).unwrap();
    assert_accepted_refl(&owner, result, variable);
}

#[test]
fn instantiate_constants_and_fixed_term_variables_are_unchanged() {
    let (owner, mut context) = build_owner();
    context.declare_free("x", nat());
    let raw = make_pair(RawTerm::free("x", nat()), RawTerm::const_("a", nat()));
    let theorem = prove_refl(&context, raw.clone());
    let result = KernelRules::instantiate(
        &context,
        &theorem,
        &TypeInstantiation::empty(),
        &[InstEntry::new("x", 0, nat(), certify(&context, RawTerm::const_("b", nat())))],
    )
    .unwrap();
    assert_eq!(result.prop(), theorem.prop());
    let closed =
        KernelRules::forall_intr(&certify(&context, RawTerm::free("x", nat())), &result).unwrap();
    let (_, token) = accept_closed_theorem(&owner, "fixed", closed.try_close().unwrap()).unwrap();
    let bound_pair = make_pair(RawTerm::bound(0), RawTerm::const_("a", nat()));
    let expected = context
        .certify_prop(RawTerm::forall("x", nat(), RawTerm::eq(bound_pair.clone(), bound_pair)))
        .unwrap();
    assert_eq!(token.prop().term(), expected.term());
}

#[test]
fn instantiate_generalized_free_roundtrip_restores_original_proposition() {
    let (_owner, mut context) = build_owner();
    context.declare_free("x", nat());
    let free = certify(&context, RawTerm::free("x", nat()));
    let theorem = KernelRules::reflexive(free.clone()).into_kernel();
    let generalized =
        KernelRules::generalize(&theorem, &BTreeSet::new(), &BTreeSet::from(["x".into()]), 0)
            .unwrap();
    let result = KernelRules::instantiate(
        &context,
        &generalized,
        &TypeInstantiation::empty(),
        &[InstEntry::new("x", 0, nat(), free)],
    )
    .unwrap();
    assert_eq!(result.prop(), theorem.prop());
    assert_eq!(result.hyps(), theorem.hyps());
    isabelle_kernel::invariant::check_kernel_thm(&result).unwrap();
}

#[test]
fn instantiate_closed_lambda_replacement_avoids_binder_capture() {
    let (owner, context) = build_owner();
    let function_type = Ty::arrow(nat(), nat());
    let original = RawTerm::abs(
        "outer",
        nat(),
        RawTerm::app(RawTerm::var("g", 0, function_type.clone()), RawTerm::bound(0)),
    );
    let theorem = prove_refl(&context, original);
    let replacement = RawTerm::abs("inner", nat(), RawTerm::bound(0));
    let result = KernelRules::instantiate(
        &context,
        &theorem,
        &TypeInstantiation::empty(),
        &[InstEntry::new("g", 0, function_type, certify(&context, replacement.clone()))],
    )
    .unwrap();
    let expected = RawTerm::abs("outer", nat(), RawTerm::app(replacement, RawTerm::bound(0)));
    assert_accepted_refl(&owner, result, expected);
}

#[test]
fn instantiate_type_pass_retypes_binders_and_cached_applications() {
    let (owner, context) = build_owner();
    let alpha = Ty::tvar("alpha", 0, Sort::empty());
    let original = RawTerm::abs(
        "x",
        alpha.clone(),
        RawTerm::app(RawTerm::var("g", 0, Ty::arrow(alpha.clone(), alpha)), RawTerm::bound(0)),
    );
    let theorem = prove_refl(&context, original);
    let types = make_types(vec![("alpha", Sort::empty(), nat())]);
    let result = KernelRules::instantiate(&context, &theorem, &types, &[]).unwrap();
    let expected = RawTerm::abs(
        "x",
        nat(),
        RawTerm::app(RawTerm::var("g", 0, Ty::arrow(nat(), nat())), RawTerm::bound(0)),
    );
    assert_accepted_refl(&owner, result, expected);
}

#[test]
fn instantiate_unused_foreign_replacement_is_rejected() {
    let (_owner, context) = build_owner();
    let foreign =
        ProofContext::new(TrustedTheory::root("Foreign", Signature::new()).snapshot().clone());
    let theorem = prove_refl(&context, RawTerm::const_("a", nat()));
    let replacement = certify(&foreign, RawTerm::var("unused", 0, Ty::prop()));
    assert!(matches!(
        KernelRules::instantiate(
            &context,
            &theorem,
            &TypeInstantiation::empty(),
            &[InstEntry::new("unused", 0, Ty::prop(), replacement)]
        ),
        Err(KernelError::MixedContext { .. })
    ));
}

#[test]
fn instantiate_unused_weak_sort_replacement_is_rejected() {
    let (_owner, context) = build_owner();
    let theorem = prove_refl(&context, RawTerm::const_("a", nat()));
    let types = make_types(vec![("unused", Sort::hol_type(), Ty::tvar("beta", 0, Sort::empty()))]);
    assert!(matches!(
        KernelRules::instantiate(&context, &theorem, &types, &[]),
        Err(KernelError::TypeSortMismatch { .. })
    ));
}

#[test]
fn instantiate_unused_conflicting_type_identity_is_rejected() {
    let (_, context) = build_owner();
    let theorem = prove_refl(&context, RawTerm::const_("P", Ty::prop()));
    let conflicting =
        Ty::arrow(Ty::tvar("same", 0, Sort::empty()), Ty::tvar("same", 0, Sort::hol_type()));
    let types = make_types(vec![("unused", Sort::empty(), conflicting)]);
    assert!(matches!(
        KernelRules::instantiate(&context, &theorem, &types, &[]),
        Err(KernelError::TypeIdentityMismatch { .. })
    ));
}
