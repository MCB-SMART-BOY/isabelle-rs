use std::collections::{BTreeMap, BTreeSet};

use isabelle_kernel::{
    AxiomSchema, EmptyClassDeclCert, InstEntry, KernelError, KernelRules, LogicBasis, ProofContext,
    RawTerm, SemanticArityCert, Signature, Sort, TrustedTheory, Ty, TypeInstantiation, TypeVarId,
    accept_closed_theorem, theorem_builder,
};

fn build_owner() -> (TrustedTheory, ProofContext) {
    let signature = Signature::new().extend_const("P", Ty::prop()).unwrap();
    let owner = TrustedTheory::root("Strip", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    (owner, context)
}

#[test]
fn strip_instantiated_empty_sort_closes_with_exact_statement() {
    let (owner, context) = build_owner();
    let alpha = Ty::tvar("a", 0, Sort::empty());
    let term = context.certify_term(RawTerm::var("x", 0, alpha)).unwrap();
    let source = KernelRules::reflexive(term).into_kernel();
    let types = TypeInstantiation::try_new(BTreeMap::from([(
        TypeVarId::new("a", 0, Sort::empty()),
        Ty::prop(),
    )]))
    .unwrap();
    let argument = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let source = KernelRules::instantiate(
        &context,
        &source,
        &types,
        &[InstEntry::new("x", 0, Ty::prop(), argument)],
    )
    .unwrap();
    assert!(source.clone().try_close().is_err());
    let stripped = KernelRules::strip_shyps(&owner, &context, &source).unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "refl_P", stripped.try_close().unwrap()).unwrap();
    assert_eq!(token.prop(), source.prop());
    assert!(token.dependencies().is_empty());
}

#[test]
fn strip_generalized_discharged_hypothesis_preserves_schema() {
    let (owner, context) = build_owner();
    let mut local = context.clone();
    local.declare_free("P_local", Ty::prop());
    let proposition = local.certify_prop(RawTerm::free("P_local", Ty::prop())).unwrap();
    let assumed = KernelRules::assume(proposition.clone()).unwrap().into_kernel();
    let closed = KernelRules::implies_intr(&proposition, &assumed).unwrap();
    let source =
        KernelRules::generalize(&closed, &BTreeSet::new(), &BTreeSet::from(["P_local".into()]), 0)
            .unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &source).unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "schema_identity", stripped.try_close().unwrap()).unwrap();
    let expected = context
        .certify_prop(RawTerm::imp(
            RawTerm::var("P_local", 0, Ty::prop()),
            RawTerm::var("P_local", 0, Ty::prop()),
        ))
        .unwrap();
    assert_eq!(token.prop(), &expected);
}

#[test]
fn strip_proof_only_free_at_final_index_accepts_without_unused_allocation() {
    let (owner, context) = build_owner();
    let mut local = context.clone();
    local.declare_free("u", Ty::prop());
    local.declare_free("x", Ty::prop());
    let variable = local.certify_term(RawTerm::var("P", usize::MAX - 1, Ty::prop())).unwrap();
    let binder = local.certify_term(RawTerm::free("u", Ty::prop())).unwrap();
    let argument = local.certify_term(RawTerm::free("x", Ty::prop())).unwrap();
    let reflexive = KernelRules::reflexive(variable);
    let quantified = KernelRules::forall_intr(&binder, reflexive.as_kernel()).unwrap();
    let source = KernelRules::forall_elim(&quantified, &argument).unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &local, &source).unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "final_proof_index", stripped.try_close().unwrap()).unwrap();
    assert_eq!(token.prop(), source.prop());
    assert!(token.dependencies().is_empty());
}

#[test]
fn strip_proof_only_free_with_exhausted_index_rejects_required_allocation() {
    let (owner, context) = build_owner();
    let mut local = context.clone();
    local.declare_free("u", Ty::prop());
    local.declare_free("x", Ty::prop());
    let variable = local.certify_term(RawTerm::var("P", usize::MAX, Ty::prop())).unwrap();
    let binder = local.certify_term(RawTerm::free("u", Ty::prop())).unwrap();
    let argument = local.certify_term(RawTerm::free("x", Ty::prop())).unwrap();
    let reflexive = KernelRules::reflexive(variable);
    let quantified = KernelRules::forall_intr(&binder, reflexive.as_kernel()).unwrap();
    let source = KernelRules::forall_elim(&quantified, &argument).unwrap();
    assert!(matches!(
        KernelRules::strip_shyps(&owner, &local, &source),
        Err(KernelError::BoundProof(isabelle_kernel::BoundProofError::IndexOverflow)),
    ));
}

#[test]
fn strip_unused_forall_argument_preserves_real_hypothesis() {
    let (owner, context) = build_owner();
    let alpha = Ty::tvar("hidden", 0, Sort::empty());
    let mut local = context.clone();
    local.declare_free("unused", alpha.clone());
    let variable = local.certify_term(RawTerm::free("unused", alpha.clone())).unwrap();
    let proposition = context.certify_prop(RawTerm::const_("P", Ty::prop())).unwrap();
    let source = KernelRules::assume(proposition.clone()).unwrap().into_kernel();
    let quantified = KernelRules::forall_intr(&variable, &source).unwrap();
    let argument = context.certify_term(RawTerm::var("argument", 0, alpha)).unwrap();
    let source = KernelRules::forall_elim(&quantified, &argument).unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &source).unwrap();
    assert_eq!(stripped.hyps(), source.hyps());
    assert!(stripped.clone().try_close().is_err());
    let closed = KernelRules::implies_intr(&proposition, &stripped).unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "real_hypothesis", closed.try_close().unwrap()).unwrap();
    let expected = context
        .certify_prop(RawTerm::imp(
            RawTerm::const_("P", Ty::prop()),
            RawTerm::const_("P", Ty::prop()),
        ))
        .unwrap();
    assert_eq!(token.prop(), &expected);
}

fn build_sorted_extra(owner: &TrustedTheory) -> (ProofContext, isabelle_kernel::KernelThm) {
    let context = ProofContext::new(owner.snapshot().clone());
    let alpha = Ty::tvar("hidden", 0, Sort::hol_type());
    let mut local = context.clone();
    local.declare_free("unused", alpha.clone());
    let variable = local.certify_term(RawTerm::free("unused", alpha.clone())).unwrap();
    let proposition = context.certify_prop(RawTerm::const_("P", Ty::prop())).unwrap();
    let assumed = KernelRules::assume(proposition).unwrap().into_kernel();
    let quantified = KernelRules::forall_intr(&variable, &assumed).unwrap();
    let argument = context.certify_term(RawTerm::var("argument", 0, alpha)).unwrap();
    (context, KernelRules::forall_elim(&quantified, &argument).unwrap())
}

#[test]
fn strip_extra_sort_without_ground_certificate_remains_open() {
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const("P", Ty::prop())
        .unwrap();
    let owner = TrustedTheory::root("Sorted", signature)
        .declare_fresh_nonempty_tycon("HOL.bool", 0)
        .unwrap();
    let (context, source) = build_sorted_extra(&owner);
    let stripped = KernelRules::strip_shyps(&owner, &context, &source).unwrap();
    assert!(stripped.shyps().contains(&Sort::hol_type()));
    let proposition = context.certify_prop(RawTerm::const_("P", Ty::prop())).unwrap();
    let closed = KernelRules::implies_intr(&proposition, &stripped).unwrap();
    assert!(closed.try_close().is_err());
}
#[test]
fn unconstrain_t_unwitnessed_extra_sort_exports_without_erasing_evidence() {
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const("P", Ty::prop())
        .unwrap();
    let owner = TrustedTheory::root("Extra", signature)
        .declare_fresh_nonempty_tycon("HOL.bool", 0)
        .unwrap();
    let (context, source) = build_sorted_extra(&owner);
    let proposition = context.certify_prop(RawTerm::const_("P", Ty::prop())).unwrap();
    let closed = KernelRules::implies_intr(&proposition, &source).unwrap();
    let exported = KernelRules::unconstrain_t(&owner, &context, &closed).unwrap();
    assert_eq!(exported.prop().term().nprems(), 2);
    assert_eq!(exported.shyps().iter().cloned().collect::<Vec<_>>(), vec![Sort::empty()]);
    let (_, token) =
        accept_closed_theorem(&owner, "unwitnessed_export", exported.try_close().unwrap()).unwrap();
    assert_eq!(token.prop().term().nprems(), 2);
}

#[test]
fn strip_extra_sort_with_ground_certificate_preserves_dependency() {
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const("P", Ty::prop())
        .unwrap();
    let owner = TrustedTheory::root("Sorted", signature)
        .declare_fresh_nonempty_tycon("HOL.bool", 0)
        .unwrap()
        .install_semantic_arity(SemanticArityCert::FreshNonemptyTyconCert {
            tycon: "HOL.bool".into(),
            arity: 0,
        })
        .unwrap();
    let (context, source) = build_sorted_extra(&owner);
    let stripped = KernelRules::strip_shyps(&owner, &context, &source).unwrap();
    assert_eq!(stripped.prop(), source.prop());
    let proposition = context.certify_prop(RawTerm::const_("P", Ty::prop())).unwrap();
    let closed = KernelRules::implies_intr(&proposition, &stripped).unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "sorted_ground", closed.try_close().unwrap()).unwrap();
    assert_eq!(token.dependencies().len(), 1);
}

#[test]
fn strip_unused_axiom_argument_preserves_exact_dependency() {
    let signature = Signature::new().extend_const("P", Ty::prop()).unwrap();
    let proposition =
        RawTerm::eq(RawTerm::const_("P", Ty::prop()), RawTerm::const_("P", Ty::prop()));
    let basis = LogicBasis::try_new(
        vec![],
        vec![AxiomSchema {
            name: "unused".into(),
            prop: RawTerm::forall("unused", Ty::prop(), proposition.clone()),
        }],
    )
    .unwrap();
    let owner = TrustedTheory::with_basis("StripBasis", signature, &basis).unwrap();
    let context = ProofContext::new(owner.snapshot().clone());
    let alpha = Ty::tvar("hidden", 0, Sort::empty());
    let argument = context
        .certify_term(RawTerm::app(
            RawTerm::abs("unused", alpha.clone(), RawTerm::const_("P", Ty::prop())),
            RawTerm::var("argument", 0, alpha),
        ))
        .unwrap();
    let source = theorem_builder::axiom_theorem(
        &context,
        &basis,
        "unused".into(),
        TypeInstantiation::empty(),
        vec![argument],
        proposition,
    )
    .unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &source).unwrap();
    let (updated, token) =
        accept_closed_theorem(&owner, "axiom_instance", stripped.try_close().unwrap()).unwrap();
    assert_eq!(token.prop(), source.prop());
    assert_eq!(token.dependencies().len(), 1);
    let reference = KernelRules::theorem_ref(&updated, &token).unwrap();
    let context = ProofContext::new(updated.snapshot().clone());
    let stripped = KernelRules::strip_shyps(&updated, &context, reference.as_kernel()).unwrap();
    let (_, second) =
        accept_closed_theorem(&updated, "reference", stripped.try_close().unwrap()).unwrap();
    assert_eq!(second.prop().term(), token.prop().term());
    assert_eq!(second.dependencies().len(), 1);
}

#[test]
fn strip_wrong_owner_rejects_before_lowering() {
    let (owner, context) = build_owner();
    let other = TrustedTheory::root("Other", owner.signature().clone());
    let term = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let source = KernelRules::reflexive(term).into_kernel();
    let result = KernelRules::strip_shyps(&other, &context, &source);
    assert!(matches!(result, Err(KernelError::MixedContext { .. })));
}

#[test]
fn strip_resolution_preserves_implication_valued_conclusion() {
    let signature = Signature::new()
        .extend_const("A", Ty::prop())
        .unwrap()
        .extend_const("B", Ty::prop())
        .unwrap();
    let owner = TrustedTheory::root("Resolution", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    let mut local = context.clone();
    local.declare_free("q", Ty::prop());
    let q = local.certify_prop(RawTerm::free("q", Ty::prop())).unwrap();
    let rule =
        KernelRules::implies_intr(&q, KernelRules::assume(q.clone()).unwrap().as_kernel()).unwrap();
    let rule =
        KernelRules::generalize(&rule, &BTreeSet::new(), &BTreeSet::from(["q".into()]), 0).unwrap();
    let premise = context
        .certify_prop(RawTerm::imp(
            RawTerm::const_("A", Ty::prop()),
            RawTerm::const_("B", Ty::prop()),
        ))
        .unwrap();
    let goal = KernelRules::implies_intr(
        &premise,
        KernelRules::assume(premise.clone()).unwrap().as_kernel(),
    )
    .unwrap();
    let source = KernelRules::resolve1_match(&rule, &goal, 0).unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &source).unwrap();
    let (_, accepted) =
        accept_closed_theorem(&owner, "composed", stripped.try_close().unwrap()).unwrap();
    assert_eq!(accepted.prop(), goal.prop());
}

#[test]
fn strip_unused_free_argument_preserves_context_and_accepts() {
    let (owner, mut context) = build_owner();
    let alpha = Ty::tvar("hidden", 0, Sort::empty());
    context.declare_free("u", alpha.clone());
    context.declare_free("x", alpha.clone());
    let variable = context.certify_term(RawTerm::free("u", alpha.clone())).unwrap();
    let argument = context.certify_term(RawTerm::free("x", alpha.clone())).unwrap();
    let constant = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let source = KernelRules::reflexive(constant).into_kernel();
    let quantified = KernelRules::forall_intr(&variable, &source).unwrap();
    let source = KernelRules::forall_elim(&quantified, &argument).unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &source).unwrap();
    let (_, accepted) =
        accept_closed_theorem(&owner, "free_argument", stripped.try_close().unwrap()).unwrap();
    assert_eq!(accepted.prop(), source.prop());
    assert!(context.certify_term(RawTerm::free("x", alpha)).is_ok());
    assert!(context.certify_term(RawTerm::free("x", Ty::prop())).is_err());
}

#[test]
fn strip_unused_axiom_free_argument_replays_source() {
    let signature = Signature::new().extend_const("P", Ty::prop()).unwrap();
    let proposition =
        RawTerm::eq(RawTerm::const_("P", Ty::prop()), RawTerm::const_("P", Ty::prop()));
    let basis = LogicBasis::try_new(
        vec![],
        vec![AxiomSchema {
            name: "unused".into(),
            prop: RawTerm::forall("unused", Ty::prop(), proposition.clone()),
        }],
    )
    .unwrap();
    let owner = TrustedTheory::with_basis("FreeArgument", signature, &basis).unwrap();
    let mut context = ProofContext::new(owner.snapshot().clone());
    let alpha = Ty::tvar("hidden", 0, Sort::empty());
    context.declare_free("argument", alpha.clone());
    let argument = context
        .certify_term(RawTerm::app(
            RawTerm::abs("unused", alpha.clone(), RawTerm::const_("P", Ty::prop())),
            RawTerm::free("argument", alpha),
        ))
        .unwrap();
    let source = theorem_builder::axiom_theorem(
        &context,
        &basis,
        "unused".into(),
        TypeInstantiation::empty(),
        vec![argument],
        proposition,
    )
    .unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &source).unwrap();
    let (updated, token) =
        accept_closed_theorem(&owner, "free_instance", stripped.try_close().unwrap()).unwrap();
    assert_eq!(token.prop(), source.prop());
    assert_eq!(token.dependencies().len(), 1);
    assert!(KernelRules::theorem_ref(&updated, &token).is_ok());
}

#[test]
fn strip_unused_substitution_free_argument_preserves_statement() {
    let (owner, mut context) = build_owner();
    context.declare_free("argument", Ty::prop());
    let constant = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let argument = context.certify_term(RawTerm::free("argument", Ty::prop())).unwrap();
    let source = KernelRules::reflexive(constant).into_kernel();
    let source = KernelRules::instantiate(
        &context,
        &source,
        &TypeInstantiation::empty(),
        &[InstEntry::new("unused", 0, Ty::prop(), argument)],
    )
    .unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &source).unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "unused_substitution", stripped.try_close().unwrap())
            .unwrap();
    assert_eq!(token.prop(), source.prop());
    assert!(token.dependencies().is_empty());
}
