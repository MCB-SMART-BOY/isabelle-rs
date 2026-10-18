use std::collections::BTreeMap;

use isabelle_kernel::{
    EmptyClassDeclCert, InstEntry, KernelError, KernelRules, PayloadError, ProofContext, RawTerm,
    Signature, Sort, TrustedTheory, Ty, TypeInstantiation, TypeVarId, accept_closed_theorem,
};

fn make_owner() -> (TrustedTheory, ProofContext) {
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const("P", Ty::prop())
        .unwrap();
    let owner = TrustedTheory::root("Payload", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    (owner, context)
}

fn instantiate_erased_type(sort: Sort) -> Result<isabelle_kernel::KernelThm, KernelError> {
    let (_, context) = make_owner();
    let atom = Ty::tvar("a", 0, sort.clone());
    let var = context.certify_term(RawTerm::var("x", 0, atom)).unwrap();
    let source = KernelRules::reflexive(var);
    let type_inst =
        TypeInstantiation::try_new(BTreeMap::from([(TypeVarId::new("a", 0, sort), Ty::prop())]))?;
    let constant = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let subst = InstEntry::new("x", 0, Ty::prop(), constant);
    KernelRules::instantiate(&context, source.as_kernel(), &type_inst, &[subst])
}

#[test]
fn theorem_erased_sorted_type_without_arity_rejects() {
    assert!(matches!(
        instantiate_erased_type(Sort::hol_type()),
        Err(KernelError::TypeSortMismatch { .. })
    ));
}

#[test]
fn close_thm_unsolved_empty_sort_constraint_rejects() {
    let instance = instantiate_erased_type(Sort::empty()).unwrap();
    assert!(matches!(
        isabelle_kernel::theorem_builder::close_thm(instance),
        Err(KernelError::TheoremObligations(PayloadError::ExtraSortHypotheses { sorts: 1 }))
    ));
}

#[test]
fn theorem_erased_empty_sort_preserves_extra_sort_hypothesis() {
    let instance = instantiate_erased_type(Sort::empty()).unwrap();
    assert!(matches!(
        instance.try_close(),
        Err(KernelError::TheoremObligations(PayloadError::ExtraSortHypotheses { sorts: 1 }))
    ));
}
#[test]
fn theorem_symmetric_preserves_disappeared_empty_sort() {
    let instance = instantiate_erased_type(Sort::empty()).unwrap();
    let symmetric = KernelRules::symmetric(&instance).unwrap();
    assert!(matches!(
        symmetric.try_close(),
        Err(KernelError::TheoremObligations(PayloadError::ExtraSortHypotheses { sorts: 1 }))
    ));
}

#[test]
fn theorem_present_schema_sort_remains_closable_and_accepted() {
    let (owner, context) = make_owner();
    let atom = Ty::tvar("a", 0, Sort::hol_type());
    let var = context.certify_term(RawTerm::var("x", 0, atom.clone())).unwrap();
    let theorem = KernelRules::reflexive(var);
    let (_, accepted) = accept_closed_theorem(&owner, "sorted_reflexive", theorem).unwrap();
    let expected = context
        .certify_prop(RawTerm::eq(RawTerm::var("x", 0, atom.clone()), RawTerm::var("x", 0, atom)))
        .unwrap();
    assert_eq!(accepted.prop().term(), expected.term());
}

fn certify_hidden_sorted_argument(context: &ProofContext) -> isabelle_kernel::CTerm {
    let alpha = Ty::tvar("hidden_type", 0, Sort::hol_type());
    context
        .certify_term(RawTerm::app(
            RawTerm::abs("unused", alpha.clone(), RawTerm::const_("P", Ty::prop())),
            RawTerm::var("hidden", 0, alpha),
        ))
        .unwrap()
}

#[test]
fn instantiate_unused_term_replacement_retains_hidden_sort() {
    let (_, context) = make_owner();
    let constant = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let source = KernelRules::reflexive(constant);
    let replacement = certify_hidden_sorted_argument(&context);
    let result = KernelRules::instantiate(
        &context,
        source.as_kernel(),
        &TypeInstantiation::empty(),
        &[InstEntry::new("unused", 0, Ty::prop(), replacement)],
    )
    .unwrap();
    assert!(matches!(
        result.try_close(),
        Err(KernelError::TheoremObligations(PayloadError::ExtraSortHypotheses { sorts: 1 }))
    ));
}

#[test]
fn forall_elim_unused_argument_retains_hidden_sort() {
    let (_, mut context) = make_owner();
    context.declare_free("unused", Ty::prop());
    let variable = context.certify_term(RawTerm::free("unused", Ty::prop())).unwrap();
    let constant = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let source = KernelRules::reflexive(constant);
    let quantified = KernelRules::forall_intr(&variable, source.as_kernel()).unwrap();
    let argument = certify_hidden_sorted_argument(&context);
    let result = KernelRules::forall_elim(&quantified, &argument).unwrap();
    assert!(matches!(
        result.try_close(),
        Err(KernelError::TheoremObligations(PayloadError::ExtraSortHypotheses { sorts: 1 }))
    ));
}

#[test]
fn axiom_instance_unused_argument_retains_hidden_sort() {
    use isabelle_kernel::{AxiomSchema, LogicBasis, theorem_builder};

    let signature = Signature::new()
        .install_empty_class(isabelle_kernel::EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const("P", Ty::prop())
        .unwrap();
    let proposition =
        RawTerm::eq(RawTerm::const_("P", Ty::prop()), RawTerm::const_("P", Ty::prop()));
    let basis = LogicBasis::try_new(
        vec![],
        vec![AxiomSchema {
            name: "unused_argument".into(),
            prop: RawTerm::forall("unused", Ty::prop(), proposition.clone()),
        }],
    )
    .unwrap();
    let owner = TrustedTheory::with_basis("Payload", signature, &basis).unwrap();
    let context = ProofContext::new(owner.snapshot().clone());
    let argument = certify_hidden_sorted_argument(&context);
    let result = theorem_builder::axiom_theorem(
        &context,
        &basis,
        "unused_argument".into(),
        TypeInstantiation::empty(),
        vec![argument],
        proposition,
    )
    .unwrap();
    assert!(matches!(
        result.try_close(),
        Err(KernelError::TheoremObligations(PayloadError::ExtraSortHypotheses { sorts: 1 }))
    ));
}
