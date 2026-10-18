use isabelle_kernel::{
    CompositionCandidate, InstEntry, KernelRules, ProofContext, RawTerm, Signature, TrustedTheory,
    Ty, TypeInstantiation, accept_closed_theorem,
};

#[test]
fn assumption_candidate_implication_valued_conclusion_preserves_source_slot() {
    let signature = Signature::new().extend_const("R", Ty::prop()).unwrap();
    let owner = TrustedTheory::root("SourceSpine", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    let r = RawTerm::const_("R", Ty::prop());
    let assumption = RawTerm::imp(r.clone(), r.clone());
    let goal = context
        .certify_prop(RawTerm::imp(assumption.clone(), RawTerm::var("X", 0, Ty::prop())))
        .unwrap();
    let reflexive = KernelRules::reflexive(context.certify_term(r).unwrap());
    let state = KernelRules::implies_intr(&goal, reflexive.as_kernel()).unwrap();
    let candidate = CompositionCandidate {
        type_inst: TypeInstantiation::empty(),
        rule_subst: Vec::new(),
        state_subst: vec![InstEntry::new(
            "X",
            0,
            Ty::prop(),
            context.certify_term(assumption).unwrap(),
        )],
        residual_pairs: Vec::new(),
        elimination_choice: Some(0),
    };
    let result =
        KernelRules::assumption_candidate(&owner, &context, 1, &state, &candidate).unwrap();
    assert_eq!(result.prop().term(), reflexive.as_kernel().prop().term());
    let (accepted, token) =
        accept_closed_theorem(&owner, "source_spine", result.try_close().unwrap()).unwrap();
    assert_eq!(
        KernelRules::theorem_ref(&accepted, &token).unwrap().as_kernel().prop().term(),
        reflexive.as_kernel().prop().term(),
    );
}

#[test]
fn assumption_candidate_first_of_two_original_premises_replays_after_implication_substitution() {
    let signature = Signature::new().extend_const("R", Ty::prop()).unwrap();
    let owner = TrustedTheory::root("TwoSourceSlots", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    let r = RawTerm::const_("R", Ty::prop());
    let first = RawTerm::imp(r.clone(), r.clone());
    let goal = context
        .certify_prop(RawTerm::imp(
            first.clone(),
            RawTerm::imp(r.clone(), RawTerm::var("X", 0, Ty::prop())),
        ))
        .unwrap();
    let reflexive = KernelRules::reflexive(context.certify_term(r).unwrap());
    let state = KernelRules::implies_intr(&goal, reflexive.as_kernel()).unwrap();
    let candidate = CompositionCandidate {
        type_inst: TypeInstantiation::empty(),
        rule_subst: Vec::new(),
        state_subst: vec![InstEntry::new("X", 0, Ty::prop(), context.certify_term(first).unwrap())],
        residual_pairs: Vec::new(),
        elimination_choice: Some(0),
    };
    let result =
        KernelRules::assumption_candidate(&owner, &context, 1, &state, &candidate).unwrap();
    assert_eq!(result.prop().term(), reflexive.as_kernel().prop().term());
    accept_closed_theorem(&owner, "two_source_slots", result.try_close().unwrap()).unwrap();
}
