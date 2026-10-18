use isabelle_kernel::{
    CompositionCandidate, InstEntry, KernelError, KernelRules, ProofContext, RawTerm, Signature,
    TrustedTheory, Ty, TypeInstantiation,
};

#[test]
fn assumption_candidate_nested_type_annotations_exceed_budget_rejected() {
    let signature = Signature::new().extend_const("R", Ty::prop()).unwrap();
    let owner = TrustedTheory::root("CandidateBudget", signature);
    let mut context = ProofContext::new(owner.snapshot().clone());
    let mut large_type = Ty::prop();
    for _ in 0..9 {
        large_type = Ty::arrow(large_type.clone(), large_type);
    }
    context.declare_free("y", large_type.clone());
    let r = RawTerm::const_("R", Ty::prop());
    let mut source = r.clone();
    for index in (0..9).rev() {
        source = RawTerm::imp(RawTerm::var(format!("x{index}"), 0, Ty::prop()), source);
    }
    let reflexive = KernelRules::reflexive(context.certify_term(source).unwrap());
    let selected = context.certify_prop(RawTerm::imp(r.clone(), r)).unwrap();
    let state = KernelRules::implies_intr(&selected, reflexive.as_kernel()).unwrap();
    let y = RawTerm::free("y", large_type);
    let mut replacement = RawTerm::eq(y.clone(), y);
    let mut state_subst = Vec::new();
    for index in (0..9).rev() {
        state_subst.push(InstEntry::new(
            format!("x{index}"),
            0,
            Ty::prop(),
            context.certify_term(replacement).unwrap(),
        ));
        let next = RawTerm::var(format!("x{index}"), 0, Ty::prop());
        replacement = RawTerm::imp(next.clone(), next);
    }
    let candidate = CompositionCandidate {
        type_inst: TypeInstantiation::empty(),
        rule_subst: Vec::new(),
        state_subst,
        residual_pairs: Vec::new(),
        elimination_choice: None,
    };
    let result = KernelRules::assumption_candidate(&owner, &context, 1, &state, &candidate);
    assert!(matches!(
        result,
        Err(KernelError::BoundProof(
            isabelle_kernel::BoundProofError::CandidateResourceLimit { .. }
        ))
    ));
}
