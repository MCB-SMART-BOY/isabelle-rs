use isabelle_kernel::{
    CompositionCandidate, CompositionFlags, CompositionOptions, EmptyClassDeclCert, InstEntry,
    KernelError, KernelRules, ProofContext, RawTerm, Signature, Sort, TrustedTheory, Ty,
    TypeInstantiation, TypeVarId, accept_closed_theorem,
};
use std::collections::BTreeMap;

fn create_owner() -> (TrustedTheory, ProofContext) {
    let signature = Signature::new().extend_const("R", Ty::prop()).unwrap();
    let owner = TrustedTheory::root("Composition", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    (owner, context)
}

fn create_state(context: &ProofContext, goal: RawTerm) -> isabelle_kernel::KernelThm {
    let premise = context.certify_prop(goal).unwrap();
    let reflexive =
        KernelRules::reflexive(context.certify_term(RawTerm::const_("R", Ty::prop())).unwrap());
    KernelRules::implies_intr(&premise, reflexive.as_kernel()).unwrap()
}

fn interleaved_goal() -> RawTerm {
    RawTerm::forall(
        "x",
        Ty::prop(),
        RawTerm::imp(
            RawTerm::bound(0),
            RawTerm::forall("y", Ty::prop(), RawTerm::imp(RawTerm::bound(0), RawTerm::bound(1))),
        ),
    )
}

#[test]
fn eq_assumption_outer_forall_then_implication_discharge_selected_goal() {
    let (owner, context) = create_owner();
    let state = create_state(
        &context,
        RawTerm::forall("x", Ty::prop(), RawTerm::imp(RawTerm::bound(0), RawTerm::bound(0))),
    );
    let result = KernelRules::eq_assumption(&owner, &context, 1, &state).unwrap();
    assert_eq!(result.prop().term(), state.prop().term().dest_imp_chain().1);
    assert_eq!(result.max_var_index(), state.max_var_index());
    accept_closed_theorem(&owner, "outer_forall", result.try_close().unwrap()).unwrap();
}

#[test]
fn eq_assumption_interleaved_inner_forall_not_an_assumption() {
    let (owner, context) = create_owner();
    let state = create_state(&context, interleaved_goal());
    assert!(matches!(
        KernelRules::eq_assumption(&owner, &context, 1, &state),
        Err(KernelError::AntecedentMismatch),
    ));
}

#[test]
fn eq_assumption_wrong_goal_or_index_rejects() {
    let (owner, context) = create_owner();
    let nonidentity = RawTerm::forall(
        "x",
        Ty::prop(),
        RawTerm::imp(RawTerm::bound(0), RawTerm::const_("R", Ty::prop())),
    );
    let state = create_state(&context, nonidentity);
    assert!(matches!(
        KernelRules::eq_assumption(&owner, &context, 1, &state),
        Err(KernelError::AntecedentMismatch),
    ));
    assert!(matches!(
        KernelRules::eq_assumption(&owner, &context, 0, &state),
        Err(KernelError::SubgoalIndexOutOfRange { .. }),
    ));
    assert!(matches!(
        KernelRules::eq_assumption(&owner, &context, 2, &state),
        Err(KernelError::SubgoalIndexOutOfRange { .. }),
    ));
}

#[test]
fn eq_assumption_eta_equivalent_equality_discharge_replays() {
    let function_type = Ty::arrow(Ty::prop(), Ty::prop());
    let signature = Signature::new()
        .extend_const("R", Ty::prop())
        .unwrap()
        .extend_const("f", function_type.clone())
        .unwrap();
    let owner = TrustedTheory::root("EtaComposition", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    let f = RawTerm::const_("f", function_type);
    let eta = RawTerm::abs("x", Ty::prop(), RawTerm::app(f.clone(), RawTerm::bound(0)));
    let goal = RawTerm::imp(RawTerm::eq(eta, f.clone()), RawTerm::eq(f.clone(), f));
    let state = create_state(&context, goal);
    let result = KernelRules::eq_assumption(&owner, &context, 1, &state).unwrap();
    assert_eq!(result.prop().term(), state.prop().term().dest_imp_chain().1);
    accept_closed_theorem(&owner, "eta_discharge", result.try_close().unwrap()).unwrap();
}

#[test]
fn eq_assumption_beta_only_antecedent_rejects() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let beta = RawTerm::app(RawTerm::abs("x", Ty::prop(), RawTerm::bound(0)), r.clone());
    let state = create_state(&context, RawTerm::imp(beta, r));
    assert!(matches!(
        KernelRules::eq_assumption(&owner, &context, 1, &state),
        Err(KernelError::AntecedentMismatch),
    ));
}

#[test]
fn assumption_candidate_new_implication_from_substitution_cannot_create_source_slot() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let variable = RawTerm::var("X", 0, Ty::prop());
    let state = create_state(&context, variable);
    let mut candidate = create_empty_candidate();
    candidate.state_subst.push(InstEntry::new(
        "X",
        0,
        Ty::prop(),
        context.certify_term(RawTerm::imp(r.clone(), r)).unwrap(),
    ));
    candidate.elimination_choice = Some(0);
    assert!(matches!(
        KernelRules::assumption_candidate(&owner, &context, 1, &state, &candidate),
        Err(KernelError::BoundProof(isabelle_kernel::BoundProofError::InvalidEliminationChoice {
            choice: 0
        },)),
    ));
}

#[test]
fn assumption_candidate_existing_implication_after_substitution_replays() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let variable = RawTerm::var("X", 0, Ty::prop());
    let state = create_state(&context, RawTerm::imp(r.clone(), variable));
    let mut candidate = create_empty_candidate();
    candidate.state_subst.push(InstEntry::new(
        "X",
        0,
        Ty::prop(),
        context.certify_term(r).unwrap(),
    ));
    let result =
        KernelRules::assumption_candidate(&owner, &context, 1, &state, &candidate).unwrap();
    accept_closed_theorem(&owner, "source_assumption", result.try_close().unwrap()).unwrap();
}

#[test]
fn bicompose_candidate_proof_only_var_type_collision_does_not_change_full_prop_unification() {
    let (owner, mut context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let eq = RawTerm::eq(r.clone(), r.clone());
    let function_type = Ty::arrow(Ty::prop(), Ty::prop());
    context.declare_free("unused_rule", Ty::prop());
    context.declare_free("unused_state", function_type.clone());
    let base = KernelRules::reflexive(context.certify_term(r).unwrap());
    let rule_quantified = KernelRules::forall_intr(
        &context.certify_term(RawTerm::free("unused_rule", Ty::prop())).unwrap(),
        base.as_kernel(),
    )
    .unwrap();
    let rule = KernelRules::forall_elim(
        &rule_quantified,
        &context.certify_term(RawTerm::var("v", 0, Ty::prop())).unwrap(),
    )
    .unwrap();
    let state_quantified = KernelRules::forall_intr(
        &context.certify_term(RawTerm::free("unused_state", function_type.clone())).unwrap(),
        base.as_kernel(),
    )
    .unwrap();
    let state_conclusion = KernelRules::forall_elim(
        &state_quantified,
        &context.certify_term(RawTerm::var("v", 0, function_type)).unwrap(),
    )
    .unwrap();
    let state =
        KernelRules::implies_intr(&context.certify_prop(eq).unwrap(), &state_conclusion).unwrap();
    for is_incremented in [false, true] {
        let result = KernelRules::bicompose_candidate(
            &owner,
            &context,
            CompositionOptions {
                flags: CompositionFlags { is_incremented, ..Default::default() },
                is_elimination: false,
                premise_count: 0,
                subgoal_index: 1,
            },
            &rule,
            &state,
            &create_empty_candidate(),
        )
        .unwrap();
        assert_eq!(result.prop(), state_conclusion.prop());
    }
}

fn create_empty_candidate() -> CompositionCandidate {
    CompositionCandidate {
        type_inst: TypeInstantiation::empty(),
        rule_subst: Vec::new(),
        state_subst: Vec::new(),
        residual_pairs: Vec::new(),
        elimination_choice: None,
    }
}

#[test]
fn bicompose_candidate_exact_rule_premise_replays_and_accepts() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let eq = RawTerm::eq(r.clone(), r.clone());
    let rule = KernelRules::implies_intr(
        &context.certify_prop(r).unwrap(),
        KernelRules::reflexive(context.certify_term(RawTerm::const_("R", Ty::prop())).unwrap())
            .as_kernel(),
    )
    .unwrap();
    let state = create_state(&context, eq);
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: false,
            premise_count: 1,
            subgoal_index: 1,
        },
        &rule,
        &state,
        &create_empty_candidate(),
    )
    .unwrap();
    assert_eq!(result.prop(), rule.prop());
    accept_closed_theorem(&owner, "resolved", result.try_close().unwrap()).unwrap();
}

#[test]
fn bicompose_candidate_beta_assignment_replays_source_and_accepts() {
    let (owner, context) = create_owner();
    let variable = RawTerm::var("v", 0, Ty::prop());
    let rule = KernelRules::reflexive(context.certify_term(variable).unwrap());
    let r = RawTerm::const_("R", Ty::prop());
    let state = create_state(&context, RawTerm::eq(r.clone(), r.clone()));
    let beta_redex = RawTerm::app(RawTerm::abs("x", Ty::prop(), RawTerm::bound(0)), r.clone());
    let mut candidate = create_empty_candidate();
    candidate.rule_subst.push(InstEntry::new(
        "v",
        0,
        Ty::prop(),
        context.certify_term(beta_redex).unwrap(),
    ));
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        rule.as_kernel(),
        &state,
        &candidate,
    )
    .unwrap();
    let expected = context.certify_prop(RawTerm::eq(r.clone(), r)).unwrap();
    assert_eq!(result.prop(), &expected);
    accept_closed_theorem(&owner, "beta_assignment", result.try_close().unwrap()).unwrap();
}

#[test]
fn bicompose_candidate_theorem_ref_beta_assignment_replays() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let function_type = Ty::arrow(Ty::prop(), Ty::prop());
    let f = RawTerm::var("f", 0, function_type.clone());
    let source = KernelRules::reflexive(context.certify_term(RawTerm::app(f, r.clone())).unwrap());
    let (accepted_owner, token) =
        accept_closed_theorem(&owner, "schematic_reflexive", source).unwrap();
    let accepted_context = ProofContext::new(accepted_owner.snapshot().clone());
    let rule = KernelRules::theorem_ref(&accepted_owner, &token).unwrap();
    let state = create_state(&accepted_context, RawTerm::eq(r.clone(), r.clone()));
    let mut candidate = create_empty_candidate();
    candidate.rule_subst.push(InstEntry::new(
        "f",
        0,
        function_type,
        accepted_context.certify_term(RawTerm::abs("x", Ty::prop(), RawTerm::bound(0))).unwrap(),
    ));
    let result = KernelRules::bicompose_candidate(
        &accepted_owner,
        &accepted_context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        rule.as_kernel(),
        &state,
        &candidate,
    )
    .unwrap();
    assert_eq!(
        result.prop(),
        &accepted_context.certify_prop(RawTerm::eq(r.clone(), r.clone())).unwrap(),
    );
    accept_closed_theorem(&accepted_owner, "instantiated_reference", result.try_close().unwrap())
        .unwrap();
}

#[test]
fn bicompose_candidate_forall_elim_created_beta_replays() {
    let (owner, mut context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let function_type = Ty::arrow(Ty::prop(), Ty::prop());
    context.declare_free("u", function_type.clone());
    let applied = RawTerm::app(RawTerm::free("u", function_type.clone()), r.clone());
    let reflexive = KernelRules::reflexive(context.certify_term(applied).unwrap());
    let forall = KernelRules::forall_intr(
        &context.certify_term(RawTerm::free("u", function_type.clone())).unwrap(),
        reflexive.as_kernel(),
    )
    .unwrap();
    let rule = KernelRules::forall_elim(
        &forall,
        &context.certify_term(RawTerm::var("f", 0, function_type.clone())).unwrap(),
    )
    .unwrap();
    let state = create_state(&context, RawTerm::eq(r.clone(), r.clone()));
    let mut candidate = create_empty_candidate();
    candidate.rule_subst.push(InstEntry::new(
        "f",
        0,
        function_type,
        context.certify_term(RawTerm::abs("x", Ty::prop(), RawTerm::bound(0))).unwrap(),
    ));
    let result = KernelRules::bicompose_candidate(
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
    assert_eq!(result.prop(), &context.certify_prop(RawTerm::eq(r.clone(), r)).unwrap(),);
    accept_closed_theorem(&owner, "elim_created_beta", result.try_close().unwrap()).unwrap();
}

#[test]
fn lift_rule_existing_sort_obligation_remains_open_after_index_shift() {
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const("R", Ty::prop())
        .unwrap();
    let owner = TrustedTheory::root("SortedComposition", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    let sort = Sort::hol_type();
    let source_ty = Ty::tvar("a", 0, sort.clone());
    let target_ty = Ty::tvar("b", 0, sort.clone());
    let source =
        KernelRules::reflexive(context.certify_term(RawTerm::var("v", 0, source_ty)).unwrap());
    let types =
        TypeInstantiation::try_new(BTreeMap::from([(TypeVarId::new("a", 0, sort), target_ty)]))
            .unwrap();
    let source = KernelRules::instantiate(&context, source.as_kernel(), &types, &[]).unwrap();
    assert!(matches!(
        source.clone().try_close(),
        Err(KernelError::TheoremObligations(
            isabelle_kernel::PayloadError::UnresolvedSortConstraints { constraints: 1 },
        )),
    ));
    let goal = context.certify_term(RawTerm::var("goal", 0, Ty::prop())).unwrap();
    let lifted = KernelRules::lift_rule(&owner, &context, &goal, &source).unwrap();
    assert!(matches!(
        lifted.try_close(),
        Err(KernelError::TheoremObligations(
            isabelle_kernel::PayloadError::UnresolvedSortConstraints { constraints: 1 },
        )),
    ));
}

#[test]
fn assumption_candidate_nested_beta_duplication_returns_resource_limit() {
    const BETA_DUPLICATIONS: usize = 16;
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let x = RawTerm::var("x", 0, Ty::prop());
    let goal = context.certify_prop(RawTerm::imp(r.clone(), r.clone())).unwrap();
    let reflexive = KernelRules::reflexive(context.certify_term(x).unwrap());
    let state = KernelRules::implies_intr(&goal, reflexive.as_kernel()).unwrap();
    let duplicate =
        RawTerm::abs("p", Ty::prop(), RawTerm::imp(RawTerm::bound(0), RawTerm::bound(0)));
    let mut expansion = r;
    for _ in 0..BETA_DUPLICATIONS {
        expansion = RawTerm::app(duplicate.clone(), expansion);
    }
    let mut candidate = create_empty_candidate();
    candidate.state_subst.push(InstEntry::new(
        "x",
        0,
        Ty::prop(),
        context.certify_term(expansion).unwrap(),
    ));
    let result = KernelRules::assumption_candidate(&owner, &context, 1, &state, &candidate);
    assert!(matches!(
        result,
        Err(KernelError::BoundProof(
            isabelle_kernel::BoundProofError::CandidateResourceLimit { .. },
        )),
    ));
}

#[test]
fn bicompose_candidate_forall_and_equality_congruence_preserve_flex() {
    let (owner, mut context) = create_owner();
    context.declare_free("x", Ty::prop());
    let r = RawTerm::const_("R", Ty::prop());
    let b = RawTerm::eq(r.clone(), r.clone());
    let source = KernelRules::reflexive(context.certify_term(r.clone()).unwrap());
    let variable = context.certify_term(RawTerm::free("x", Ty::prop())).unwrap();
    let rule = KernelRules::forall_intr(&variable, source.as_kernel()).unwrap();
    let state =
        create_state(&context, RawTerm::forall("x", Ty::prop(), RawTerm::eq(b.clone(), b.clone())));
    let mut candidate = create_empty_candidate();
    candidate
        .residual_pairs
        .push((context.certify_term(r).unwrap(), context.certify_term(b).unwrap()));
    let result = KernelRules::bicompose_candidate(
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
    assert!(result.try_close().is_err());
}

#[test]
fn bicompose_candidate_lambda_closed_flex_applies_with_beta_under_forall() {
    let (owner, mut context) = create_owner();
    context.declare_free("u", Ty::prop());
    let function_type = Ty::arrow(Ty::prop(), Ty::prop());
    let f = RawTerm::var("F", 0, function_type.clone());
    let g = RawTerm::var("G", 1, function_type);
    let fu = RawTerm::app(f.clone(), RawTerm::free("u", Ty::prop()));
    let source = KernelRules::reflexive(context.certify_term(fu).unwrap());
    let rule = KernelRules::forall_intr(
        &context.certify_term(RawTerm::free("u", Ty::prop())).unwrap(),
        source.as_kernel(),
    )
    .unwrap();
    let gx = RawTerm::app(g.clone(), RawTerm::bound(0));
    let state =
        create_state(&context, RawTerm::forall("x", Ty::prop(), RawTerm::eq(gx.clone(), gx)));
    let closed_f = RawTerm::abs("x", Ty::prop(), RawTerm::app(f, RawTerm::bound(0)));
    let closed_g = RawTerm::abs("x", Ty::prop(), RawTerm::app(g, RawTerm::bound(0)));
    let mut candidate = create_empty_candidate();
    candidate
        .residual_pairs
        .push((context.certify_term(closed_f).unwrap(), context.certify_term(closed_g).unwrap()));
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags { is_lifted: true, ..Default::default() },
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        &rule,
        &state,
        &candidate,
    )
    .unwrap();
    assert!(result.try_close().is_err());
}

#[test]
fn bicompose_candidate_wrong_lambda_closed_flex_rejects() {
    let (owner, mut context) = create_owner();
    context.declare_free("u", Ty::prop());
    let function_type = Ty::arrow(Ty::prop(), Ty::prop());
    let f = RawTerm::var("F", 0, function_type.clone());
    let g = RawTerm::var("G", 1, function_type);
    let source = KernelRules::reflexive(
        context.certify_term(RawTerm::app(f.clone(), RawTerm::free("u", Ty::prop()))).unwrap(),
    );
    let rule = KernelRules::forall_intr(
        &context.certify_term(RawTerm::free("u", Ty::prop())).unwrap(),
        source.as_kernel(),
    )
    .unwrap();
    let gx = RawTerm::app(g, RawTerm::bound(0));
    let state =
        create_state(&context, RawTerm::forall("x", Ty::prop(), RawTerm::eq(gx.clone(), gx)));
    let mut candidate = create_empty_candidate();
    candidate.residual_pairs.push((
        context
            .certify_term(RawTerm::abs("x", Ty::prop(), RawTerm::app(f, RawTerm::bound(0))))
            .unwrap(),
        context
            .certify_term(RawTerm::abs("x", Ty::prop(), RawTerm::const_("R", Ty::prop())))
            .unwrap(),
    ));
    assert!(matches!(
        KernelRules::bicompose_candidate(
            &owner,
            &context,
            CompositionOptions {
                flags: CompositionFlags { is_lifted: true, ..Default::default() },
                is_elimination: false,
                premise_count: 0,
                subgoal_index: 1,
            },
            &rule,
            &state,
            &candidate,
        ),
        Err(KernelError::BoundProof(_)),
    ));
}

#[test]
fn bicompose_candidate_implication_congruence_preserves_flex() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let b = RawTerm::eq(r.clone(), r.clone());
    let source = KernelRules::assume(context.certify_prop(r.clone()).unwrap()).unwrap();
    let rule =
        KernelRules::implies_intr(&context.certify_prop(r.clone()).unwrap(), source.as_kernel())
            .unwrap();
    let state = create_state(&context, RawTerm::imp(b.clone(), b.clone()));
    let mut candidate = create_empty_candidate();
    candidate
        .residual_pairs
        .push((context.certify_term(r).unwrap(), context.certify_term(b).unwrap()));
    let result = KernelRules::bicompose_candidate(
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
    assert!(result.try_close().is_err());
}

#[test]
fn bicompose_candidate_abstraction_congruence_preserves_flex() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let b = RawTerm::eq(r.clone(), r.clone());
    let left = RawTerm::abs("x", Ty::prop(), r.clone());
    let right = RawTerm::abs("x", Ty::prop(), b.clone());
    let source = KernelRules::reflexive(context.certify_term(left).unwrap());
    let state = create_state(&context, RawTerm::eq(right.clone(), right));
    let mut candidate = create_empty_candidate();
    candidate
        .residual_pairs
        .push((context.certify_term(r).unwrap(), context.certify_term(b).unwrap()));
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        source.as_kernel(),
        &state,
        &candidate,
    )
    .unwrap();
    assert!(result.try_close().is_err());
}

#[test]
fn bicompose_candidate_application_congruence_preserves_flex() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let b = RawTerm::eq(r.clone(), r.clone());
    let identity = RawTerm::abs("x", Ty::prop(), RawTerm::bound(0));
    let left = RawTerm::app(identity.clone(), r.clone());
    let right = RawTerm::app(identity, b.clone());
    let source = KernelRules::reflexive(context.certify_term(left).unwrap());
    let state = create_state(&context, RawTerm::eq(right.clone(), right));
    let mut candidate = create_empty_candidate();
    candidate
        .residual_pairs
        .push((context.certify_term(r).unwrap(), context.certify_term(b).unwrap()));
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        source.as_kernel(),
        &state,
        &candidate,
    )
    .unwrap();
    assert!(result.try_close().is_err());
}

#[test]
fn bicompose_candidate_same_name_typed_collision_without_type_env_rejected() {
    let (owner, context) = create_owner();
    let source_var = RawTerm::var("v", 0, Ty::tvar("a", 0, Sort::empty()));
    let state_var = RawTerm::var("v", 0, Ty::prop());
    let rule = KernelRules::reflexive(context.certify_term(source_var).unwrap());
    let state = create_state(&context, RawTerm::eq(state_var.clone(), state_var));
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        rule.as_kernel(),
        &state,
        &create_empty_candidate(),
    );
    assert!(matches!(result, Err(KernelError::TypeMismatch { .. })));
}

#[test]
fn bicompose_candidate_same_name_typed_collision_with_type_env_preserves_extra_sort() {
    let (owner, context) = create_owner();
    let source_var = RawTerm::var("v", 0, Ty::tvar("a", 0, Sort::empty()));
    let state_var = RawTerm::var("v", 0, Ty::prop());
    let rule = KernelRules::reflexive(context.certify_term(source_var).unwrap());
    let state = create_state(&context, RawTerm::eq(state_var.clone(), state_var));
    let mut candidate = create_empty_candidate();
    candidate.type_inst = TypeInstantiation::try_new(BTreeMap::from([(
        TypeVarId::new("a", 0, Sort::empty()),
        Ty::prop(),
    )]))
    .unwrap();
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        rule.as_kernel(),
        &state,
        &candidate,
    )
    .unwrap();
    assert!(matches!(result.try_close(), Err(KernelError::TheoremObligations(_))));
}

#[test]
fn bicompose_candidate_match_state_assignment_rejected() {
    let (owner, context) = create_owner();
    let variable = RawTerm::var("v", 0, Ty::prop());
    let proposition = RawTerm::eq(variable.clone(), variable.clone());
    let rule = KernelRules::reflexive(context.certify_term(variable).unwrap());
    let state = create_state(&context, proposition);
    let replacement = context.certify_term(RawTerm::const_("R", Ty::prop())).unwrap();
    let mut candidate = create_empty_candidate();
    candidate.state_subst.push(InstEntry::new("v", 0, Ty::prop(), replacement));
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags { is_match: true, ..Default::default() },
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        rule.as_kernel(),
        &state,
        &candidate,
    );
    assert!(matches!(result, Err(KernelError::BoundProof(_))));
}

#[test]
fn bicompose_candidate_unsolved_flex_never_closes() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let rule = KernelRules::reflexive(context.certify_term(r.clone()).unwrap());
    let state = create_state(&context, r.clone());
    let mut candidate = create_empty_candidate();
    candidate.residual_pairs.push((
        context.certify_term(RawTerm::eq(r.clone(), r)).unwrap(),
        context.certify_term(RawTerm::const_("R", Ty::prop())).unwrap(),
    ));
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        rule.as_kernel(),
        &state,
        &candidate,
    )
    .unwrap();
    assert!(result.try_close().is_err());
}

#[test]
fn bicompose_candidate_flatten_interleaved_premise_replays_and_accepts() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let premise = interleaved_goal();
    let rule = KernelRules::implies_intr(
        &context.certify_prop(premise).unwrap(),
        KernelRules::reflexive(context.certify_term(r.clone()).unwrap()).as_kernel(),
    )
    .unwrap();
    let state = create_state(&context, RawTerm::eq(r.clone(), r));
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags { is_flattened: true, ..Default::default() },
            is_elimination: false,
            premise_count: 1,
            subgoal_index: 1,
        },
        &rule,
        &state,
        &create_empty_candidate(),
    )
    .unwrap();
    let expected = context
        .certify_prop(RawTerm::forall(
            "x",
            Ty::prop(),
            RawTerm::forall(
                "y",
                Ty::prop(),
                RawTerm::imp(RawTerm::bound(1), RawTerm::imp(RawTerm::bound(0), RawTerm::bound(1))),
            ),
        ))
        .unwrap();
    assert!(result.prop().term().dest_imp_chain().0[0].alpha_eq(expected.term()));
    accept_closed_theorem(&owner, "flattened", result.try_close().unwrap()).unwrap();
}

#[test]
fn bicompose_candidate_elimination_removes_first_premise_and_replays() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let identity =
        RawTerm::forall("x", Ty::prop(), RawTerm::imp(RawTerm::bound(0), RawTerm::bound(0)));
    let reflexive = KernelRules::reflexive(context.certify_term(r.clone()).unwrap());
    let conclusion =
        KernelRules::implies_intr(&context.certify_prop(r.clone()).unwrap(), reflexive.as_kernel())
            .unwrap();
    let second =
        KernelRules::implies_intr(&context.certify_prop(identity.clone()).unwrap(), &conclusion)
            .unwrap();
    let rule =
        KernelRules::implies_intr(&context.certify_prop(identity).unwrap(), &second).unwrap();
    let state = create_state(&context, RawTerm::imp(r.clone(), RawTerm::eq(r.clone(), r)));
    let mut candidate = create_empty_candidate();
    candidate.elimination_choice = Some(0);
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags { is_flattened: true, ..Default::default() },
            is_elimination: true,
            premise_count: 2,
            subgoal_index: 1,
        },
        &rule,
        &state,
        &candidate,
    )
    .unwrap();
    let expected =
        context.certify_prop(RawTerm::forall("x", Ty::prop(), RawTerm::bound(0))).unwrap();
    assert!(result.prop().term().dest_imp_chain().0[0].alpha_eq(expected.term()));
    accept_closed_theorem(&owner, "elimination", result.try_close().unwrap()).unwrap();
}

#[test]
fn bicompose_candidate_elimination_exceeds_nlift_assumption_limit_rejected() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let hypothesis = context.certify_prop(r.clone()).unwrap();
    let base = KernelRules::assume(hypothesis.clone()).unwrap();
    let identity = KernelRules::implies_intr(&hypothesis, base.as_kernel()).unwrap();
    let first = RawTerm::imp(r.clone(), RawTerm::imp(r.clone(), r.clone()));
    let rule = KernelRules::implies_intr(&context.certify_prop(first).unwrap(), &identity).unwrap();
    let state = create_state(&context, RawTerm::imp(r.clone(), r));
    let mut candidate = create_empty_candidate();
    candidate.elimination_choice = Some(1);
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: true,
            premise_count: 1,
            subgoal_index: 1,
        },
        &rule,
        &state,
        &candidate,
    );
    assert!(matches!(
        result,
        Err(KernelError::BoundProof(isabelle_kernel::BoundProofError::InvalidEliminationChoice {
            choice: 1
        },)),
    ));
}

#[test]
fn lift_rule_interleaved_goal_replays_in_bicomposition() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let eq = RawTerm::eq(r.clone(), r.clone());
    let rule = KernelRules::implies_intr(
        &context.certify_prop(r).unwrap(),
        KernelRules::reflexive(context.certify_term(RawTerm::const_("R", Ty::prop())).unwrap())
            .as_kernel(),
    )
    .unwrap();
    let goal = RawTerm::forall("x", Ty::prop(), RawTerm::imp(RawTerm::bound(0), eq.clone()));
    let certified_goal = context.certify_term(goal.clone()).unwrap();
    let lifted = KernelRules::lift_rule(&owner, &context, &certified_goal, &rule).unwrap();
    let state = create_state(&context, goal);
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags { is_lifted: true, is_incremented: true, ..Default::default() },
            is_elimination: false,
            premise_count: 1,
            subgoal_index: 1,
        },
        &lifted,
        &state,
        &create_empty_candidate(),
    )
    .unwrap();
    assert_eq!(result.prop().term().nprems(), 1);
    accept_closed_theorem(&owner, "lifted", result.try_close().unwrap()).unwrap();
}

#[test]
fn assumption_candidate_instantiates_state_then_discharge() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let goal = RawTerm::imp(RawTerm::var("v", 0, Ty::prop()), r.clone());
    let state = create_state(&context, goal);
    let mut candidate = create_empty_candidate();
    candidate.state_subst.push(InstEntry::new(
        "v",
        0,
        Ty::prop(),
        context.certify_term(r).unwrap(),
    ));
    let result =
        KernelRules::assumption_candidate(&owner, &context, 1, &state, &candidate).unwrap();
    assert_eq!(result.prop().term(), state.prop().term().dest_imp_chain().1);
    accept_closed_theorem(&owner, "assumption", result.try_close().unwrap()).unwrap();
}

#[test]
fn assumption_candidate_residual_flex_remains_unclosed() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let eq = RawTerm::eq(r.clone(), r.clone());
    let state = create_state(&context, RawTerm::imp(r.clone(), eq.clone()));
    let mut candidate = create_empty_candidate();
    candidate
        .residual_pairs
        .push((context.certify_term(r.clone()).unwrap(), context.certify_term(eq).unwrap()));
    let result =
        KernelRules::assumption_candidate(&owner, &context, 1, &state, &candidate).unwrap();
    assert!(result.try_close().is_err());
}

#[test]
fn assumption_candidate_first_matching_premise_replays() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let state = create_state(&context, RawTerm::imp(r.clone(), RawTerm::imp(r.clone(), r)));
    let mut candidate = create_empty_candidate();
    candidate.elimination_choice = Some(0);
    let result =
        KernelRules::assumption_candidate(&owner, &context, 1, &state, &candidate).unwrap();
    accept_closed_theorem(&owner, "first_assumption", result.try_close().unwrap()).unwrap();
}

#[test]
fn assumption_candidate_second_matching_premise_replays() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let state = create_state(&context, RawTerm::imp(r.clone(), RawTerm::imp(r.clone(), r)));
    let mut candidate = create_empty_candidate();
    candidate.elimination_choice = Some(1);
    let result =
        KernelRules::assumption_candidate(&owner, &context, 1, &state, &candidate).unwrap();
    accept_closed_theorem(&owner, "second_assumption", result.try_close().unwrap()).unwrap();
}

#[test]
fn bicompose_candidate_preincremented_shared_typed_variable_replays() {
    let (owner, context) = create_owner();
    let variable = RawTerm::var("v", 0, Ty::prop());
    let proposition = RawTerm::eq(variable.clone(), variable.clone());
    let rule = KernelRules::reflexive(context.certify_term(variable).unwrap());
    let state = create_state(&context, proposition);
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags { is_incremented: true, ..Default::default() },
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        rule.as_kernel(),
        &state,
        &create_empty_candidate(),
    )
    .unwrap();
    accept_closed_theorem(&owner, "shared_typed_var", result.try_close().unwrap()).unwrap();
}

#[test]
fn bicompose_candidate_cannot_drop_prior_flex_pair() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let eq = RawTerm::eq(r.clone(), r.clone());
    let rule = KernelRules::reflexive(context.certify_term(r.clone()).unwrap());
    let state = create_state(&context, r.clone());
    let mut candidate = create_empty_candidate();
    candidate
        .residual_pairs
        .push((context.certify_term(eq.clone()).unwrap(), context.certify_term(r).unwrap()));
    let open = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        rule.as_kernel(),
        &state,
        &candidate,
    )
    .unwrap();
    let next_state = create_state(&context, eq);
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        &open,
        &next_state,
        &create_empty_candidate(),
    );
    assert!(result.is_err());
}

#[test]
fn bicompose_candidate_foreign_owner_source_rejected() {
    let (owner, context) = create_owner();
    let foreign = TrustedTheory::root(
        "ForeignComposition",
        Signature::new().extend_const("R", Ty::prop()).unwrap(),
    );
    let foreign_context = ProofContext::new(foreign.snapshot().clone());
    let foreign_rule = KernelRules::reflexive(
        foreign_context.certify_term(RawTerm::const_("R", Ty::prop())).unwrap(),
    );
    let r = RawTerm::const_("R", Ty::prop());
    let state = create_state(&context, RawTerm::eq(r.clone(), r));
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        foreign_rule.as_kernel(),
        &state,
        &create_empty_candidate(),
    );
    assert!(result.is_err());
}

#[test]
fn lift_rule_fresh_index_exceeds_representation_rejected() {
    let (owner, context) = create_owner();
    let goal = context.certify_term(RawTerm::var("last", usize::MAX, Ty::prop())).unwrap();
    let rule =
        KernelRules::reflexive(context.certify_term(RawTerm::const_("R", Ty::prop())).unwrap());
    assert!(KernelRules::lift_rule(&owner, &context, &goal, rule.as_kernel()).is_err());
}

#[test]
fn bicompose_candidate_rule_premise_count_exceeds_rule_rejected() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let rule = KernelRules::reflexive(context.certify_term(r.clone()).unwrap());
    let state = create_state(&context, RawTerm::eq(r.clone(), r));
    let result = KernelRules::bicompose_candidate(
        &owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: false,
            premise_count: 1,
            subgoal_index: 1,
        },
        rule.as_kernel(),
        &state,
        &create_empty_candidate(),
    );
    assert!(matches!(
        result,
        Err(KernelError::BoundProof(
            isabelle_kernel::BoundProofError::RulePremisesOutOfRange { .. }
        )),
    ));
}

#[test]
fn lift_rule_schematic_variable_applies_local_goal_parameter() {
    let (owner, context) = create_owner();
    let proposition =
        RawTerm::forall("x", Ty::prop(), RawTerm::imp(RawTerm::bound(0), RawTerm::bound(0)));
    let goal = context.certify_term(proposition).unwrap();
    let variable = RawTerm::var("v", 0, Ty::prop());
    let rule = KernelRules::reflexive(context.certify_term(variable).unwrap());
    let lifted = KernelRules::lift_rule(&owner, &context, &goal, rule.as_kernel()).unwrap();
    let applied =
        RawTerm::app(RawTerm::var("v", 0, Ty::arrow(Ty::prop(), Ty::prop())), RawTerm::bound(0));
    let expected = context
        .certify_prop(RawTerm::forall(
            "x",
            Ty::prop(),
            RawTerm::imp(RawTerm::bound(0), RawTerm::eq(applied.clone(), applied)),
        ))
        .unwrap();
    assert!(lifted.prop().term().alpha_eq(expected.term()));
    accept_closed_theorem(&owner, "schematic_lift", lifted.try_close().unwrap()).unwrap();
}

#[test]
fn lift_rule_residual_flex_is_lifted_and_never_closed() {
    let (owner, context) = create_owner();
    let r = RawTerm::const_("R", Ty::prop());
    let equality = RawTerm::eq(r.clone(), r.clone());
    let state = create_state(&context, RawTerm::imp(r.clone(), equality.clone()));
    let mut candidate = create_empty_candidate();
    candidate
        .residual_pairs
        .push((context.certify_term(r).unwrap(), context.certify_term(equality).unwrap()));
    let source =
        KernelRules::assumption_candidate(&owner, &context, 1, &state, &candidate).unwrap();
    let goal = context
        .certify_term(RawTerm::forall(
            "x",
            Ty::prop(),
            RawTerm::imp(RawTerm::bound(0), RawTerm::bound(0)),
        ))
        .unwrap();
    let lifted = KernelRules::lift_rule(&owner, &context, &goal, &source).unwrap();
    let expected = context
        .certify_prop(RawTerm::forall(
            "x",
            Ty::prop(),
            RawTerm::imp(
                RawTerm::bound(0),
                RawTerm::eq(RawTerm::const_("R", Ty::prop()), RawTerm::const_("R", Ty::prop())),
            ),
        ))
        .unwrap();
    assert!(lifted.prop().term().alpha_eq(expected.term()));
    assert!(matches!(lifted.try_close(), Err(KernelError::TheoremObligations(_))));
}
