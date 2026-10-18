use std::sync::Arc;

use isabelle_rs::{
    core::{
        logic::Pure,
        term::Term,
        thm::{CTerm, Thm, ThmKernel, ThmTrust},
        types::Typ,
    },
    hol::hol_loader::HolTheoremDb,
    isar::{
        proof_context::ProofCertContext,
        proof_result::GoalExportError,
        proof_state::{ProofState, interpret_proof_script},
    },
};

fn checked_goal(term: Term, ctx: &ProofCertContext) -> ProofState {
    ProofState::new_checked_goal(ctx.certify_prop(term).unwrap()).unwrap()
}

fn identity() -> (ProofCertContext, Term, Arc<Thm>) {
    let prop = Typ::base("prop");
    let a = Term::const_("A", prop.clone());
    let ctx = ProofCertContext::new().with_const("A", prop);
    let assumption = ctx.certify_prop(a.clone()).unwrap();
    let theorem =
        ThmKernel::implies_intr(&assumption, &ThmKernel::assume(assumption.clone()).unwrap())
            .unwrap();
    (ctx, Pure::mk_implies(a.clone(), a), Arc::new(theorem))
}

fn forall_identity(prop: &Typ) -> Term {
    Term::app(
        Term::const_("Pure.all", Typ::arrow(Typ::arrow(prop.clone(), prop.clone()), prop.clone())),
        Term::abs("x", prop.clone(), Pure::mk_implies(Term::bound(0), Term::bound(0))),
    )
}

#[test]
fn proof_state_fresh_goal_qed_rejects_unproved_obligation() {
    let (ctx, target, _) = identity();
    let mut state = checked_goal(target, &ctx);
    assert!(matches!(state.qed(), Err(GoalExportError::MissingProofResult)));
    state.begin_proof();
    assert!(matches!(state.qed(), Err(GoalExportError::MissingProofResult)));
    assert!(matches!(state, ProofState::Proving { .. }));
}

#[test]
fn proof_state_strict_identity_fact_completes_full_implication() {
    let (ctx, target, real_proof) = identity();
    let mut state = checked_goal(target.clone(), &ctx);
    state.begin_proof();
    state.show(&target, "this", &[real_proof], &HolTheoremDb::new()).unwrap();
    let theorem = state.qed().unwrap();
    assert_eq!(theorem.trust_status(), ThmTrust::Strict);
    assert!(theorem.hyps().is_empty());
    assert_eq!(theorem.prop().term(), &target);
    assert!(theorem.nprems() > 0, "logical implication is not a tactic obligation");
}

#[test]
fn proof_state_have_then_show_uses_real_fact_without_promoting_assumption() {
    let (ctx, target, real_proof) = identity();
    let mut state = checked_goal(target.clone(), &ctx);
    state.begin_proof();
    let have = state.have(&target, "this", &[real_proof], &HolTheoremDb::new()).unwrap();
    assert!(have.hyps().is_empty());
    state.show(&target, "this", &[], &HolTheoremDb::new()).unwrap();
    let result = state.qed().unwrap();
    assert_eq!(result.prop().term(), &target);
    assert!(result.hyps().is_empty());
}

#[test]
fn proof_state_wrong_goal_and_unlicensed_hypothesis_never_complete() {
    let (ctx, _, _) = identity();
    let a = Term::const_("A", Typ::base("prop"));
    let mut state = checked_goal(a.clone(), &ctx);
    state.begin_proof();
    let unauthorized = Arc::new(ThmKernel::assume(ctx.certify_prop(a.clone()).unwrap()).unwrap());
    assert!(state.show(&a, "assumption", &[unauthorized], &HolTheoremDb::new()).is_err());
    assert!(matches!(state.qed(), Err(GoalExportError::MissingProofResult)));
    state.assume_checked(ctx.certify_prop(a.clone()).unwrap()).unwrap();
    state.show(&a, "assumption", &[], &HolTheoremDb::new()).unwrap();
    assert!(matches!(state.qed(), Err(GoalExportError::PropositionMismatch)));
    assert!(matches!(state, ProofState::Proving { .. }));
}

#[test]
fn proof_state_compat_fact_never_authorizes_completion() {
    let (ctx, target, _) = identity();
    let compat = Arc::new(ThmKernel::assume_compat(CTerm::certify(target.clone())));
    let mut state = checked_goal(target.clone(), &ctx);
    state.begin_proof();
    assert!(state.show(&target, "this", &[compat], &HolTheoremDb::new()).is_err());
    assert!(matches!(state.qed(), Err(GoalExportError::MissingProofResult)));
}

#[test]
fn proof_state_independent_subgoals_have_no_composition() {
    let (ctx, target, real_proof) = identity();
    let mut state = checked_goal(target.clone(), &ctx);
    state.begin_proof();
    state.set_subgoals_checked(vec![ctx.certify_prop(target.clone()).unwrap()]).unwrap();
    state.show(&target, "this", &[real_proof], &HolTheoremDb::new()).unwrap();
    assert!(matches!(state.qed(), Err(GoalExportError::UnsupportedComposition)));
    assert!(matches!(state, ProofState::Proving { .. }));
}

#[test]
fn proof_state_local_fix_and_assumption_export_scoped_forall() {
    let prop = Typ::base("prop");
    let x = Term::free("x", prop.clone());
    let all = forall_identity(&prop);
    let mut state = checked_goal(all.clone(), &ProofCertContext::new());
    state.begin_proof();
    state.fix("x", prop.clone()).unwrap();
    assert!(state.fix("x", prop.clone()).is_err());
    state
        .assume_checked(
            ProofCertContext::new().with_free("x", prop).certify_prop(x.clone()).unwrap(),
        )
        .unwrap();
    state.show(&x, "assumption", &[], &HolTheoremDb::new()).unwrap();
    let result = state.qed().unwrap();
    assert_eq!(result.prop().term(), &all);
    assert!(result.hyps().is_empty());
    assert_eq!(result.trust_status(), ThmTrust::Strict);
}

#[test]
fn proof_script_scoped_forall_from_checked_assumption_closes() {
    let prop = Typ::base("prop");
    let goal = forall_identity(&prop);
    let mut state = checked_goal(goal.clone(), &ProofCertContext::new());
    let result = interpret_proof_script(
        &mut state,
        "proof\nfix x::prop\nassume \"x\"\nshow \"x\" by assumption\nqed",
        &[],
        &HolTheoremDb::new(),
    )
    .unwrap();
    assert_eq!(result.prop().term(), &goal);
    assert!(result.hyps().is_empty());
}

#[test]
fn proof_script_checked_commands_require_explicit_terminal() {
    let (ctx, target, proof) = identity();
    for script in [
        "proof\nshow \"A ==> A\" by this",
        "proof\nshow \"A ==> A\" by nonsense\nqed",
        "proof\nlet x = A\nqed",
        "proof\nshow \"A ==> A\" by this\nqed\nunknown",
    ] {
        let mut state = checked_goal(target.clone(), &ctx);
        assert!(
            interpret_proof_script(
                &mut state,
                script,
                &[Arc::clone(&proof)],
                &HolTheoremDb::new(),
            )
            .is_err(),
            "{script}"
        );
    }
    let mut state = checked_goal(target.clone(), &ctx);
    let result =
        interpret_proof_script(&mut state, "by this", &[proof], &HolTheoremDb::new()).unwrap();
    assert_eq!(result.prop().term(), &target);
}

#[test]
fn proof_script_malformed_lexical_and_method_arguments_reject() {
    let (ctx, target, fact) = identity();
    for script in [
        "by this extra",
        "by (assumption",
        "proof\nassume \"A\nqed",
        "proof\nshow \"A ==> A\" by this; qed",
        "proof\nfix x::prop\nfix x::prop\nqed",
        "proof\nshow \"A ==> A\" by this\nqed\nby this",
    ] {
        let mut state = checked_goal(target.clone(), &ctx);
        assert!(
            interpret_proof_script(&mut state, script, &[Arc::clone(&fact)], &HolTheoremDb::new(),)
                .is_err(),
            "{script}"
        );
    }
}
