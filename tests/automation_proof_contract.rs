use std::sync::Arc;

use isabelle_rs::{
    core::{
        logic::Pure,
        term::Term,
        thm::{CTerm, Thm, ThmKernel},
        types::{Typ, TypeEnv},
    },
    tools::{
        meson::{MesonProver, meson_tac},
        metis::{MetisProver, MetisReplay, reconstruct_atp_proof},
        reconstruct::{ProofReconstructor, ProofStep, reconstruct_from_atp},
    },
};

fn checked_atom(name: &str) -> CTerm {
    let mut env = TypeEnv::new();
    env.declare_const(name, Typ::base("prop"));
    CTerm::certify_checked(Term::const_(name, Typ::base("prop")), &env).unwrap()
}

fn closed_identity(name: &str) -> Thm {
    let atom = checked_atom(name);
    let assumed = ThmKernel::assume_checked(atom.clone()).unwrap();
    ThmKernel::implies_intr(&atom, &assumed).unwrap()
}

fn request(prop: Term) -> Thm {
    ThmKernel::assume_compat(CTerm::certify(prop))
}

fn step(name: &str, rule: &str, formula: Term, premises: &[&str]) -> ProofStep {
    ProofStep {
        name: name.into(),
        rule: rule.into(),
        formula,
        premises: premises.iter().map(|s| (*s).to_owned()).collect(),
    }
}

#[test]
fn replay_closed_identity_requires_complete_matching_goal() {
    let identity = Arc::new(closed_identity("p"));
    let named = vec![("given".into(), Arc::clone(&identity))];
    let proof = [step("result", "assumption", identity.prop().term().clone(), &["given"])];
    let replay = ProofReconstructor::new(named.clone()).unwrap();
    assert!(replay.validate(&proof, identity.prop().term()));
    let wrong_goal = Term::const_("p", Typ::base("prop"));
    assert!(!replay.validate(&proof, &wrong_goal));
    let mut metis = MetisReplay::new(&request(identity.prop().term().clone()), &named).unwrap();
    assert!(metis.replay(&proof).is_some());
    let mut wrong = MetisReplay::new(&request(wrong_goal), &named).unwrap();
    assert!(wrong.replay(&proof).is_none());
}

#[test]
fn replay_real_two_premise_resolution_derives_exact_closed_result() {
    let prop = Typ::base("prop");
    let function_type = Typ::arrow(prop.clone(), prop.clone());
    let mut env = TypeEnv::new();
    env.declare_const("f", function_type.clone());
    env.declare_const("x", prop.clone());
    let function = CTerm::certify_checked(Term::const_("f", function_type), &env).unwrap();
    let argument = CTerm::certify_checked(Term::const_("x", prop), &env).unwrap();
    let proved_p = Arc::new(ThmKernel::reflexive(function).unwrap());
    let assumed_p = ThmKernel::assume_checked(proved_p.prop().clone()).unwrap();
    let composed =
        ThmKernel::combination(&assumed_p, &ThmKernel::reflexive(argument).unwrap()).unwrap();
    let expected = composed.prop().term().clone();
    let conditional = Arc::new(ThmKernel::implies_intr(proved_p.prop(), &composed).unwrap());
    let named = vec![("p0".into(), proved_p), ("p_to_q".into(), conditional)];
    let proof = [step("derived", "resolution", expected.clone(), &["p0", "p_to_q"])];
    let replay = ProofReconstructor::new(named.clone()).unwrap();
    assert!(replay.validate(&proof, &expected));
    let mut metis = MetisReplay::new(&request(expected), &named).unwrap();
    assert!(metis.replay(&proof).is_some());
}

#[test]
fn replay_bad_steps_never_use_search_or_previous_partial_run() {
    let identity = Arc::new(closed_identity("p"));
    let goal = request(identity.prop().term().clone());
    let named = vec![("given".into(), identity.clone())];
    let valid = step("ok", "axiom", identity.prop().term().clone(), &["given"]);
    let bad_steps = [
        step("bad", "unknown", identity.prop().term().clone(), &["given"]),
        step("bad", "axiom", identity.prop().term().clone(), &["missing"]),
        step("bad", "axiom", Term::const_("other", Typ::base("prop")), &["given"]),
        step("bad", "axiom", identity.prop().term().clone(), &[]),
        step("given", "axiom", identity.prop().term().clone(), &["given"]),
    ];
    let mut recon = ProofReconstructor::new(named.clone()).unwrap();
    let mut metis = MetisReplay::new(&goal, &named).unwrap();
    for bad in bad_steps {
        assert!(recon.reconstruct(&[valid.clone(), bad.clone()]).is_none());
        assert!(metis.replay(&[valid.clone(), bad]).is_none());
        assert!(recon.reconstruct(std::slice::from_ref(&valid)).is_some());
        assert!(metis.replay(std::slice::from_ref(&valid)).is_some());
    }
    assert!(recon.reconstruct(&[valid.clone(), valid]).is_none());
    assert!(
        ProofReconstructor::new(vec![
            ("same".into(), identity.clone()),
            ("same".into(), identity.clone())
        ])
        .is_err()
    );
    assert!(
        MetisReplay::new(&goal, &[("same".into(), identity.clone()), ("same".into(), identity)])
            .is_err()
    );
}

#[test]
fn tstp_parser_rejects_unsupported_and_malformed_proof_lines() {
    let supported = "fof(result, plain, (p => p), inference(assumption, [], [given])).";
    let parsed = ProofReconstructor::parse_tstp(supported).unwrap();
    assert_eq!(parsed.len(), 1);
    assert_eq!(
        parsed[0].formula,
        Pure::mk_implies(
            Term::const_("p", Typ::base("prop")),
            Term::const_("p", Typ::base("prop"))
        )
    );
    for invalid in [
        "fof(x, plain, p(a), inference(axiom, [], [given])).",
        "fof(x, plain, p junk, inference(axiom, [], [given])).",
        "fof(x, plain, p, inference(axiom, status(thm), [given])).",
        "fof(x, plain, p, inference(axiom, [], [given,])).",
        "fof(x, plain, p, inference(axiom, [], [given])). garbage",
        "fof(x, plain, p, inference(axiom, [], [given])",
        "cnf(x, plain, p, inference(axiom, [], [given])).",
    ] {
        assert_eq!(
            ProofReconstructor::parse_tstp(&format!("% status\n{invalid}")).unwrap_err().line,
            2
        );
    }
}

#[test]
fn reconstruct_from_atp_does_not_fallback_on_invalid_proof() {
    let identity = Arc::new(closed_identity("p"));
    let goal = request(identity.prop().term().clone());
    let named = vec![("given".into(), identity.clone())];
    assert!(reconstruct_from_atp("", named.clone(), &goal).is_none());
    assert!(
        reconstruct_from_atp(
            "fof(x, plain, p(a), inference(axiom, [], [given])).",
            named.clone(),
            &goal
        )
        .is_none()
    );
    assert!(
        reconstruct_from_atp(
            "fof(x, plain, (p => p), inference(unknown, [], [given])).",
            named.clone(),
            &goal
        )
        .is_none()
    );
    assert!(
        reconstruct_from_atp(
            "fof(x, plain, (p => p), inference(axiom, [], [missing])).",
            named.clone(),
            &goal
        )
        .is_none()
    );
    assert!(
        reconstruct_from_atp(
            "fof(x, plain, (p => p), inference(axiom, [], [given])).",
            named,
            &goal
        )
        .is_some()
    );
}

#[test]
fn meson_conditional_or_compat_fact_cannot_prove_conclusion() {
    let identity = Arc::new(closed_identity("p"));
    let proposition = identity.prop().term().clone();
    let mut prover = MesonProver::new();
    prover.add_clause(identity);
    assert!(prover.prove(&request(proposition)).is_some());
    assert!(prover.prove(&request(Term::const_("p", Typ::base("prop")))).is_none());
    let compat =
        Arc::new(ThmKernel::reflexive_compat(CTerm::certify(Term::const_("p", Typ::base("prop")))));
    prover.add_clause(compat.clone());
    assert!(prover.prove(&request(compat.prop().term().clone())).is_none());
}

#[test]
fn meson_tactic_composes_proved_premise_into_original_state() {
    let fact = Arc::new(ThmKernel::reflexive(checked_atom("p")).unwrap());
    let obligation = CTerm::certify(fact.prop().term().clone());
    let state = ThmKernel::trivial(obligation).unwrap();
    assert_eq!(state.nprems(), 1);
    let next = meson_tac(&state, std::slice::from_ref(&fact));
    assert_eq!(next.len(), 1);
    assert_eq!(next[0].nprems(), 0);
    assert_eq!(next[0].prop().term(), fact.prop().term());
    let conditional = Arc::new(ThmKernel::trivial(fact.prop().clone()).unwrap());
    assert!(meson_tac(&state, &[conditional]).is_empty());
}

#[test]
fn numbered_atp_replay_consumes_supplied_step_without_local_fallback() {
    let fact = Arc::new(closed_identity("p"));
    let goal = request(fact.prop().term().clone());
    let valid = "fof(result, plain, (p => p), inference(assumption, [], [p0])).";
    assert!(reconstruct_atp_proof(valid, std::slice::from_ref(&fact), &goal).is_some());
    let unsupported = "fof(result, plain, (p => p), inference(cnf, [], [p0])).";
    assert!(reconstruct_atp_proof(unsupported, &[fact], &goal).is_none());
}

#[test]
fn metis_exact_fact_proves_only_complete_goal() {
    let fact = Arc::new(closed_identity("p"));
    let mut prover = MetisProver::new();
    prover.add_premises(std::slice::from_ref(&fact));
    let exact = request(fact.prop().term().clone());
    assert!(prover.prove(&exact).is_some());
    let wrong = request(Term::const_("p", Typ::base("prop")));
    assert!(prover.prove(&wrong).is_none());
}
