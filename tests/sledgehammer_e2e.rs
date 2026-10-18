//! ATP-facing reconstruction behavior without relying on an installed ATP.

use std::sync::Arc;

use isabelle_rs::{
    core::{
        term::Term,
        thm::{CTerm, ThmKernel},
        types::{Typ, TypeEnv},
    },
    tools::{
        reconstruct::{ProofReconstructor, reconstruct_from_atp},
        sledgehammer::{Sledgehammer, SledgehammerConfig},
    },
};

fn proved_identity() -> isabelle_rs::core::thm::Thm {
    let mut env = TypeEnv::new();
    env.declare_const("p", Typ::base("prop"));
    let atom = CTerm::certify_checked(Term::const_("p", Typ::base("prop")), &env).unwrap();
    let assumed = ThmKernel::assume_checked(atom.clone()).unwrap();
    ThmKernel::implies_intr(&atom, &assumed).unwrap()
}

#[test]
fn sledgehammer_config_respects_selected_provers() {
    let hammer = Sledgehammer::with_config(SledgehammerConfig {
        provers: Vec::new(),
        timeout: 30,
        max_premises: 100,
        use_types: true,
    });
    assert!(hammer.available_provers().is_empty());
    assert!(hammer.run(&proved_identity(), &[]).is_none());
    assert!(hammer.run(&proved_identity(), &[proved_identity()]).is_none());
}

#[test]
fn tstp_closed_identity_reference_reconstructs_only_full_proposition() {
    let fact = Arc::new(proved_identity());
    let request = ThmKernel::assume_compat(CTerm::certify(fact.prop().term().clone()));
    let proof = "fof(result, plain, (p => p), inference(assumption, [], [given])).";
    let steps = ProofReconstructor::parse_tstp(proof).unwrap();
    assert_eq!(steps[0].formula, *fact.prop().term());
    let reconstructed = reconstruct_from_atp(proof, vec![("given".into(), fact.clone())], &request)
        .expect("actual named closed identity theorem must replay");
    assert!(reconstructed.is_strict_closed_proved());
    assert_eq!(reconstructed.prop().term(), request.prop().term());
    let wrong = ThmKernel::assume_compat(CTerm::certify(Term::const_("p", Typ::base("prop"))));
    assert!(reconstruct_from_atp(proof, vec![("given".into(), fact)], &wrong).is_none());
}

#[test]
fn tstp_corrupted_step_is_not_hidden_by_available_fact() {
    let fact = Arc::new(proved_identity());
    let request = ThmKernel::assume_compat(CTerm::certify(fact.prop().term().clone()));
    for proof in [
        "",
        "fof(result, plain, (p => p), inference(clausify, [], [given])).",
        "fof(result, plain, p, inference(assumption, [], [given])).",
        "fof(result, plain, (p => p), inference(assumption, [], [missing])).",
    ] {
        assert!(
            reconstruct_from_atp(proof, vec![("given".into(), fact.clone())], &request).is_none()
        );
    }
}
