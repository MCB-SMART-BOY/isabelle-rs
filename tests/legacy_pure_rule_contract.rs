use isabelle_rs::core::{
    envir::Envir,
    error::KernelError,
    logic::Pure,
    term::Term,
    thm::{CTerm, KernelCheckMode, ThmKernel, ThmTrust},
    types::{Typ, TypeEnv},
};

fn certify(term: Term) -> CTerm {
    CTerm::certify_checked(term, &TypeEnv::new()).expect("well-typed Pure fixture")
}

fn assert_strict(thm: &isabelle_rs::core::thm::Thm) {
    assert_eq!(thm.trust_status(), ThmTrust::Strict);
    assert!(thm.prop().is_checked());
    assert!(thm.hyps().iter().all(CTerm::is_checked));
    thm.check_kernel_invariants(KernelCheckMode::Strict)
        .expect("strict Pure rule preserves invariant");
}

#[test]
fn forall_intr_nested_binder_captures_only_the_typed_free() {
    let prop = Typ::base("prop");
    let identity = Term::abs("inner", prop.clone(), Term::free("x", prop.clone()));
    let refl = ThmKernel::reflexive(certify(identity)).expect("strict reflexivity");
    let quantified =
        ThmKernel::forall_intr("x", prop.clone(), &refl).expect("typed quantifier introduction");
    let ((_, bound_type), body) = Pure::dest_all(quantified.prop().term()).unwrap();
    assert_eq!(bound_type, &prop);
    let (left, right) = Pure::dest_equals(body).unwrap();
    let expected = Term::abs("inner", prop, Term::bound(1));
    assert_eq!(left, &expected);
    assert_eq!(right, &expected);
    assert!(quantified.is_strict_closed_proved());
    assert_strict(&quantified);
}

#[test]
fn abstraction_nested_binder_captures_without_leaking_or_capturing_schematic() {
    let prop = Typ::base("prop");
    let body = Term::abs("inner", prop.clone(), Term::free("x", prop.clone()));
    let refl = ThmKernel::reflexive(certify(body)).unwrap();
    let lifted = ThmKernel::abstraction("x", prop.clone(), &refl).unwrap();
    let (left, right) = Pure::dest_equals(lifted.prop().term()).unwrap();
    let expected = Term::abs("x", prop.clone(), Term::abs("inner", prop.clone(), Term::bound(1)));
    assert_eq!(left, &expected);
    assert_eq!(right, &expected);
    assert_strict(&lifted);

    let nested = Term::abs(
        "x",
        prop.clone(),
        Pure::mk_implies(Term::free("x", prop.clone()), Term::bound(0)),
    );
    let nested_refl = ThmKernel::reflexive(certify(nested)).unwrap();
    let nested_lifted = ThmKernel::abstraction("x", prop.clone(), &nested_refl).unwrap();
    let (nested_left, _) = Pure::dest_equals(nested_lifted.prop().term()).unwrap();
    let expected_nested = Term::abs(
        "x",
        prop.clone(),
        Term::abs("x", prop.clone(), Pure::mk_implies(Term::bound(1), Term::bound(0))),
    );
    assert_eq!(nested_left, &expected_nested);
    assert_strict(&nested_lifted);

    let schematic = ThmKernel::reflexive(certify(Term::var("x", 0, prop.clone()))).unwrap();
    let lifted_schematic = ThmKernel::abstraction("x", prop.clone(), &schematic).unwrap();
    let (left, _) = Pure::dest_equals(lifted_schematic.prop().term()).unwrap();
    assert_eq!(left, &Term::abs("x", prop.clone(), Term::var("x", 0, prop)));
    assert_strict(&lifted_schematic);
}

#[test]
fn typed_binding_conflict_and_hypothesis_capture_are_rejected() {
    let prop = Typ::base("prop");
    let bool_type = Typ::base("bool");
    let x = Term::free("x", prop.clone());
    let refl = ThmKernel::reflexive(certify(x.clone())).unwrap();
    assert!(matches!(
        ThmKernel::abstraction("x", bool_type.clone(), &refl),
        Err(KernelError::TypeMismatch { .. })
    ));
    assert!(matches!(
        ThmKernel::forall_intr("x", bool_type.clone(), &refl),
        Err(KernelError::TypeMismatch { .. })
    ));
    let mixed = Term::app(
        Term::abs("b", bool_type.clone(), Term::free("x", prop.clone())),
        Term::free("x", bool_type),
    );
    let mixed_refl = ThmKernel::reflexive(certify(mixed)).unwrap();
    assert!(matches!(
        ThmKernel::abstraction("x", prop.clone(), &mixed_refl),
        Err(KernelError::TypeMismatch { .. })
    ));

    let hyp = certify(Pure::mk_equals(prop.clone(), x.clone(), x));
    let assumed = ThmKernel::assume(hyp).unwrap();
    assert!(matches!(
        ThmKernel::forall_intr("x", prop.clone(), &assumed),
        Err(KernelError::FreeVarInHypotheses { .. })
    ));
    assert!(matches!(
        ThmKernel::abstraction("x", prop, &assumed),
        Err(KernelError::FreeVarInHypotheses { .. })
    ));
}

#[test]
fn combination_instantiation_and_composition_preserve_strict_certificates() {
    let prop = Typ::base("prop");
    let function = Term::abs("x", prop.clone(), Term::bound(0));
    let argument = Term::free("A", prop.clone());
    let function_refl = ThmKernel::reflexive(certify(function.clone())).unwrap();
    let argument_refl = ThmKernel::reflexive(certify(argument.clone())).unwrap();
    let combined = ThmKernel::combination(&function_refl, &argument_refl).unwrap();
    let (left, right) = Pure::dest_equals(combined.prop().term()).unwrap();
    let application = Term::app(function, argument);
    assert_eq!(left, &application);
    assert_eq!(right, &application);
    assert_strict(&combined);

    let schematic = Term::var("P", 0, prop.clone());
    let variable_refl = ThmKernel::reflexive(certify(schematic)).unwrap();
    let mut env = Envir::empty(0);
    env.update("P".into(), 0, prop.clone(), Term::free("A", prop.clone()));
    let instantiated = ThmKernel::instantiate_checked(&env, &variable_refl).unwrap();
    assert_strict(&instantiated);
    assert_eq!(instantiated.prop().term(), argument_refl.prop().term());

    let state = ThmKernel::trivial(certify(combined.prop().term().clone())).unwrap();
    let resolved = ThmKernel::bicompose(false, &combined, &state, 0).unwrap();
    assert_eq!(resolved.prop().term(), combined.prop().term());
    assert_strict(&resolved);
}

#[test]
fn bicompose_complete_implication_premise_preserves_strict_proof() {
    let a = Term::free("A", Typ::base("prop"));
    let proof = ThmKernel::trivial(certify(a)).unwrap();
    let state = ThmKernel::trivial(certify(proof.prop().term().clone())).unwrap();
    let resolved = ThmKernel::bicompose(false, &proof, &state, 0).unwrap();
    assert_eq!(resolved.prop().term(), proof.prop().term());
    assert_strict(&resolved);
}

#[test]
fn instantiation_rejects_nested_ill_typed_replacement_and_hypotheses() {
    let prop = Typ::base("prop");
    let schematic = Term::var("P", 0, prop.clone());
    let thm = ThmKernel::assume(certify(schematic)).unwrap();
    let malformed = Term::app(
        Term::free("f", Typ::arrow(prop.clone(), prop.clone())),
        Term::free("wrong", Typ::base("bool")),
    );
    let mut env = Envir::empty(0);
    env.update("P".into(), 0, prop, malformed);
    assert!(matches!(
        ThmKernel::instantiate_checked(&env, &thm),
        Err(KernelError::TypeMismatch { .. })
    ));
}

#[test]
fn compatibility_and_admission_never_upgrade_across_pure_rules() {
    let prop = Typ::base("prop");
    let free = Term::free("A", prop.clone());
    let strict = ThmKernel::reflexive(certify(free.clone())).unwrap();
    let compat = ThmKernel::reflexive_compat(CTerm::certify(free.clone()));
    let admitted =
        ThmKernel::admit(certify(strict.prop().term().clone()), "admitted:pure-rule-contract");

    for theorem in [&compat, &admitted] {
        let expected = theorem.trust_status();
        let all = ThmKernel::forall_intr("unused", prop.clone(), theorem).unwrap();
        let abs = ThmKernel::abstraction("unused", prop.clone(), theorem).unwrap();
        let inst = ThmKernel::instantiate_checked(&Envir::init(), theorem).unwrap();
        let state = ThmKernel::trivial(certify(theorem.prop().term().clone())).unwrap();
        let composed = ThmKernel::bicompose(false, theorem, &state, 0).unwrap();
        for derived in [&all, &abs, &inst, &composed] {
            assert_eq!(derived.trust_status(), expected);
            assert_eq!(derived.has_oracles(), theorem.has_oracles());
            assert!(!derived.is_strict_closed_proved());
        }
    }
    let strict_fn =
        ThmKernel::reflexive(certify(Term::abs("x", prop.clone(), Term::bound(0)))).unwrap();
    let mixed = ThmKernel::combination(&strict_fn, &compat).unwrap();
    assert_eq!(mixed.trust_status(), ThmTrust::Compat);
    let with_oracle = ThmKernel::combination(&strict_fn, &admitted).unwrap();
    assert_eq!(with_oracle.trust_status(), ThmTrust::Admitted);
    assert!(with_oracle.has_oracles());
}
