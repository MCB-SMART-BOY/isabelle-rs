use std::sync::Arc;

use isabelle_rs::core::{
    conv::rewr_conv,
    envir::Envir,
    error::KernelError,
    logic::Pure,
    term::Term,
    thm::{CTerm, ThmKernel},
    types::Typ,
};

fn prop(name: &str) -> CTerm {
    CTerm::certify(Term::const_(name, Typ::base("prop")))
}

#[test]
fn transitive_rejects_known_equality_type_mismatch() {
    let nat = Typ::base("nat");
    let bool_t = Typ::base("bool");
    let a = Term::const_("a", nat.clone());
    let b_nat = Term::const_("b", nat.clone());
    let b_bool = Term::const_("b", bool_t.clone());
    let c = Term::const_("c", bool_t.clone());

    let left = ThmKernel::admit(
        CTerm::certify(Pure::mk_equals(nat, a, b_nat)),
        "admitted:kernel_soundness_left",
    );
    let right = ThmKernel::admit(
        CTerm::certify(Pure::mk_equals(bool_t, b_bool, c)),
        "admitted:kernel_soundness_right",
    );

    let result = ThmKernel::transitive(&left, &right);
    assert!(
        matches!(result, Err(KernelError::TypeMismatch { .. })),
        "transitive accepted a chain across distinct known equality types: {result:?}"
    );
}

#[test]
fn transitive_rejects_dummy_equality_type_with_known_middle_type_mismatch() {
    let nat = Typ::base("nat");
    let bool_t = Typ::base("bool");
    let dummy_eq = Typ::dummy();
    let a = Term::const_("a", nat.clone());
    let b_nat = Term::free("b", nat);
    let b_bool = Term::free("b", bool_t.clone());
    let c = Term::const_("c", bool_t);

    let left = ThmKernel::admit(
        CTerm::certify(Pure::mk_equals(dummy_eq.clone(), a, b_nat)),
        "admitted:kernel_soundness_dummy_left",
    );
    let right = ThmKernel::admit(
        CTerm::certify(Pure::mk_equals(dummy_eq, b_bool, c)),
        "admitted:kernel_soundness_dummy_right",
    );

    let result = ThmKernel::transitive(&left, &right);
    assert!(
        matches!(&result, Err(KernelError::TypeMismatch { .. })),
        "transitive accepted dummy equality types despite known middle-term type mismatch: {result:?}"
    );
}

#[test]
fn beta_conversion_substitutes_the_argument() {
    let nat = Typ::base("nat");
    let lam = Term::abs("x", nat.clone(), Term::bound(0));
    let arg = Term::free("a", nat.clone());
    let redex = CTerm::certify_typed(Term::app(lam, arg.clone()), nat);

    let thm = ThmKernel::beta_conversion(redex).expect("well-formed beta redex");
    let (_, rhs) = Pure::dest_equals(thm.prop().term()).expect("beta conversion yields equality");

    assert_eq!(rhs, &arg);
    assert_ne!(rhs, &Term::bound(0));
    assert!(thm.is_fully_proved());
}

#[test]
fn abstraction_rejects_free_variable_in_hypotheses() {
    let nat = Typ::base("nat");
    let x = Term::free("x", nat.clone());
    let hyp_eq = CTerm::certify(Pure::mk_equals(nat.clone(), x.clone(), x));
    let thm = ThmKernel::assume(hyp_eq);

    let result = ThmKernel::abstraction("x", nat, &thm);
    assert!(
        matches!(&result, Err(KernelError::FreeVarInHypotheses { name }) if name == "x"),
        "abstraction ignored a free variable in hypotheses: {result:?}"
    );
}

#[test]
fn implies_intro_is_the_only_way_to_discharge_assume_here() {
    let a = prop("A");

    let assumed = ThmKernel::assume(a.clone());
    assert_eq!(assumed.hyps().len(), 1);
    assert!(assumed.is_fully_proved());
    assert!(!assumed.is_closed());
    assert!(!assumed.is_closed_proved());

    let discharged = ThmKernel::implies_intr(&a, &assumed).expect("A is present in hypotheses");
    assert!(discharged.hyps().is_empty());
    assert_eq!(discharged.nprems(), 1);
    assert!(discharged.is_fully_proved());
    assert!(discharged.is_closed());
    assert!(discharged.is_closed_proved());
}

#[test]
fn dummy_type_is_detectable_at_kernel_boundaries() {
    let ct = CTerm::certify_typed(Term::free("x", Typ::dummy()), Typ::dummy());
    let result = ct.require_non_dummy("kernel_soundness_test");

    assert!(matches!(result, Err(KernelError::DummyType { op }) if op == "kernel_soundness_test"));
}

#[test]
fn implies_elim_rejects_known_antecedent_type_mismatch() {
    let nat = Typ::base("nat");
    let bool_t = Typ::base("bool");
    let antecedent_nat = Term::free("A", nat);
    let antecedent_bool = Term::free("A", bool_t.clone());
    let conclusion = Term::const_("C", Typ::base("prop"));
    let implication = ThmKernel::admit(
        CTerm::certify(Pure::mk_implies(antecedent_nat, conclusion)),
        "admitted:implies_elim_attack",
    );
    let minor = ThmKernel::admit(
        CTerm::certify_typed(antecedent_bool, bool_t),
        "admitted:implies_elim_attack_minor",
    );

    let result = ThmKernel::implies_elim(&implication, &minor);
    assert!(
        matches!(&result, Err(KernelError::TypeMismatch { .. })),
        "implies_elim accepted alpha-equal antecedents with incompatible known types: {result:?}"
    );
}

#[test]
fn forall_elim_rejects_known_binder_argument_type_mismatch() {
    let nat = Typ::base("nat");
    let bool_t = Typ::base("bool");
    let pred = Term::const_("P", Typ::arrow(nat.clone(), Typ::base("prop")));
    let body = Term::app(pred, Term::bound(0));
    let all = Term::app(
        Term::const_(
            "Pure.all",
            Typ::arrow(Typ::arrow(nat.clone(), Typ::base("prop")), Typ::base("prop")),
        ),
        Term::abs("x", nat, body),
    );
    let all_thm = ThmKernel::admit(CTerm::certify(all), "admitted:forall_elim_attack");
    let bad_arg = CTerm::certify_typed(Term::free("b", bool_t.clone()), bool_t);

    let result = ThmKernel::forall_elim(bad_arg, &all_thm);
    assert!(
        matches!(&result, Err(KernelError::TypeMismatch { .. })),
        "forall_elim accepted an argument whose known type mismatches the binder: {result:?}"
    );
}

#[test]
fn instantiate_checked_rejects_known_type_mismatch() {
    let nat = Typ::base("nat");
    let bool_t = Typ::base("bool");
    let pred = Term::const_("P", Typ::arrow(nat.clone(), Typ::base("prop")));
    let x = Term::var("x", 0, nat.clone());
    let thm = ThmKernel::assume(CTerm::certify(Term::app(pred, x)));

    let mut env = Envir::empty(0);
    env.update("x".into(), 0, nat, Term::const_("True", bool_t));

    let checked = ThmKernel::instantiate_checked(&env, &thm);
    assert!(
        matches!(&checked, Err(KernelError::TypeMismatch { .. })),
        "instantiate_checked accepted a known ill-typed substitution: {checked:?}"
    );

    // The legacy infallible `instantiate` API is intentionally not public;
    // callers at this boundary must observe and handle the checked error.
}

#[test]
fn subst_premise_rejects_known_lhs_premise_type_mismatch() {
    let nat = Typ::base("nat");
    let bool_t = Typ::base("bool");
    let lhs_nat = Term::free("x", nat.clone());
    let rhs_nat = Term::free("y", nat.clone());
    let eq = ThmKernel::admit(
        CTerm::certify(Pure::mk_equals(nat, lhs_nat, rhs_nat)),
        "admitted:subst_attack_eq",
    );
    let bad_premise = Term::free("x", bool_t);
    let state = ThmKernel::admit(
        CTerm::certify(Pure::mk_implies(bad_premise, Term::const_("C", Typ::base("prop")))),
        "admitted:subst_attack_state",
    );

    let result = ThmKernel::subst_premise(&eq, &state, 0);
    assert!(
        result.is_none(),
        "subst_premise rewrote across alpha-equal terms with incompatible known types: {result:?}"
    );
}

#[test]
fn bicompose_rejects_known_alpha_match_type_mismatch() {
    let nat = Typ::base("nat");
    let bool_t = Typ::base("bool");
    let rule = ThmKernel::assume(CTerm::certify_typed(Term::free("A", nat.clone()), nat));
    let state = ThmKernel::admit(
        CTerm::certify(Pure::mk_implies(
            Term::free("A", bool_t),
            Term::const_("C", Typ::base("prop")),
        )),
        "admitted:bicompose_attack_state",
    );

    let result = ThmKernel::bicompose(false, &rule, &state, 0);
    assert!(
        result.is_none(),
        "bicompose discharged an alpha-equal subgoal with incompatible known types: {result:?}"
    );
}

#[test]
fn bicompose_eresolve_rejects_known_unifier_type_mismatch() {
    let nat = Typ::base("nat");
    let bool_t = Typ::base("bool");
    let rule = ThmKernel::admit(
        CTerm::certify(Pure::mk_implies(Term::free("H", nat.clone()), Term::free("A", nat))),
        "admitted:eresolve_attack_rule",
    );
    let state = ThmKernel::admit(
        CTerm::certify(Pure::mk_implies(
            Term::free("A", bool_t.clone()),
            Term::const_("C", Typ::base("prop")),
        )),
        "admitted:eresolve_attack_state",
    );
    let premise = Arc::new(ThmKernel::admit(
        CTerm::certify_typed(Term::free("H", bool_t.clone()), bool_t),
        "admitted:eresolve_attack_premise",
    ));

    let result = ThmKernel::bicompose_eresolve(true, &rule, &state, 0, &[premise]);
    assert!(
        result.is_none(),
        "bicompose_eresolve unified same-name terms with incompatible known types: {result:?}"
    );
}

#[test]
fn rewr_conv_rejects_ill_typed_rule_instantiation() {
    let nat = Typ::base("nat");
    let bool_t = Typ::base("bool");
    let x = Term::var("x", 0, nat.clone());
    let zero = Term::const_("zero", nat.clone());
    let rule = ThmKernel::admit(
        CTerm::certify(Pure::mk_equals(nat, x, zero)),
        "admitted:rewr_conv_attack_rule",
    );
    let target =
        ThmKernel::assume(CTerm::certify_typed(Term::const_("True", bool_t.clone()), bool_t));

    let conv = rewr_conv(rule);
    let result = conv(&target);
    assert!(
        result.is_none(),
        "rewr_conv returned a theorem for an ill-typed rewrite-rule instantiation: {result:?}"
    );
}
