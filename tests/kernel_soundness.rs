use std::sync::Arc;

use isabelle_rs::core::{
    conv::rewr_conv,
    envir::Envir,
    error::KernelError,
    logic::Pure,
    term::Term,
    theory::Theory,
    thm::{CTerm, CertStatus, KernelCheckMode, ThmKernel, ThmTrust},
    types::{Typ, TypeEnv},
};

fn prop(name: &str) -> CTerm {
    checked_prop(name)
}

fn declare_term(term: &Term, env: &mut TypeEnv) {
    match term {
        Term::Const { name, typ } if !typ.is_dummy() && !name.as_ref().starts_with("Pure.") => {
            env.declare_const(name.as_ref(), typ.clone());
        },
        Term::Free { name, typ } if !typ.is_dummy() => {
            env.declare_free(name.as_ref(), typ.clone());
        },
        Term::Abs { body, .. } => declare_term(body, env),
        Term::App { func, arg } => {
            declare_term(func, env);
            declare_term(arg, env);
        },
        Term::Const { .. } | Term::Free { .. } | Term::Var { .. } | Term::Bound(_) => {},
    }
}

fn checked_cterm(term: Term) -> CTerm {
    let mut env = TypeEnv::new();
    declare_term(&term, &mut env);
    CTerm::certify_checked(term, &env).expect("test fixture should certify as checked")
}

fn checked_prop(name: &str) -> CTerm {
    checked_cterm(Term::const_(name, Typ::base("prop")))
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
fn transitive_rejects_free_const_suffix_middle_term() {
    let nat = Typ::base("nat");
    let a = Term::const_("a", nat.clone());
    let free_zero = Term::free("zero", nat.clone());
    let const_zero = Term::const_("Groups.zero", nat.clone());
    let c = Term::const_("c", nat.clone());

    let left = ThmKernel::admit(
        checked_cterm(Pure::mk_equals(nat.clone(), a, free_zero)),
        "admitted:kernel_alpha_left",
    );
    let right = ThmKernel::admit(
        checked_cterm(Pure::mk_equals(nat, const_zero, c)),
        "admitted:kernel_alpha_right",
    );

    let result = ThmKernel::transitive(&left, &right);
    assert!(
        matches!(&result, Err(KernelError::MidTermsNotEquiv)),
        "transitive accepted Free/Const suffix matching through trusted alpha equality: {result:?}"
    );
}

#[test]
fn beta_conversion_substitutes_the_argument() {
    let nat = Typ::base("nat");
    let lam = Term::abs("x", nat.clone(), Term::bound(0));
    let arg = Term::free("a", nat.clone());
    let redex = checked_cterm(Term::app(lam, arg.clone()));

    let thm = ThmKernel::beta_conversion(redex).expect("well-formed beta redex");
    let (_, rhs) = Pure::dest_equals(thm.prop().term()).expect("beta conversion yields equality");

    assert_eq!(rhs, &arg);
    assert_ne!(rhs, &Term::bound(0));
    assert!(thm.is_fully_proved());
    assert!(thm.is_strict_closed_proved());
}

#[test]
fn abstraction_rejects_free_variable_in_hypotheses() {
    let nat = Typ::base("nat");
    let x = Term::free("x", nat.clone());
    let hyp_eq = checked_cterm(Pure::mk_equals(nat.clone(), x.clone(), x));
    let thm = ThmKernel::assume(hyp_eq).expect("checked hypothesis should enter strict assume");

    let result = ThmKernel::abstraction("x", nat, &thm);
    assert!(
        matches!(&result, Err(KernelError::FreeVarInHypotheses { name }) if name == "x"),
        "abstraction ignored a free variable in hypotheses: {result:?}"
    );
}

#[test]
fn implies_intro_is_the_only_way_to_discharge_assume_here() {
    let a = checked_prop("A");

    let assumed = ThmKernel::assume(a.clone()).expect("checked proposition should assume");
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
    assert!(discharged.is_strict_closed_proved());
}

#[test]
fn dummy_type_is_detectable_at_kernel_boundaries() {
    let ct = CTerm::certify_typed(Term::free("x", Typ::dummy()), Typ::dummy());
    let result = ct.require_non_dummy("kernel_soundness_test");

    assert!(matches!(result, Err(KernelError::DummyType { op }) if op == "kernel_soundness_test"));
}

#[test]
fn certify_checked_rejects_unresolved_dummy_type() {
    let env = TypeEnv::new();
    let result = CTerm::certify_checked(Term::free("x", Typ::dummy()), &env);

    assert!(
        matches!(&result, Err(KernelError::DummyType { op }) if *op == "CTerm::certify_checked"),
        "certify_checked accepted a Free with unresolved dummy type: {result:?}"
    );
}

#[test]
fn certify_checked_rejects_ill_typed_application() {
    let env = TypeEnv::new();
    let nat = Typ::base("nat");
    let bool_t = Typ::base("bool");
    let prop_t = Typ::base("prop");
    let func = Term::free("f", Typ::arrow(nat.clone(), prop_t));
    let arg = Term::free("b", bool_t);

    let result = CTerm::certify_checked(Term::app(func, arg), &env);
    assert!(
        matches!(&result, Err(KernelError::TypeMismatch { expected, actual })
            if expected == &nat && actual == &Typ::base("bool")),
        "certify_checked accepted an ill-typed application: {result:?}"
    );
}

#[test]
fn certify_checked_accepts_fully_typed_simple_proposition() {
    let mut env = TypeEnv::new();
    let prop_t = Typ::base("prop");
    env.declare_const("A", prop_t.clone());

    let ct = CTerm::certify_checked(Term::const_("A", prop_t.clone()), &env)
        .expect("declared, fully typed proposition should certify");

    assert_eq!(ct.term_type(), &prop_t);
    assert_eq!(ct.cert_status(), CertStatus::Checked);
    assert!(!ct.contains_dummy_type());
}

#[test]
fn certify_checked_rejects_inconsistent_polymorphic_application() {
    let env = TypeEnv::new();
    let nat = Typ::base("nat");
    let bool_t = Typ::base("bool");
    let lhs = Term::free("n", nat);
    let rhs = Term::free("b", bool_t);
    let eq = Term::app(Term::app(Term::const_("Pure.eq", Typ::dummy()), lhs), rhs);

    let result = CTerm::certify_checked(eq, &env);
    assert!(
        matches!(&result, Err(KernelError::TypeMismatch { .. })),
        "certify_checked accepted inconsistent instantiation of polymorphic equality: {result:?}"
    );
}

#[test]
fn checked_kernel_entry_rejects_dummy_typed_cterm() {
    let ct = CTerm::certify_compat(Term::free("x", Typ::dummy()));
    assert_eq!(ct.cert_status(), CertStatus::Compat);
    assert!(ct.contains_dummy_type());

    let checked = ThmKernel::reflexive(ct.clone());
    assert!(
        matches!(&checked, Err(KernelError::CompatCTerm { op })
            if *op == "ThmKernel::reflexive"),
        "strict reflexive entry accepted a compat CTerm: {checked:?}"
    );

    let legacy = ThmKernel::reflexive_compat(ct);
    assert!(
        legacy.prop().contains_dummy_type(),
        "legacy compatibility reflexive should remain visibly dummy-tainted"
    );
    assert!(
        legacy.prop().require_no_dummy_types("kernel_soundness_strict_gate").is_err(),
        "strict dummy gate failed to reject legacy compatibility theorem proposition"
    );
}

#[test]
fn checked_cterm_constructs_checked_reflexive_theorem() {
    let mut env = TypeEnv::new();
    let nat = Typ::base("nat");
    env.declare_type("nat", 0);
    env.declare_const("a", nat.clone());
    let ct = CTerm::certify_checked(Term::const_("a", nat.clone()), &env)
        .expect("declared constant should certify as checked");

    let thm = ThmKernel::reflexive(ct).expect("checked cterm should enter strict reflexive");

    assert!(thm.is_closed_proved());
    assert_eq!(thm.trust_status(), ThmTrust::Strict);
    assert!(thm.is_strict_kernel_theorem());
    assert!(thm.is_strict_closed_proved());
    assert_eq!(thm.prop().cert_status(), CertStatus::Checked);
    assert_eq!(thm.prop().term_type(), &Typ::base("prop"));
    assert!(!thm.prop().contains_dummy_type());
    assert!(thm.check_kernel_invariants(KernelCheckMode::Strict).is_ok());
}

#[test]
fn reflexive_compat_is_closed_shaped_but_not_strict_trusted() {
    let nat = Typ::base("nat");
    let ct = CTerm::certify(Term::const_("a", nat));

    let thm = ThmKernel::reflexive_compat(ct);

    assert_eq!(thm.trust_status(), ThmTrust::Compat);
    assert!(thm.is_compat_theorem());
    assert!(thm.is_fully_proved());
    assert!(thm.is_closed_proved(), "compat theorem can still have closed shape");
    assert!(!thm.is_strict_closed_proved(), "compat theorem must not be trusted");
    assert!(thm.check_kernel_invariants(KernelCheckMode::Compat).is_ok());
    assert!(
        matches!(
            thm.check_kernel_invariants(KernelCheckMode::Strict),
            Err(KernelError::KernelInvariant { .. })
        ),
        "strict invariant accepted a compat theorem"
    );
}

#[test]
fn trusted_theory_rejects_compat_closed_shaped_theorem() {
    let nat = Typ::base("nat");
    let thm = ThmKernel::reflexive_compat(CTerm::certify(Term::const_("a", nat)));
    assert!(thm.is_closed_proved());
    assert!(!thm.is_strict_closed_proved());

    let mut theory = Theory::begin("CompatReject", vec![Theory::pure()]);
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        theory.add_theorem("compat_refl", thm);
    }));

    assert!(result.is_err(), "trusted Theory accepted a compat closed-shaped theorem");
}

#[test]
fn strict_and_compat_premises_do_not_produce_strict_result() {
    let mut env = TypeEnv::new();
    let nat = Typ::base("nat");
    env.declare_type("nat", 0);
    env.declare_const("a", nat.clone());

    let checked = CTerm::certify_checked(Term::const_("a", nat.clone()), &env)
        .expect("declared constant should certify");
    let strict = ThmKernel::reflexive(checked).expect("checked reflexive should be strict");
    let compat = ThmKernel::reflexive_compat(CTerm::certify(Term::const_("a", nat)));

    let result = ThmKernel::transitive(&strict, &compat).expect("a == a transitive a == a");

    assert_eq!(strict.trust_status(), ThmTrust::Strict);
    assert_eq!(compat.trust_status(), ThmTrust::Compat);
    assert_eq!(result.trust_status(), ThmTrust::Compat);
    assert!(result.is_closed_proved());
    assert!(!result.is_strict_closed_proved());
}

#[test]
fn admitted_theorem_is_not_strict_trusted() {
    let admitted = ThmKernel::admit(prop("A"), "admitted:kernel_soundness");

    assert_eq!(admitted.trust_status(), ThmTrust::Admitted);
    assert!(admitted.is_admitted_theorem());
    assert!(!admitted.is_fully_proved());
    assert!(!admitted.is_strict_kernel_theorem());
    assert!(!admitted.is_strict_closed_proved());
    assert!(
        matches!(
            admitted.check_kernel_invariants(KernelCheckMode::Strict),
            Err(KernelError::KernelInvariant { .. })
        ),
        "strict invariant accepted an admitted theorem"
    );
}

#[test]
fn compat_cterm_cannot_enter_strict_assume() {
    let ct = CTerm::certify_compat(Term::const_("A", Typ::base("prop")));
    let result = ThmKernel::assume(ct);

    assert!(
        matches!(&result, Err(KernelError::CompatCTerm { op }) if *op == "ThmKernel::assume"),
        "strict assume accepted a compat CTerm: {result:?}"
    );
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
fn implies_elim_rejects_var_free_antecedent_confusion() {
    let prop_t = Typ::base("prop");
    let schematic = Term::var("A", 7, prop_t.clone());
    let free = Term::free("A", prop_t.clone());
    let conclusion = Term::const_("C", prop_t);

    let implication = ThmKernel::admit(
        CTerm::certify(Pure::mk_implies(schematic, conclusion)),
        "admitted:implies_elim_var_free_attack",
    );
    let minor =
        ThmKernel::admit(CTerm::certify(free), "admitted:implies_elim_var_free_attack_minor");

    let result = ThmKernel::implies_elim(&implication, &minor);
    assert!(
        matches!(&result, Err(KernelError::AntecedentMismatch)),
        "implies_elim accepted Var/Free matching through trusted alpha equality: {result:?}"
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
    let thm = ThmKernel::assume(checked_cterm(Term::app(pred, x)))
        .expect("checked proposition should enter strict assume");

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
    let rule = ThmKernel::admit(
        checked_cterm(Term::free("A", nat.clone())),
        "admitted:bicompose_attack_rule",
    );
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
    let target = ThmKernel::admit(
        checked_cterm(Term::const_("True", bool_t.clone())),
        "admitted:rewr_conv_attack_target",
    );

    let conv = rewr_conv(rule);
    let result = conv(&target);
    assert!(
        result.is_none(),
        "rewr_conv returned a theorem for an ill-typed rewrite-rule instantiation: {result:?}"
    );
}
