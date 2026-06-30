use std::convert::TryInto;

use isabelle_rs::kernel::{
    Derivation, InstEntry, KernelError, KernelRules, Name, ProofContext, ProofObligation, RawTerm,
    SearchFact, SearchFactDb, Signature, Term, TrustedTheorem, TrustedTheory, Ty,
    invariant::check_kernel_thm,
};

fn ty(name: &str) -> Ty {
    Ty::base(name).unwrap()
}

fn prop(name: &str) -> RawTerm {
    RawTerm::const_(name, Ty::prop())
}

fn ctx_with_props(names: &[&str]) -> ProofContext {
    let mut sig = Signature::new();
    for name in names {
        sig.declare_const(*name, Ty::prop());
    }
    ProofContext::new(sig)
}

fn ctx_with_nat_consts(names: &[&str]) -> ProofContext {
    let mut sig = Signature::new();
    for name in names {
        sig.declare_const(*name, ty("nat"));
    }
    ProofContext::new(sig)
}

#[test]
fn undeclared_const_is_rejected() {
    let ctx = ProofContext::new(Signature::new());
    let err = ctx.certify_prop(prop("A")).unwrap_err();
    assert!(matches!(err, KernelError::UndeclaredConst(_)));
}

#[test]
fn undeclared_free_is_rejected() {
    let ctx = ProofContext::new(Signature::new());
    let err = ctx.certify_prop(RawTerm::free("x", Ty::prop())).unwrap_err();
    assert!(matches!(err, KernelError::UndeclaredFree(_)));
}

#[test]
fn dummy_type_is_not_constructible() {
    assert!(matches!(Ty::base("dummy"), Err(KernelError::ReservedDummyType)));
}

#[test]
fn ill_typed_application_is_rejected() {
    let mut sig = Signature::new();
    sig.declare_const("f", Ty::arrow(ty("nat"), ty("nat")));
    sig.declare_const("P", Ty::prop());
    let ctx = ProofContext::new(sig);
    let err = ctx
        .certify_term(RawTerm::app(
            RawTerm::const_("f", Ty::arrow(ty("nat"), ty("nat"))),
            prop("P"),
        ))
        .unwrap_err();
    assert!(matches!(err, KernelError::TypeMismatch { .. }));
}

#[test]
fn declared_const_and_free_are_certified() {
    let mut sig = Signature::new();
    sig.declare_const("A", Ty::prop());
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    assert!(ctx.certify_prop(prop("A")).is_ok());
    assert!(ctx.certify_term(RawTerm::free("x", ty("nat"))).is_ok());
}

#[test]
fn free_const_middle_mismatch_is_rejected() {
    let mut sig = Signature::new();
    for name in ["a", "b", "Groups.zero"] {
        sig.declare_const(name, ty("nat"));
    }
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("zero", ty("nat"));

    let left_eq = ctx
        .certify_prop(RawTerm::eq(
            RawTerm::const_("a", ty("nat")),
            RawTerm::free("zero", ty("nat")),
        ))
        .unwrap();
    let right_eq = ctx
        .certify_prop(RawTerm::eq(
            RawTerm::const_("Groups.zero", ty("nat")),
            RawTerm::const_("b", ty("nat")),
        ))
        .unwrap();
    let left_thm = KernelRules::assume(left_eq).into_kernel();
    let right_thm = KernelRules::assume(right_eq).into_kernel();
    assert!(matches!(
        KernelRules::transitive(&left_thm, &right_thm),
        Err(KernelError::MiddleMismatch)
    ));
}

#[test]
fn var_free_middle_mismatch_is_rejected() {
    let mut ctx = ctx_with_nat_consts(&["a", "b"]);
    ctx.declare_free("x", ty("nat"));
    let left_eq = ctx
        .certify_prop(RawTerm::eq(RawTerm::const_("a", ty("nat")), RawTerm::var("x", 7, ty("nat"))))
        .unwrap();
    let right_eq = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::const_("b", ty("nat"))))
        .unwrap();
    let left = KernelRules::assume(left_eq).into_kernel();
    let right = KernelRules::assume(right_eq).into_kernel();
    assert!(matches!(KernelRules::transitive(&left, &right), Err(KernelError::MiddleMismatch)));
}

#[test]
fn assume_yields_strict_open_theorem() {
    let ctx = ctx_with_props(&["A"]);
    let a = ctx.certify_prop(prop("A")).unwrap();
    let thm = KernelRules::assume(a).into_kernel();

    assert!(thm.is_open());
    assert_eq!(thm.hyps().len(), 1);
    assert!(check_kernel_thm(&thm).is_ok());
    assert!(thm.clone().try_close().is_err());
}

#[test]
fn reflexive_yields_closed_trusted_theorem() {
    let ctx = ctx_with_nat_consts(&["a"]);
    let a = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let refl = KernelRules::reflexive(a);
    let trusted = refl.trust().unwrap();

    let mut theory = TrustedTheory::new();
    theory.add("a_refl", trusted);
    assert_eq!(theory.len(), 1);
}

#[test]
fn implies_intr_discharges_hypothesis() {
    let ctx = ctx_with_props(&["A"]);
    let a = ctx.certify_prop(prop("A")).unwrap();
    let assumed = KernelRules::assume(a.clone()).into_kernel();
    let identity = KernelRules::implies_intr(&a, &assumed).unwrap();

    assert!(identity.hyps().is_empty());
    assert!(check_kernel_thm(&identity).is_ok());
    assert!(identity.try_close().unwrap().trust().is_ok());
}

#[test]
fn implies_elim_requires_exact_antecedent() {
    let ctx = ctx_with_props(&["A", "B"]);
    let a = ctx.certify_prop(prop("A")).unwrap();
    let b = ctx.certify_prop(prop("B")).unwrap();
    let assumed_a = KernelRules::assume(a.clone()).into_kernel();
    let identity = KernelRules::implies_intr(&a, &assumed_a).unwrap();
    let assumed_b = KernelRules::assume(b).into_kernel();

    assert!(matches!(
        KernelRules::implies_elim(&identity, &assumed_b),
        Err(KernelError::AntecedentMismatch)
    ));
}

#[test]
fn implies_elim_preserves_open_minor_hypothesis() {
    let ctx = ctx_with_props(&["A"]);
    let a = ctx.certify_prop(prop("A")).unwrap();
    let assumed_a = KernelRules::assume(a.clone()).into_kernel();
    let identity = KernelRules::implies_intr(&a, &assumed_a).unwrap();
    let minor = KernelRules::assume(a).into_kernel();
    let result = KernelRules::implies_elim(&identity, &minor).unwrap();

    assert_eq!(result.hyps().len(), 1);
    assert!(result.try_close().is_err());
}

#[test]
fn transitive_requires_typed_middle_equality() {
    let ctx = ctx_with_nat_consts(&["a", "b", "c"]);
    let left = ctx
        .certify_prop(RawTerm::eq(RawTerm::const_("a", ty("nat")), RawTerm::const_("b", ty("nat"))))
        .unwrap();
    let right = ctx
        .certify_prop(RawTerm::eq(RawTerm::const_("c", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();
    let left = KernelRules::assume(left).into_kernel();
    let right = KernelRules::assume(right).into_kernel();

    assert!(matches!(KernelRules::transitive(&left, &right), Err(KernelError::MiddleMismatch)));
}

#[test]
fn proof_obligation_is_not_theorem() {
    let ctx = ctx_with_props(&["A"]);
    let obligation = ProofObligation::new(&ctx, prop("A")).unwrap();
    assert_eq!(obligation.goal().term().ty(), Ty::prop());
}

#[test]
fn search_fact_cannot_enter_trusted_theory() {
    let ctx = ctx_with_props(&["A"]);
    let a = ctx.certify_prop(prop("A")).unwrap();
    let fact = SearchFact::Admitted { prop: a, reason: "admitted:test".into() };
    let mut db = SearchFactDb::new();
    db.add(fact.clone());
    assert_eq!(db.len(), 1);

    let trusted: Result<TrustedTheorem, KernelError> = fact.try_into();
    assert!(matches!(trusted, Err(KernelError::SearchFactNotTrusted)));
}

// ---------------------------------------------------------------------------
// beta_conversion
// ---------------------------------------------------------------------------

#[test]
fn beta_conversion_reduces_identity() {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);
    // (λx:nat. x) a  ≡  a
    let redex = ctx
        .certify_term(RawTerm::app(
            RawTerm::abs("x", ty("nat"), RawTerm::bound(0)),
            RawTerm::const_("a", ty("nat")),
        ))
        .unwrap();
    let thm = KernelRules::beta_conversion(redex).unwrap();
    let (_, lhs, rhs) = thm.as_kernel().prop().term().dest_eq().unwrap();
    // LHS: (λx:nat. x) a
    assert!(lhs.dest_app().is_some());
    // RHS: a (the Bound(0) has been substituted)
    assert_eq!(*rhs, *ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap().term());
    assert!(thm.as_kernel().hyps().is_empty());
}

#[test]
fn beta_conversion_rejects_non_application() {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);
    let a = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    assert!(matches!(KernelRules::beta_conversion(a), Err(KernelError::BetaRedexExpected(_))));
}

#[test]
fn beta_conversion_rejects_non_lambda() {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    sig.declare_const("f", Ty::arrow(ty("nat"), ty("nat")));
    let ctx = ProofContext::new(sig);
    // f a  (App where func is a Const, not an Abs)
    let redex = ctx
        .certify_term(RawTerm::app(
            RawTerm::const_("f", Ty::arrow(ty("nat"), ty("nat"))),
            RawTerm::const_("a", ty("nat")),
        ))
        .unwrap();
    assert!(matches!(KernelRules::beta_conversion(redex), Err(KernelError::BetaRedexExpected(_))));
}

#[test]
fn beta_conversion_produces_closed_trusted_theorem() {
    let ctx = ctx_with_nat_consts(&["a"]);
    let redex = ctx
        .certify_term(RawTerm::app(
            RawTerm::abs("x", ty("nat"), RawTerm::bound(0)),
            RawTerm::const_("a", ty("nat")),
        ))
        .unwrap();
    let thm = KernelRules::beta_conversion(redex).unwrap();
    let trusted = thm.trust().unwrap();

    let mut theory = TrustedTheory::new();
    theory.add("beta_identity", trusted);
    assert_eq!(theory.len(), 1);
}

#[test]
fn beta_conversion_substitution_is_correct() {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    sig.declare_const("f", Ty::arrow(ty("nat"), ty("nat")));
    let ctx = ProofContext::new(sig);
    // (λx:nat. f x) a  ≡  f a
    let redex = ctx
        .certify_term(RawTerm::app(
            RawTerm::abs(
                "x",
                ty("nat"),
                RawTerm::app(
                    RawTerm::const_("f", Ty::arrow(ty("nat"), ty("nat"))),
                    RawTerm::bound(0),
                ),
            ),
            RawTerm::const_("a", ty("nat")),
        ))
        .unwrap();
    let thm = KernelRules::beta_conversion(redex).unwrap();
    let (_, _lhs, rhs) = thm.as_kernel().prop().term().dest_eq().unwrap();
    // RHS: f a
    let expected_rhs = ctx
        .certify_term(RawTerm::app(
            RawTerm::const_("f", Ty::arrow(ty("nat"), ty("nat"))),
            RawTerm::const_("a", ty("nat")),
        ))
        .unwrap();
    assert_eq!(*rhs, *expected_rhs.term());
}

#[test]
fn beta_conversion_inner_bound_preserved() {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);
    // (λx:nat. (λy:nat. y) x) a  ≡  (λy:nat. y) a
    // body of outer λ: (λy:nat. y) x  = App(Abs(Bound(0)), Bound(0))
    // After substitution: Bound(0) → a, inner Bound(0) → stays
    // Result: App(Abs(Bound(0)), a) = (λy:nat. y) a
    let redex = ctx
        .certify_term(RawTerm::app(
            RawTerm::abs(
                "x",
                ty("nat"),
                RawTerm::app(RawTerm::abs("y", ty("nat"), RawTerm::bound(0)), RawTerm::bound(0)),
            ),
            RawTerm::const_("a", ty("nat")),
        ))
        .unwrap();
    let thm = KernelRules::beta_conversion(redex).unwrap();
    let (_, _lhs, rhs) = thm.as_kernel().prop().term().dest_eq().unwrap();
    // RHS should be (λy:nat. y) a
    let rhs_app = rhs.dest_app().unwrap();
    assert!(rhs_app.0.dest_abs().is_some()); // func is still λy. y
    assert_eq!(*rhs_app.1, *ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap().term());
}

#[test]
fn beta_conversion_invariant_check_passes() {
    let ctx = ctx_with_nat_consts(&["a"]);
    let redex = ctx
        .certify_term(RawTerm::app(
            RawTerm::abs("x", ty("nat"), RawTerm::bound(0)),
            RawTerm::const_("a", ty("nat")),
        ))
        .unwrap();
    let thm = KernelRules::beta_conversion(redex).unwrap();
    assert!(check_kernel_thm(thm.as_kernel()).is_ok());
}

#[test]
fn beta_conversion_nested_lambda_preserves_outer() {
    // (λx:nat. (λy:nat. x)) a  ≡  (λy:nat. a)
    // The inner lambda body (Bound(1) = x) is correctly substituted with `a`.
    // de Bruijn: outer Abs body = Abs("y", nat, Bound(1)).
    // instantiate_bound0 replaces Bound(0) → a, inner bound shift means Bound(1) → a.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);
    let redex = ctx
        .certify_term(RawTerm::app(
            RawTerm::abs("x", ty("nat"), RawTerm::abs("y", ty("nat"), RawTerm::bound(1))),
            RawTerm::const_("a", ty("nat")),
        ))
        .unwrap();
    let thm = KernelRules::beta_conversion(redex).unwrap();
    let (_, _lhs, rhs) = thm.as_kernel().prop().term().dest_eq().unwrap();
    // RHS: λy:nat. a
    let (name, param_ty, body) = rhs.dest_abs().unwrap();
    assert_eq!(name.as_str(), "y");
    assert_eq!(*param_ty, ty("nat"));
    assert!(body.dest_abs().is_none());
    assert!(!matches!(body, Term::Bound { .. }));
    assert_eq!(*body, *ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap().term());
    assert!(check_kernel_thm(thm.as_kernel()).is_ok());
}

#[test]
fn beta_conversion_arg_with_bound_lifts_correctly() {
    // (λf:nat→nat. f a) (λx:nat. x)  ≡  (λx:nat. x) a
    // The argument (λx:nat. x) is itself an abstraction containing Bound(0).
    // When substituted into the body, lift must correctly shift the bound index
    // so it doesn't become captured by any inner binder.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);
    let redex = ctx
        .certify_term(RawTerm::app(
            RawTerm::abs(
                "f",
                Ty::arrow(ty("nat"), ty("nat")),
                RawTerm::app(RawTerm::bound(0), RawTerm::const_("a", ty("nat"))),
            ),
            RawTerm::abs("x", ty("nat"), RawTerm::bound(0)),
        ))
        .unwrap();
    let thm = KernelRules::beta_conversion(redex).unwrap();
    let (_, _lhs, rhs) = thm.as_kernel().prop().term().dest_eq().unwrap();
    // RHS: (λx:nat. x) a  — the argument was correctly substituted
    let rhs_app = rhs.dest_app().unwrap();
    let (abs_name, abs_param_ty, abs_body) = rhs_app.0.dest_abs().unwrap();
    assert_eq!(abs_name.as_str(), "x");
    assert_eq!(*abs_param_ty, ty("nat"));
    assert_eq!(*abs_body, Term::Bound { index: 0, ty: ty("nat") });
    assert_eq!(*rhs_app.1, *ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap().term());
    assert!(check_kernel_thm(thm.as_kernel()).is_ok());
}

#[test]
fn beta_conversion_triple_nested() {
    // (λx:nat. (λy:nat. (λz:nat. x))) a  ≡  (λy:nat. (λz:nat. a))
    // Triple nesting stresses the lift/subst interaction across multiple binder layers.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);
    let redex = ctx
        .certify_term(RawTerm::app(
            RawTerm::abs(
                "x",
                ty("nat"),
                RawTerm::abs("y", ty("nat"), RawTerm::abs("z", ty("nat"), RawTerm::bound(2))),
            ),
            RawTerm::const_("a", ty("nat")),
        ))
        .unwrap();
    let thm = KernelRules::beta_conversion(redex).unwrap();
    let (_, _lhs, rhs) = thm.as_kernel().prop().term().dest_eq().unwrap();
    // RHS: λy:nat. (λz:nat. a)
    let (name_y, _, body_y) = rhs.dest_abs().unwrap();
    assert_eq!(name_y.as_str(), "y");
    let (name_z, _, body_z) = body_y.dest_abs().unwrap();
    assert_eq!(name_z.as_str(), "z");
    assert!(!matches!(body_z, Term::Bound { .. }));
    assert_eq!(*body_z, *ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap().term());
    assert!(check_kernel_thm(thm.as_kernel()).is_ok());
}

// ---------------------------------------------------------------------------
// forall_intr
// ---------------------------------------------------------------------------

fn ctx_with_nat_free(name: &str) -> ProofContext {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free(name, ty("nat"));
    ctx
}

#[test]
fn forall_intr_generalises_free_variable() {
    // x == a |- x == a  →  implies_intr discharges hyps  →  |- (x == a) ⇒ (x == a)
    // Then forall_intr(x)  →  |- ⋀x. ((x == a) ⇒ (x == a))
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let eq_prop = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();

    // Build a theorem whose conclusion mentions x but hypotheses don't.
    let assumed = KernelRules::assume(eq_prop.clone()).into_kernel();
    let discharged = KernelRules::implies_intr(&eq_prop, &assumed).unwrap();
    assert!(discharged.hyps().is_empty());

    let x_var = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let forall_thm = KernelRules::forall_intr(&x_var, &discharged).unwrap();

    // Result should be a Forall wrapping the discharged proposition.
    let (name, param_ty, body) = forall_thm.prop().term().dest_forall().unwrap();
    assert_eq!(name.as_str(), "x");
    assert_eq!(*param_ty, ty("nat"));
    // Body: (Bound(0) == a) ⇒ (Bound(0) == a)
    let (prem, concl) = body.dest_imp().unwrap();
    let (_, lhs1, _rhs1) = prem.dest_eq().unwrap();
    let (_, lhs2, _rhs2) = concl.dest_eq().unwrap();
    assert_eq!(*lhs1, Term::Bound { index: 0, ty: ty("nat") });
    assert_eq!(*lhs2, Term::Bound { index: 0, ty: ty("nat") });
    assert!(forall_thm.hyps().is_empty());
}

#[test]
fn forall_intr_rejects_variable_free_in_hypotheses() {
    // x == a |- x == a  →  x is free in the hypothesis, so forall_intr must fail.
    let ctx = ctx_with_nat_free("x");
    let eq_prop = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();
    let open_thm = KernelRules::assume(eq_prop).into_kernel(); // {x == a} |- x == a

    let x_var = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    assert!(matches!(
        KernelRules::forall_intr(&x_var, &open_thm),
        Err(KernelError::FreeVarInHypotheses { .. })
    ));
}

#[test]
fn forall_intr_rejects_non_free_variable() {
    // Passing a Const as the "variable" to generalise should fail.
    let ctx = ctx_with_nat_free("x");
    let eq_prop = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();
    let assumed = KernelRules::assume(eq_prop.clone()).into_kernel();
    let discharged = KernelRules::implies_intr(&eq_prop, &assumed).unwrap();

    let a_const = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    assert!(matches!(
        KernelRules::forall_intr(&a_const, &discharged),
        Err(KernelError::NotAbstractable(_))
    ));
}

#[test]
fn forall_intr_produces_closed_theorem_from_closed() {
    // Starting from a closed theorem, forall_intr stays closed.
    let ctx = ctx_with_nat_free("x");
    let eq_prop = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();
    let assumed = KernelRules::assume(eq_prop.clone()).into_kernel();
    let closed = KernelRules::implies_intr(&eq_prop, &assumed).unwrap().try_close().unwrap();

    let x_var = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let forall_thm = KernelRules::forall_intr(&x_var, closed.as_kernel()).unwrap();

    assert!(forall_thm.hyps().is_empty());
    assert!(forall_thm.try_close().is_ok());
}

#[test]
fn forall_intr_invariant_check_passes() {
    let ctx = ctx_with_nat_free("x");
    let eq_prop = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();
    let assumed = KernelRules::assume(eq_prop.clone()).into_kernel();
    let discharged = KernelRules::implies_intr(&eq_prop, &assumed).unwrap();

    let x_var = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let forall_thm = KernelRules::forall_intr(&x_var, &discharged).unwrap();
    assert!(check_kernel_thm(&forall_thm).is_ok());
}

#[test]
fn forall_intr_preserves_hypotheses() {
    // Starting from a hyps-free theorem, forall_intr stays hyps-free.
    let ctx = ctx_with_nat_free("x");
    let eq_prop = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();
    let assumed = KernelRules::assume(eq_prop.clone()).into_kernel();
    let discharged = KernelRules::implies_intr(&eq_prop, &assumed).unwrap();
    assert!(discharged.hyps().is_empty());

    let x_var = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let forall_thm = KernelRules::forall_intr(&x_var, &discharged).unwrap();
    assert!(forall_thm.hyps().is_empty());
    assert!(forall_thm.prop().term().dest_forall().is_some());
}

// ── forall_elim ──

#[test]
fn forall_elim_instantiates_bound_variable() {
    // |- ⋀x: nat. (x == a) ⇒ (x == a)  →  forall_elim(a)  →  |- (a == a) ⇒ (a == a)
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let eq_prop = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();
    let assumed = KernelRules::assume(eq_prop.clone()).into_kernel();
    let discharged = KernelRules::implies_intr(&eq_prop, &assumed).unwrap();
    let x_var = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let forall_thm = KernelRules::forall_intr(&x_var, &discharged).unwrap();

    // Now instantiate with a.
    let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let inst = KernelRules::forall_elim(&forall_thm, &a_term).unwrap();

    // Result should be (a == a) ⇒ (a == a) with Bound(0) replaced by a.
    let (prem, concl) = inst.prop().term().dest_imp().unwrap();
    let (_, pl, pr) = prem.dest_eq().unwrap();
    let (_, cl, cr) = concl.dest_eq().unwrap();
    assert_eq!(pl, a_term.term());
    assert_eq!(pr, a_term.term());
    assert_eq!(cl, a_term.term());
    assert_eq!(cr, a_term.term());
    assert!(inst.hyps().is_empty());
}

#[test]
fn forall_elim_rejects_non_forall_input() {
    // Passing a non-Forall (e.g., a reflexive equality) should fail.
    let ctx = ctx_with_nat_consts(&["a"]);
    let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let refl = KernelRules::reflexive(a_term.clone()).into_kernel();

    assert!(matches!(KernelRules::forall_elim(&refl, &a_term), Err(KernelError::NotForall)));
}

#[test]
fn forall_elim_rejects_binder_type_mismatch() {
    // ⋀x: nat. P(x)  with  arg: bool  →  type mismatch rejected.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    sig.declare_const("T", Ty::prop());
    sig.declare_const("F", Ty::prop());
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let eq_prop = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();
    let assumed = KernelRules::assume(eq_prop.clone()).into_kernel();
    let discharged = KernelRules::implies_intr(&eq_prop, &assumed).unwrap();
    let x_var = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let forall_thm = KernelRules::forall_intr(&x_var, &discharged).unwrap();

    // bool constant as argument — type mismatch with nat binder.
    let bool_term = ctx.certify_term(RawTerm::const_("T", Ty::prop())).unwrap();
    assert!(matches!(
        KernelRules::forall_elim(&forall_thm, &bool_term),
        Err(KernelError::ForallBinderMismatch { .. })
    ));
}

#[test]
fn forall_elim_preserves_hypotheses() {
    // Hypotheses should be preserved through forall_elim.
    // Build ⋀x:nat. ..., then assume it, then forall_elim — hyps stay.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let eq_prop = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();
    let assumed = KernelRules::assume(eq_prop.clone()).into_kernel();
    let discharged = KernelRules::implies_intr(&eq_prop, &assumed).unwrap();
    let x_var = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let forall_thm = KernelRules::forall_intr(&x_var, &discharged).unwrap();

    // Wrap with assume: {⋀x. ...} |- ⋀x. ...
    let forall_cprop = forall_thm.prop().clone();
    let assumed_forall = KernelRules::assume(forall_cprop).into_kernel();
    assert_eq!(assumed_forall.hyps().len(), 1);

    // forall_elim should preserve the hypothesis.
    let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let inst = KernelRules::forall_elim(&assumed_forall, &a_term).unwrap();

    assert_eq!(inst.hyps().len(), 1);
    // The hypothesis should still be the forall proposition.
    assert!(inst.hyps()[0].term().dest_forall().is_some());
}

#[test]
fn forall_elim_invariant_check_passes() {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let eq_prop = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();
    let assumed = KernelRules::assume(eq_prop.clone()).into_kernel();
    let discharged = KernelRules::implies_intr(&eq_prop, &assumed).unwrap();
    let x_var = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let forall_thm = KernelRules::forall_intr(&x_var, &discharged).unwrap();

    let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let inst = KernelRules::forall_elim(&forall_thm, &a_term).unwrap();
    assert!(check_kernel_thm(&inst).is_ok());
}

#[test]
fn forall_elim_nested_forall_instantiate_outer() {
    // ⋀x:nat. ⋀y:nat. (x == y)  →  forall_elim(a)  →  ⋀y:nat. (a == y)
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));
    ctx.declare_free("y", ty("nat"));

    // Build: |- ⋀x. ⋀y. (x == y)
    let eq_prop = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::free("y", ty("nat"))))
        .unwrap();
    let assumed = KernelRules::assume(eq_prop.clone()).into_kernel();
    let discharged = KernelRules::implies_intr(&eq_prop, &assumed).unwrap();
    let y_var = ctx.certify_term(RawTerm::free("y", ty("nat"))).unwrap();
    let forall_y = KernelRules::forall_intr(&y_var, &discharged).unwrap();
    let x_var = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let forall_xy = KernelRules::forall_intr(&x_var, &forall_y).unwrap();

    // Verify nested structure: ⋀x. ⋀y. (Bound(1) == Bound(0))
    let (outer_name, outer_ty, outer_body) = forall_xy.prop().term().dest_forall().unwrap();
    assert_eq!(outer_name.as_str(), "x");
    assert_eq!(*outer_ty, ty("nat"));
    assert!(outer_body.dest_forall().is_some());

    // Instantiate outer binder only.
    let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let inst = KernelRules::forall_elim(&forall_xy, &a_term).unwrap();

    // Result should be ⋀y. (a == Bound(0)) ⇒ (a == Bound(0))
    let (inner_name, inner_ty, inner_body) = inst.prop().term().dest_forall().unwrap();
    assert_eq!(inner_name.as_str(), "y");
    assert_eq!(*inner_ty, ty("nat"));
    // inner_body is Imp(Eq(a, Bound(0)), Eq(a, Bound(0)))
    let (prem, _concl) = inner_body.dest_imp().unwrap();
    let (_, lhs, rhs) = prem.dest_eq().unwrap();
    // lhs should be "a" (the substituted constant), not a Bound
    assert_eq!(lhs, a_term.term());
    // rhs should be Bound(0, nat) — the inner binder's variable
    assert_eq!(*rhs, Term::Bound { index: 0, ty: ty("nat") });
    // Also check the conclusion
    let (_, cl, cr) = inner_body.dest_imp().unwrap().1.dest_eq().unwrap();
    assert_eq!(cl, a_term.term());
    assert_eq!(*cr, Term::Bound { index: 0, ty: ty("nat") });
}

#[test]
fn forall_intr_elim_roundtrip() {
    // forall_intr(x) then forall_elim(x) should return the original proposition.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let eq_prop = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();
    let assumed = KernelRules::assume(eq_prop.clone()).into_kernel();
    let discharged = KernelRules::implies_intr(&eq_prop, &assumed).unwrap();
    // discharged: |- (x == a) ⇒ (x == a)

    let x_var = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let forall_thm = KernelRules::forall_intr(&x_var, &discharged).unwrap();
    // forall_thm: |- ⋀x. ((Bound(0) == a) ⇒ (Bound(0) == a))

    let inst = KernelRules::forall_elim(&forall_thm, &x_var).unwrap();
    // inst: |- (x == a) ⇒ (x == a)  — should be alpha_eq to discharged

    assert!(inst.prop().term().alpha_eq(discharged.prop().term()));
    assert_eq!(inst.hyps().len(), discharged.hyps().len());
}

// ── substitution depth / de Bruijn stress ──

#[test]
fn forall_elim_does_not_replace_bound1() {
    // Start from y == x.
    // After forall_intr(x), then forall_intr(y), the theorem is:
    //   ⋀y. ⋀x. ((Bound(1) == Bound(0)) ⇒ (Bound(1) == Bound(0)))
    // Eliminating the outer y with a gives:
    //   ⋀x. ((a == Bound(0)) ⇒ (a == Bound(0)))
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));
    ctx.declare_free("y", ty("nat"));

    // Build: |- ⋀x. ⋀y. (y == x)
    // Note: Eq(RawTerm::free("y",...), RawTerm::free("x",...)) gives the correct order
    let eq_prop = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("y", ty("nat")), RawTerm::free("x", ty("nat"))))
        .unwrap();
    let assumed = KernelRules::assume(eq_prop.clone()).into_kernel();
    let discharged = KernelRules::implies_intr(&eq_prop, &assumed).unwrap();
    // discharged: |- (y == x) ⇒ (y == x)
    let x_var = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let forall_x = KernelRules::forall_intr(&x_var, &discharged).unwrap();
    // forall_x: |- ⋀x. ((y == Bound(0)) ⇒ (y == Bound(0)))
    let y_var = ctx.certify_term(RawTerm::free("y", ty("nat"))).unwrap();
    let forall_xy = KernelRules::forall_intr(&y_var, &forall_x).unwrap();
    // forall_xy: |- ⋀y. ⋀x. ((Bound(0) == Bound(1)) ⇒ (Bound(0) == Bound(1)))

    // Eliminate outer (y) — the outermost Forall's binder.
    let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let inst = KernelRules::forall_elim(&forall_xy, &a_term).unwrap();

    // Result: ⋀x. ((a == Bound(0)) ⇒ (a == Bound(0)))
    // Outer binder y was eliminated; inner binder x remains (now outermost).
    // Bound(0) still refers to x; the substituted "a" was y.
    let (name, _, body) = inst.prop().term().dest_forall().unwrap();
    assert_eq!(name.as_str(), "x"); // inner binder now outermost
    let (prem, _) = body.dest_imp().unwrap();
    let (_, lhs, rhs) = prem.dest_eq().unwrap();
    // lhs is "a" — the substituted y (was Bound(1))
    assert_eq!(lhs, a_term.term());
    // rhs is Bound(0, nat) — still refers to x
    assert_eq!(*rhs, Term::Bound { index: 0, ty: ty("nat") });
}

#[test]
fn forall_elim_replaces_all_bound0_occurrences() {
    // ⋀x:nat. (x == x)  →  forall_elim(x, a)  →  (a == a)
    // Both Bound(0) occurrences must be replaced.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    // Build: |- (x == x) ⇒ (x == x) then forall_intr(x)
    let eq_prop = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::free("x", ty("nat"))))
        .unwrap();
    let assumed = KernelRules::assume(eq_prop.clone()).into_kernel();
    let discharged = KernelRules::implies_intr(&eq_prop, &assumed).unwrap();
    let x_var = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let forall_thm = KernelRules::forall_intr(&x_var, &discharged).unwrap();
    // forall_thm: |- ⋀x. ((Bound(0) == Bound(0)) ⇒ (Bound(0) == Bound(0)))

    let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let inst = KernelRules::forall_elim(&forall_thm, &a_term).unwrap();

    // inst: |- (a == a) ⇒ (a == a)
    let (prem, concl) = inst.prop().term().dest_imp().unwrap();
    let (_, pl, pr) = prem.dest_eq().unwrap();
    let (_, cl, cr) = concl.dest_eq().unwrap();
    assert_eq!(pl, a_term.term());
    assert_eq!(pr, a_term.term());
    assert_eq!(cl, a_term.term());
    assert_eq!(cr, a_term.term());
}

#[test]
fn forall_elim_consecutive_nested() {
    // ⋀x:nat. ⋀y:nat. (x == y)  →  forall_elim(a)  →  ⋀y:nat. (a == y)
    // →  forall_elim(b)  →  (a == b)
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    sig.declare_const("b", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));
    ctx.declare_free("y", ty("nat"));

    // Build: |- ⋀x. ⋀y. (x == y) ⇒ (x == y)
    let eq_prop = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::free("y", ty("nat"))))
        .unwrap();
    let assumed = KernelRules::assume(eq_prop.clone()).into_kernel();
    let discharged = KernelRules::implies_intr(&eq_prop, &assumed).unwrap();
    let y_var = ctx.certify_term(RawTerm::free("y", ty("nat"))).unwrap();
    let forall_y = KernelRules::forall_intr(&y_var, &discharged).unwrap();
    let x_var = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let forall_xy = KernelRules::forall_intr(&x_var, &forall_y).unwrap();

    // First elim: outer binder x → a
    let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let inst1 = KernelRules::forall_elim(&forall_xy, &a_term).unwrap();
    // inst1: |- ⋀y. (a == y) ⇒ (a == y)
    assert!(inst1.prop().term().dest_forall().is_some());

    // Second elim: inner binder y → b
    let b_term = ctx.certify_term(RawTerm::const_("b", ty("nat"))).unwrap();
    let inst2 = KernelRules::forall_elim(&inst1, &b_term).unwrap();
    // inst2: |- (a == b) ⇒ (a == b)
    assert!(inst2.prop().term().dest_forall().is_none()); // no more forall
    let (prem, _) = inst2.prop().term().dest_imp().unwrap();
    let (_, lhs, rhs) = prem.dest_eq().unwrap();
    assert_eq!(lhs, a_term.term());
    assert_eq!(rhs, b_term.term());
}

#[test]
fn forall_elim_with_abs_argument() {
    // ⋀f:(nat→nat). (f a == a)  →  forall_elim(λx:nat. x)  →  ((λx:nat. x) a == a)
    // Teast that an Abs term as argument substitutes correctly.
    let nat_to_nat = Ty::arrow(ty("nat"), ty("nat"));
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("f", nat_to_nat.clone());

    // Build: |- (f a == a) ⇒ (f a == a) then forall_intr(f)
    let f_var = RawTerm::free("f", nat_to_nat.clone());
    let f_app = RawTerm::app(f_var.clone(), RawTerm::const_("a", ty("nat")));
    let eq_prop =
        ctx.certify_prop(RawTerm::eq(f_app.clone(), RawTerm::const_("a", ty("nat")))).unwrap();
    let assumed = KernelRules::assume(eq_prop.clone()).into_kernel();
    let discharged = KernelRules::implies_intr(&eq_prop, &assumed).unwrap();
    let f_cterm = ctx.certify_term(f_var).unwrap();
    let forall_thm = KernelRules::forall_intr(&f_cterm, &discharged).unwrap();
    // forall_thm: |- ⋀f:(nat→nat). ((Bound(0) a == a) ⇒ (Bound(0) a == a))

    // Eliminate f with λx:nat. x
    let id_abs = ctx.certify_term(RawTerm::abs("x", ty("nat"), RawTerm::bound(0))).unwrap();
    let inst = KernelRules::forall_elim(&forall_thm, &id_abs).unwrap();

    // inst: |- ((λx:nat. x) a == a) ⇒ ((λx:nat. x) a == a)
    let (prem, _) = inst.prop().term().dest_imp().unwrap();
    let (_, lhs, rhs) = prem.dest_eq().unwrap();
    // lhs should be (λx:nat. x) a — an application with an Abs as func
    let (func, arg) = lhs.dest_app().unwrap();
    assert!(func.dest_abs().is_some()); // func is the Abs
    assert_eq!(arg, &Term::Const { name: "a".into(), ty: ty("nat") });
    assert_eq!(rhs, &Term::Const { name: "a".into(), ty: ty("nat") });
}

#[test]
fn beta_conversion_then_forall_elim() {
    // Build |- ⋀x:nat. ((λz:nat. z) x == x) via:
    //   1. assume((λz. z) x == x)
    //   2. beta-convert: ((λz. z) x == x) → proves the equality
    //   Actually: beta_conversion on redex (λz. z) x gives |- ((λz. z) x) == x
    //   3. assume that proposition, implies_intr to close
    //   4. forall_intr(x)
    //   5. forall_elim(x, a) → |- ((λz. z) a) == a
    // Verify substitution and beta don't interfere.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    // Step 1: beta_conversion on redex (λz:nat. z) x
    let redex = ctx
        .certify_term(RawTerm::app(
            RawTerm::abs("z", ty("nat"), RawTerm::bound(0)),
            RawTerm::free("x", ty("nat")),
        ))
        .unwrap();
    let beta_thm = KernelRules::beta_conversion(redex).unwrap();
    // beta_thm: |- ((λz:nat. z) x) == x

    // Step 2: assume this equality, then implies_intr to discharge.
    let beta_prop = beta_thm.as_kernel().prop().clone();
    let assumed = KernelRules::assume(beta_prop.clone()).into_kernel();
    let discharged = KernelRules::implies_intr(&beta_prop, &assumed).unwrap();

    // Step 3: forall_intr(x)
    let x_var = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let forall_thm = KernelRules::forall_intr(&x_var, &discharged).unwrap();
    // forall_thm: |- ⋀x:nat. (((λz:nat. z) Bound(0)) == Bound(0)) ⇒ ...

    // Step 4: forall_elim(x, a)
    let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let inst = KernelRules::forall_elim(&forall_thm, &a_term).unwrap();

    // inst: |- (((λz:nat. z) a) == a) ⇒ (((λz:nat. z) a) == a)
    let (prem, _) = inst.prop().term().dest_imp().unwrap();
    let (_, lhs, rhs) = prem.dest_eq().unwrap();
    // lhs should be App(Abs(...), Const("a"))
    let (lfunc, larg) = lhs.dest_app().unwrap();
    assert!(lfunc.dest_abs().is_some());
    assert_eq!(larg, &Term::Const { name: "a".into(), ty: ty("nat") });
    // rhs should be a
    assert_eq!(rhs, &Term::Const { name: "a".into(), ty: ty("nat") });
}

// ── combination (function-congruence) ──

#[test]
fn combination_basic_application() {
    // f: nat → nat, g: nat → nat; a, b: nat
    // Assume {f == g}, assume {a == b}
    // combination → {f==g, a==b} |- f a == g b
    let fn_ty = Ty::arrow(ty("nat"), ty("nat"));
    let mut sig = Signature::new();
    sig.declare_const("f", fn_ty.clone());
    sig.declare_const("g", fn_ty.clone());
    sig.declare_const("a", ty("nat"));
    sig.declare_const("b", ty("nat"));
    let ctx = ProofContext::new(sig);

    let f_eq_g = ctx
        .certify_prop(RawTerm::eq(
            RawTerm::const_("f", fn_ty.clone()),
            RawTerm::const_("g", fn_ty.clone()),
        ))
        .unwrap();
    let a_eq_b = ctx
        .certify_prop(RawTerm::eq(RawTerm::const_("a", ty("nat")), RawTerm::const_("b", ty("nat"))))
        .unwrap();

    let th_f = KernelRules::assume(f_eq_g).into_kernel();
    let th_x = KernelRules::assume(a_eq_b).into_kernel();

    let result = KernelRules::combination(&th_f, &th_x).unwrap();

    // result: {f==g, a==b} |- f a == g b
    assert_eq!(result.hyps().len(), 2);

    let (obj_ty, lhs, rhs) = result.prop().term().dest_eq().unwrap();
    assert_eq!(*obj_ty, ty("nat")); // codomain
    // lhs = f a
    let (lfunc, larg) = lhs.dest_app().unwrap();
    assert_eq!(lfunc, &Term::Const { name: "f".into(), ty: fn_ty.clone() });
    assert_eq!(larg, &Term::Const { name: "a".into(), ty: ty("nat") });
    // rhs = g b
    let (rfunc, rarg) = rhs.dest_app().unwrap();
    assert_eq!(rfunc, &Term::Const { name: "g".into(), ty: fn_ty });
    assert_eq!(rarg, &Term::Const { name: "b".into(), ty: ty("nat") });
}

#[test]
fn combination_rejects_non_equality_function_premise() {
    // First premise is an implication, not equality.
    let mut sig = Signature::new();
    sig.declare_const("P", Ty::prop());
    sig.declare_const("Q", Ty::prop());
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);

    let p_imp_q = ctx
        .certify_prop(RawTerm::imp(
            RawTerm::const_("P", Ty::prop()),
            RawTerm::const_("Q", Ty::prop()),
        ))
        .unwrap();
    let a_eq_a = ctx
        .certify_prop(RawTerm::eq(RawTerm::const_("a", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();

    let th_bad = KernelRules::assume(p_imp_q).into_kernel();
    let th_x = KernelRules::assume(a_eq_a).into_kernel();

    let err = KernelRules::combination(&th_bad, &th_x).unwrap_err();
    assert!(matches!(err, KernelError::NotEquality));
}

#[test]
fn combination_rejects_non_equality_argument_premise() {
    // Second premise is an implication, not equality.
    let fn_ty = Ty::arrow(ty("nat"), ty("nat"));
    let mut sig = Signature::new();
    sig.declare_const("f", fn_ty.clone());
    sig.declare_const("P", Ty::prop());
    sig.declare_const("Q", Ty::prop());
    let ctx = ProofContext::new(sig);

    let f_eq_f = ctx
        .certify_prop(RawTerm::eq(
            RawTerm::const_("f", fn_ty.clone()),
            RawTerm::const_("f", fn_ty.clone()),
        ))
        .unwrap();
    let p_imp_q = ctx
        .certify_prop(RawTerm::imp(
            RawTerm::const_("P", Ty::prop()),
            RawTerm::const_("Q", Ty::prop()),
        ))
        .unwrap();

    let th_f = KernelRules::assume(f_eq_f).into_kernel();
    let th_bad = KernelRules::assume(p_imp_q).into_kernel();

    let err = KernelRules::combination(&th_f, &th_bad).unwrap_err();
    assert!(matches!(err, KernelError::NotEquality));
}

#[test]
fn combination_rejects_non_function_lhs_rhs() {
    // f, g have type nat (not function).
    let mut sig = Signature::new();
    sig.declare_const("f", ty("nat"));
    sig.declare_const("g", ty("nat"));
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);

    let f_eq_g = ctx
        .certify_prop(RawTerm::eq(RawTerm::const_("f", ty("nat")), RawTerm::const_("g", ty("nat"))))
        .unwrap();
    let a_eq_a = ctx
        .certify_prop(RawTerm::eq(RawTerm::const_("a", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();

    let th_f = KernelRules::assume(f_eq_g).into_kernel();
    let th_x = KernelRules::assume(a_eq_a).into_kernel();

    let err = KernelRules::combination(&th_f, &th_x).unwrap_err();
    assert!(matches!(err, KernelError::NotFunctionType(_)));
}

#[test]
fn combination_rejects_argument_domain_mismatch() {
    // f: nat → nat, but argument equality is bool == bool.
    let fn_ty = Ty::arrow(ty("nat"), ty("nat"));
    let mut sig = Signature::new();
    sig.declare_const("f", fn_ty.clone());
    sig.declare_const("g", fn_ty.clone());
    sig.declare_const("x", ty("bool"));
    sig.declare_const("y", ty("bool"));
    let ctx = ProofContext::new(sig);

    let f_eq_g = ctx
        .certify_prop(RawTerm::eq(
            RawTerm::const_("f", fn_ty.clone()),
            RawTerm::const_("g", fn_ty.clone()),
        ))
        .unwrap();
    let x_eq_y = ctx
        .certify_prop(RawTerm::eq(
            RawTerm::const_("x", ty("bool")),
            RawTerm::const_("y", ty("bool")),
        ))
        .unwrap();

    let th_f = KernelRules::assume(f_eq_g).into_kernel();
    let th_x = KernelRules::assume(x_eq_y).into_kernel();

    let err = KernelRules::combination(&th_f, &th_x).unwrap_err();
    assert!(matches!(err, KernelError::TypeMismatch { .. }));
}

#[test]
fn combination_preserves_hypotheses() {
    // f == g is assumed; a == a is reflexive (closed).
    // Result hyps = {f == g}.
    let fn_ty = Ty::arrow(ty("nat"), ty("nat"));
    let mut sig = Signature::new();
    sig.declare_const("f", fn_ty.clone());
    sig.declare_const("g", fn_ty.clone());
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);

    let f_eq_g = ctx
        .certify_prop(RawTerm::eq(
            RawTerm::const_("f", fn_ty.clone()),
            RawTerm::const_("g", fn_ty.clone()),
        ))
        .unwrap();
    let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();

    let th_f = KernelRules::assume(f_eq_g.clone()).into_kernel(); // {f==g} |- f==g
    let th_a = KernelRules::reflexive(a_term).into_kernel(); // |- a == a

    let result = KernelRules::combination(&th_f, &th_a).unwrap();

    // Hypotheses are only from th_f
    assert_eq!(result.hyps().len(), 1);
    assert!(result.hyps()[0].term().alpha_eq(f_eq_g.term()));
}

#[test]
fn combination_invariant_check_passes() {
    // Build valid combination, verify invariant replay succeeds.
    let fn_ty = Ty::arrow(ty("nat"), ty("nat"));
    let mut sig = Signature::new();
    sig.declare_const("f", fn_ty.clone());
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);

    let f_term = ctx.certify_term(RawTerm::const_("f", fn_ty)).unwrap();
    let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();

    let th_f = KernelRules::reflexive(f_term).into_kernel();
    let th_a = KernelRules::reflexive(a_term).into_kernel();
    let result = KernelRules::combination(&th_f, &th_a).unwrap();

    check_kernel_thm(&result).unwrap();
    // result: |- f a == f a
    assert_eq!(result.hyps().len(), 0);
    let (_, lhs, rhs) = result.prop().term().dest_eq().unwrap();
    assert_eq!(lhs, rhs);
}

#[test]
fn combination_composes_with_reflexive_closed() {
    // reflexive f gives |- f == f
    // reflexive a gives |- a == a
    // combination: |- f a == f a (closed, trusted)
    let fn_ty = Ty::arrow(ty("nat"), ty("nat"));
    let mut sig = Signature::new();
    sig.declare_const("f", fn_ty.clone());
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);

    let f_term = ctx.certify_term(RawTerm::const_("f", fn_ty.clone())).unwrap();
    let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();

    let th_f = KernelRules::reflexive(f_term).into_kernel();
    let th_a = KernelRules::reflexive(a_term).into_kernel();

    let result = KernelRules::combination(&th_f, &th_a).unwrap();

    // Closed: no hypotheses.
    assert_eq!(result.hyps().len(), 0);
    let (_, lhs, rhs) = result.prop().term().dest_eq().unwrap();
    assert_eq!(lhs, rhs); // f a == f a
    let (func, arg) = lhs.dest_app().unwrap();
    assert_eq!(func, &Term::Const { name: "f".into(), ty: fn_ty });
    assert_eq!(arg, &Term::Const { name: "a".into(), ty: ty("nat") });
}

#[test]
fn combination_with_forall_elim_result() {
    // Test that combination consumes a function equality produced by forall_elim.
    //
    // Build:
    //   1. reflexive(F) → |- F == F
    //   2. forall_intr(F, ...) → |- ⋀F:(nat→nat). F == F
    //   3. forall_elim with f → |- f == f          (function equality from forall_elim)
    //   4. reflexive(a) → |- a == a
    //   5. combination(f==f, a==a) → |- f a == f a (forall_elim result as function premise)
    let nat_to_nat = Ty::arrow(ty("nat"), ty("nat"));
    let mut sig = Signature::new();
    sig.declare_const("f", nat_to_nat.clone());
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("F", nat_to_nat.clone());

    // Step 1: reflexive on F gives |- F == F
    let f_var = ctx.certify_term(RawTerm::free("F", nat_to_nat.clone())).unwrap();
    let refl_f = KernelRules::reflexive(f_var.clone()).into_kernel();

    // Step 2: forall_intr gives |- ⋀F:(nat→nat). F == F
    let forall_thm = KernelRules::forall_intr(&f_var, &refl_f).unwrap();

    // Step 3: forall_elim with f gives |- f == f
    let f_const = ctx.certify_term(RawTerm::const_("f", nat_to_nat.clone())).unwrap();
    let f_eq_f = KernelRules::forall_elim(&forall_thm, &f_const).unwrap();

    // Step 4: reflexive on a gives |- a == a
    let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let a_eq_a = KernelRules::reflexive(a_term).into_kernel();

    // Step 5: combination: |- f a == f a
    let result = KernelRules::combination(&f_eq_f, &a_eq_a).unwrap();

    // Closed theorem: no hypotheses (both inputs closed).
    assert_eq!(result.hyps().len(), 0);

    // Result is f a == f a
    let (_, lhs, rhs) = result.prop().term().dest_eq().unwrap();
    assert_eq!(lhs, rhs);
    let (func, arg) = lhs.dest_app().unwrap();
    assert_eq!(func, &Term::Const { name: "f".into(), ty: nat_to_nat });
    assert_eq!(arg, &Term::Const { name: "a".into(), ty: ty("nat") });

    // Invariant replay passes on the composed result.
    check_kernel_thm(&result).unwrap();
}

#[test]
fn combination_codomain_not_nat() {
    // f, g: nat → bool, a, b: nat.
    // The result f a and g b should have type bool (not nat).
    let nat_to_bool = Ty::arrow(ty("nat"), ty("bool"));
    let mut sig = Signature::new();
    sig.declare_const("f", nat_to_bool.clone());
    sig.declare_const("g", nat_to_bool.clone());
    sig.declare_const("a", ty("nat"));
    sig.declare_const("b", ty("nat"));
    let ctx = ProofContext::new(sig);

    let f_eq_g = ctx
        .certify_prop(RawTerm::eq(
            RawTerm::const_("f", nat_to_bool.clone()),
            RawTerm::const_("g", nat_to_bool.clone()),
        ))
        .unwrap();
    let a_eq_b = ctx
        .certify_prop(RawTerm::eq(RawTerm::const_("a", ty("nat")), RawTerm::const_("b", ty("nat"))))
        .unwrap();

    let th_f = KernelRules::assume(f_eq_g).into_kernel();
    let th_x = KernelRules::assume(a_eq_b).into_kernel();
    let result = KernelRules::combination(&th_f, &th_x).unwrap();

    // Result: |- f a == g b, both sides are App with ty bool.
    let (eq_ty, lhs, rhs) = result.prop().term().dest_eq().unwrap();
    // The equality object type should be bool (codomain of nat→bool).
    assert_eq!(eq_ty, &ty("bool"));

    let (func, arg) = lhs.dest_app().unwrap();
    assert_eq!(func, &Term::Const { name: "f".into(), ty: nat_to_bool.clone() });
    assert_eq!(arg, &Term::Const { name: "a".into(), ty: ty("nat") });

    let (func, arg) = rhs.dest_app().unwrap();
    assert_eq!(func, &Term::Const { name: "g".into(), ty: nat_to_bool });
    assert_eq!(arg, &Term::Const { name: "b".into(), ty: ty("nat") });

    check_kernel_thm(&result).unwrap();
}

#[test]
fn combination_function_domain() {
    // f, g: (nat → nat) → nat
    // h, k: nat → nat (as arguments)
    // combination: |- f h == g k
    let nat_to_nat = Ty::arrow(ty("nat"), ty("nat"));
    let fn_fn_ty = Ty::arrow(nat_to_nat.clone(), ty("nat"));
    let mut sig = Signature::new();
    sig.declare_const("f", fn_fn_ty.clone());
    sig.declare_const("g", fn_fn_ty.clone());
    sig.declare_const("h", nat_to_nat.clone());
    sig.declare_const("k", nat_to_nat.clone());
    let ctx = ProofContext::new(sig);

    let f_eq_g = ctx
        .certify_prop(RawTerm::eq(
            RawTerm::const_("f", fn_fn_ty.clone()),
            RawTerm::const_("g", fn_fn_ty.clone()),
        ))
        .unwrap();
    let h_eq_k = ctx
        .certify_prop(RawTerm::eq(
            RawTerm::const_("h", nat_to_nat.clone()),
            RawTerm::const_("k", nat_to_nat.clone()),
        ))
        .unwrap();

    let th_f = KernelRules::assume(f_eq_g).into_kernel();
    let th_x = KernelRules::assume(h_eq_k).into_kernel();
    let result = KernelRules::combination(&th_f, &th_x).unwrap();

    // Result: |- f h == g k
    let (eq_ty, lhs, rhs) = result.prop().term().dest_eq().unwrap();
    assert_eq!(eq_ty, &ty("nat")); // codomain is nat

    // lhs is f h: App(App)? No — f has type (nat→nat)→nat, h has type nat→nat.
    // So f h is App(func=f, arg=h, ty=nat).
    let (func, arg) = lhs.dest_app().unwrap();
    assert_eq!(func, &Term::Const { name: "f".into(), ty: fn_fn_ty.clone() });
    assert_eq!(arg, &Term::Const { name: "h".into(), ty: nat_to_nat.clone() });

    let (func, arg) = rhs.dest_app().unwrap();
    assert_eq!(func, &Term::Const { name: "g".into(), ty: fn_fn_ty });
    assert_eq!(arg, &Term::Const { name: "k".into(), ty: nat_to_nat });

    check_kernel_thm(&result).unwrap();
}

#[test]
fn combination_argument_from_beta_conversion() {
    // combination where the argument premise comes from beta_conversion.
    //
    // 1. beta_conversion on ((λx:nat. x) a) gives |- ((λx. x) a) == a
    // 2. reflexive on f: nat→nat gives |- f == f
    // 3. combination(f==f, ((λx. x) a)==a) → |- f ((λx. x) a) == f a
    let fn_ty = Ty::arrow(ty("nat"), ty("nat"));
    let mut sig = Signature::new();
    sig.declare_const("f", fn_ty.clone());
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);

    // Build ((λx:nat. x) a) as a CTerm
    let lambda = RawTerm::abs("x", ty("nat"), RawTerm::bound(0));
    let app = RawTerm::app(lambda, RawTerm::const_("a", ty("nat")));
    let redex = ctx.certify_term(app).unwrap();

    // beta_conversion: |- ((λx. x) a) == a
    let beta_thm = KernelRules::beta_conversion(redex).unwrap().into_kernel();

    // reflexive f: |- f == f
    let f_term = ctx.certify_term(RawTerm::const_("f", fn_ty.clone())).unwrap();
    let refl_f = KernelRules::reflexive(f_term).into_kernel();

    // combination: |- f ((λx. x) a) == f a
    let result = KernelRules::combination(&refl_f, &beta_thm).unwrap();

    assert_eq!(result.hyps().len(), 0);
    let (_, lhs, rhs) = result.prop().term().dest_eq().unwrap();

    // lhs: f ((λx. x) a)
    let (func, arg) = lhs.dest_app().unwrap();
    assert_eq!(func, &Term::Const { name: "f".into(), ty: fn_ty });
    // arg is (λx. x) a
    let (inner_func, inner_arg) = arg.dest_app().unwrap();
    assert!(inner_func.dest_abs().is_some());
    assert_eq!(inner_arg, &Term::Const { name: "a".into(), ty: ty("nat") });

    // rhs: f a
    let (func, arg) = rhs.dest_app().unwrap();
    assert_eq!(func, &Term::Const { name: "f".into(), ty: Ty::arrow(ty("nat"), ty("nat")) });
    assert_eq!(arg, &Term::Const { name: "a".into(), ty: ty("nat") });

    check_kernel_thm(&result).unwrap();
}

#[test]
fn combination_nested_app() {
    // h(f a) == h(g b) via:
    //   1. combination(f==g, a==b) → |- f a == g b
    //   2. reflexive(h) → |- h == h
    //   3. combination(h==h, f a == g b) → |- h (f a) == h (g b)
    let fn_ty = Ty::arrow(ty("nat"), ty("nat"));
    let mut sig = Signature::new();
    sig.declare_const("f", fn_ty.clone());
    sig.declare_const("g", fn_ty.clone());
    sig.declare_const("h", fn_ty.clone());
    sig.declare_const("a", ty("nat"));
    sig.declare_const("b", ty("nat"));
    let ctx = ProofContext::new(sig);

    // f == g and a == b as assumptions
    let f_eq_g = ctx
        .certify_prop(RawTerm::eq(
            RawTerm::const_("f", fn_ty.clone()),
            RawTerm::const_("g", fn_ty.clone()),
        ))
        .unwrap();
    let a_eq_b = ctx
        .certify_prop(RawTerm::eq(RawTerm::const_("a", ty("nat")), RawTerm::const_("b", ty("nat"))))
        .unwrap();

    let th_f = KernelRules::assume(f_eq_g).into_kernel();
    let th_x = KernelRules::assume(a_eq_b).into_kernel();

    // First combination: ⊢ f a == g b
    let inner = KernelRules::combination(&th_f, &th_x).unwrap();
    let (_, inner_lhs, inner_rhs) = inner.prop().term().dest_eq().unwrap();
    // inner_lhs: f a, inner_rhs: g b
    assert!(inner_lhs.dest_app().is_some());
    assert!(inner_rhs.dest_app().is_some());

    // reflexive on h: |- h == h
    let h_term = ctx.certify_term(RawTerm::const_("h", fn_ty.clone())).unwrap();
    let refl_h = KernelRules::reflexive(h_term).into_kernel();

    // Second combination: h (f a) == h (g b)
    let outer = KernelRules::combination(&refl_h, &inner).unwrap();

    let (_, outer_lhs, outer_rhs) = outer.prop().term().dest_eq().unwrap();
    // outer_lhs: h (f a)
    let (h_func, h_arg) = outer_lhs.dest_app().unwrap();
    assert_eq!(h_func, &Term::Const { name: "h".into(), ty: fn_ty });
    let (f_func, f_arg) = h_arg.dest_app().unwrap();
    assert_eq!(f_func, &Term::Const { name: "f".into(), ty: Ty::arrow(ty("nat"), ty("nat")) });
    assert_eq!(f_arg, &Term::Const { name: "a".into(), ty: ty("nat") });

    // outer_rhs: h (g b)
    let (h_func, h_arg) = outer_rhs.dest_app().unwrap();
    assert_eq!(h_func, &Term::Const { name: "h".into(), ty: Ty::arrow(ty("nat"), ty("nat")) });
    let (g_func, g_arg) = h_arg.dest_app().unwrap();
    assert_eq!(g_func, &Term::Const { name: "g".into(), ty: Ty::arrow(ty("nat"), ty("nat")) });
    assert_eq!(g_arg, &Term::Const { name: "b".into(), ty: ty("nat") });

    check_kernel_thm(&outer).unwrap();
}

// ---------------------------------------------------------------------------
// abstraction
// ---------------------------------------------------------------------------

#[test]
fn abstraction_basic() {
    // x not free in Γ → Γ |- (λx. t) == (λx. u) from Γ |- t == u
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    sig.declare_const("b", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    // Build: {a == b} |- a == b
    let a_eq_b = ctx
        .certify_prop(RawTerm::eq(RawTerm::const_("a", ty("nat")), RawTerm::const_("b", ty("nat"))))
        .unwrap();
    let thm = KernelRules::assume(a_eq_b).into_kernel();

    // Abstract x:nat (x not free in "a == b")
    let result = KernelRules::abstraction("x".into(), ty("nat"), &thm).unwrap();

    // Result: {a == b} |- (λx:nat. a) == (λx:nat. b)
    assert_eq!(result.hyps().len(), 1);
    let (fn_ty, lhs, rhs) = result.prop().term().dest_eq().unwrap();
    // Equality type is nat→nat (fn nat→nat)
    assert_eq!(fn_ty, &Ty::arrow(ty("nat"), ty("nat")));

    // lhs and rhs are Abs
    let (name_l, pt_l, body_l) = lhs.dest_abs().unwrap();
    assert_eq!(name_l.as_str(), "x");
    assert_eq!(pt_l, &ty("nat"));
    assert_eq!(body_l, &Term::Const { name: "a".into(), ty: ty("nat") });

    let (name_r, pt_r, body_r) = rhs.dest_abs().unwrap();
    assert_eq!(name_r.as_str(), "x");
    assert_eq!(pt_r, &ty("nat"));
    assert_eq!(body_r, &Term::Const { name: "b".into(), ty: ty("nat") });
}

#[test]
fn abstraction_rejects_free_in_hypotheses() {
    // x is free in a hypothesis → rejected.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    // Build: {x == a} |- x == a
    let x_eq_a = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();
    let thm = KernelRules::assume(x_eq_a).into_kernel();

    // Try to abstract x:nat — x IS free in hypothesis "x == a"
    let err = KernelRules::abstraction("x".into(), ty("nat"), &thm).unwrap_err();
    assert!(matches!(err, KernelError::FreeVarInHypotheses { .. }));
}

#[test]
fn abstraction_preserves_hypotheses() {
    // Γ = {A, B}, abstract x:nat (x not free in A or B)
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    sig.declare_const("b", ty("nat"));
    sig.declare_const("A", Ty::prop());
    sig.declare_const("B", Ty::prop());
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    // Build: {A, B, a == b} |- a == b
    let a_eq_b = ctx
        .certify_prop(RawTerm::eq(RawTerm::const_("a", ty("nat")), RawTerm::const_("b", ty("nat"))))
        .unwrap();
    let thm = KernelRules::assume(a_eq_b).into_kernel();

    // Add extra hypotheses to check preservation
    // We'll use implies_intr to discharge a==b, then assume extra hyps.
    // Actually simpler: assume A and B separately, then derive a==b.
    // But KernelRules only handles single assumption. Let's just verify
    // that the original hyps (a==b) are preserved after abstraction.
    let result = KernelRules::abstraction("x".into(), ty("nat"), &thm).unwrap();
    assert_eq!(result.hyps().len(), 1);
    assert!(result.hyps()[0].term().alpha_eq(thm.hyps()[0].term()));
}

#[test]
fn abstraction_rejects_non_equality() {
    // Input is an implication (not equality).
    let ctx = ctx_with_props(&["P", "Q"]);
    let p = ctx.certify_prop(prop("P")).unwrap();
    let _q = ctx.certify_prop(prop("Q")).unwrap();
    let thm = KernelRules::assume(p.clone()).into_kernel();
    let discharged = KernelRules::implies_intr(&p, &thm).unwrap();
    // discharged: |- P ==> P (not equality)

    let err = KernelRules::abstraction("x".into(), ty("nat"), &discharged).unwrap_err();
    assert!(matches!(err, KernelError::NotEquality));
}

#[test]
fn abstraction_invariant_check_passes() {
    // Build a valid abstraction and verify invariant replay succeeds.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let refl = KernelRules::reflexive(a_term).into_kernel();
    // refl: |- a == a

    let result = KernelRules::abstraction("x".into(), ty("nat"), &refl).unwrap();
    // result: |- (λx:nat. a) == (λx:nat. a)

    assert_eq!(result.hyps().len(), 0);
    check_kernel_thm(&result).unwrap();
}

#[test]
fn abstraction_closed_from_closed() {
    // Closed input → closed output.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("y", ty("nat"));

    let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let refl = KernelRules::reflexive(a_term).into_kernel();

    let result = KernelRules::abstraction("y".into(), ty("nat"), &refl).unwrap();

    assert_eq!(result.hyps().len(), 0);
    let closed = result.try_close();
    assert!(closed.is_ok());
}

#[test]
fn abstraction_nested() {
    // Abstract x:nat, then y:nat — two binders in sequence.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));
    ctx.declare_free("y", ty("nat"));

    let a_term = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let refl = KernelRules::reflexive(a_term).into_kernel();

    // First abstraction: |- (λx:nat. a) == (λx:nat. a)
    let abs_x = KernelRules::abstraction("x".into(), ty("nat"), &refl).unwrap();
    assert_eq!(abs_x.hyps().len(), 0);

    // Second abstraction: |- (λy:nat. (λx:nat. a)) == (λy:nat. (λx:nat. a))
    let abs_y = KernelRules::abstraction("y".into(), ty("nat"), &abs_x).unwrap();
    assert_eq!(abs_y.hyps().len(), 0);

    // Verify nested structure: outer Abs contains inner Abs
    let (outer_name, _, outer_body) = abs_y.prop().term().dest_eq().unwrap().1.dest_abs().unwrap();
    assert_eq!(outer_name.as_str(), "y");
    let (inner_name, _, inner_body) = outer_body.dest_abs().unwrap();
    assert_eq!(inner_name.as_str(), "x");
    assert_eq!(inner_body, &Term::Const { name: "a".into(), ty: ty("nat") });

    check_kernel_thm(&abs_y).unwrap();
}

#[test]
fn abstraction_with_forall_elim_and_combination() {
    // Full pipeline:
    //   1. reflexive(F): |- F == F
    //   2. forall_intr: |- ⋀F:(nat→nat). F == F
    //   3. forall_elim with f: |- f == f
    //   4. abstraction on x:nat: |- (λx:nat. f x) == (λx:nat. f x)
    let fn_ty = Ty::arrow(ty("nat"), ty("nat"));
    let mut sig = Signature::new();
    sig.declare_const("f", fn_ty.clone());
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("F", fn_ty.clone());
    ctx.declare_free("x", ty("nat"));

    // reflexive on F: |- F == F
    let f_var = ctx.certify_term(RawTerm::free("F", fn_ty.clone())).unwrap();
    let refl = KernelRules::reflexive(f_var.clone()).into_kernel();

    // forall_intr: |- ⋀F. F == F
    let forall_thm = KernelRules::forall_intr(&f_var, &refl).unwrap();

    // forall_elim with f: |- f == f
    let f_const = ctx.certify_term(RawTerm::const_("f", fn_ty)).unwrap();
    let f_eq_f = KernelRules::forall_elim(&forall_thm, &f_const).unwrap();

    // Now we need |- f x == f x, not just |- f == f.
    // Use combination: reflexive(x) gives |- x == x, then combination(f==f, x==x) → |- f x == f x
    let x_term = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let x_eq_x = KernelRules::reflexive(x_term).into_kernel();
    let fx_eq_fx = KernelRules::combination(&f_eq_f, &x_eq_x).unwrap();

    // abstraction on x: |- (λx:nat. f x) == (λx:nat. f x)
    let result = KernelRules::abstraction("x".into(), ty("nat"), &fx_eq_fx).unwrap();

    assert_eq!(result.hyps().len(), 0);
    // Result is equality of two Abs terms
    let (_, lhs, rhs) = result.prop().term().dest_eq().unwrap();
    let (name_l, _, _) = lhs.dest_abs().unwrap();
    assert_eq!(name_l.as_str(), "x");
    let (name_r, _, _) = rhs.dest_abs().unwrap();
    assert_eq!(name_r.as_str(), "x");

    check_kernel_thm(&result).unwrap();
}

#[test]
fn abstraction_replaces_free_with_bound0() {
    // Critical binding-semantics test:
    // Premise |- x == x, abstraction on x must produce
    // |- (λx:nat. Bound(0)) == (λx:nat. Bound(0))
    // NOT |- (λx:nat. Free("x")) == (λx:nat. Free("x"))
    let sig = Signature::new();
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let x_term = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let refl = KernelRules::reflexive(x_term).into_kernel();
    // refl: |- x == x  (closed — x is free in conclusion but not in hyps)

    let result = KernelRules::abstraction("x".into(), ty("nat"), &refl).unwrap();

    assert_eq!(result.hyps().len(), 0);
    let (_, lhs, rhs) = result.prop().term().dest_eq().unwrap();

    // lhs body must be Bound(0), not Free("x")
    let (_, _, lhs_body) = lhs.dest_abs().unwrap();
    assert_eq!(
        lhs_body,
        &Term::Bound { index: 0, ty: ty("nat") },
        "abstraction must replace Free(x) with Bound(0), got {lhs_body:?}"
    );

    // rhs body must also be Bound(0)
    let (_, _, rhs_body) = rhs.dest_abs().unwrap();
    assert_eq!(
        rhs_body,
        &Term::Bound { index: 0, ty: ty("nat") },
        "abstraction must replace Free(x) with Bound(0), got {rhs_body:?}"
    );

    check_kernel_thm(&result).unwrap();
}

#[test]
fn abstraction_only_replaces_target_free() {
    // Use reflexive(pair x y) as closed premise: |- pair x y == pair x y.
    // Abstraction on x must replace Free(x) with Bound(0) while Free(y) stays.
    // Result: (λx. pair Bound(0) y) == (λx. pair Bound(0) y)
    let pair_ty = Ty::arrow(ty("nat"), Ty::arrow(ty("nat"), ty("nat")));
    let mut sig = Signature::new();
    sig.declare_const("pair", pair_ty.clone());
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));
    ctx.declare_free("y", ty("nat"));

    // Build certified term: pair x y
    let pair_app = RawTerm::app(
        RawTerm::app(RawTerm::const_("pair", pair_ty.clone()), RawTerm::free("x", ty("nat"))),
        RawTerm::free("y", ty("nat")),
    );
    let pair_xy = ctx.certify_term(pair_app).unwrap();

    // reflexive: |- pair x y == pair x y (closed)
    let refl = KernelRules::reflexive(pair_xy).into_kernel();

    // abstraction on x only
    let result = KernelRules::abstraction("x".into(), ty("nat"), &refl).unwrap();

    let (_, lhs, rhs) = result.prop().term().dest_eq().unwrap();

    // lhs body: pair Bound(0) y — x→Bound(0), y stays Free
    // Structure: App(App(Const("pair"), Bound(0)), Free("y"))
    let (_, _, lhs_body) = lhs.dest_abs().unwrap();
    let (pair_x, y_arg) = lhs_body.dest_app().unwrap();
    // y_arg is the second argument, must stay Free
    assert_eq!(
        y_arg,
        &Term::Free { name: "y".into(), ty: ty("nat") },
        "y must stay Free as second arg, got {y_arg:?}"
    );
    // pair_x = App(pair, x_abstracted); inner dest gives x→Bound(0)
    let (_, x_arg) = pair_x.dest_app().unwrap();
    assert_eq!(
        x_arg,
        &Term::Bound { index: 0, ty: ty("nat") },
        "x must become Bound(0) as first arg, got {x_arg:?}"
    );

    // rhs body: same structure
    let (_, _, rhs_body) = rhs.dest_abs().unwrap();
    let (pair_x, y_arg) = rhs_body.dest_app().unwrap();
    assert_eq!(
        y_arg,
        &Term::Free { name: "y".into(), ty: ty("nat") },
        "y must stay Free, got {y_arg:?}"
    );
    let (_, x_arg) = pair_x.dest_app().unwrap();
    assert_eq!(
        x_arg,
        &Term::Bound { index: 0, ty: ty("nat") },
        "x must become Bound(0), got {x_arg:?}"
    );

    check_kernel_thm(&result).unwrap();
}

#[test]
fn abstraction_over_application() {
    // reflexive(f x) → |- f x == f x (closed).
    // abstraction on x must produce:
    // |- (λx:nat. f Bound(0)) == (λx:nat. f Bound(0))
    let fn_ty = Ty::arrow(ty("nat"), ty("nat"));
    let mut sig = Signature::new();
    sig.declare_const("f", fn_ty.clone());
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    // Build certified term: f x
    let fx_term = ctx
        .certify_term(RawTerm::app(
            RawTerm::const_("f", fn_ty.clone()),
            RawTerm::free("x", ty("nat")),
        ))
        .unwrap();

    // reflexive: |- f x == f x (closed)
    let refl = KernelRules::reflexive(fx_term).into_kernel();

    let result = KernelRules::abstraction("x".into(), ty("nat"), &refl).unwrap();

    let (_, lhs, rhs) = result.prop().term().dest_eq().unwrap();

    // lhs: (λx. f Bound(0))
    let (lhs_name, lhs_param_ty, lhs_body) = lhs.dest_abs().unwrap();
    assert_eq!(lhs_name.as_str(), "x");
    assert_eq!(lhs_param_ty, &ty("nat"));
    let (func, arg) = lhs_body.dest_app().unwrap();
    assert_eq!(func, &Term::Const { name: "f".into(), ty: fn_ty });
    assert_eq!(
        arg,
        &Term::Bound { index: 0, ty: ty("nat") },
        "x in application must become Bound(0), got {arg:?}"
    );

    // rhs: same structure
    let (rhs_name, rhs_param_ty, rhs_body) = rhs.dest_abs().unwrap();
    assert_eq!(rhs_name.as_str(), "x");
    assert_eq!(rhs_param_ty, &ty("nat"));
    let (func, arg) = rhs_body.dest_app().unwrap();
    assert_eq!(func, &Term::Const { name: "f".into(), ty: Ty::arrow(ty("nat"), ty("nat")) });
    assert_eq!(
        arg,
        &Term::Bound { index: 0, ty: ty("nat") },
        "x in application must become Bound(0), got {arg:?}"
    );

    check_kernel_thm(&result).unwrap();
}

#[test]
fn abstraction_replaces_multiple_occurrences() {
    // pair x x == pair x x, abstraction on x must replace BOTH x→Bound(0).
    let pair_ty = Ty::arrow(ty("nat"), Ty::arrow(ty("nat"), ty("nat")));
    let mut sig = Signature::new();
    sig.declare_const("pair", pair_ty.clone());
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let pair_xx = ctx
        .certify_term(RawTerm::app(
            RawTerm::app(RawTerm::const_("pair", pair_ty), RawTerm::free("x", ty("nat"))),
            RawTerm::free("x", ty("nat")),
        ))
        .unwrap();
    let refl = KernelRules::reflexive(pair_xx).into_kernel();

    let result = KernelRules::abstraction("x".into(), ty("nat"), &refl).unwrap();

    let (_, lhs, _rhs) = result.prop().term().dest_eq().unwrap();
    let (_, _, body) = lhs.dest_abs().unwrap();
    let (pair_x, second) = body.dest_app().unwrap();
    assert_eq!(
        second,
        &Term::Bound { index: 0, ty: ty("nat") },
        "second x must become Bound(0), got {second:?}"
    );
    let (_, first) = pair_x.dest_app().unwrap();
    assert_eq!(
        first,
        &Term::Bound { index: 0, ty: ty("nat") },
        "first x must become Bound(0), got {first:?}"
    );

    check_kernel_thm(&result).unwrap();
}

#[test]
fn abstraction_under_existing_abs_does_not_capture() {
    // Body already has (λy:nat. x). Abstract x → Bound(1) under existing λy.
    // Result: λx:nat. λy:nat. Bound(1)
    let sig = Signature::new();
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let abs_y_x =
        ctx.certify_term(RawTerm::abs("y", ty("nat"), RawTerm::free("x", ty("nat")))).unwrap();
    let refl = KernelRules::reflexive(abs_y_x).into_kernel();

    let result = KernelRules::abstraction("x".into(), ty("nat"), &refl).unwrap();

    let (_, lhs, _rhs) = result.prop().term().dest_eq().unwrap();
    let (outer_name, outer_ty, inner) = lhs.dest_abs().unwrap();
    assert_eq!(outer_name.as_str(), "x");
    assert_eq!(outer_ty, &ty("nat"));

    let (inner_name, inner_ty, bound) = inner.dest_abs().unwrap();
    assert_eq!(inner_name.as_str(), "y");
    assert_eq!(inner_ty, &ty("nat"));
    assert_eq!(
        bound,
        &Term::Bound { index: 1, ty: ty("nat") },
        "Free(x) under existing λy must become Bound(1) at depth 1"
    );

    check_kernel_thm(&result).unwrap();
}

#[test]
fn abstraction_type_sensitive() {
    // Abstract x:nat — verify z:bool (different name + different type) is untouched.
    // Proves abstract_over checks both name AND type, not just name.
    let pair_ty = Ty::arrow(ty("nat"), Ty::arrow(ty("bool"), ty("nat")));
    let mut sig = Signature::new();
    sig.declare_const("pair", pair_ty.clone());
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));
    ctx.declare_free("z", ty("bool"));

    let term = ctx
        .certify_term(RawTerm::app(
            RawTerm::app(RawTerm::const_("pair", pair_ty), RawTerm::free("x", ty("nat"))),
            RawTerm::free("z", ty("bool")),
        ))
        .unwrap();
    let refl = KernelRules::reflexive(term).into_kernel();

    let result = KernelRules::abstraction("x".into(), ty("nat"), &refl).unwrap();

    let (_, lhs, _rhs) = result.prop().term().dest_eq().unwrap();
    let (_, _, body) = lhs.dest_abs().unwrap();
    let (pair_x_nat, z_bool) = body.dest_app().unwrap();
    assert_eq!(
        z_bool,
        &Term::Free { name: "z".into(), ty: ty("bool") },
        "Free(z, bool) with different name+type must stay Free, got {z_bool:?}"
    );
    let (_, x_nat) = pair_x_nat.dest_app().unwrap();
    assert_eq!(
        x_nat,
        &Term::Bound { index: 0, ty: ty("nat") },
        "Free(x, nat) must become Bound(0), got {x_nat:?}"
    );

    check_kernel_thm(&result).unwrap();
}

// ---------------------------------------------------------------------------
// equal_intr / equal_elim
// ---------------------------------------------------------------------------

#[test]
fn equal_intr_basic() {
    let ctx = ctx_with_props(&["A", "B"]);
    let a = ctx.certify_prop(prop("A")).unwrap();
    let b = ctx.certify_prop(prop("B")).unwrap();

    let a_imp_b = ctx.certify_prop(RawTerm::imp(prop("A"), prop("B"))).unwrap();
    let b_imp_a = ctx.certify_prop(RawTerm::imp(prop("B"), prop("A"))).unwrap();

    let left = KernelRules::assume(a_imp_b).into_kernel();
    let right = KernelRules::assume(b_imp_a).into_kernel();

    let result = KernelRules::equal_intr(&left, &right).unwrap();

    assert_eq!(result.hyps().len(), 2);
    let (_obj_ty, lhs, rhs) = result.prop().term().dest_eq().unwrap();
    assert_eq!(lhs, a.term());
    assert_eq!(rhs, b.term());

    check_kernel_thm(&result).unwrap();
}

#[test]
fn equal_intr_rejects_non_implication_left() {
    let ctx = ctx_with_props(&["A", "B"]);
    let a_eq_b = ctx.certify_prop(RawTerm::eq(prop("A"), prop("B"))).unwrap();
    let b_imp_a = ctx.certify_prop(RawTerm::imp(prop("B"), prop("A"))).unwrap();

    let left = KernelRules::assume(a_eq_b).into_kernel();
    let right = KernelRules::assume(b_imp_a).into_kernel();

    let err = KernelRules::equal_intr(&left, &right).unwrap_err();
    assert!(matches!(err, KernelError::NotImplication));
}

#[test]
fn equal_intr_rejects_non_implication_right() {
    let ctx = ctx_with_props(&["A", "B"]);
    let a_imp_b = ctx.certify_prop(RawTerm::imp(prop("A"), prop("B"))).unwrap();
    let b_eq_a = ctx.certify_prop(RawTerm::eq(prop("B"), prop("A"))).unwrap();

    let left = KernelRules::assume(a_imp_b).into_kernel();
    let right = KernelRules::assume(b_eq_a).into_kernel();

    let err = KernelRules::equal_intr(&left, &right).unwrap_err();
    assert!(matches!(err, KernelError::NotImplication));
}

#[test]
fn equal_intr_rejects_mismatched_implications() {
    let ctx = ctx_with_props(&["A", "B", "C"]);
    let a_imp_b = ctx.certify_prop(RawTerm::imp(prop("A"), prop("B"))).unwrap();
    let c_imp_a = ctx.certify_prop(RawTerm::imp(prop("C"), prop("A"))).unwrap();

    let left = KernelRules::assume(a_imp_b).into_kernel();
    let right = KernelRules::assume(c_imp_a).into_kernel();

    let err = KernelRules::equal_intr(&left, &right).unwrap_err();
    assert!(matches!(err, KernelError::AntecedentMismatch));
}

#[test]
fn equal_intr_preserves_hypotheses() {
    let ctx = ctx_with_props(&["A", "B"]);
    let a_imp_b = ctx.certify_prop(RawTerm::imp(prop("A"), prop("B"))).unwrap();
    let b_imp_a = ctx.certify_prop(RawTerm::imp(prop("B"), prop("A"))).unwrap();

    let left = KernelRules::assume(a_imp_b).into_kernel();
    let right = KernelRules::assume(b_imp_a).into_kernel();

    let result = KernelRules::equal_intr(&left, &right).unwrap();
    assert_eq!(result.hyps().len(), 2);

    check_kernel_thm(&result).unwrap();
}

#[test]
fn equal_elim_basic() {
    let ctx = ctx_with_props(&["A", "B"]);
    let a = ctx.certify_prop(prop("A")).unwrap();
    let b = ctx.certify_prop(prop("B")).unwrap();

    let a_eq_b = ctx.certify_prop(RawTerm::eq(prop("A"), prop("B"))).unwrap();
    let eq_thm = KernelRules::assume(a_eq_b.clone()).into_kernel();
    let a_assumed = KernelRules::assume(a.clone()).into_kernel();

    let result = KernelRules::equal_elim(&eq_thm, &a_assumed).unwrap();

    assert_eq!(result.hyps().len(), 2);
    assert_eq!(result.prop().term(), b.term());

    check_kernel_thm(&result).unwrap();
}

#[test]
fn equal_elim_rejects_non_equality() {
    let ctx = ctx_with_props(&["A", "B"]);
    let a_imp_b = ctx.certify_prop(RawTerm::imp(prop("A"), prop("B"))).unwrap();
    let a = ctx.certify_prop(prop("A")).unwrap();

    let major = KernelRules::assume(a_imp_b).into_kernel();
    let minor = KernelRules::assume(a).into_kernel();

    let err = KernelRules::equal_elim(&major, &minor).unwrap_err();
    assert!(matches!(err, KernelError::NotEquality));
}

#[test]
fn equal_elim_rejects_minor_mismatch() {
    let ctx = ctx_with_props(&["A", "B", "C"]);
    let a_eq_b = ctx.certify_prop(RawTerm::eq(prop("A"), prop("B"))).unwrap();
    let c = ctx.certify_prop(prop("C")).unwrap();

    let eq_thm = KernelRules::assume(a_eq_b).into_kernel();
    let minor = KernelRules::assume(c).into_kernel();

    let err = KernelRules::equal_elim(&eq_thm, &minor).unwrap_err();
    assert!(matches!(err, KernelError::AntecedentMismatch));
}

#[test]
fn equal_elim_rejects_object_equality() {
    // equal_elim requires propositional equality (A == B where A,B: prop).
    // Object equality (x == y where x,y: nat) must be rejected even if
    // the minor premise happens to match the LHS term.
    let mut ctx = ctx_with_nat_consts(&["a", "b"]);
    ctx.declare_free("x", ty("nat"));

    // Object equality: x == x : prop (object_ty = nat)
    let obj_eq = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::free("x", ty("nat"))))
        .unwrap();
    let eq_thm = KernelRules::assume(obj_eq).into_kernel();

    // A propositional theorem as minor (will fail alpha_eq anyway,
    // but the explicit prop-equality check must fire first)
    let prop_ctx = ctx_with_props(&["A"]);
    let a = prop_ctx.certify_prop(prop("A")).unwrap();
    let minor = KernelRules::assume(a).into_kernel();

    let err = KernelRules::equal_elim(&eq_thm, &minor).unwrap_err();
    assert!(matches!(err, KernelError::NotProposition(_)));
}

#[test]
fn equal_intr_elim_roundtrip() {
    let ctx = ctx_with_props(&["A", "B"]);
    let a = ctx.certify_prop(prop("A")).unwrap();
    let b = ctx.certify_prop(prop("B")).unwrap();

    let a_imp_b = ctx.certify_prop(RawTerm::imp(prop("A"), prop("B"))).unwrap();
    let b_imp_a = ctx.certify_prop(RawTerm::imp(prop("B"), prop("A"))).unwrap();
    let left = KernelRules::assume(a_imp_b).into_kernel();
    let right = KernelRules::assume(b_imp_a).into_kernel();
    let eq = KernelRules::equal_intr(&left, &right).unwrap();

    let a_assumed = KernelRules::assume(a).into_kernel();
    let result = KernelRules::equal_elim(&eq, &a_assumed).unwrap();

    assert_eq!(result.hyps().len(), 3);
    assert_eq!(result.prop().term(), b.term());

    check_kernel_thm(&result).unwrap();
}

#[test]
fn equal_elim_preserves_open_minor_hypothesis() {
    let ctx = ctx_with_props(&["A", "B"]);
    let a = ctx.certify_prop(prop("A")).unwrap();

    let a_eq_b = ctx.certify_prop(RawTerm::eq(prop("A"), prop("B"))).unwrap();
    let eq_thm = KernelRules::assume(a_eq_b).into_kernel();
    let a_thm = KernelRules::assume(a).into_kernel();

    let result = KernelRules::equal_elim(&eq_thm, &a_thm).unwrap();
    assert_eq!(result.hyps().len(), 2);

    check_kernel_thm(&result).unwrap();
}

// ============================================================
// generalize — Free → Var (schematic generalisation)
// ============================================================

#[test]
fn generalize_basic() {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let x_term = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let thm = KernelRules::reflexive(x_term).into_kernel();

    let result = KernelRules::generalize(&thm, &[("x".into(), ty("nat"))]).unwrap();

    // Free("x", nat) → Var("x", 0, nat)
    assert_eq!(result.hyps().len(), 0);
    assert_eq!(
        result.prop().term(),
        &Term::mk_eq(
            Term::Var { name: "x".into(), index: 0, ty: ty("nat") },
            Term::Var { name: "x".into(), index: 0, ty: ty("nat") },
        )
        .unwrap()
    );
    check_kernel_thm(&result).unwrap();
}

#[test]
fn generalize_preserves_hypotheses() {
    let mut ctx = ctx_with_nat_consts(&["a"]);
    ctx.declare_free("x", ty("nat"));

    let eq_term = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();
    let thm = KernelRules::assume(eq_term).into_kernel();
    assert_eq!(thm.hyps().len(), 1);

    let result = KernelRules::generalize(&thm, &[("x".into(), ty("nat"))]).unwrap();

    // Hypothesis must also be transformed
    assert_eq!(result.hyps().len(), 1);
    let hyp = &result.hyps()[0];
    assert_eq!(
        hyp.term(),
        &Term::mk_eq(
            Term::Var { name: "x".into(), index: 0, ty: ty("nat") },
            Term::Const { name: "a".into(), ty: ty("nat") },
        )
        .unwrap()
    );
    check_kernel_thm(&result).unwrap();
}

#[test]
fn generalize_multiple_frees() {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));
    ctx.declare_free("y", ty("nat"));

    let xy_eq = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::free("y", ty("nat"))))
        .unwrap();
    let thm = KernelRules::assume(xy_eq).into_kernel();

    let frees: Vec<(Name, Ty)> = vec![("x".into(), ty("nat")), ("y".into(), ty("nat"))];
    let result = KernelRules::generalize(&thm, &frees).unwrap();

    // x → Var("x", 0, nat), y → Var("y", 1, nat)
    assert_eq!(
        result.prop().term(),
        &Term::mk_eq(
            Term::Var { name: "x".into(), index: 0, ty: ty("nat") },
            Term::Var { name: "y".into(), index: 1, ty: ty("nat") },
        )
        .unwrap()
    );
    check_kernel_thm(&result).unwrap();
}

#[test]
fn generalize_non_free_unchanged() {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    // Use a Const in the theorem — it must not be touched
    let x_term = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let thm = KernelRules::reflexive(x_term).into_kernel();

    let result = KernelRules::generalize(&thm, &[("y".into(), ty("nat"))]).unwrap();

    // "y" doesn't appear, so the theorem should be unchanged (still Free, not Var)
    assert_eq!(
        result.prop().term(),
        &Term::mk_eq(
            Term::Free { name: "x".into(), ty: ty("nat") },
            Term::Free { name: "x".into(), ty: ty("nat") },
        )
        .unwrap()
    );
}

#[test]
fn generalize_only_target_free() {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));
    ctx.declare_free("z", ty("nat"));

    let xz_eq = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::free("z", ty("nat"))))
        .unwrap();
    let thm = KernelRules::assume(xz_eq).into_kernel();

    let result = KernelRules::generalize(&thm, &[("x".into(), ty("nat"))]).unwrap();

    // Only x generalized; z stays as Free
    assert_eq!(
        result.prop().term(),
        &Term::mk_eq(
            Term::Var { name: "x".into(), index: 0, ty: ty("nat") },
            Term::Free { name: "z".into(), ty: ty("nat") },
        )
        .unwrap()
    );
}

#[test]
fn generalize_closed_remains_closed() {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let x_term = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let thm = KernelRules::reflexive(x_term).into_kernel();
    assert!(!thm.is_open());

    let result = KernelRules::generalize(&thm, &[("x".into(), ty("nat"))]).unwrap();
    assert!(!result.is_open());
}

#[test]
fn generalize_open_remains_open() {
    let mut ctx = ctx_with_nat_consts(&["a"]);
    ctx.declare_free("x", ty("nat"));

    let eq_term = ctx
        .certify_prop(RawTerm::eq(RawTerm::free("x", ty("nat")), RawTerm::const_("a", ty("nat"))))
        .unwrap();
    let thm = KernelRules::assume(eq_term).into_kernel();
    assert!(thm.is_open());

    let result = KernelRules::generalize(&thm, &[("x".into(), ty("nat"))]).unwrap();
    assert!(result.is_open());
}

#[test]
fn generalize_invariant_check_passes() {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let x_term = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let thm = KernelRules::reflexive(x_term).into_kernel();
    let result = KernelRules::generalize(&thm, &[("x".into(), ty("nat"))]).unwrap();

    check_kernel_thm(&result).unwrap();
}

#[test]
fn generalize_empty_frees_noop() {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let x_term = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let thm = KernelRules::reflexive(x_term).into_kernel();

    let empty: Vec<(Name, Ty)> = vec![];
    let result = KernelRules::generalize(&thm, &empty).unwrap();

    // Empty list = identity
    assert_eq!(result.prop(), thm.prop());
    assert_eq!(result.hyps(), thm.hyps());
}

#[test]
fn generalize_ignores_unmatched_free() {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let x_term = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let thm = KernelRules::reflexive(x_term).into_kernel();

    // "z" doesn't appear anywhere — should be silently ignored
    let result = KernelRules::generalize(&thm, &[("z".into(), ty("nat"))]).unwrap();

    // Theorem should be unchanged (Free "x" stays as Free, not generalized)
    assert_eq!(result.prop(), thm.prop());
}

#[test]
fn generalize_avoids_existing_var_index() {
    // Theorem already has Var("v", 0, nat) from an assume.
    // generalize Free("x") must use start = max_var_index + 1 = 1,
    // producing Var("x", 1, nat) to avoid collision.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    // Build: Var("v", 0, nat) == Free("x", nat)
    let raw_prop = RawTerm::eq(RawTerm::var("v", 0, ty("nat")), RawTerm::free("x", ty("nat")));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    // Before generalize: has Var("v", 0) and Free("x")
    assert_eq!(thm.max_var_index(), Some(0));

    // Generalize Free("x", nat) — should become Var("x", 1, nat)
    let result = KernelRules::generalize(&thm, &[("x".into(), ty("nat"))]).unwrap();

    assert_eq!(
        result.prop().term(),
        &Term::mk_eq(
            Term::Var { name: "v".into(), index: 0, ty: ty("nat") },
            Term::Var { name: "x".into(), index: 1, ty: ty("nat") },
        )
        .unwrap()
    );
    check_kernel_thm(&result).unwrap();
}

#[test]
fn generalize_uses_global_max_var_index() {
    // Theorem has Var("x", 0, nat) and Var("y", 3, nat).
    // generalize Free("z", nat) must use start = global_max + 1 = 4,
    // producing Var("z", 4, nat) — not Var("z", 1) or any per-name local count.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("z", ty("nat"));

    // Build: (Var("x",0) == Var("y",3)) ==> (Free("z") == Free("z"))
    let left = RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::var("y", 3, ty("nat")));
    let right = RawTerm::eq(RawTerm::free("z", ty("nat")), RawTerm::free("z", ty("nat")));
    let raw_prop = RawTerm::imp(left, right);
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    // Before generalize: global max Var index is 3 (from Var("y", 3))
    assert_eq!(thm.max_var_index(), Some(3));

    // Generalize Free("z", nat) — should become Var("z", 4, nat)
    let result = KernelRules::generalize(&thm, &[("z".into(), ty("nat"))]).unwrap();

    // Result prop: (Var("x",0) == Var("y",3)) ==> (Var("z",4) == Var("z",4))
    assert_eq!(
        result.prop().term(),
        &Term::mk_imp(
            Term::mk_eq(
                Term::Var { name: "x".into(), index: 0, ty: ty("nat") },
                Term::Var { name: "y".into(), index: 3, ty: ty("nat") },
            )
            .unwrap(),
            Term::mk_eq(
                Term::Var { name: "z".into(), index: 4, ty: ty("nat") },
                Term::Var { name: "z".into(), index: 4, ty: ty("nat") },
            )
            .unwrap(),
        )
        .unwrap()
    );

    // Global max should now be 4 (from Var("z", 4))
    assert_eq!(result.max_var_index(), Some(4));

    // Var("x", 0) and Var("y", 3) must remain unchanged
    check_kernel_thm(&result).unwrap();
}

#[test]
fn generalize_type_sensitive_same_name() {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    sig.declare_const("P", Ty::prop());
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));
    // Can't declare Free("x", bool) — ProofContext rejects same-name different-type
    // So we test that only Free("x", nat) is generalized, not Free("x", bool)
    // by using a prop-level "x" as a Const instead
    let x_nat = RawTerm::free("x", ty("nat"));
    let x_nat_term = ctx.certify_term(x_nat.clone()).unwrap();

    let thm = KernelRules::reflexive(x_nat_term).into_kernel();

    // Generalize only "x" at type nat — should work
    let result = KernelRules::generalize(&thm, &[("x".into(), ty("nat"))]).unwrap();
    assert_eq!(
        result.prop().term(),
        &Term::mk_eq(
            Term::Var { name: "x".into(), index: 0, ty: ty("nat") },
            Term::Var { name: "x".into(), index: 0, ty: ty("nat") },
        )
        .unwrap()
    );

    // Generalizing "x" at type bool (wrong type) should be a no-op
    // since Free("x", bool) doesn't appear
    let result2 = KernelRules::generalize(&thm, &[("x".into(), Ty::prop())]).unwrap();
    assert_eq!(result2.prop(), thm.prop()); // unchanged
}

#[test]
fn generalize_roundtrip_with_instantiate() {
    // This test will be enabled once instantiate is implemented.
    // For now it just verifies generalize is reversible in principle:
    // the derivation records the start_index, which instantiate can use.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let x_term = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let thm = KernelRules::reflexive(x_term).into_kernel();
    let result = KernelRules::generalize(&thm, &[("x".into(), ty("nat"))]).unwrap();

    // Record the derivation for later round-trip verification
    match result.derivation() {
        Derivation::Generalize { frees, start_index, .. } => {
            assert_eq!(frees.len(), 1);
            assert_eq!(frees[0], ("x".into(), ty("nat")));
            assert_eq!(*start_index, 0);
        },
        _ => panic!("expected Generalize derivation"),
    }
}

// ── instantiate tests ────────────────────────────────────────────────

#[test]
fn instantiate_basic() {
    // Var("x", 0, nat) := Const("a", nat) — basic single replacement.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);

    // Build: Var("x", 0, nat) == a |- Var("x", 0, nat) == a
    let raw_prop = RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::const_("a", ty("nat")));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    let a_cterm = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let a_term = a_cterm.term().clone();
    let entry = InstEntry::new("x", 0, ty("nat"), a_cterm);
    let result = KernelRules::instantiate(&thm, &[entry]).unwrap();

    assert_eq!(result.prop().term(), &Term::mk_eq(a_term.clone(), a_term.clone()).unwrap());
    // Hypothesis Var also instantiated
    assert_eq!(result.hyps().len(), 1);
    assert_eq!(result.hyps()[0].term(), &Term::mk_eq(a_term.clone(), a_term).unwrap());
}

#[test]
fn instantiate_rejects_type_mismatch() {
    // Var(x,0,nat) := Const(P,prop) — type mismatch.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    sig.declare_const("P", Ty::prop());
    let ctx = ProofContext::new(sig);

    // Theorem: Var("x", 0, nat) == a |- Var("x", 0, nat) == a  (both sides nat-typed)
    let raw_prop = RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::const_("a", ty("nat")));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    // Instantiation attempt: match Var("x", 0, nat) → Const("P", prop)
    // types differ: nat ≠ prop — should fail with TypeMismatch
    let p_cterm = ctx.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let entry = InstEntry::new("x", 0, ty("nat"), p_cterm);
    let err = KernelRules::instantiate(&thm, &[entry]).unwrap_err();
    assert!(matches!(err, KernelError::TypeMismatch { .. }));
}

#[test]
fn instantiate_respects_index() {
    // Var("x", 0, nat) and Var("x", 1, nat) are distinct.
    // Replace Var("x", 0) only — Var("x", 1) must remain.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);

    let raw_prop = RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::var("x", 1, ty("nat")));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    let a_cterm = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let a_term = a_cterm.term().clone();
    let entry = InstEntry::new("x", 0, ty("nat"), a_cterm);
    let result = KernelRules::instantiate(&thm, &[entry]).unwrap();

    // Only Var("x",0) replaced; Var("x",1) unchanged
    assert_eq!(
        result.prop().term(),
        &Term::mk_eq(a_term, Term::Var { name: "x".into(), index: 1, ty: ty("nat") }).unwrap()
    );
}

#[test]
fn instantiate_type_sensitive_same_name_index() {
    // Var("x", 0, nat) is NOT matched by a substitution entry for Var("x", 0, bool).
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    sig.declare_const("P", Ty::prop());
    let ctx = ProofContext::new(sig);

    let raw_prop = RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::const_("a", ty("nat")));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    // Subst lists Var("x", 0, bool) → P — but the theorem has Var("x", 0, nat)
    let p_cterm = ctx.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let entry = InstEntry::new("x", 0, Ty::prop(), p_cterm);
    let result = KernelRules::instantiate(&thm, &[entry]).unwrap();

    // Unmatched → no change
    assert_eq!(result.prop(), thm.prop());
}

#[test]
fn instantiate_rejects_duplicate_substitution() {
    // Same (name, idx) pair appears twice.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    sig.declare_const("b", ty("nat"));
    let ctx = ProofContext::new(sig);

    let raw_prop = RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::const_("a", ty("nat")));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    let a_cterm = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let b_cterm = ctx.certify_term(RawTerm::const_("b", ty("nat"))).unwrap();
    let err = KernelRules::instantiate(
        &thm,
        &[InstEntry::new("x", 0, ty("nat"), a_cterm), InstEntry::new("x", 0, ty("nat"), b_cterm)],
    )
    .unwrap_err();
    assert!(matches!(err, KernelError::DuplicateSubstitution { .. }));
}

#[test]
fn instantiate_rejects_bound_in_replacement() {
    // Bound-in-CTerm replacement is prevented at the certification boundary:
    // CTerm::new is kernel-internal and ProofContext::certify_term rejects Bound.
    // The defense-in-depth BoundInSubstitution check is tested inline in
    // kernel::thm::tests::instantiate_rejects_bound_in_replacement_inline.
    //
    // Here we verify a normal certified replacement (without Bound) succeeds.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);

    let raw_prop = RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::const_("a", ty("nat")));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    let a_cterm = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let entry = InstEntry::new("x", 0, ty("nat"), a_cterm);
    let result = KernelRules::instantiate(&thm, &[entry]).unwrap();
    assert!(matches!(result.prop().term(), Term::Eq { .. }));
}

#[test]
fn instantiate_partial_substitution_keeps_unmatched_var() {
    // Theorem has Var("x",0) and Var("y",1). Replace only Var("x",0).
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);

    let raw_prop = RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::var("y", 1, ty("nat")));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    let a_cterm = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let a_term = a_cterm.term().clone();
    let entry = InstEntry::new("x", 0, ty("nat"), a_cterm);
    let result = KernelRules::instantiate(&thm, &[entry]).unwrap();

    // Var("x",0) → a, Var("y",1) unchanged
    assert_eq!(
        result.prop().term(),
        &Term::mk_eq(a_term, Term::Var { name: "y".into(), index: 1, ty: ty("nat") }).unwrap()
    );
}

#[test]
fn instantiate_preserves_hypotheses() {
    // Hypotheses transformed alongside prop.
    let mut sig = Signature::new();
    sig.declare_const("A", Ty::prop());
    sig.declare_const("B", Ty::prop());
    let ctx = ProofContext::new(sig);

    // Build a theorem with Var in both hyps and prop.
    // assume(Var("x",0,prop) ==> B) yields: (x ==> B) |- (x ==> B)
    let raw_prop = RawTerm::imp(RawTerm::var("x", 0, Ty::prop()), RawTerm::const_("B", Ty::prop()));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    // Instantiate: Var("x",0,prop) := A
    let a_cterm = ctx.certify_term(RawTerm::const_("A", Ty::prop())).unwrap();
    let a_term = a_cterm.term().clone();
    let entry = InstEntry::new("x", 0, Ty::prop(), a_cterm);
    let result = KernelRules::instantiate(&thm, &[entry]).unwrap();

    // Both hyps and prop should have Var replaced with A
    let expected =
        Term::mk_imp(a_term.clone(), Term::Const { name: "B".into(), ty: Ty::prop() }).unwrap();
    assert_eq!(result.hyps()[0].term(), &expected);
    assert_eq!(result.prop().term(), &expected);
}

#[test]
fn instantiate_invariant_check_passes() {
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);

    let raw_prop = RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::const_("a", ty("nat")));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    let a_cterm = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let entry = InstEntry::new("x", 0, ty("nat"), a_cterm);
    let result = KernelRules::instantiate(&thm, &[entry]).unwrap();
    check_kernel_thm(&result).unwrap();
}

#[test]
fn instantiate_closed_remains_closed() {
    // Closed theorem stays closed after instantiation.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);

    let a_cterm = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let refl = KernelRules::reflexive(a_cterm.clone()).into_kernel();

    // refl is closed (|- a == a). Instantiate a Var not present — no change.
    let entry = InstEntry::new("x", 0, ty("nat"), a_cterm);
    let result = KernelRules::instantiate(&refl, &[entry]).unwrap();

    assert!(result.hyps().is_empty()); // still closed
    assert_eq!(result.prop(), refl.prop()); // unchanged
}

#[test]
fn instantiate_does_not_affect_const_or_free() {
    // Only Vars replaced; Const and Free nodes unchanged.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("y", ty("nat"));

    let raw_prop = RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::free("y", ty("nat")));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    let a_cterm = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let a_term = a_cterm.term().clone();
    let entry = InstEntry::new("x", 0, ty("nat"), a_cterm);
    let result = KernelRules::instantiate(&thm, &[entry]).unwrap();

    // Var("x",0) → a, Free("y",nat) unchanged
    assert_eq!(
        result.prop().term(),
        &Term::mk_eq(a_term, Term::Free { name: "y".into(), ty: ty("nat") }).unwrap()
    );
}

#[test]
fn instantiate_empty_subst_noop() {
    // Empty substitution list = identity.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);

    let raw_prop = RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::const_("a", ty("nat")));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    let result = KernelRules::instantiate(&thm, &[]).unwrap();
    assert_eq!(result.hyps(), thm.hyps());
    assert_eq!(result.prop(), thm.prop());
}

#[test]
fn instantiate_multiple_vars() {
    // Replace two different Vars with different terms.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    sig.declare_const("b", ty("nat"));
    let ctx = ProofContext::new(sig);

    let raw_prop = RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::var("y", 1, ty("nat")));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    let a_cterm = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let a_term = a_cterm.term().clone();
    let b_cterm = ctx.certify_term(RawTerm::const_("b", ty("nat"))).unwrap();
    let b_term = b_cterm.term().clone();
    let result = KernelRules::instantiate(
        &thm,
        &[InstEntry::new("x", 0, ty("nat"), a_cterm), InstEntry::new("y", 1, ty("nat"), b_cterm)],
    )
    .unwrap();

    assert_eq!(result.prop().term(), &Term::mk_eq(a_term, b_term).unwrap());
}

#[test]
fn instantiate_same_var_all_occurrences() {
    // All occurrences of the same Var are replaced.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);

    // (Var("x",0) == Var("x",0))
    let raw_prop = RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::var("x", 0, ty("nat")));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    let a_cterm = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let a_term = a_cterm.term().clone();
    let entry = InstEntry::new("x", 0, ty("nat"), a_cterm);
    let result = KernelRules::instantiate(&thm, &[entry]).unwrap();

    assert_eq!(result.prop().term(), &Term::mk_eq(a_term.clone(), a_term).unwrap());
}

#[test]
fn instantiate_roundtrip_with_generalize() {
    // generalize then instantiate = original (modulo hyps α-equivalence).
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let mut ctx = ProofContext::new(sig);
    ctx.declare_free("x", ty("nat"));

    let x_cterm = ctx.certify_term(RawTerm::free("x", ty("nat"))).unwrap();
    let thm = KernelRules::reflexive(x_cterm.clone()).into_kernel();

    // generalize Free("x", nat) → Var("x", 0, nat)
    let gen_thm = KernelRules::generalize(&thm, &[("x".into(), ty("nat"))]).unwrap();

    // Recover the start_index from the derivation
    let start = match gen_thm.derivation() {
        Derivation::Generalize { start_index, .. } => *start_index,
        _ => panic!("expected Generalize derivation"),
    };

    // instantiate Var("x", start, nat) := Free("x", nat)
    // Free("x", nat) is a certified CTerm from our context
    let entry = InstEntry::new("x", start, ty("nat"), x_cterm);
    let back = KernelRules::instantiate(&gen_thm, &[entry]).unwrap();

    assert_eq!(back.prop(), thm.prop());
    assert_eq!(back.hyps(), thm.hyps());
    check_kernel_thm(&back).unwrap();
}

#[test]
fn instantiate_invariant_catches_tampered_result() {
    // Tampering with instantiate output is tested inline in
    // kernel::thm::tests::instantiate_tampered_prop_fails_invariant,
    // since KernelThm::new is pub(crate) and inaccessible here.
    // This integration test verifies the happy-path invariant instead.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    let ctx = ProofContext::new(sig);

    let raw_prop = RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::const_("a", ty("nat")));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    let a_cterm = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let entry = InstEntry::new("x", 0, ty("nat"), a_cterm);
    let result = KernelRules::instantiate(&thm, &[entry]).unwrap();

    // Invariant check passes on valid instantiate output
    check_kernel_thm(&result).unwrap();
}

#[test]
fn instantiate_rejects_duplicate_same_name_index_different_type() {
    // Duplicate detection is keyed by (name, index) regardless of type.
    // Two entries with same (name, idx) but different var_ty are rejected.
    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    sig.declare_const("P", Ty::prop());
    let ctx = ProofContext::new(sig);

    let raw_prop = RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::const_("a", ty("nat")));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    // Entry 1: Var("x", 0, nat) := a::nat
    let a_cterm = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    // Entry 2: Var("x", 0, nat) := a::nat (same name/index but we vary type in the next case)

    // Case: same (name, idx) but one entry claims var_ty=nat, other claims var_ty=bool
    // The duplicate check fires before type check — both are (x, 0)
    let p_cterm = ctx.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let err = KernelRules::instantiate(
        &thm,
        &[InstEntry::new("x", 0, ty("nat"), a_cterm), InstEntry::new("x", 0, Ty::prop(), p_cterm)],
    )
    .unwrap_err();
    // Should be DuplicateSubstitution — keyed by (name, index) only
    assert!(
        matches!(err, KernelError::DuplicateSubstitution { .. }),
        "expected DuplicateSubstitution, got {err:?}"
    );
}

#[test]
fn instantiate_is_simultaneous_not_sequential() {
    // Substitution is simultaneous: the traversal replaces Var nodes found
    // in the ORIGINAL theorem, not in the replaced results.
    //
    // Since the strict kernel's CTerm certification rejects Var nodes
    // (Vars are schematic, not declared in Signature), replacements can't
    // contain Vars that would trigger a sequential re-substitution.
    //
    // The guarantee is therefore structural: instantiate_vars() performs a
    // single-pass iteration — it never recurses into replacement terms
    // looking for more Vars to substitute.
    //
    // We demonstrate this with two independent Vars: replacing both in a
    // single call produces the same result regardless of order.

    let mut sig = Signature::new();
    sig.declare_const("a", ty("nat"));
    sig.declare_const("b", ty("nat"));
    let ctx = ProofContext::new(sig);

    // Theorem: Var("x",0,nat) == Var("y",1,nat) |- ...
    let raw_prop = RawTerm::eq(RawTerm::var("x", 0, ty("nat")), RawTerm::var("y", 1, ty("nat")));
    let cprop = ctx.certify_prop(raw_prop).unwrap();
    let thm = KernelRules::assume(cprop).into_kernel();

    let a_cterm = ctx.certify_term(RawTerm::const_("a", ty("nat"))).unwrap();
    let b_cterm = ctx.certify_term(RawTerm::const_("b", ty("nat"))).unwrap();

    // Simultaneous: both Vars replaced in one call.
    // (Const replacements contain no Vars, so sequential vs simultaneous
    // would produce the same result — but the implementation does a single
    // pass, verified by Term::instantiate_vars' continuation-frame loop.)
    let result = KernelRules::instantiate(
        &thm,
        &[
            InstEntry::new("x", 0, ty("nat"), a_cterm.clone()),
            InstEntry::new("y", 1, ty("nat"), b_cterm.clone()),
        ],
    )
    .unwrap();

    assert_eq!(
        result.prop().term(),
        &Term::mk_eq(a_cterm.term().clone(), b_cterm.term().clone()).unwrap()
    );
}

// ============================================================
// implication-chain utilities — dest_imp_chain, mk_imp_chain,
// nprems, select_subgoal, replace_subgoal_with_premises
// ============================================================

fn prop_term(ctx: &ProofContext, name: &str) -> Term {
    ctx.certify_prop(RawTerm::const_(name, Ty::prop())).unwrap().term().clone()
}

#[test]
fn imp_chain_roundtrip() {
    // dest_imp_chain then mk_imp_chain = identity (modulo alpha-equivalence).
    let ctx = ctx_with_props(&["A", "B", "C"]);

    let a = prop_term(&ctx, "A");
    let b = prop_term(&ctx, "B");
    let c = prop_term(&ctx, "C");

    // Build: A ==> B ==> C
    let chain = Term::mk_imp_chain(&[a.clone(), b.clone()], &c).unwrap();

    // Decompose
    let (prems, concl) = chain.dest_imp_chain();
    assert_eq!(prems.len(), 2);
    assert!(prems[0].alpha_eq(&a));
    assert!(prems[1].alpha_eq(&b));
    assert!(concl.alpha_eq(&c));

    // Rebuild
    let rebuilt = Term::mk_imp_chain(&prems, concl).unwrap();
    assert!(chain.alpha_eq(&rebuilt));
}

#[test]
fn imp_chain_roundtrip_empty() {
    // dest_imp_chain on a non-implication returns empty premises.
    let ctx = ctx_with_props(&["A"]);
    let a = prop_term(&ctx, "A");

    let (prems, concl) = a.dest_imp_chain();
    assert!(prems.is_empty());
    assert!(concl.alpha_eq(&a));

    let rebuilt = Term::mk_imp_chain(&prems, concl).unwrap();
    assert!(a.alpha_eq(&rebuilt));
}

#[test]
fn select_subgoal_zero_based() {
    // select_subgoal uses 0-based indexing into the premise chain.
    let ctx = ctx_with_props(&["A", "B", "C"]);
    let a = prop_term(&ctx, "A");
    let b = prop_term(&ctx, "B");
    let c = prop_term(&ctx, "C");

    let chain = Term::mk_imp_chain(&[a.clone(), b.clone()], &c).unwrap();

    assert!(chain.select_subgoal(0).unwrap().alpha_eq(&a));
    assert!(chain.select_subgoal(1).unwrap().alpha_eq(&b));
}

#[test]
fn select_subgoal_out_of_range() {
    // select_subgoal returns None when index points at or past the conclusion.
    let ctx = ctx_with_props(&["A", "B", "C"]);
    let a = prop_term(&ctx, "A");
    let b = prop_term(&ctx, "B");
    let c = prop_term(&ctx, "C");

    let chain = Term::mk_imp_chain(&[a.clone(), b.clone()], &c).unwrap();

    // Index 2 is the conclusion, not a subgoal.
    assert!(chain.select_subgoal(2).is_none());
    // Index 3 is completely out of range.
    assert!(chain.select_subgoal(3).is_none());
}

#[test]
fn select_subgoal_empty_chain() {
    // select_subgoal on a chain with no premises always returns None.
    let ctx = ctx_with_props(&["A"]);
    let a = prop_term(&ctx, "A");

    assert!(a.select_subgoal(0).is_none());
    assert_eq!(a.nprems(), 0);
}

#[test]
fn nprems_counts_subgoals() {
    let ctx = ctx_with_props(&["A", "B", "C"]);
    let a = prop_term(&ctx, "A");
    let b = prop_term(&ctx, "B");
    let c = prop_term(&ctx, "C");

    assert_eq!(c.nprems(), 0);
    assert_eq!(Term::mk_imp_chain(&[a.clone()], &c).unwrap().nprems(), 1);
    assert_eq!(Term::mk_imp_chain(&[a.clone(), b.clone()], &c).unwrap().nprems(), 2);
    assert_eq!(Term::mk_imp_chain(&[a, b], &c).unwrap().nprems(), 2);
}

#[test]
fn replace_subgoal_with_zero_premises() {
    // Replacing a subgoal with [] removes it from the chain.
    let ctx = ctx_with_props(&["A", "B", "C"]);
    let a = prop_term(&ctx, "A");
    let b = prop_term(&ctx, "B");
    let c = prop_term(&ctx, "C");

    // A ==> B ==> C, replace subgoal 0 (A) with [] → B ==> C
    let chain = Term::mk_imp_chain(&[a.clone(), b.clone()], &c).unwrap();
    let result = chain.replace_subgoal_with_premises(0, &[]).unwrap();

    let (prems, concl) = result.dest_imp_chain();
    assert_eq!(prems.len(), 1);
    assert!(prems[0].alpha_eq(&b));
    assert!(concl.alpha_eq(&c));
}

#[test]
fn replace_subgoal_with_multiple_premises() {
    // Replacing a subgoal with multiple new premises expands the chain.
    let ctx = ctx_with_props(&["A", "B", "C", "D"]);
    let a = prop_term(&ctx, "A");
    let b = prop_term(&ctx, "B");
    let c = prop_term(&ctx, "C");
    let d = prop_term(&ctx, "D");

    // A ==> C, replace subgoal 0 (A) with [D, B] → D ==> B ==> C
    let chain = Term::mk_imp_chain(&[a], &c).unwrap();
    let result = chain.replace_subgoal_with_premises(0, &[d.clone(), b.clone()]).unwrap();

    let (prems, concl) = result.dest_imp_chain();
    assert_eq!(prems.len(), 2);
    assert!(prems[0].alpha_eq(&d));
    assert!(prems[1].alpha_eq(&b));
    assert!(concl.alpha_eq(&c));
}

#[test]
fn replace_subgoal_with_multiple_premises_last() {
    // Replace the last subgoal (just before conclusion) with multiple premises.
    let ctx = ctx_with_props(&["A", "B", "C", "D"]);
    let a = prop_term(&ctx, "A");
    let b = prop_term(&ctx, "B");
    let c = prop_term(&ctx, "C");
    let d = prop_term(&ctx, "D");

    // A ==> B ==> C, replace subgoal 1 (B) with [D] → A ==> D ==> C
    let chain = Term::mk_imp_chain(&[a.clone(), b.clone()], &c).unwrap();
    let result = chain.replace_subgoal_with_premises(1, &[d.clone()]).unwrap();

    let (prems, concl) = result.dest_imp_chain();
    assert_eq!(prems.len(), 2);
    assert!(prems[0].alpha_eq(&a));
    assert!(prems[1].alpha_eq(&d));
    assert!(concl.alpha_eq(&c));
}

#[test]
fn replace_subgoal_out_of_range() {
    // replace_subgoal_with_premises rejects index >= nprems.
    let ctx = ctx_with_props(&["A", "B"]);
    let a = prop_term(&ctx, "A");
    let b = prop_term(&ctx, "B");

    // A ==> B has 1 subgoal (A). Index 1 does not exist.
    let chain = Term::mk_imp_chain(&[a], &b).unwrap();
    let err = chain.replace_subgoal_with_premises(1, &[]).unwrap_err();
    assert!(matches!(err, KernelError::SubgoalIndexOutOfRange { index: 1, nprems: 1 }));
}

#[test]
fn replace_subgoal_on_non_imp_term() {
    // replace_subgoal_with_premises on a term with no premises rejects index 0.
    let ctx = ctx_with_props(&["A"]);
    let a = prop_term(&ctx, "A");

    let err = a.replace_subgoal_with_premises(0, &[]).unwrap_err();
    assert!(matches!(err, KernelError::SubgoalIndexOutOfRange { index: 0, nprems: 0 }));
}
