use std::sync::Arc;

use isabelle_rs::{
    core::{
        logic::Pure,
        simplifier::{RewriteRule, Simplifier, arg_conv, beta_simp, fun_conv},
        term::Term,
        thm::{CTerm, Thm, ThmKernel, ThmTrust},
        types::{Typ, TypeEnv},
    },
    tools::simp::HolSimplifier,
};

fn prop() -> Typ {
    Typ::base("prop")
}

fn checked(term: Term) -> CTerm {
    CTerm::certify_checked(term, &TypeEnv::new()).expect("typed rewrite fixture")
}

fn prove_refl(term: Term) -> Arc<Thm> {
    Arc::new(ThmKernel::reflexive(checked(term)).expect("reflexive rule"))
}

fn same_alpha(left: &Term, right: &Term) -> bool {
    match (left, right) {
        (Term::Abs { typ: lt, body: lb, .. }, Term::Abs { typ: rt, body: rb, .. }) => {
            lt == rt && same_alpha(lb, rb)
        },
        (Term::App { func: lf, arg: la }, Term::App { func: rf, arg: ra }) => {
            same_alpha(lf, rf) && same_alpha(la, ra)
        },
        _ => left == right,
    }
}

fn assert_endpoints(theorem: &Thm, original: &Term, rewritten: &Term) {
    let (left, right) = Pure::dest_equals(theorem.prop().term()).expect("equality evidence");
    assert_eq!(left, original);
    assert_eq!(right, rewritten);
    assert!(theorem.hyps().is_empty());
    assert!(theorem.tpairs().is_empty());
    assert!(!theorem.has_oracles());
}

#[test]
fn schematic_rewrite_matches_only_variable_and_instantiates_certificate() {
    let pattern = Term::var("x", 0, prop());
    let target = Term::free("y", prop());
    let rule = RewriteRule::from_thm(prove_refl(pattern)).unwrap();
    let simp = Simplifier::new(vec![rule.clone()]);
    let (result, theorem) = simp.rewrite(&target).expect("schematic rule matches y");
    assert_eq!(result, target);
    assert_endpoints(&theorem, &target, &result);
    assert_eq!(theorem.trust_status(), ThmTrust::Strict);
    assert!(theorem.prop().is_checked());

    let hol = HolSimplifier::with_rules(vec![rule]);
    let (hol_result, hol_proof) = hol.hol_rewrite(&target).unwrap();
    assert_endpoints(&hol_proof, &target, &hol_result);
}

#[test]
fn compatibility_rewrite_never_acquires_strict_provenance() {
    let term = Term::free("legacy", prop());
    let source = ThmKernel::reflexive_compat(CTerm::certify(term.clone()));
    let rule = RewriteRule::from_thm(Arc::new(source)).unwrap();
    let (_, result) = Simplifier::new(vec![rule]).rewrite(&term).unwrap();
    assert_eq!(result.trust_status(), ThmTrust::Compat);
    assert!(!result.is_strict_closed_proved());
    assert_endpoints(&result, &term, &term);
}

#[test]
fn rigid_free_and_tampered_cache_or_condition_never_rewrite() {
    let x = Term::free("x", prop());
    let y = Term::free("y", prop());
    let rule = RewriteRule::from_thm(prove_refl(x.clone())).unwrap();
    assert!(Simplifier::new(vec![rule.clone()]).rewrite(&y).is_none());
    assert!(HolSimplifier::with_rules(vec![rule.clone()]).hol_rewrite(&y).is_none());

    let mut cache = rule.clone();
    cache.lhs = y.clone();
    cache.rhs = y.clone();
    assert!(Simplifier::new(vec![cache.clone()]).rewrite(&y).is_none());
    assert!(HolSimplifier::with_rules(vec![cache]).hol_rewrite(&y).is_none());

    let mut conditional = rule;
    conditional.condition = Some(x.clone());
    assert!(Simplifier::new(vec![conditional.clone()]).rewrite(&x).is_none());
    assert!(HolSimplifier::with_rules(vec![conditional]).hol_rewrite(&x).is_none());
}

#[test]
fn beta_rewrite_under_application_has_exact_congruence_certificate() {
    let ty = prop();
    let y = Term::free("y", ty.clone());
    let id = Term::abs("z", ty.clone(), Term::bound(0));
    let input = Term::app(Term::free("f", Typ::arrow(ty.clone(), ty)), Term::app(id, y.clone()));
    let expected = Term::app(Term::free("f", Typ::arrow(prop(), prop())), y);
    let (rewritten, theorem) = beta_simp().rewrite_deep(&input).expect("deep beta rewrite");
    assert_eq!(rewritten, expected);
    assert_endpoints(&theorem, &input, &expected);
    let (hol_term, hol_proof) = HolSimplifier::with_beta().hol_rewrite_deep(&input).unwrap();
    assert_eq!(hol_term, expected);
    assert_endpoints(&hol_proof, &input, &expected);
}

#[test]
fn beta_rewrite_two_stages_composes_from_original_to_final_term() {
    let ty = prop();
    let y = Term::free("y", ty.clone());
    let id = Term::abs("x", ty.clone(), Term::bound(0));
    let original = Term::app(id.clone(), Term::app(id, y.clone()));
    let (result, proof) = beta_simp().rewrite_deep(&original).expect("both beta stages");
    assert_eq!(result, y);
    assert_endpoints(&proof, &original, &result);
}

#[test]
fn reversed_cache_requires_symmetric_theorem_before_rewriting() {
    let ty = prop();
    let y = Term::free("y", ty.clone());
    let application = Term::app(Term::abs("x", ty, Term::bound(0)), y.clone());
    let forward = Arc::new(ThmKernel::beta_conversion(checked(application.clone())).unwrap());
    let reversed =
        RewriteRule { lhs: y.clone(), rhs: application.clone(), condition: None, thm: forward };
    let (result, proof) = Simplifier::new(vec![reversed]).rewrite(&y).unwrap();
    assert_eq!(result, application);
    assert_endpoints(&proof, &y, &result);
}

#[test]
fn beta_rewrite_under_nested_abstraction_avoids_existing_free_name() {
    let ty = prop();
    let free_collision = Term::free("_simp_bound_0", ty.clone());
    let function = Term::free("f", Typ::arrows(vec![ty.clone(), ty.clone()], ty.clone()));
    let beta = Term::app(Term::abs("z", ty.clone(), Term::bound(0)), Term::bound(1));
    let original = Term::abs(
        "outer",
        ty.clone(),
        Term::abs(
            "inner",
            ty.clone(),
            Term::apps(function.clone(), [free_collision.clone(), beta]),
        ),
    );
    let expected_body = Term::apps(function, [free_collision.clone(), Term::bound(1)]);
    let expected = Term::abs("outer", ty.clone(), Term::abs("inner", ty, expected_body));
    let (rewritten, theorem) = beta_simp().rewrite_deep(&original).expect("nested beta conversion");
    let (left, right) = Pure::dest_equals(theorem.prop().term()).unwrap();
    assert!(same_alpha(&rewritten, &expected));
    assert!(same_alpha(left, &original));
    assert!(same_alpha(right, &expected));
    for endpoint in [left, right] {
        let Term::Abs { body: outer, .. } = endpoint else { panic!("outer binder absent") };
        let Term::Abs { body: inner, .. } = outer.as_ref() else { panic!("inner binder absent") };
        let Term::App { func: partial, .. } = inner.as_ref() else { panic!("function absent") };
        assert_eq!(
            partial.as_ref(),
            &Term::app(
                Term::free("f", Typ::arrows(vec![prop(), prop()], prop())),
                free_collision.clone(),
            )
        );
    }
}

#[test]
fn conversion_congruence_rejects_wrong_endpoint_and_keeps_correct_argument() {
    let ty = prop();
    let y = Term::free("y", ty.clone());
    let function_type = Typ::arrow(ty.clone(), ty.clone());
    let id = Term::abs("z", function_type.clone(), Term::bound(0));
    let g = Term::free("g", function_type);
    let input = Term::app(Term::app(id, g.clone()), y.clone());
    let beta = Arc::new(|term: &Term| ThmKernel::beta_conversion(checked(term.clone())).ok());
    let function = fun_conv(beta.clone());
    let result = function(&input).expect("function side beta conversion");
    let expected = Term::app(g, y.clone());
    assert_endpoints(&result, &input, &expected);

    let wrong = Arc::new(|_: &Term| {
        Some(ThmKernel::reflexive(checked(Term::free("wrong", prop()))).unwrap())
    });
    assert!(arg_conv(0, wrong)(&input).is_none());
}
