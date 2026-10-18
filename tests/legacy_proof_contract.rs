use std::sync::Arc;

use isabelle_rs::{
    core::{
        logic::Pure,
        term::Term,
        theory::Theory,
        thm::{CTerm, Thm, ThmKernel},
        types::Typ,
    },
    hol::hol_loader::HolTheoremDb,
    isar::{proof::IsarProof, proof_context::ProofCertContext, proof_result::GoalExportError},
};

fn make_context() -> ProofCertContext {
    ProofCertContext::new().with_const("A", Typ::base("prop")).with_const("B", Typ::base("prop"))
}

fn make_proof() -> IsarProof {
    let mut theory = Theory::begin("Test", vec![Theory::pure()]).unwrap();
    theory.declare_const("A", Typ::base("prop"));
    theory.declare_const("B", Typ::base("prop"));
    IsarProof::init(Arc::new(theory))
}

fn make_proposition(name: &str) -> Term {
    Term::const_(name, Typ::base("prop"))
}

fn prove_identity(name: &str) -> Thm {
    let proposition = make_context().certify_prop(make_proposition(name)).unwrap();
    let assumed = ThmKernel::assume(proposition.clone()).unwrap();
    ThmKernel::implies_intr(&proposition, &assumed).unwrap()
}

#[test]
fn isar_proof_fresh_goal_cannot_finish_or_extract() {
    let mut proof = make_proof();
    proof.lemma("unproved", make_proposition("A")).unwrap();
    assert!(proof.qed().is_err());
    assert!(proof.done().is_err());
    assert!(proof.extract_theorem().is_err());
    assert_eq!(proof.apply("assumption", &HolTheoremDb::new()), 1);
    assert!(proof.done().is_err());
    proof.sorry();
    assert!(matches!(proof.extract_theorem(), Err(GoalExportError::OracleOrAdmitted)));
}

#[test]
fn isar_proof_supplied_identity_proves_entire_implication() {
    let theorem = prove_identity("A");
    let mut proof = make_proof();
    proof.lemma("identity", theorem.prop().term().clone()).unwrap();
    proof.using(vec![theorem.clone()]);
    proof.by("this", &HolTheoremDb::new()).unwrap();
    let (name, actual) = proof.extract_theorem().unwrap();
    assert_eq!(name, "identity");
    assert!(actual.is_strict_closed_proved());
    assert_eq!(actual.prop().term(), theorem.prop().term());
    assert_eq!(proof.remaining_subgoals(), 0);
}

#[test]
fn isar_proof_wrong_show_cannot_close_parent() {
    let mut proof = make_proof();
    proof.lemma("identity_a", prove_identity("A").prop().term().clone()).unwrap();
    proof.proof().unwrap();
    let other = prove_identity("B");
    proof.show("wrong", other.prop().term().clone()).unwrap();
    proof.using(vec![other]);
    assert!(matches!(
        proof.by("this", &HolTheoremDb::new()),
        Err(GoalExportError::PropositionMismatch)
    ));
    assert!(proof.extract_theorem().is_err());
}

#[test]
fn isar_proof_compat_identity_cannot_become_completion() {
    let theorem = ThmKernel::trivial(CTerm::certify(make_proposition("A"))).unwrap();
    let mut proof = make_proof();
    proof.lemma("identity", theorem.prop().term().clone()).unwrap();
    proof.using(vec![theorem]);
    assert!(proof.by("this", &HolTheoremDb::new()).is_err());
    assert!(proof.extract_theorem().is_err());
}

#[test]
fn isar_proof_named_method_must_consume_all_arguments() {
    for method in ["assumptoin", "assumption extra", "this extra", "(this) garbage", "rule missing"]
    {
        let mut proof = make_proof();
        let theorem = prove_identity("A");
        proof.lemma("identity", theorem.prop().term().clone()).unwrap();
        proof.using(vec![theorem]);
        let empty = HolTheoremDb::new();
        let result = proof.by(method, &empty);
        assert!(
            matches!(result, Err(GoalExportError::InvalidScript { .. })),
            "{method}: {result:?}"
        );
        assert!(proof.extract_theorem().is_err());
    }
}

#[test]
fn isar_proof_scoped_assumption_exports_once_through_nested_have() {
    let mut proof = make_proof();
    let a = make_proposition("A");
    let expected = Pure::mk_implies(a.clone(), a.clone());
    proof.lemma("identity", expected.clone()).unwrap();
    proof.proof().unwrap();
    proof.assume(std::slice::from_ref(&a)).unwrap();
    proof.have("local", a.clone()).unwrap();
    proof.proof().unwrap();
    proof.show("local_result", a.clone()).unwrap();
    proof.by("assumption", &HolTheoremDb::new()).unwrap();
    proof.qed().unwrap();
    proof.show("result", a).unwrap();
    proof.by("this", &HolTheoremDb::new()).unwrap();
    proof.qed().unwrap();
    let result = proof.close_lemma().unwrap();
    assert!(result.is_strict_closed_proved());
    assert_eq!(result.prop().term(), &expected);
}

#[test]
fn isar_proof_local_fix_exports_quantifier_without_free_escape() {
    let mut proof = IsarProof::init(Theory::pure());
    let prop = Typ::base("prop");
    let expected = Term::app(
        Term::const_("Pure.all", Typ::arrow(Typ::arrow(prop.clone(), prop.clone()), prop.clone())),
        Term::abs("P", prop.clone(), Pure::mk_implies(Term::bound(0), Term::bound(0))),
    );
    proof.lemma("identity", expected.clone()).unwrap();
    proof.proof().unwrap();
    proof.fix(&[("P", prop.clone())]).unwrap();
    assert!(proof.fix(&[("P", prop.clone())]).is_err());
    let p = Term::free("P", prop);
    proof.assume(std::slice::from_ref(&p)).unwrap();
    proof.show("result", p).unwrap();
    proof.by("assumption", &HolTheoremDb::new()).unwrap();
    proof.qed().unwrap();
    let result = proof.close_lemma().unwrap();
    assert!(result.is_strict_closed_proved());
    assert_eq!(result.prop().term(), &expected);
}

#[test]
fn isar_proof_unknown_hypothesis_is_not_authorized_by_using() {
    let a = make_context().certify_prop(make_proposition("A")).unwrap();
    let mut proof = make_proof();
    proof.lemma("unproved", a.term().clone()).unwrap();
    proof.using(vec![ThmKernel::assume(a).unwrap()]);
    assert!(proof.by("this", &HolTheoremDb::new()).is_err());
    assert!(proof.extract_theorem().is_err());
}

#[test]
fn proof_result_same_names_at_different_types_do_not_authorize_hypotheses() {
    use isabelle_rs::isar::proof_result::validate_proof_result;
    fn certify_application(argument_type: Typ) -> CTerm {
        let predicate_type = Typ::arrow(argument_type.clone(), Typ::base("prop"));
        let context = ProofCertContext::new()
            .with_free("P", predicate_type.clone())
            .with_free("x", argument_type.clone());
        context
            .certify_prop(Term::app(
                Term::free("P", predicate_type),
                Term::free("x", argument_type),
            ))
            .unwrap()
    }
    let actual = certify_application(Typ::base("prop"));
    let different = certify_application(Typ::base("bool"));
    let proof = ThmKernel::assume(actual.clone()).unwrap();
    assert!(matches!(
        validate_proof_result(actual.term(), &proof, std::slice::from_ref(&different)),
        Err(GoalExportError::UnknownHypotheses)
    ));
    assert!(matches!(
        validate_proof_result(different.term(), &proof, &[actual]),
        Err(GoalExportError::PropositionMismatch)
    ));
}

#[test]
fn isar_proof_unfinished_structured_scope_cannot_be_extracted_or_discarded() {
    let mut proof = make_proof();
    let a = make_proposition("A");
    proof.lemma("identity", Pure::mk_implies(a.clone(), a.clone())).unwrap();
    proof.proof().unwrap();
    proof.assume(std::slice::from_ref(&a)).unwrap();
    proof.show("result", a).unwrap();
    proof.by("assumption", &HolTheoremDb::new()).unwrap();
    let level = proof.level();
    assert!(proof.extract_theorem().is_err());
    assert!(proof.close_lemma().is_err());
    assert_eq!(proof.level(), level);
    proof.have("pending", make_proposition("B")).unwrap();
    assert!(proof.extract_theorem().is_err());
    assert!(proof.close_lemma().is_err());
    assert_eq!(proof.level(), level + 1);
}
