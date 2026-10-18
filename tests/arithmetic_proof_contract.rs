use std::sync::Arc;

use isabelle_rs::{
    core::{
        logic::Pure,
        term::Term,
        thm::{CTerm, ThmKernel, ThmTrust},
        types::Typ,
    },
    hol::{hol_loader::HolTheoremDb, hologic},
    isar::{
        linarith::arith_tac,
        method::{ProofOutcome, VerifyOutcome, classify_proof_outcome},
        proof_result::{GoalExportError, validate_proof_result},
    },
    tools::simp::{ArithSolver, Solver},
};

fn build_arithmetic_db() -> HolTheoremDb {
    let mut db = HolTheoremDb::new();
    let nat = hologic::natT();
    db.type_env.declare_type("Nat.nat", 0);
    for constant in [
        hologic::trueprop_const(),
        hologic::eq_const(nat.clone()),
        hologic::false_const(),
        hologic::suc_const(),
        hologic::zero_nat(),
        hologic::plus_const(nat.clone()),
        Term::const_("Orderings.less", Typ::arrow(nat.clone(), Typ::arrow(nat, hologic::boolT()))),
    ] {
        let Term::Const { name, typ } = constant else { unreachable!() };
        db.type_env.declare_const(&name, typ);
    }
    db
}

fn make_nat(name: &str) -> Term {
    Term::free(name, hologic::natT())
}

fn make_suc(term: Term) -> Term {
    Term::app(hologic::suc_const(), term)
}

fn make_equality(left: Term, right: Term) -> Term {
    hologic::mk_Trueprop(hologic::mk_eq_typed(hologic::natT(), left, right))
}

fn make_less(left: Term, right: Term) -> Term {
    let nat = hologic::natT();
    let relation =
        Term::const_("Orderings.less", Typ::arrow(nat.clone(), Typ::arrow(nat, hologic::boolT())));
    hologic::mk_Trueprop(Term::apps(relation, [left, right]))
}

fn assert_unproved_without_arithmetic_basis(goal: Term) {
    let db = build_arithmetic_db();
    let expected = CTerm::certify_checked(goal, &db.type_env).unwrap();
    let state = ThmKernel::trivial(expected.clone()).unwrap();
    let results = arith_tac(&state, &[], &db);
    let [result] = results.as_slice() else { panic!("expected one unresolved obligation") };
    assert_eq!(result.prop().term(), state.prop().term());
    assert_eq!(result.nprems(), state.nprems());
    assert_eq!(result.prem(0).as_ref(), Some(expected.term()));
    assert!(result.hyps().is_empty());
    assert!(result.tpairs().is_empty());
    assert!(result.oracles().is_empty());
    assert_eq!(result.trust_status(), ThmTrust::Strict);
    assert!(matches!(
        validate_proof_result(expected.term(), result, &[]),
        Err(GoalExportError::PropositionMismatch)
    ));
    assert!(ArithSolver.solve(expected.term(), &[], &db).is_none());
}

#[test]
fn arith_tac_hol_reflexivity_without_basis_remains_unproved() {
    let n = make_nat("n");
    assert_unproved_without_arithmetic_basis(make_equality(n.clone(), n));
}

#[test]
fn arith_tac_less_transitivity_without_basis_remains_unproved() {
    let (x, y, z) = (make_nat("x"), make_nat("y"), make_nat("z"));
    let expected = Pure::mk_implies(
        make_less(x.clone(), y.clone()),
        Pure::mk_implies(make_less(y, z.clone()), make_less(x, z)),
    );
    assert_unproved_without_arithmetic_basis(expected);
}

#[test]
fn arith_tac_zero_suc_contradiction_without_basis_remains_unproved() {
    let expected = Pure::mk_implies(
        make_equality(hologic::zero_nat(), make_suc(make_nat("n"))),
        hologic::mk_Trueprop(hologic::false_const()),
    );
    assert_unproved_without_arithmetic_basis(expected);
}

#[test]
fn arith_tac_nat_05_contradiction_without_basis_remains_unproved() {
    let (x, y) = (make_nat("x"), make_nat("y"));
    let one = make_suc(hologic::zero_nat());
    let three = make_suc(make_suc(one.clone()));
    let x_plus_three = Term::apps(hologic::plus_const(hologic::natT()), [x.clone(), three]);
    let x_plus_one = Term::apps(hologic::plus_const(hologic::natT()), [x, one]);
    let expected = Pure::mk_implies(
        make_less(x_plus_three, y.clone()),
        Pure::mk_implies(make_less(y, x_plus_one), hologic::mk_Trueprop(hologic::false_const())),
    );
    assert_unproved_without_arithmetic_basis(expected);
}

#[test]
fn arith_tac_suc_injectivity_without_basis_remains_unproved() {
    let (n, m) = (make_nat("n"), make_nat("m"));
    let expected = Pure::mk_implies(
        make_equality(make_suc(n.clone()), make_suc(m.clone())),
        make_equality(n, m),
    );
    assert_unproved_without_arithmetic_basis(expected);
}

#[test]
fn arith_tac_zero_less_suc_without_basis_remains_unproved() {
    assert_unproved_without_arithmetic_basis(make_less(
        hologic::zero_nat(),
        make_suc(make_nat("n")),
    ));
}

#[test]
fn arith_solver_unproved_atom_does_not_return_its_own_assumption() {
    let db = build_arithmetic_db();
    let goal = hologic::mk_Trueprop(hologic::false_const());
    assert!(ArithSolver.solve(&goal, &[], &db).is_none());
}

#[test]
fn arith_solver_checked_pure_fact_closes_exact_goal_without_hypotheses() {
    let mut db = build_arithmetic_db();
    let zero = CTerm::certify_checked(hologic::zero_nat(), &db.type_env).unwrap();
    let fact = Arc::new(ThmKernel::reflexive(zero).unwrap());
    db.intros.push(Arc::clone(&fact));
    let result = ArithSolver.solve(fact.prop().term(), &[], &db).unwrap();
    assert_eq!(result.prop().term(), fact.prop().term());
    assert_eq!(result.nprems(), 0);
    assert!(result.hyps().is_empty());
    validate_proof_result(fact.prop().term(), &result, &[]).unwrap();
    assert!(matches!(
        classify_proof_outcome("pure_reflexivity", None, Some((&result, VerifyOutcome::Proved))),
        ProofOutcome::TransitionalStrictClosed { .. }
    ));
}

#[test]
fn arith_solver_compatibility_fact_cannot_authorize_goal() {
    let mut db = build_arithmetic_db();
    let goal = hologic::mk_Trueprop(hologic::false_const());
    db.intros.push(Arc::new(ThmKernel::assume_compat(CTerm::certify(goal.clone()))));
    assert!(ArithSolver.solve(&goal, &[], &db).is_none());
}

#[test]
fn arith_solver_undeclared_goal_is_rejected() {
    let goal = Term::const_("undeclared", Pure::prop_type());
    assert!(ArithSolver.solve(&goal, &[], &HolTheoremDb::new()).is_none());
}

#[test]
fn arith_solver_database_hypothesis_cannot_authorize_goal() {
    let mut db = build_arithmetic_db();
    let goal =
        CTerm::certify_checked(hologic::mk_Trueprop(hologic::false_const()), &db.type_env).unwrap();
    db.intros.push(Arc::new(ThmKernel::assume_checked(goal.clone()).unwrap()));
    let obligation = ThmKernel::trivial(goal.clone()).unwrap();
    let candidates = arith_tac(&obligation, &[], &db);
    let candidate = candidates.iter().find(|result| result.prop().term() == goal.term()).unwrap();
    assert!(matches!(
        validate_proof_result(goal.term(), candidate, &[]),
        Err(GoalExportError::UnknownHypotheses)
    ));
    assert!(ArithSolver.solve(goal.term(), &[], &db).is_none());
}

#[test]
fn arith_solver_explicit_context_keeps_only_authorized_hypotheses() {
    let mut db = build_arithmetic_db();
    let goal =
        CTerm::certify_checked(hologic::mk_Trueprop(hologic::false_const()), &db.type_env).unwrap();
    let premise = ThmKernel::assume_checked(goal.clone()).unwrap();
    db.intros.push(Arc::new(premise.clone()));
    let result = ArithSolver.solve(goal.term(), &[premise], &db).unwrap();
    assert_eq!(result.prop().term(), goal.term());
    assert_eq!(result.nprems(), 0);
    assert_eq!(result.hyps().len(), 1);
    validate_proof_result(goal.term(), &result, std::slice::from_ref(&goal)).unwrap();
    assert!(matches!(
        classify_proof_outcome("local_assumption", None, Some((&result, VerifyOutcome::Proved))),
        ProofOutcome::OpenOracleFree { .. }
    ));
}

#[test]
fn arith_solver_non_proposition_goal_is_rejected() {
    let db = build_arithmetic_db();
    assert!(ArithSolver.solve(&hologic::false_const(), &[], &db).is_none());
}

#[test]
fn arith_solver_checked_fact_for_different_goal_is_rejected() {
    let mut db = build_arithmetic_db();
    let zero = CTerm::certify_checked(hologic::zero_nat(), &db.type_env).unwrap();
    db.intros.push(Arc::new(ThmKernel::reflexive(zero).unwrap()));
    let goal = Pure::mk_equals(hologic::natT(), hologic::zero_nat(), make_suc(hologic::zero_nat()));
    assert!(ArithSolver.solve(&goal, &[], &db).is_none());
}

#[test]
fn arith_solver_admitted_candidate_is_rejected_without_authorizing_false() {
    let mut db = build_arithmetic_db();
    let goal =
        CTerm::certify_checked(hologic::mk_Trueprop(hologic::false_const()), &db.type_env).unwrap();
    db.intros.push(Arc::new(ThmKernel::admit(goal.clone(), "admitted:arithmetic_regression")));
    let obligation = ThmKernel::trivial(goal.clone()).unwrap();
    let candidates = arith_tac(&obligation, &[], &db);
    let candidate = candidates.iter().find(|result| result.prop().term() == goal.term()).unwrap();
    assert!(matches!(
        validate_proof_result(goal.term(), candidate, &[]),
        Err(GoalExportError::OracleOrAdmitted)
    ));
    assert!(ArithSolver.solve(goal.term(), &[], &db).is_none());
}

#[test]
fn arith_solver_unresolved_dummy_goal_is_rejected() {
    let goal = Term::free("unresolved", Typ::dummy());
    assert!(ArithSolver.solve(&goal, &[], &build_arithmetic_db()).is_none());
}
