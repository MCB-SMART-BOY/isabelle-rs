use std::sync::Arc;

use isabelle_rs::{
    core::{
        logic::Pure,
        term::Term,
        thm::{CTerm, ThmKernel},
        types::{Typ, TypeEnv},
    },
    hol::hol_loader::{HolTheoremDb, ParsedLemma},
    isar::method::exec_single_method,
};

#[test]
fn search_context_same_named_fact_in_one_database_is_not_visible_in_another() {
    let mut type_env = TypeEnv::new();
    let prop_type = Typ::base("prop");
    type_env.declare_const("A", prop_type.clone());
    let statement = Term::const_("A", prop_type.clone());
    let fact = ThmKernel::reflexive(CTerm::certify_checked(statement.clone(), &type_env).unwrap())
        .unwrap();
    let goal = ThmKernel::trivial(
        CTerm::certify_checked(Pure::mk_equals(prop_type, statement.clone(), statement), &type_env)
            .unwrap(),
    )
    .unwrap();

    let mut with_fact = HolTheoremDb::new();
    with_fact.by_name.insert("local_identity".into(), Arc::new(fact));
    let without_fact = HolTheoremDb::new();

    let result = exec_single_method(&goal, "(fact local_identity)", &[], &with_fact);
    assert!(result.iter().any(|theorem| theorem.nprems() == 0));
    assert!(exec_single_method(&goal, "(fact local_identity)", &[], &without_fact).is_empty());
}

#[test]
fn search_context_extend_after_intro_lookup_exposes_new_rule() {
    let proposition = Term::free("P", Typ::base("prop"));
    let mut db = HolTheoremDb::new();
    assert!(db.intro_net().lookup(&proposition).is_empty());

    let rule = ParsedLemma::new_synthetic(
        "local_intro".into(),
        vec!["intro".into()],
        Arc::new(ThmKernel::assume_compat(CTerm::certify(proposition.clone()))),
        None,
        None,
    );
    db.extend(&[rule]);
    let matches = db.intro_net().lookup(&proposition);
    assert_eq!(matches.len(), 1);
    assert_eq!(matches[0].prop().term(), &proposition);
}
