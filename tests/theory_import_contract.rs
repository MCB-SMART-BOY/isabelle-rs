use std::sync::Arc;

use isabelle_rs::{
    core::{
        sign::SignatureMergeError,
        term::Term,
        theory::{Definition, Theory, TheoryMergeError},
        types::Typ,
    },
    theory::{
        loader::{TheoryLoadError, TheoryProcessor},
        registry::TheoryRegistry,
    },
};

#[test]
fn begin_distinct_parent_identities_with_same_name_are_rejected() {
    let first = Arc::new(Theory::begin("Same", vec![Theory::pure()]).unwrap());
    let second = Arc::new(Theory::begin("Same", vec![Theory::pure()]).unwrap());
    assert!(matches!(Theory::begin("Join", vec![first, second]),
        Err(TheoryMergeError::IdentityConflict { name }) if name.as_ref() == "Same"));
}

#[test]
fn begin_distinct_constant_declarations_with_equal_types_are_rejected() {
    let mut first = Theory::begin("First", vec![Theory::pure()]).unwrap();
    let mut second = Theory::begin("Second", vec![Theory::pure()]).unwrap();
    first.declare_const("collision", Typ::base("prop"));
    second.declare_const("collision", Typ::base("prop"));
    assert!(matches!(Theory::begin("Join", vec![Arc::new(first), Arc::new(second)]),
        Err(TheoryMergeError::Signature(SignatureMergeError::Declaration { namespace: "constant", name }))
            if name.as_ref() == "collision"));
}

#[test]
fn begin_conflicting_axioms_are_rejected_without_changing_parents() {
    let mut first = Theory::begin("First", vec![Theory::pure()]).unwrap();
    let mut second = Theory::begin("Second", vec![Theory::pure()]).unwrap();
    first.add_axiom("collision", Term::const_("P", Typ::base("prop")));
    second.add_axiom("collision", Term::const_("Q", Typ::base("prop")));
    let first = Arc::new(first);
    let second = Arc::new(second);
    assert!(matches!(Theory::begin("Join", vec![Arc::clone(&first), second]),
        Err(TheoryMergeError::ItemConflict { namespace: "axiom", name }) if name.as_ref() == "collision"));
    assert_eq!(first.all_axiom_names(), ["collision"]);
}

#[test]
fn begin_conflicting_definitions_are_rejected() {
    let mut first = Theory::begin("First", vec![Theory::pure()]).unwrap();
    let mut second = Theory::begin("Second", vec![Theory::pure()]).unwrap();
    for (theory, name) in [(&mut first, "P"), (&mut second, "Q")] {
        theory.add_definition(Definition {
            name: Arc::from("collision"),
            term: Arc::new(Term::const_(name, Typ::base("prop"))),
        });
    }
    assert!(matches!(Theory::begin("Join", vec![Arc::new(first), Arc::new(second)]),
        Err(TheoryMergeError::ItemConflict { namespace: "definition", name }) if name.as_ref() == "collision"));
}

fn prove_identity(name: &str, fact: &str) -> Arc<Theory> {
    let source = format!(
        "theory {name} imports Pure begin
        lemma {fact}: \"!!x::prop. x ==> x\"
        proof fix x::prop assume \"x::prop\" show \"x::prop\" by assumption qed end"
    );
    TheoryProcessor::new(TheoryRegistry::new()).process_source(&source).unwrap()
}

#[test]
fn begin_shared_fact_through_diamond_preserves_theorem_and_deduplicates_names() {
    let base = prove_identity("Base", "identity");
    let first = Arc::new(Theory::begin("First", vec![Arc::clone(&base)]).unwrap());
    let second = Arc::new(Theory::begin("Second", vec![Arc::clone(&base)]).unwrap());
    let joined = Theory::begin("Join", vec![first, second]).unwrap();
    assert_eq!(joined.all_theorem_names(), ["identity"]);
    assert!(Arc::ptr_eq(
        joined.lookup_theorem("identity").unwrap(),
        base.lookup_theorem("identity").unwrap()
    ));
}

#[test]
fn process_source_independent_same_name_facts_reject_import_transaction() {
    let mut registry = TheoryRegistry::new();
    registry.register(prove_identity("First", "collision"));
    registry.register(prove_identity("Second", "collision"));
    let mut processor = TheoryProcessor::new(registry);
    let error = processor.process_source("theory Join imports First Second begin end").unwrap_err();
    assert!(matches!(
        error.as_slice(),
        [TheoryLoadError::ImportMerge {
            source: TheoryMergeError::ItemConflict { namespace: "theorem", .. },
            ..
        }]
    ));
    assert_eq!(processor.theorem_count(), 0);
}
