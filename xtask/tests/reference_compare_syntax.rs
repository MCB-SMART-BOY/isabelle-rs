use isabelle_evidence::compare_syntax::{
    match_judgments, match_judgments_with_constraints, match_terms, match_types,
    match_validated_records,
};
use serde_json::{Value, json};

fn make_type() -> Value {
    json!({"kind":"Type","name":"prop","args":[]})
}
fn make_tvar(name: &str, index: u64, sort: Value) -> Value {
    json!({"kind":"TVar","name":name,"index":index,"sort":sort})
}
fn make_var(name: &str) -> Value {
    json!({"kind":"Var","name":name,"index":0,"type":make_type()})
}
fn make_const(name: &str) -> Value {
    json!({"kind":"Const","name":name,"type":make_type()})
}
fn make_judgment(proposition: Value, hypotheses: Value, tpairs: Value, shyps: Value) -> Value {
    json!({"proposition":proposition,"hypotheses":hypotheses,"tpairs":tpairs,"shyps":shyps})
}

#[test]
fn comparison_shared_renaming_across_burdens_accepts() {
    let mut x = make_var("x");
    x["type"] = make_tvar("a", 0, json!([]));
    let mut y = x.clone();
    y["name"] = json!("y");
    let mut u = make_var("u");
    u["type"] = make_tvar("b", 7, json!([]));
    u["index"] = json!(2);
    let mut v = u.clone();
    v["name"] = json!("v");
    v["index"] = json!(3);
    let left = make_judgment(x.clone(), json!([]), json!([[x, y]]), json!([]));
    let right = make_judgment(u.clone(), json!([]), json!([[u, v]]), json!([]));
    assert!(match_judgments(&left, &right).unwrap());
}

#[test]
fn comparison_conflicting_and_collapsed_cross_field_renaming_rejects() {
    let left =
        make_judgment(make_var("x"), json!([]), json!([[make_var("x"), make_var("y")]]), json!([]));
    let right =
        make_judgment(make_var("a"), json!([]), json!([[make_var("b"), make_var("a")]]), json!([]));
    assert!(!match_judgments(&left, &right).unwrap());
    let right =
        make_judgment(make_var("a"), json!([]), json!([[make_var("a"), make_var("a")]]), json!([]));
    assert!(!match_judgments(&left, &right).unwrap());
}

#[test]
fn comparison_ambiguous_pair_order_backtracks() {
    let left = make_judgment(
        make_const("C"),
        json!([]),
        json!([
            [make_var("x"), make_var("z")],
            [make_var("y"), make_var("z")],
            [make_var("x"), make_var("y")]
        ]),
        json!([]),
    );
    let right = make_judgment(
        make_const("C"),
        json!([]),
        json!([
            [make_var("a"), make_var("c")],
            [make_var("b"), make_var("c")],
            [make_var("b"), make_var("a")]
        ]),
        json!([]),
    );
    assert!(match_judgments(&left, &right).unwrap());
}

#[test]
fn comparison_hypothesis_membership_preserves_order_independence() {
    let left = make_judgment(
        make_const("P"),
        json!([make_const("P"), make_const("Q")]),
        json!([]),
        json!([]),
    );
    let mut right = left.clone();
    right["hypotheses"].as_array_mut().unwrap().reverse();
    assert!(match_judgments(&left, &right).unwrap());
    right["hypotheses"].as_array_mut().unwrap().pop();
    assert!(!match_judgments(&left, &right).unwrap());
}

#[test]
fn comparison_erased_sort_hypothesis_rejects() {
    let left =
        make_judgment(make_const("C"), json!([]), json!([]), json!([["HOL.type"], ["Groups.ord"]]));
    let mut right = left.clone();
    right["shyps"].as_array_mut().unwrap().pop();
    assert!(!match_judgments(&left, &right).unwrap());
}

#[test]
fn comparison_bound_display_names_ignore_spelling_but_not_scope() {
    let left =
        json!({"kind":"Abs","name":"x","type":make_type(),"body":{"kind":"Bound","index":0}});
    let mut right = left.clone();
    right["name"] = json!("renamed");
    assert!(match_terms(&left, &right).unwrap());
    assert!(match_terms(&left["body"], &right["body"]).is_err());
}

#[test]
fn comparison_free_names_and_schematic_kinds_remain_distinct() {
    assert!(!match_terms(&make_const("A"), &make_const("B")).unwrap());
    let free = json!({"kind":"Free","name":"x","type":make_type()});
    let mut renamed = free.clone();
    renamed["name"] = json!("y");
    assert!(!match_terms(&free, &renamed).unwrap());
    assert!(!match_terms(&free, &make_var("x")).unwrap());
    let free_type = json!({"kind":"TFree","name":"a","sort":[]});
    let mut renamed_type = free_type.clone();
    renamed_type["name"] = json!("b");
    assert!(!match_types(&free_type, &renamed_type).unwrap());
    assert!(!match_types(&free_type, &make_tvar("a", 0, json!([]))).unwrap());
}

#[test]
fn comparison_sort_order_matches_but_erasure_rejects() {
    let left = make_tvar("a", 0, json!(["A", "B"]));
    assert!(match_types(&left, &make_tvar("b", 0, json!(["B", "A"]))).unwrap());
    assert!(!match_types(&left, &make_tvar("b", 0, json!([]))).unwrap());
}

#[test]
fn comparison_conflicting_type_annotations_rejects() {
    let mut variable = make_var("x");
    variable["type"] = make_tvar("a", 0, json!([]));
    let mut conflicting = variable.clone();
    conflicting["type"]["sort"] = json!(["HOL.type"]);
    let left =
        make_judgment(variable, json!([]), json!([[conflicting, make_const("C")]]), json!([]));
    assert!(match_judgments(&left, &left).is_err());
}

#[test]
fn comparison_invalid_schematic_indices_reject() {
    for index in [json!(-1), json!(true), json!("0"), Value::Null] {
        let mut variable = make_var("x");
        variable["index"] = index;
        assert!(match_terms(&variable, &make_var("x")).is_err());
    }
}

#[test]
fn comparison_missing_judgment_burden_never_becomes_empty() {
    let left = make_judgment(make_const("C"), json!([]), json!([]), json!([]));
    for field in ["proposition", "hypotheses", "shyps", "tpairs"] {
        let mut right = left.clone();
        right.as_object_mut().unwrap().remove(field);
        assert!(match_judgments(&left, &right).is_err(), "{field}");
    }
}

#[test]
fn comparison_dependency_reordering_preserves_shared_variables() {
    let a = make_tvar("a", 0, json!([]));
    let b = make_tvar("b", 3, json!([]));
    let left =
        json!({"subject":a,"dependencies":[{"type":a,"name":"first"},{"type":a,"name":"second"}]});
    let mut right =
        json!({"subject":b,"dependencies":[{"type":b,"name":"second"},{"type":b,"name":"first"}]});
    assert!(match_validated_records(&left, &right).unwrap());
    right["dependencies"][0]["type"]["name"] = json!("different");
    assert!(!match_validated_records(&left, &right).unwrap());
}

#[test]
fn comparison_constraints_conflicting_alpha_binding_rejects() {
    let left = make_judgment(make_var("x"), json!([]), json!([]), json!([]));
    let right = make_judgment(make_var("a"), json!([]), json!([]), json!([]));
    let c_left = json!([{"subject":make_var("x")}]);
    let c_right = json!([{"subject":make_var("b")}]);
    assert!(
        !match_judgments_with_constraints(
            &left,
            &right,
            c_left.as_array().unwrap(),
            c_right.as_array().unwrap()
        )
        .unwrap()
    );
}
