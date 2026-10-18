use serde_json::{Value, json};
use xtask::reference::classify_axioms::classify_axioms;

fn term() -> Value {
    json!({"kind": "Const", "name": "Pure.dummy_pattern", "type": {"kind": "Type", "name": "prop", "args": []}})
}
fn theory(owner: &str, source: &str, names: &[&str]) -> Value {
    json!({"name": owner, "source": source, "axioms": names.iter().map(|name| json!({"name": name, "term": term()})).collect::<Vec<_>>(), "specifications": [], "constant_definitions": []})
}
fn inventory(theories: Vec<Value>) -> Value {
    json!({"schema_version": 1, "reference": "Isabelle2025", "theories": theories})
}
fn specification(name: &str) -> Value {
    json!({"description": name, "axiom_name": name, "subject": {"kind": "const", "name": "HOL.defined", "types": []}, "dependencies": [{"kind": "const", "name": "HOL.True", "types": []}]})
}
fn error_contains(value: &Value, expected: &str) {
    let error =
        classify_axioms(value).expect_err("must reject malformed or unsupported provenance");
    assert!(error.to_string().contains(expected), "{error}");
}

#[test]
fn classify_axioms_exact_candidates_preserve_distinct_mechanisms() {
    let hol =
        theory("HOL.HOL", "src/HOL/HOL.thy", &["HOL.arity_type_bool", "HOL.fun_arity", "HOL.refl"]);
    let nat = theory(
        "HOL.Nat",
        "src/HOL/Nat.thy",
        &["Nat.arity_type_nat", "Nat.nat.type_definition_nat"],
    );
    let pure = theory("Pure", "src/Pure/Pure.thy", &["Pure.reflexive"]);
    let result = classify_axioms(&inventory(vec![hol, nat, pure])).unwrap();
    let entries = result["entries"].as_array().unwrap();
    let categories: Vec<&str> =
        entries.iter().map(|entry| entry["category"].as_str().unwrap()).collect();
    assert_eq!(
        categories,
        [
            "object_base_sort_arity",
            "explicit_object_arity",
            "explicit_logic_axiom_candidate",
            "object_base_sort_arity",
            "conditional_typedef_extension",
            "pure_primitive_mirror"
        ]
    );
    assert_eq!(
        entries[4]["introduction"],
        json!([{"path": "src/HOL/Tools/typedef.ML", "line_start": 129, "line_end": 150}])
    );
    assert_eq!(entries[0]["introduction"][0]["path"], "src/Pure/Isar/typedecl.ML");
    assert_eq!(entries[5]["term"], term());
    assert_eq!(result["authorization"], "none_reference_provenance_only");
    assert_eq!(result["unclassified"], json!([]));
}

#[test]
fn classify_axioms_unknown_candidate_remains_unclassified() {
    let result = classify_axioms(&inventory(vec![theory(
        "HOL.HOL",
        "src/HOL/HOL.thy",
        &["HOL.arity_type_unobserved"],
    )]))
    .unwrap();
    assert_eq!(result["counts"], json!({"unclassified": 1}));
    assert_eq!(
        result["unclassified"],
        json!([{"theory": "HOL.HOL", "name": "HOL.arity_type_unobserved"}])
    );
    assert_eq!(result["entries"][0]["introduction"], json!([]));
}

#[test]
fn classify_axioms_wrong_candidate_owner_or_source_rejected() {
    for (owner, source) in [("HOL.Set", "src/HOL/Set.thy"), ("HOL.HOL", "src/HOL/Nat.thy")] {
        error_contains(
            &inventory(vec![theory(owner, source, &["HOL.fun_arity"])]),
            "Wrong owner/source",
        );
    }
}

#[test]
fn classify_axioms_duplicate_identity_across_theories_rejected() {
    error_contains(
        &inventory(vec![
            theory("HOL.HOL", "src/HOL/HOL.thy", &["unreviewed.axiom"]),
            theory("HOL.Set", "src/HOL/Set.thy", &["unreviewed.axiom"]),
        ]),
        "Duplicate axiom identity",
    );
}

#[test]
fn classify_axioms_definition_associations_retain_term_and_locations() {
    let mut item = theory("HOL.HOL", "src/HOL/HOL.thy", &["HOL.defined_def", "HOL.other_ax"]);
    item["specifications"] = json!([specification("HOL.defined_def")]);
    item["constant_definitions"] = json!([{"constant": "HOL.defined", "axiom": "HOL.defined_def"}]);
    let result = classify_axioms(&inventory(vec![item.clone()])).unwrap();
    assert_eq!(result["entries"][0]["category"], "definition_associated");
    assert_eq!(result["entries"][0]["term"], term());
    assert_eq!(
        result["entries"][0]["associations"],
        json!({"specifications": item["specifications"], "constant_definitions": item["constant_definitions"]})
    );
    assert_eq!(
        result["entries"][0]["introduction"],
        json!([{"path": "src/Pure/theory.ML", "line_start": 323, "line_end": 358}])
    );
    assert_eq!(result["unclassified"], json!([{"theory": "HOL.HOL", "name": "HOL.other_ax"}]));
}

#[test]
fn classify_axioms_specification_without_definition_remains_associated() {
    let mut item = theory("HOL.HOL", "src/HOL/HOL.thy", &["HOL.overloaded_def"]);
    item["specifications"] = json!([specification("HOL.overloaded_def")]);
    let result = classify_axioms(&inventory(vec![item])).unwrap();
    assert_eq!(result["entries"][0]["category"], "definition_associated");
    assert_eq!(result["entries"][0]["associations"]["constant_definitions"], json!([]));
}

#[test]
fn classify_axioms_invalid_associations_rejected() {
    let mut missing_spec = theory("HOL.HOL", "src/HOL/HOL.thy", &["HOL.defined_def"]);
    missing_spec["specifications"] = json!([specification("HOL.missing_def")]);
    error_contains(&inventory(vec![missing_spec]), "Unresolved specification");
    let mut missing_definition = theory("HOL.HOL", "src/HOL/HOL.thy", &["HOL.defined_def"]);
    missing_definition["constant_definitions"] =
        json!([{"constant": "HOL.defined", "axiom": "HOL.missing_def"}]);
    error_contains(&inventory(vec![missing_definition]), "Unresolved constant definition");
    let mut unmatched = theory("HOL.HOL", "src/HOL/HOL.thy", &["HOL.defined_def"]);
    unmatched["specifications"] = json!([specification("HOL.defined_def")]);
    unmatched["constant_definitions"] =
        json!([{"constant": "HOL.unrelated", "axiom": "HOL.defined_def"}]);
    error_contains(&inventory(vec![unmatched]), "lacks matching specification");
    let mut malformed = theory("HOL.HOL", "src/HOL/HOL.thy", &["HOL.defined_def"]);
    let mut spec = specification("HOL.defined_def");
    spec["axiom_name"] = json!(["HOL.defined_def"]);
    malformed["specifications"] = json!([spec]);
    error_contains(&inventory(vec![malformed]), "Malformed specification axiom identity");
}

#[test]
fn classify_axioms_type_subject_does_not_claim_definition() {
    let mut item = theory("HOL.HOL", "src/HOL/HOL.thy", &["HOL.unreviewed_type_spec"]);
    let mut spec = specification("HOL.unreviewed_type_spec");
    spec["subject"] = json!({"kind": "type", "name": "HOL.other", "types": []});
    item["specifications"] = json!([spec.clone()]);
    let result = classify_axioms(&inventory(vec![item])).unwrap();
    assert_eq!(result["entries"][0]["category"], "unclassified");
    assert_eq!(result["entries"][0]["associations"]["specifications"], json!([spec]));
}

#[test]
fn classify_axioms_candidate_conflicting_association_rejected() {
    let mut item = theory("HOL.HOL", "src/HOL/HOL.thy", &["HOL.fun_arity"]);
    item["specifications"] = json!([specification("HOL.fun_arity")]);
    error_contains(&inventory(vec![item]), "conflicting definition association");
}

#[test]
fn classify_axioms_missing_or_invalid_term_rejected() {
    let mut item = theory("HOL.HOL", "src/HOL/HOL.thy", &["HOL.refl"]);
    item["axioms"][0].as_object_mut().unwrap().remove("term");
    error_contains(&inventory(vec![item]), "Malformed axiom");
    let mut item = theory("HOL.HOL", "src/HOL/HOL.thy", &["HOL.refl"]);
    item["axioms"][0]["term"] = json!({"kind": "Const", "name": "HOL.True"});
    error_contains(&inventory(vec![item]), "Malformed axiom term atom");
}

#[test]
fn classify_axioms_empty_inventory_or_observation_rejected() {
    error_contains(&inventory(vec![]), "empty reference inventory");
    error_contains(
        &inventory(vec![theory("HOL.HOL", "src/HOL/HOL.thy", &[])]),
        "no observed axioms",
    );
}

#[test]
fn classify_axioms_malformed_subject_and_dependency_types_rejected() {
    for field in ["subject", "dependencies"] {
        for invalid in [Value::Null, json!({"kind": "Unknown"})] {
            let mut item = theory("HOL.HOL", "src/HOL/HOL.thy", &["HOL.defined_def"]);
            let mut spec = specification("HOL.defined_def");
            if field == "subject" {
                spec["subject"]["types"] = json!([invalid]);
            } else {
                spec["dependencies"][0]["types"] = json!([invalid]);
            }
            item["specifications"] = json!([spec]);
            error_contains(&inventory(vec![item]), "axiom type");
        }
    }
}
