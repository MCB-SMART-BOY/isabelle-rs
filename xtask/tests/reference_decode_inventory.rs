mod reference_decode_support;
use isabelle_evidence::{validate_entities, validate_graph};
use reference_decode_support::{Element, Fragment, element, write_source};
use serde_json::{Value, json};
use xtask::reference::{
    decode_inventory::{EXPECTED_THEORY_COUNT, ROOTS, decode_inventory},
    yxml,
};
const SECTIONS: [(&str, &str); 15] = [
    ("parents", "parent"),
    ("import_specifications", "import_specification"),
    ("default_sort", "sort"),
    ("types", "type_declaration"),
    ("classes", "class"),
    ("class_relations", "class_relation"),
    ("arities", "arity"),
    ("constants", "constant"),
    ("axioms", "axiom"),
    ("specifications", "specification"),
    ("constant_definitions", "constant_definition"),
    ("fact_indexes", "fact_index"),
    ("fact_groups", "fact_group"),
    ("named_derivations", "named_derivation"),
    ("oracle_registrations", "oracle_registration"),
];
fn reference_theory(name: &str, parent: Option<&str>) -> Element {
    let source = format!("/work/fixed-source/src/{name}.thy");
    let mut sections =
        SECTIONS.iter().map(|(section, _)| element(section, &[])).collect::<Vec<_>>();
    if let Some(parent) = parent {
        sections[0].body.push(Fragment::Node(element("parent", &[("name", parent)])));
    }
    if name == "HOL.HOL" {
        sections[11].body.push(Fragment::Node(element(
            "fact_index",
            &[
                ("name", "HOL.TrueI"),
                ("concealed", "false"),
                ("dynamic", "false"),
                ("origin", "HOL.HOL"),
            ],
        )));
        let term = element("term", &[]).nodes(vec![element("3", &[]).text("0")]);
        let theorem = element(
            "theorem",
            &[
                ("name", "HOL.TrueI"),
                ("index", "0"),
                ("owner", "HOL.HOL"),
                ("derivation_name", "HOL.TrueI"),
                ("has_skip_proof", "false"),
            ],
        )
        .nodes(vec![
            element("proposition", &[]).nodes(vec![term]),
            element("hypotheses", &[]),
            element("shyps", &[]),
            element("tpairs", &[]),
            element("dependencies", &[]),
            element("oracle_footprint", &[]),
        ]);
        sections[12].body.push(Fragment::Node(
            element("fact_group", &[("name", "HOL.TrueI")]).nodes(vec![theorem]),
        ));
    }
    element(
        "theory",
        &[("name", name), ("master_directory", "/work/fixed-source/src"), ("source", &source)],
    )
    .nodes(sections)
}
fn fixture() -> (tempfile::TempDir, Element, Value) {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path().join("fixed-source");
    let mut names = (0..57).map(|index| format!("Aux.{index:02}")).collect::<Vec<_>>();
    names.extend(ROOTS.map(str::to_owned));
    names.push("Pure".into());
    names.sort();
    let mut theories = vec![];
    let mut source_map = serde_json::Map::new();
    for name in &names {
        let relative = format!("src/{name}.thy");
        let symbolic = format!("/work/fixed-source/{relative}");
        write_source(&root, &relative, format!("theory {name}\n").as_bytes());
        source_map.insert(name.clone(), json!({"source":symbolic}));
        let parent = if name == "Pure" {
            None
        } else if name == "Aux.00" {
            Some("Pure")
        } else if let Some(number) = name.strip_prefix("Aux.") {
            let index = number.parse::<usize>().expect("Aux number");
            Some(
                names
                    .iter()
                    .find(|candidate| candidate.as_str() == format!("Aux.{:02}", index - 1))
                    .expect("Aux predecessor")
                    .as_str(),
            )
        } else if name == "HOL.HOL" {
            Some("Aux.56")
        } else {
            Some("HOL.HOL")
        };
        theories.push(reference_theory(name, parent));
    }
    let observed = [
        "static_theory_snapshot",
        "raw_named_static_facts",
        "registered_oracles",
        "transitive_oracle_footprints",
        "named_theorem_dependencies",
    ];
    let unavailable = [
        "executed_commands",
        "ML_load_events",
        "resource_load_events",
        "anonymous_ephemeral_facts",
        "unregistered_proof_steps",
        "external_process_events",
        "dynamic_fact_evaluations",
    ];
    let coverage = element("coverage", &[]).nodes(
        observed
            .iter()
            .map(|value| element("observed", &[]).text(value))
            .chain(unavailable.iter().map(|value| element("unavailable", &[]).text(value)))
            .collect(),
    );
    let snapshot =
        element("reference_snapshot", &[("version", "1"), ("reference", "Isabelle2025")]).nodes(
            vec![
                element("roots", &[])
                    .nodes(ROOTS.iter().map(|root| element("root", &[("name", root)])).collect()),
                coverage,
                element("theories", &[]).nodes(theories),
            ],
        );
    (temp, snapshot, Value::Object(source_map))
}
#[test]
fn inventory_complete_fixed_closure_preserves_structural_observation() {
    let (temp, snapshot, source_map) = fixture();
    let decoded =
        decode_inventory(&snapshot.serialize(), &temp.path().join("fixed-source"), &source_map)
            .expect("complete closure");
    assert_eq!(decoded["theories"].as_array().expect("theories").len(), EXPECTED_THEORY_COUNT);
    assert_eq!(
        decoded["source_sha256"].as_object().expect("manifest").len(),
        EXPECTED_THEORY_COUNT
    );
    let hol = decoded["theories"]
        .as_array()
        .expect("theories")
        .iter()
        .find(|item| item["name"] == "HOL.HOL")
        .expect("HOL");
    assert_eq!(
        hol["fact_groups"][0]["theorems"][0]["proposition"],
        json!({"kind":"Bound","index":0})
    );
    assert_eq!(hol["source"], "src/HOL.HOL.thy");
    assert_eq!(decoded["coverage"]["unavailable"][0], "executed_commands");
}
#[test]
fn inventory_rejects_incomplete_graph_and_forged_coverage() {
    let (temp, snapshot, source_map) = fixture();
    let root = temp.path().join("fixed-source");
    let mut cases = vec![];
    let mut case = snapshot.clone();
    case.node(2).body.pop();
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(0).body.pop();
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(1).body.pop();
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(2).body.reverse();
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(2).node(0).node(0).node(0).set("name", "Aux.00");
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(2).node(0).node(0).node(0).set("name", "Unknown");
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(2).node(0).node(2).attrs.push(("not_supported".into(), "true".into()));
    cases.push(case);
    for (index, case) in cases.into_iter().enumerate() {
        assert!(
            decode_inventory(&case.serialize(), &root, &source_map).is_err(),
            "graph/coverage mutation {index} accepted"
        );
    }
}
#[test]
fn inventory_rejects_source_mapping_spoof_and_encoded_term_errors() {
    let (temp, snapshot, source_map) = fixture();
    let root = temp.path().join("fixed-source");
    let mut case = snapshot.clone();
    case.node(2).node(0).set("source", "/work/fixed-source/src/../src/Aux.00.thy");
    assert!(decode_inventory(&case.serialize(), &root, &source_map).is_err());
    let mut case = snapshot.clone();
    case.node(2).node(0).set("source", "/work/fixed-source/src/Aux.01.thy");
    assert!(decode_inventory(&case.serialize(), &root, &source_map).is_err());
    let mut case = snapshot.clone();
    let hol = case
        .node(2)
        .body
        .iter_mut()
        .filter_map(|part| match part {
            Fragment::Node(node) if node.attrs[0].1 == "HOL.HOL" => Some(node),
            _ => None,
        })
        .next()
        .expect("HOL");
    hol.node(12).node(0).node(0).node(0).node(0).tag = "6".into();
    assert!(decode_inventory(&case.serialize(), &root, &source_map).is_err());
    let duplicate = "\u{5}\u{6}reference_snapshot\u{6}version=1\u{6}version=2\u{5}\u{5}\u{6}\u{5}";
    assert!(yxml::parse(duplicate).is_err());
}
#[test]
fn inventory_rejects_reversed_xml_encode_variant_attribute_vector() {
    let (temp, mut snapshot, source_map) = fixture();
    let root = temp.path().join("fixed-source");
    let hol = snapshot
        .node(2)
        .body
        .iter_mut()
        .filter_map(|part| match part {
            Fragment::Node(node) if node.attrs[0].1 == "HOL.HOL" => Some(node),
            _ => None,
        })
        .next()
        .expect("HOL");
    let variant = hol.node(12).node(0).node(0).node(0).node(0).node(0);
    *variant = element("2", &[("0", "x"), ("1", "0")]).nodes(vec![element("0", &[("0", "prop")])]);
    let decoded =
        decode_inventory(&snapshot.serialize(), &root, &source_map).expect("ordered variant");
    let hol = decoded["theories"]
        .as_array()
        .expect("theories")
        .iter()
        .find(|item| item["name"] == "HOL.HOL")
        .expect("HOL");
    assert_eq!(hol["fact_groups"][0]["theorems"][0]["proposition"]["kind"], "Var");
    let hol = snapshot
        .node(2)
        .body
        .iter_mut()
        .filter_map(|part| match part {
            Fragment::Node(node) if node.attrs[0].1 == "HOL.HOL" => Some(node),
            _ => None,
        })
        .next()
        .expect("HOL");
    hol.node(12).node(0).node(0).node(0).node(0).node(0).attrs.reverse();
    assert!(decode_inventory(&snapshot.serialize(), &root, &source_map).is_err());
}
#[test]
fn inventory_semantic_validator_rejects_unknown_dependencies() {
    let (temp, snapshot, source_map) = fixture();
    let root = temp.path().join("fixed-source");
    let decoded =
        decode_inventory(&snapshot.serialize(), &root, &source_map).expect("complete closure");
    let mut theories = decoded["theories"].clone();
    assert!(validate_graph(theories.as_array().unwrap()).is_ok());
    assert!(validate_entities(theories.as_array().unwrap()).is_ok());
    let hol = theories
        .as_array_mut()
        .expect("theories")
        .iter_mut()
        .find(|item| item["name"] == "HOL.HOL")
        .expect("HOL");
    hol["fact_groups"][0]["theorems"][0]["dependencies"] =
        json!([{"name":"HOL.Unknown","index":0,"origin":"HOL.HOL","serial":42}]);
    assert!(validate_entities(theories.as_array().unwrap()).is_err());
}
