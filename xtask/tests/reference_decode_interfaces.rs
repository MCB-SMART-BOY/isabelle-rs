mod reference_decode_support;
use reference_decode_support::{Element, Fragment, element};
use serde_json::{Value, json};
use xtask::reference::{decode_interfaces::decode_interfaces, decode_inventory::ROOTS};
const STRUCTURES: [&str; 17] = [
    "Thm",
    "Type",
    "Sign",
    "Consts",
    "Defs",
    "Theory",
    "Context",
    "Proofterm",
    "ML_Compiler",
    "ML_Env",
    "ML_Name_Space",
    "ML_Context",
    "Thread",
    "OS",
    "TextIO",
    "BinIO",
    "PolyML",
];
fn unavailable() -> Element {
    element("declaration_position", &[("availability", "unavailable")])
}
fn structure(name: &str, value_name: &str, parent: &str) -> Element {
    let path = if parent.is_empty() { name.into() } else { format!("{parent}.{name}") };
    element("structure", &[("name", name), ("path", &path), ("availability", "available")]).nodes(
        vec![
            unavailable(),
            element("values", &[]).nodes(vec![
                element("value", &[("name", value_name), ("type_print_depth", "40")])
                    .nodes(vec![unavailable(), element("type_text", &[]).text("cterm -> thm")]),
            ]),
            element("type_constructors", &[]).nodes(vec![
                element("type_constructor", &[("name", "thm")]).nodes(vec![unavailable()]),
            ]),
            element("signatures", &[]),
            element("functors", &[]),
            element("structures", &[]),
        ],
    )
}
fn theory(name: &str) -> Element {
    let structures = STRUCTURES
        .into_iter()
        .map(|structure_name| {
            if structure_name == "Thm" {
                structure("Thm", "assume", "")
            } else {
                element(
                    "structure",
                    &[
                        ("name", structure_name),
                        ("path", structure_name),
                        ("availability", "unavailable"),
                        ("reason", "not_in_theory_namespace"),
                    ],
                )
            }
        })
        .collect();
    let mut namespace = ["values", "type_constructors", "signatures", "functors"]
        .map(|group| element(group, &[]))
        .to_vec();
    namespace.push(element("selected_structures", &[]).nodes(structures));
    element("theory", &[("name", name)]).nodes(vec![
        element("commands", &[]).nodes(
            ["theory", "end"]
                .into_iter()
                .map(|command| {
                    element(
                        "command",
                        &[
                            ("name", command),
                            ("kind", "thy_end"),
                            ("registration", "at_end_checked"),
                        ],
                    )
                })
                .collect(),
        ),
        element(
            "ml_abi",
            &[("read_global", if name == "ML_Bootstrap" { "false" } else { "true" })],
        )
        .nodes(namespace),
    ])
}
fn setup() -> (Element, Value, Value) {
    let names = std::iter::once("Pure").chain(ROOTS).collect::<Vec<_>>();
    let inventory = json!({"roots":ROOTS,"theories":names.iter().map(|name|json!({"name":name})).collect::<Vec<_>>()});
    let execution = json!({"roots":ROOTS,"theories":ROOTS.iter().map(|name|json!({"name":name,"commands":[{"name":"theory"},{"name":"end"}]})).collect::<Vec<_>>()});
    let coverage = element("coverage", &[]).nodes(
        [
            ("observed", "theory_scoped_command_keywords_and_kinds"),
            ("observed", "selected_public_ml_namespace_declarations"),
            ("unavailable", "runtime_call_graph"),
            ("unavailable", "signature_and_functor_members"),
            ("unavailable", "private_bootstrap_runtime_structures"),
        ]
        .into_iter()
        .map(|(tag, name)| element(tag, &[("name", name)]))
        .collect(),
    );
    let snapshot = element(
        "interface_snapshot",
        &[
            ("version", "1"),
            ("reference", "Isabelle2025"),
            ("authorization", "none_reference_requirements_only"),
            ("type_text_semantics", "display_only_not_structural_type_identity"),
            ("namespace_semantics", "theory_tables_with_current_global_fallback_when_enabled"),
        ],
    )
    .nodes(vec![
        element("roots", &[])
            .nodes(ROOTS.into_iter().map(|name| element("root", &[("name", name)])).collect()),
        coverage,
        element("theories", &[]).nodes(names.iter().map(|name| theory(name)).collect()),
        element("bootstrap_interfaces", &[]).nodes(vec![theory("ML_Bootstrap")]),
    ]);
    (snapshot, inventory, execution)
}
fn thm(snapshot: &mut Element) -> &mut Element {
    snapshot.node(2).node(1).node(1).node(4).node(0)
}
fn decode(
    snapshot: &Element,
    inventory: &Value,
    execution: &Value,
) -> Result<Value, xtask::runner::StepError> {
    decode_interfaces(&snapshot.serialize(), inventory, execution)
}
#[test]
fn interfaces_preserve_theory_local_bindings_and_bootstrap_boundary() {
    let (mut snapshot, inventory, execution) = setup();
    snapshot.node(2).node(9).node(1).node(4).body[0] =
        Fragment::Node(structure("Thm", "local_assume", ""));
    let decoded = decode(&snapshot, &inventory, &execution).expect("valid namespace");
    assert_eq!(
        decoded["theories"][9]["ml_abi"]["selected_structures"][0]["values"][0]["name"],
        "local_assume"
    );
    assert_eq!(
        decoded["theories"][0]["ml_abi"]["selected_structures"][0]["values"][0]["name"],
        "assume"
    );
    assert_eq!(decoded["bootstrap_interfaces"][0]["ml_abi"]["read_global"], false);
    assert_eq!(
        decoded["namespace_semantics"],
        "theory_tables_with_current_global_fallback_when_enabled"
    );
    assert_eq!(decoded["type_text_semantics"], "display_only_not_structural_type_identity");
    assert_eq!(decoded["coverage"]["unavailable"][0], "runtime_call_graph");
}
#[test]
fn interfaces_nested_public_structures_preserve_host_requirements() {
    let (mut snapshot, inventory, execution) = setup();
    let selected = &mut snapshot.node(2).node(1).node(1).node(4).body;
    let mut context = structure("Context", "theory_name", "");
    context.node(5).body.push(Fragment::Node(structure("Proof_Context", "init_global", "Context")));
    let mut polyml = structure("PolyML", "compiler", "");
    polyml.node(5).body.extend(
        [
            structure("Compiler", "CPNameSpace", "PolyML"),
            structure("SaveState", "saveState", "PolyML"),
        ]
        .into_iter()
        .map(Fragment::Node),
    );
    selected[STRUCTURES.iter().position(|name| *name == "Context").expect("Context")] =
        Fragment::Node(context);
    selected[STRUCTURES.iter().position(|name| *name == "PolyML").expect("PolyML")] =
        Fragment::Node(polyml);
    let decoded = decode(&snapshot, &inventory, &execution).expect("nested namespace");
    assert_eq!(
        decoded["theories"][1]["ml_abi"]["selected_structures"][6]["structures"][0]["path"],
        "Context.Proof_Context"
    );
    assert_eq!(
        decoded["theories"][1]["ml_abi"]["selected_structures"][16]["structures"][1]["values"][0]["name"],
        "saveState"
    );
}
#[test]
fn interfaces_forged_coverage_and_missing_bindings_rejected() {
    let (snapshot, inventory, execution) = setup();
    let mut cases = vec![];
    let mut case = snapshot.clone();
    case.node(2).body.pop();
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(2).node(1).node(1).node(4).body.pop();
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(2).node(1).node(0).body.pop();
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(2).node(1).node(0).node(0).set("registration", "keyword_only_bootstrap");
    cases.push(case);
    let mut case = snapshot.clone();
    let duplicate = thm(&mut case).node(1).body[0].clone();
    thm(&mut case).node(1).body.push(duplicate);
    cases.push(case);
    let mut case = snapshot.clone();
    thm(&mut case).set("path", "Other.Thm");
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(3).body.clear();
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(3).node(0).node(1).set("read_global", "true");
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(2).node(1).node(1).set("read_global", "unknown");
    cases.push(case);
    let mut case = snapshot.clone();
    thm(&mut case).node(0).set("availability", "assumed");
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(1).body.pop();
    cases.push(case);
    for (index, case) in cases.into_iter().enumerate() {
        assert!(decode(&case, &inventory, &execution).is_err(), "forgery {index} accepted");
    }
}
#[test]
fn interfaces_nested_structure_identity_and_order_rejected() {
    let (snapshot, inventory, execution) = setup();
    for mutation in ["parent_path", "duplicate", "unordered"] {
        let mut case = snapshot.clone();
        let mut children = vec![structure("A", "a", "Thm"), structure("B", "b", "Thm")];
        match mutation {
            "parent_path" => children[0].set("path", "Other.A"),
            "duplicate" => children.push(children[0].clone()),
            _ => children.reverse(),
        };
        thm(&mut case).node(5).body.extend(children.into_iter().map(Fragment::Node));
        assert!(
            decode(&case, &inventory, &execution).is_err(),
            "nested mutation {mutation} accepted"
        );
    }
}
