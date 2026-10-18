mod reference_decode_support;
use reference_decode_support::{
    Element, command, element, sha1_hex, source_workspace, write_source,
};
use serde_json::Value;
use xtask::reference::{decode_execution::decode_execution, decode_inventory::ROOTS};

fn snapshot(inventory: &Value, root: &std::path::Path, resource: &str) -> Element {
    let source_resource = root.join(resource);
    let sha1 = sha1_hex(&std::fs::read(source_resource).expect("fixture resource"));
    let theories = inventory["theories"]
        .as_array()
        .expect("fixture theories")
        .iter()
        .filter(|item| item["name"] != "Pure")
        .map(|item| {
            let name = item["name"].as_str().expect("name");
            let relative = item["source"].as_str().expect("source");
            let prefix = if name == "HOL.HOL" { "$ISABELLE_HOME/" } else { "/work/fixed-source/" };
            let source = format!("{prefix}{relative}");
            let mut commands = vec![command("theory", &source, "1", "1", vec![])];
            if name == "HOL.HOL" {
                commands.push(command(
                    "ML_file",
                    &source,
                    "2",
                    "10",
                    vec![element(
                        "file",
                        &[("path", "$ISABELLE_HOME/src/HOL/Tools/probe.ML"), ("sha1", &sha1)],
                    )],
                ));
            }
            commands.push(command("end", &source, "3", "20", vec![]));
            element("theory", &[("name", name), ("source", &source)]).nodes(commands)
        })
        .chain(std::iter::once({
            let source = "/work/session/Reference_Observer.thy";
            element(
                "theory",
                &[("name", "Reference_Execution.Reference_Observer"), ("source", source)],
            )
            .nodes(vec![command(
                "ML_file",
                source,
                "1",
                "1",
                vec![element(
                    "file",
                    &[("path", "/work/session/Reference_Observer.ML"), ("sha1", &"0".repeat(40))],
                )],
            )])
        }))
        .collect();
    element(
        "execution_snapshot",
        &[("version", "1"), ("reference", "Isabelle2025"), ("session", "Reference_Execution")],
    )
    .nodes(vec![
        element("roots", &[])
            .nodes(ROOTS.iter().map(|name| element("root", &[("name", name)])).collect()),
        element("initial_theories", &[]).nodes(
            ["Pure", "ML_Bootstrap", "Pure.Sessions"]
                .iter()
                .map(|name| element("theory", &[("name", name)]))
                .collect(),
        ),
        element("theories", &[]).nodes(theories),
    ])
}
fn hol(snapshot: &mut Element) -> &mut Element {
    snapshot.node(2).node(0)
}
fn setup() -> (tempfile::TempDir, Value, String, Element) {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path().join("fixed-source");
    let (inventory, resource) = source_workspace(&root);
    let raw = snapshot(&inventory, &root, &resource);
    (temp, inventory, resource, raw)
}
#[test]
fn execution_complete_observation_preserves_files_and_unavailable_coverage() {
    let (temp, inventory, resource, mut snapshot) = setup();
    snapshot.node(2).body.reverse();
    let decoded =
        decode_execution(&snapshot.serialize(), &temp.path().join("fixed-source"), &inventory)
            .expect("complete execution");
    assert_eq!(decoded["theories"].as_array().expect("theories").len(), ROOTS.len());
    assert_eq!(decoded["theories"][0]["name"], "HOL.Fun");
    let hol = decoded["theories"]
        .as_array()
        .expect("theories")
        .iter()
        .find(|item| item["name"] == "HOL.HOL")
        .expect("HOL.HOL");
    assert_eq!(
        hol["commands"]
            .as_array()
            .expect("commands")
            .iter()
            .map(|item| item["name"].as_str().expect("command name"))
            .collect::<Vec<_>>(),
        ["theory", "ML_file", "end"]
    );
    assert_eq!(hol["commands"][1]["sequence"], 2);
    assert_eq!(
        hol["commands"][1]["files"][0]["sha1"],
        sha1_hex(
            &std::fs::read(temp.path().join("fixed-source").join(resource)).expect("resource")
        )
    );
    assert_eq!(
        decoded["coverage"]["unavailable"],
        serde_json::json!([
            "Pure_bootstrap_command_spans",
            "anonymous_ephemeral_facts",
            "unregistered_proof_steps",
            "dynamic_fact_evaluations",
            "ML_runtime_call_graph",
            "implicit_ML_load_events"
        ])
    );
    assert_eq!(
        decoded["coverage"]["ordering"],
        "per_theory_source_segments_not_global_thread_order"
    );
}
#[test]
fn execution_incomplete_foreign_and_skipped_observations_rejected() {
    let (temp, inventory, _, snapshot) = setup();
    let root = temp.path().join("fixed-source");
    let mut cases = vec![];
    let mut case = snapshot.clone();
    case.node(2).body.pop();
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(0).body.pop();
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(1).body.reverse();
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(1).body.pop();
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(1)
        .body
        .push(reference_decode_support::Fragment::Node(element("theory", &[("name", "HOL.HOL")])));
    cases.push(case);
    let mut case = snapshot.clone();
    let repeated = case.node(2).body[0].clone();
    case.node(2).body.push(repeated);
    cases.push(case);
    let mut case = snapshot.clone();
    hol(&mut case).body.pop();
    cases.push(case);
    let mut case = snapshot.clone();
    hol(&mut case).body.clear();
    cases.push(case);
    let mut case = snapshot.clone();
    hol(&mut case).node(0).set("skipped", "true");
    cases.push(case);
    let mut case = snapshot.clone();
    hol(&mut case).node(0).set("source", "/work/fixed-source/src/HOL/Set.thy");
    cases.push(case);
    let mut case = snapshot.clone();
    hol(&mut case).node(1).set("offset", "1");
    cases.push(case);
    let mut case = snapshot.clone();
    hol(&mut case).node(0).set("line", "0");
    cases.push(case);
    let mut case = snapshot.clone();
    hol(&mut case)
        .body
        .push(reference_decode_support::Fragment::Node(element("unrecognized", &[])));
    cases.push(case);
    let mut case = snapshot.clone();
    hol(&mut case).node(1).node(0).attrs.push(("unexpected".into(), "yes".into()));
    cases.push(case);
    let mut case = snapshot.clone();
    hol(&mut case).node(1).body.clear();
    cases.push(case);
    let mut case = snapshot.clone();
    let file = hol(&mut case).node(1).body[0].clone();
    hol(&mut case).node(0).body.push(file);
    cases.push(case);
    let mut case = snapshot.clone();
    case.node(2).body.pop();
    cases.push(case);
    for (index, case) in cases.into_iter().enumerate() {
        assert!(
            decode_execution(&case.serialize(), &root, &inventory).is_err(),
            "mutation {index} accepted"
        );
    }
}
#[test]
fn execution_resource_variants_and_theory_preamble_preserved() {
    let (temp, inventory, _, snapshot) = setup();
    let root = temp.path().join("fixed-source");
    for name in [
        "ML_file",
        "ML_file_debug",
        "ML_file_no_debug",
        "SML_file",
        "SML_file_debug",
        "SML_file_no_debug",
    ] {
        let mut case = snapshot.clone();
        hol(&mut case).node(1).set("name", name);
        let decoded =
            decode_execution(&case.serialize(), &root, &inventory).expect("resource command");
        assert_eq!(
            decoded["theories"]
                .as_array()
                .expect("theories")
                .iter()
                .find(|item| item["name"] == "HOL.HOL")
                .expect("HOL")["commands"][1]["name"],
            name
        );
    }
    let mut case = snapshot.clone();
    let other = case.node(2).node(1);
    let source = other.attrs[1].1.clone();
    other.node(0).set("line", "2");
    other.node(0).set("offset", "10");
    other.body.insert(
        0,
        reference_decode_support::Fragment::Node(command("section", &source, "1", "1", vec![])),
    );
    let decoded = decode_execution(&case.serialize(), &root, &inventory).expect("preamble");
    assert_eq!(
        decoded["theories"]
            .as_array()
            .expect("theories")
            .iter()
            .find(|item| item["name"] == "HOL.Orderings")
            .expect("ordering")["commands"][0]["name"],
        "section"
    );
}
#[test]
fn execution_rejects_source_escape_symlink_hash_drift_and_theory_header_errors() {
    let (temp, inventory, resource, snapshot) = setup();
    let root = temp.path().join("fixed-source");
    let mut case = snapshot.clone();
    hol(&mut case).set("source", "/work/fixed-source/src/HOL/../../Pure/Pure.thy");
    assert!(decode_execution(&case.serialize(), &root, &inventory).is_err());
    let mut case = snapshot.clone();
    hol(&mut case).node(0).set("name", "section");
    assert!(decode_execution(&case.serialize(), &root, &inventory).is_err());
    let mut case = snapshot.clone();
    hol(&mut case).body.remove(0);
    assert!(decode_execution(&case.serialize(), &root, &inventory).is_err());
    let mut case = snapshot.clone();
    hol(&mut case).body.drain(..2);
    assert!(decode_execution(&case.serialize(), &root, &inventory).is_err());
    let mut case = snapshot.clone();
    hol(&mut case).node(1).set("name", "theory");
    hol(&mut case).node(1).body.clear();
    assert!(decode_execution(&case.serialize(), &root, &inventory).is_err());
    assert!(decode_execution("\u{5}\u{6}execution_snapshot\u{5}", &root, &inventory).is_err());
    let original = std::fs::read(root.join(&resource)).expect("resource");
    write_source(&root, &resource, b"val observed = false;\n");
    assert!(
        decode_execution(&snapshot.serialize(), &root, &inventory)
            .expect_err("SHA1 drift")
            .to_string()
            .contains("SHA1 drift")
    );
    write_source(&root, &resource, &original);
    write_source(
        &root,
        inventory["theories"][0]["source"].as_str().expect("source"),
        b"changed bootstrap",
    );
    assert!(
        decode_execution(&snapshot.serialize(), &root, &inventory)
            .expect_err("SHA256 drift")
            .to_string()
            .contains("SHA256 differs")
    );
}
#[cfg(unix)]
#[test]
fn execution_resource_symlink_escape_rejected() {
    use std::os::unix::fs::symlink;
    let (temp, inventory, resource, snapshot) = setup();
    let root = temp.path().join("fixed-source");
    let outside = temp.path().join("outside.ML");
    std::fs::write(&outside, b"val external = true;\n").expect("outside");
    std::fs::remove_file(root.join(&resource)).expect("remove resource");
    symlink(&outside, root.join(resource)).expect("symlink");
    assert!(decode_execution(&snapshot.serialize(), &root, &inventory).is_err());
}
