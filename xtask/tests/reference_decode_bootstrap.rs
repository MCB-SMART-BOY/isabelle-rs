mod reference_decode_support;
use reference_decode_support::{Element, element, sha1_hex, write_source};
use serde_json::{Value, json};
use xtask::reference::decode_bootstrap::decode_bootstrap;
const SOURCES: [&str; 2] = ["src/Pure/ROOT0.ML", "src/Pure/ROOT.ML"];
const PRELUDE: [&str; 4] = [
    "src/Pure/ML/ml_process.scala",
    "src/Pure/Build/build_job.scala",
    "src/Pure/ML/ml_name_space.ML",
    "src/Pure/Concurrent/thread_attributes.ML",
];
fn setup() -> (tempfile::TempDir, Element, Value) {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path().join("fixed-source");
    let mut records = vec![];
    let mut reads = vec![];
    for (index, source) in SOURCES.iter().enumerate() {
        let argument = format!("ML/phase{index}.ML");
        let content = format!("ML_file \"{argument}\";\n");
        write_source(&root, source, content.as_bytes());
        let loaded = format!("src/Pure/{argument}");
        write_source(&root, &loaded, b"val result = true;\n");
        let file = element(
            "file",
            &[
                ("path", &format!("/work/fixed-source/{loaded}")),
                ("sha1", &sha1_hex(b"val result = true;\n")),
            ],
        );
        let statement = element(
            "statement",
            &[("command", "ML_file"), ("kind", "load"), ("argument", &argument), ("line", "1")],
        )
        .nodes(vec![file]);
        records.push(
            element(
                "source",
                &[
                    ("path", &format!("/work/fixed-source/{source}")),
                    ("sha1", &sha1_hex(content.as_bytes())),
                ],
            )
            .nodes(vec![statement]),
        );
        for path in [*source, loaded.as_str()] {
            reads.push(json!({"source":path,"phase":"build","tid":5,"sequence":reads.len()+1,"timestamp":"1.0"}));
        }
    }
    for source in PRELUDE {
        write_source(&root, source, "source provenance fixture\n".repeat(160).as_bytes());
    }
    let snapshot = element(
        "bootstrap_snapshot",
        &[
            ("version", "1"),
            ("reference", "Isabelle2025"),
            ("semantics", "source_declared_order_not_call_trace"),
        ],
    )
    .nodes(records);
    (temp, snapshot, json!({"fixed_source_reads":reads}))
}
fn decode(
    temp: &tempfile::TempDir,
    snapshot: &Element,
    profile: &Value,
) -> Result<Value, xtask::runner::StepError> {
    decode_bootstrap(&snapshot.serialize(), &temp.path().join("fixed-source"), profile)
}
#[test]
fn bootstrap_ordered_sources_bind_only_build_observations() {
    let (temp, snapshot, profile) = setup();
    let decoded = decode(&temp, &snapshot, &profile).expect("valid bootstrap");
    assert_eq!(decoded["sources"][0]["source"], SOURCES[0]);
    assert_eq!(decoded["sources"][1]["source"], SOURCES[1]);
    assert_eq!(decoded["sources"][0]["statements"][0]["file"]["source"], "src/Pure/ML/phase0.ML");
    assert_eq!(decoded["sources"][1]["statements"][0]["file"]["build_reads"][0]["sequence"], 4);
    assert_eq!(decoded["ordering"], "source_declared_order_not_call_trace");
    assert_eq!(decoded["prelude_sources"][3]["line_end"], 160);
    assert_eq!(
        decoded["prelude_sources"][0]["evidence"],
        "audited_source_not_observed_ML_execution"
    );
}
#[test]
fn bootstrap_heading_preserves_source_declaration_order() {
    let (temp, mut snapshot, profile) = setup();
    snapshot.node(0).node(0).set("line", "2");
    snapshot.node(0).body.insert(
        0,
        reference_decode_support::Fragment::Node(element(
            "statement",
            &[
                ("command", "chapter"),
                ("kind", "heading"),
                ("argument", "Bootstrap"),
                ("line", "1"),
            ],
        )),
    );
    let result = decode(&temp, &snapshot, &profile).expect("heading");
    assert_eq!(result["sources"][0]["statements"][0]["kind"], "heading");
    assert_eq!(result["sources"][0]["statements"][1]["sequence"], 2);
}
#[test]
fn bootstrap_missing_or_inconsistent_provenance_rejected() {
    let (temp, snapshot, profile) = setup();
    let mut changed_profile = profile.clone();
    for item in changed_profile["fixed_source_reads"].as_array_mut().expect("reads") {
        item["phase"] = json!("inventory");
    }
    assert!(decode(&temp, &snapshot, &changed_profile).is_err());
    let root = temp.path().join("fixed-source");
    write_source(&root, "src/Pure/ML/phase0.ML", b"changed");
    assert!(decode(&temp, &snapshot, &profile).is_err());
    write_source(&root, "src/Pure/ML/phase0.ML", b"val result = true;\n");
    for (argument, label) in [("../../outside.ML", "escaping"), ("ML/phase1.ML", "foreign")] {
        let mut case = snapshot.clone();
        case.node(0).node(0).set("argument", argument);
        assert!(decode(&temp, &case, &profile).is_err(), "{label} argument accepted");
    }
    let mut case = snapshot.clone();
    case.body.reverse();
    assert!(decode(&temp, &case, &profile).is_err());
}
#[test]
fn bootstrap_rejects_wrong_statement_order_and_unavailable_read() {
    let (temp, snapshot, mut profile) = setup();
    let mut case = snapshot.clone();
    let repeated = case.node(0).body[0].clone();
    case.node(0).body.push(repeated);
    assert!(decode(&temp, &case, &profile).is_err());
    profile["fixed_source_reads"]
        .as_array_mut()
        .expect("reads")
        .retain(|item| item["source"] != "src/Pure/ROOT.ML");
    assert!(decode(&temp, &snapshot, &profile).is_err());
    let mut case = snapshot.clone();
    case.node(0).node(0).set("kind", "heading");
    assert!(decode(&temp, &case, &json!({"fixed_source_reads":[]})).is_err());
}
