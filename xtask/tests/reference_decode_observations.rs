mod reference_decode_support;
use reference_decode_support::{element, write_source};
use serde_json::{Value, json};
use xtask::reference::decode_observations::decode_fact_origins;

fn observed_run() -> (tempfile::TempDir, String, Value) {
    let temp = tempfile::tempdir().expect("tempdir");
    write_source(temp.path(), "src/HOL/HOL.thy", b"theory HOL\n");
    let origin = element(
        "fact_group",
        &[
            ("theory", "HOL.HOL"),
            ("sequence", "2"),
            ("source", "/work/fixed-source/src/HOL/HOL.thy"),
            ("operation", "theorem"),
            ("name", "HOL.TrueI"),
        ],
    );
    let raw = element("fact_observations", &[("version", "1"), ("session", "Reference_Execution")])
        .nodes(vec![origin])
        .serialize();
    let execution = json!({"theories":[{"name":"HOL.HOL","commands":[
        {"sequence":2,"name":"theorem","source":"src/HOL/HOL.thy"}
    ]}]});
    (temp, raw, execution)
}

#[test]
fn decode_fact_origins_real_command_retains_partial_coverage() {
    let (root, raw, execution) = observed_run();
    let decoded = decode_fact_origins(&raw, root.path(), &execution).expect("decode");
    assert_eq!(decoded["observations"][0]["fact_group_name"], "HOL.TrueI");
    assert_eq!(decoded["observations"][0]["execution_event"], 2);
    assert_eq!(decoded["completeness"], "partial_completed_command_states_only");
}

#[test]
fn decode_fact_origins_foreign_command_or_source_rejects() {
    let (root, raw, mut execution) = observed_run();
    execution["theories"][0]["commands"][0]["name"] = json!("definition");
    assert!(decode_fact_origins(&raw, root.path(), &execution).is_err());
    execution["theories"][0]["commands"][0]["name"] = json!("theorem");
    execution["theories"][0]["commands"][0]["source"] = json!("src/HOL/Other.thy");
    assert!(decode_fact_origins(&raw, root.path(), &execution).is_err());
}
