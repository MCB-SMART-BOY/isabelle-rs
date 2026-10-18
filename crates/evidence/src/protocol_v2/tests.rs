use super::raw;
use super::{
    ApprovedObserverIdentity, ObserverHostInputs, ObserverRecordInputs, validate_bootstrap,
    validate_observer_records, validate_runs, validate_sources,
};
use serde_json::{Value, json};
use std::collections::BTreeMap;

const COMMIT: &str = "765fb2460a57eb46e8490283241ad46f1fac857f";
const TEST_MAX_DEPTH: usize = 64;

fn hash(symbol: char) -> String {
    symbol.to_string().repeat(64)
}

fn make_approval() -> (Value, Value, Value, BTreeMap<String, String>) {
    let original = hash('a');
    let observer = hash('d');
    let approved_patch = json!({"path":"session/reference_observation.ML",
        "original_sha256":null,"patched_sha256":observer,"patch_sha256":hash('c')});
    let budget = json!({"memory_bytes":1024,"swap_bytes":0,"pids":1,
        "cpu_quota_us":1,"cpu_period_us":1,"wall_seconds":1,
        "scratch_bytes":1024,"raw_total_bytes":1024,"decoded_total_bytes":1024,
        "max_artifacts":6,"max_events":20,"max_depth":8});
    let pre = json!({"schema_version":1,"purpose":"instrumented_reference_preapproval",
        "source_commit":COMMIT,"p0_manifest_sha256":hash('b'),"overlay_id":hash('c'),
        "observer_sha256":observer,"generator_sha256":hash('e'),
        "approved_patch_sha256":[approved_patch.clone()],"isabelle_binary_sha256":hash('f'),
        "threat_model":"trusted_same_uid","resource_budget":budget});
    let mut post = pre.clone();
    post["purpose"] = json!("instrumented_reference_approval");
    post["preapproval_sha256"] = json!(hash('a'));
    post["approved_manifest_sha256"] = json!(hash('b'));
    post["approved_run_root"] = json!("/approved/run");
    post["receipt_sha256"] = json!(hash('c'));
    let manifest = json!({"source_files":[{"path":"src/Pure/ROOT.ML","sha256":original}],
        "overlay":{"id":hash('c'),"patches":[approved_patch],
            "observer_sha256":hash('d'),"generator_sha256":hash('e')}});
    let sources = BTreeMap::from([("src/Pure/ROOT.ML".to_owned(), hash('a'))]);
    (pre, post, manifest, sources)
}

fn approve(
    pre: &Value,
    post: &Value,
    manifest: &Value,
    sources: BTreeMap<String, String>,
) -> Result<ApprovedObserverIdentity, crate::EvidenceError> {
    ApprovedObserverIdentity::from_verified_host(ObserverHostInputs {
        preapproval: pre,
        approval: post,
        preapproval_sha256: &hash('a'),
        manifest_sha256: &hash('b'),
        receipt_sha256: &hash('c'),
        run_root: "/approved/run",
        original_sources: sources,
        manifest,
    })
}

#[test]
fn approved_identity_wrong_postapproval_manifest_rejects() {
    let (pre, mut post, manifest, sources) = make_approval();
    post["approved_manifest_sha256"] = json!(hash('f'));
    assert!(approve(&pre, &post, &manifest, sources).is_err());
}

#[test]
fn approved_identity_budget_over_limit_rejects() {
    let (mut pre, mut post, manifest, sources) = make_approval();
    pre["resource_budget"]["max_events"] = json!(2_000_001);
    post["resource_budget"] = pre["resource_budget"].clone();
    assert!(approve(&pre, &post, &manifest, sources).is_err());
}

#[test]
fn validate_sources_patched_bootstrap_checks_original_and_executed_hashes() {
    let (mut pre, mut post, mut manifest, sources) = make_approval();
    let patch = json!({"path":"src/Pure/ROOT.ML","original_sha256":hash('a'),
        "patched_sha256":hash('f'),"patch_sha256":hash('b')});
    pre["approved_patch_sha256"] = json!([pre["approved_patch_sha256"][0], patch]);
    post["approved_patch_sha256"] = pre["approved_patch_sha256"].clone();
    manifest["overlay"]["patches"] = pre["approved_patch_sha256"].clone();
    let approved = approve(&pre, &post, &manifest, sources).unwrap();
    let executed = validate_sources(&manifest, &approved).unwrap();
    assert_eq!(executed["src/Pure/ROOT.ML"], hash('f'));
    assert_eq!(executed["session/reference_observation.ML"], hash('d'));
    manifest["overlay"]["patches"][1]["original_sha256"] = json!(hash('c'));
    assert!(validate_sources(&manifest, &approved).is_err());
}

#[test]
fn validate_sources_unlisted_new_observer_or_changed_bytes_rejects() {
    let (pre, post, mut manifest, sources) = make_approval();
    let approved = approve(&pre, &post, &manifest, sources).unwrap();
    manifest["overlay"]["patches"] = json!([]);
    assert!(validate_sources(&manifest, &approved).is_err());
    manifest["overlay"]["patches"] = pre["approved_patch_sha256"].clone();
    manifest["source_files"][0]["sha256"] = json!(hash('b'));
    assert!(validate_sources(&manifest, &approved).is_err());
}

fn make_runs() -> (Value, Value, Value) {
    let entry = |phase: &str, id: &str| {
        json!({"phase":phase,"run_id":id,
        "prepared_sha256":hash('a'),"source_snapshot_sha256":hash('a'),
        "heap_tree_sha256":hash('b'),"command_sha256":hash('c'),"result_sha256":hash('d')})
    };
    let manifest = json!({"runs":[entry("build","build-id"),entry("inventory","inventory-id")]});
    let inventory = json!({"run_id":"inventory-id", "loaded_pure_heap_tree_sha256":hash('b'),
        "initial_theories":["Pure"]});
    let execution = json!({"run_id":"inventory-id","initial_theories":["Pure"]});
    (manifest, inventory, execution)
}

#[test]
fn validate_runs_build_heap_inherited_but_swapped_inventory_rejects() {
    let (mut manifest, inventory, execution) = make_runs();
    assert!(validate_runs(&manifest, &inventory, &execution).is_ok());
    manifest["runs"][1]["heap_tree_sha256"] = json!(hash('a'));
    assert!(validate_runs(&manifest, &inventory, &execution).is_err());
    manifest["runs"][1]["heap_tree_sha256"] = json!(hash('b'));
    manifest["runs"][1]["run_id"] = json!("build-id");
    assert!(validate_runs(&manifest, &inventory, &execution).is_err());
}

fn tlv(fields: &[&[u8]]) -> Vec<u8> {
    let mut payload = format!("{}\n", fields.len()).into_bytes();
    for field in fields {
        payload.extend(format!("{}\n", field.len()).as_bytes());
        payload.extend(*field);
    }
    payload
}

fn frame(fields: &[&[u8]]) -> Vec<u8> {
    let payload = tlv(fields);
    let mut framed = format!("{}\n", payload.len()).into_bytes();
    framed.extend(payload);
    framed
}

#[test]
fn validate_bootstrap_immutable_use_never_claims_actual_consumption() {
    let source = b"src/Pure/ROOT0.ML";
    let payload = tlv(&[source, b"", b"Pure", b"Pure", b"1", b"immutable_bootstrap_use", b""]);
    let begin = frame(&[b"bootstrap", b"load_begin", b"build-id", b"root0", b"begin", &payload]);
    let end = frame(&[b"bootstrap", b"load_end", b"build-id", b"root0", b"end", &payload]);
    let seal = frame(&[b"bootstrap", b"load_seal", b"build-id", b"root0", b"seal", &payload]);
    let mut bytes = begin;
    bytes.extend(end);
    bytes.extend(seal);
    let frames = raw::parse_frames(&bytes, 3).unwrap();
    let load = json!({"run_id":"build-id","load_id":"root0","source":"src/Pure/ROOT0.ML",
        "source_sha256":hash('a'),"source_provenance":"immutable_bootstrap_use",
        "session":"Pure","theory":"Pure","source_order":1,"parent_load_id":null,
        "started":true,"finished":true,"sealed":true,
        "raw_begin_index":0,"raw_begin_sha256":frames[0].sha256,
        "raw_record_index":1,"raw_frame_sha256":frames[1].sha256,
        "raw_seal_index":2,"raw_seal_sha256":frames[2].sha256});
    let bootstrap = json!({"schema_version":2,"source_commit":COMMIT,"overlay_id":hash('c'),
        "loads":[load],"events":[]});
    let sources = BTreeMap::from([("src/Pure/ROOT0.ML".into(), hash('a'))]);
    assert!(
        !validate_bootstrap(
            &bootstrap,
            &frames,
            "build-id",
            "inventory-id",
            &sources,
            TEST_MAX_DEPTH
        )
        .unwrap()
    );
    let mut unsealed = bootstrap.clone();
    unsealed["loads"][0]["sealed"] = json!(false);
    unsealed["loads"][0].as_object_mut().unwrap().remove("raw_seal_index");
    unsealed["loads"][0].as_object_mut().unwrap().remove("raw_seal_sha256");
    assert!(
        !validate_bootstrap(
            &unsealed,
            &frames,
            "build-id",
            "inventory-id",
            &sources,
            TEST_MAX_DEPTH
        )
        .unwrap()
    );
    unsealed["loads"][0]["theory"] = json!("forged");
    assert!(
        validate_bootstrap(
            &unsealed,
            &frames,
            "build-id",
            "inventory-id",
            &sources,
            TEST_MAX_DEPTH
        )
        .is_err()
    );
    let mut tampered = bootstrap;
    tampered["loads"][0]["source_provenance"] = json!("actual_read_bytes");
    assert!(
        validate_bootstrap(
            &tampered,
            &frames,
            "build-id",
            "inventory-id",
            &sources,
            TEST_MAX_DEPTH
        )
        .is_err()
    );
}

#[test]
fn validate_observer_records_absent_six_fields_remains_incomplete() {
    let observer = json!({"schema_version":2,"source_commit":COMMIT,
        "overlay_id":hash('c'),"records":[],"coverage":[]});
    let closure = json!({"schema_version":2,"source_commit":COMMIT,"fields":{}});
    let execution = json!({"theories":[]});
    let missing = validate_observer_records(
        &observer,
        &closure,
        ObserverRecordInputs {
            frames: &[],
            build: "build-id",
            inventory: "inventory-id",
            executed: &BTreeMap::new(),
            bootstrap: &json!({}),
            reference_inventory: &json!({}),
            execution: &execution,
            is_bootstrap_verified: false,
            max_depth: TEST_MAX_DEPTH,
        },
    )
    .unwrap();
    assert_eq!(missing, crate::P0_MISSING);
}

fn observer_payload(field: &str, value: &Value) -> Vec<u8> {
    format!(
        "\u{5}\u{6}observation\u{6}phase=original_target\u{6}theory=HOL\u{6}source=src/Pure/ROOT.ML\u{6}source_sha256={}\u{6}field={field}\u{5}\u{5}\u{6}payload\u{5}{}\u{5}\u{6}\u{5}\u{5}\u{6}\u{5}",
        hash('a'), serde_json::to_string(value).unwrap(),
    ).into_bytes()
}

#[test]
fn observer_raw_event_payload_mismatch_rejects() {
    let field = "runtime_registration_effects";
    let bytes =
        frame(&[b"observer", b"event", b"inventory-id", b"r1", b"1", b"not-an-observation"]);
    let frames = raw::parse_frames(&bytes, 1).unwrap();
    let observer = json!({"schema_version":2,"source_commit":COMMIT,"overlay_id":hash('c'),"records":[{
        "run_id":"inventory-id","field":field,"value":[{
            "metadata":{"run_id":"inventory-id","phase":"original_target",
                "theory":"HOL","source":"src/Pure/ROOT.ML","source_sha256":hash('a'),
                "root_id":"r1","local_id":"1"},
            "value":{"kind":"actual registration"},
            "raw_record_index":0,"raw_frame_sha256":frames[0].sha256}]}],
        "coverage":[]});
    let closure = json!({"schema_version":2,"source_commit":COMMIT,"fields":{}});
    let sources = BTreeMap::from([("src/Pure/ROOT.ML".into(), hash('a'))]);
    assert!(
        validate_observer_records(
            &observer,
            &closure,
            ObserverRecordInputs {
                frames: &frames,
                build: "build-id",
                inventory: "inventory-id",
                executed: &sources,
                bootstrap: &json!({}),
                reference_inventory: &json!({}),
                execution: &json!({"theories":[]}),
                is_bootstrap_verified: false,
                max_depth: TEST_MAX_DEPTH,
            }
        )
        .is_err()
    );
}

#[test]
fn observer_named_seal_without_member_events_stays_incomplete() {
    let name = "declaration_origin";
    let seal_value = json!({"named_members":[{"theory":"HOL","fact_group_name":"g",
        "member_index":0}],"executed_commands":[],"bootstrap_loads":[]});
    let bytes = frame(&[
        b"observer",
        b"seal",
        b"inventory-id",
        b"r1",
        b"1",
        &observer_payload(name, &seal_value),
    ]);
    let frames = raw::parse_frames(&bytes, 1).unwrap();
    let observer = json!({"schema_version":2,"source_commit":COMMIT,"overlay_id":hash('c'),"records":[{
        "run_id":"inventory-id","field":name,"value":[]}],"coverage":[{
        "run_id":"inventory-id","field":name,"named_members":seal_value["named_members"],
        "executed_commands":[],"bootstrap_loads":[],
        "raw_record_index":0,"raw_frame_sha256":frames[0].sha256}]});
    let closure = json!({"schema_version":2,"source_commit":COMMIT,"fields":{
        "declaration_origin":{"status":"Available","value":[],"evidence":{
            "artifact":"observer-events","pointer":"/records/0"},"completeness":"complete"}}});
    let inventory = json!({"run_id":"inventory-id","theories":[{"name":"HOL","fact_groups":[{"name":"g",
        "theorems":[{"index":0}]}]}]});
    let sources = BTreeMap::from([("src/Pure/ROOT.ML".into(), hash('a'))]);
    let incomplete = validate_observer_records(
        &observer,
        &closure,
        ObserverRecordInputs {
            frames: &frames,
            build: "build-id",
            inventory: "inventory-id",
            executed: &sources,
            bootstrap: &json!({"loads":[]}),
            reference_inventory: &inventory,
            execution: &json!({"theories":[]}),
            is_bootstrap_verified: true,
            max_depth: TEST_MAX_DEPTH,
        },
    )
    .unwrap();
    assert!(incomplete.contains(&name));
}
