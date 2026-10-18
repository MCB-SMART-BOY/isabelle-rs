use super::{COMMIT, Comparison, Fixture, MISSING, OfficialCompatibilityResult, digest};
use isabelle_evidence::{
    ApprovedObserverIdentity, EvidenceError, VerifiedReferenceEvidence, compare_candidate,
    verify_reference_v2,
};
use serde_json::{Value, json};
use std::collections::BTreeMap;

const SOURCE: &str = "src/Pure/ROOT0.ML";
const SOURCE_BYTES: &[u8] = b"val original_bootstrap = ();";
const IMPORT_BUDGET: usize = 1024 * 1024;
const NAMED_PAIR: &str = "HOL.synthetic_pair";

fn append_named_pair(document: &mut Value) {
    let theory = document["theories"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|theory| theory["name"] == "HOL.HOL")
        .unwrap();
    let mut first = theory["fact_groups"][0]["theorems"][0].clone();
    first["name"] = json!(NAMED_PAIR);
    first["index"] = json!(1);
    let mut second = first.clone();
    second["index"] = json!(2);
    theory["fact_groups"]
        .as_array_mut()
        .unwrap()
        .push(json!({"name":NAMED_PAIR,"theorems":[first,second]}));
    theory["fact_indexes"]
        .as_array_mut()
        .unwrap()
        .push(json!({"name":NAMED_PAIR,"dynamic":false,"origin":"HOL.HOL"}));
}

// Synthetic protocol input only: this does not attest to an official Isabelle run.
#[path = "bootstrap.rs"]
mod bootstrap;

struct ObservedFixture {
    base: Fixture,
    events: BTreeMap<&'static str, Vec<Value>>,
    raw_override: Option<(&'static str, Vec<u8>)>,
    seal_override: Option<(&'static str, Value)>,
    extra_named_member: bool,
    omit_second_coverage: bool,
    duplicate_named_coverage: bool,
    limits: Value,
    is_bootstrap_sealed: bool,
}

fn make_run(phase: &str) -> Value {
    json!({"phase":phase,"run_id":format!("{phase}-id"),
        "prepared_sha256":digest(b"prepared"),"source_snapshot_sha256":digest(b"snapshot"),
        "heap_tree_sha256":digest(b"heap"),"command_sha256":digest(b"command"),
        "result_sha256":digest(b"result")})
}

fn encode_tlv(fields: &[&[u8]]) -> Vec<u8> {
    let mut body = format!("{}\n", fields.len()).into_bytes();
    for field in fields {
        body.extend(format!("{}\n", field.len()).bytes());
        body.extend_from_slice(field);
    }
    body
}

fn push_frame(
    frames: &mut Vec<Vec<u8>>,
    channel: &str,
    tag: &str,
    run: &str,
    root: &str,
    payload: &[u8],
) -> Value {
    let index = frames.len();
    let local = index.to_string();
    let body = encode_tlv(&[
        channel.as_bytes(),
        tag.as_bytes(),
        run.as_bytes(),
        root.as_bytes(),
        local.as_bytes(),
        payload,
    ]);
    let reference = json!({"raw_record_index":index,"raw_frame_sha256":digest(&body)});
    let mut bytes = format!("{}\n", body.len()).into_bytes();
    bytes.extend(body);
    frames.push(bytes);
    reference
}

fn encode_observation(name: &str, phase: &str, value: &Value) -> Vec<u8> {
    let theory = if phase == "original_bootstrap" { "Pure" } else { "HOL.HOL" };
    format!("\u{5}\u{6}observation\u{6}phase={phase}\u{6}theory={theory}\u{6}source={SOURCE}\u{6}source_sha256={}\u{6}field={name}\u{5}\u{5}\u{6}payload\u{5}{value}\u{5}\u{6}\u{5}\u{5}\u{6}\u{5}", digest(SOURCE_BYTES)).into_bytes()
}

fn make_bootstrap(frames: &mut Vec<Vec<u8>>, records: &mut Vec<Value>, is_sealed: bool) -> Value {
    let empty =
        encode_tlv(&[SOURCE.as_bytes(), b"", b"Pure", b"Pure", b"1", b"actual_read_bytes", b""]);
    let consumed = encode_tlv(&[
        SOURCE.as_bytes(),
        b"",
        b"Pure",
        b"Pure",
        b"1",
        b"actual_read_bytes",
        SOURCE_BYTES,
    ]);
    let begin = push_frame(frames, "bootstrap", "load_begin", "build-id", "root0", &empty);
    let event = make_bootstrap_event(frames, records);
    let end = push_frame(frames, "bootstrap", "load_end", "build-id", "root0", &consumed);
    let mut load = json!({"run_id":"build-id","load_id":"root0","source":SOURCE,
        "source_sha256":digest(SOURCE_BYTES),"source_provenance":"actual_read_bytes",
        "session":"Pure","theory":"Pure","source_order":1,"parent_load_id":null,
        "started":true,"finished":true,"sealed":is_sealed,
        "observed_local_ids":[event["local_id"]],
        "raw_begin_index":begin["raw_record_index"],"raw_begin_sha256":begin["raw_frame_sha256"],
        "raw_record_index":end["raw_record_index"],"raw_frame_sha256":end["raw_frame_sha256"]});
    if is_sealed {
        let seal = push_frame(frames, "bootstrap", "load_seal", "build-id", "root0", &empty);
        load["raw_seal_index"] = seal["raw_record_index"].clone();
        load["raw_seal_sha256"] = seal["raw_frame_sha256"].clone();
    }
    json!({"schema_version":2,"source_commit":COMMIT,"overlay_id":digest(b"overlay"),
        "events":[event],"loads":[load]})
}

fn make_bootstrap_event(frames: &mut Vec<Vec<u8>>, records: &mut Vec<Value>) -> Value {
    let name = "runtime_registration_effects";
    let value = json!({"kind":"synthetic_bootstrap_registration"});
    let local = frames.len().to_string();
    let reference = push_frame(
        frames,
        "observer",
        "event",
        "build-id",
        "root0",
        &encode_observation(name, "original_bootstrap", &value),
    );
    let mut item = reference.clone();
    item["value"] = value.clone();
    item["metadata"] = json!({"run_id":"build-id","phase":"original_bootstrap",
        "theory":"Pure","source":SOURCE,"source_sha256":digest(SOURCE_BYTES),
        "root_id":"root0","local_id":local,"load_root":{
            "source":SOURCE,"parent_source":null,"source_order":1,"session":"Pure",
            "theory":"Pure","source_provenance":"actual_read_bytes","missing_parent":false}});
    records.push(json!({"run_id":"build-id","field":name,"value":[item]}));
    let mut event = reference;
    event["run_id"] = json!("build-id");
    event["load_id"] = json!("root0");
    event["local_id"] = json!(local);
    event["field"] = json!(name);
    event["value"] = value;
    event
}

impl ObservedFixture {
    fn new() -> Self {
        let mut base = Fixture::new();
        base.candidate["purpose"] = json!("native_build_result");
        base.manifest["schema_version"] = json!(2);
        base.manifest["source_files"].as_array_mut().unwrap().push(json!({
            "path":SOURCE,"sha256":digest(SOURCE_BYTES)}));
        base.candidate["source_files"] = base.manifest["source_files"].clone();
        base.manifest["runs"] = json!([make_run("build"), make_run("inventory")]);
        base.manifest["overlay"] = json!({"id":digest(b"overlay"),"observer_sha256":digest(b"observer"),
            "generator_sha256":digest(b"generator"),"patches":[{"path":"session/reference_observation.ML",
                "original_sha256":null,"patched_sha256":digest(b"observer"),"patch_sha256":digest(b"patch")}]});
        for name in ["inventory", "execution"] {
            let mut document: Value = serde_json::from_slice(&base.artifacts[name]).unwrap();
            document["run_id"] = json!("inventory-id");
            document["initial_theories"] = json!(["Pure"]);
            if name == "inventory" {
                document["loaded_pure_heap_tree_sha256"] = json!(digest(b"heap"));
            }
            base.artifacts.insert(name.into(), serde_json::to_vec(&document).unwrap());
        }
        let mut events = BTreeMap::new();
        for name in MISSING {
            let values = if matches!(
                name,
                "full_axiom_extension_dependencies"
                    | "unresolved_sort_obligations"
                    | "declaration_origin"
            ) {
                vec![json!({"phase":"original_target","value":{"theory":"HOL.HOL",
                    "fact_group_name":"HOL.TrueI","member_index":0,
                    "value":if name == "declaration_origin" { json!("HOL.HOL") } else { json!([]) }}})]
            } else {
                base.candidate["execution"][name] = json!([]);
                Vec::new()
            };
            events.insert(name, values);
        }
        let limits = json!({"memory_bytes":IMPORT_BUDGET,"swap_bytes":0,"pids":1,
            "cpu_quota_us":1,"cpu_period_us":1,"wall_seconds":1,"scratch_bytes":IMPORT_BUDGET,
            "raw_total_bytes":IMPORT_BUDGET,"decoded_total_bytes":IMPORT_BUDGET,
            "max_artifacts":6,"max_events":64,"max_depth":64});
        Self {
            base,
            events,
            raw_override: None,
            seal_override: None,
            extra_named_member: false,
            omit_second_coverage: false,
            duplicate_named_coverage: false,
            is_bootstrap_sealed: true,
            limits,
        }
    }

    fn encode_events(&self, frames: &mut Vec<Vec<u8>>, name: &str) -> Vec<Value> {
        self.events[name]
            .iter()
            .map(|event| {
                let phase = event["phase"].as_str().unwrap();
                let payload = self
                    .raw_override
                    .as_ref()
                    .filter(|(field, _)| *field == name)
                    .map(|(_, bytes)| bytes.clone())
                    .unwrap_or_else(|| encode_observation(name, phase, &event["value"]));
                let index = frames.len();
                let mut item = push_frame(
                    frames,
                    "observer",
                    "event",
                    "inventory-id",
                    "command-root",
                    &payload,
                );
                item["metadata"] = json!({"run_id":"inventory-id","phase":phase,"theory":"HOL.HOL",
                "source":SOURCE,"source_sha256":digest(SOURCE_BYTES),"root_id":"command-root",
                "local_id":index.to_string()});
                item["value"] = event["value"].clone();
                item
            })
            .collect()
    }

    fn add_named_pair(&mut self) {
        let mut inventory: Value =
            serde_json::from_slice(&self.base.artifacts["inventory"]).unwrap();
        append_named_pair(&mut inventory);
        self.base.artifacts.insert("inventory".into(), serde_json::to_vec(&inventory).unwrap());
        append_named_pair(&mut self.base.candidate);
        for name in [
            "full_axiom_extension_dependencies",
            "unresolved_sort_obligations",
            "declaration_origin",
        ] {
            let events = self.events.get_mut(name).unwrap();
            let mut first_member = events[0].clone();
            first_member["value"]["fact_group_name"] = json!(NAMED_PAIR);
            first_member["value"]["member_index"] = json!(1);
            events.push(first_member);
        }
    }

    fn assemble_observations(&mut self) {
        if self.extra_named_member {
            self.add_named_pair();
        }
        let mut frames = Vec::new();
        let mut records = Vec::new();
        let bootstrap = make_bootstrap(&mut frames, &mut records, self.is_bootstrap_sealed);
        let mut coverage = Vec::new();
        let mut fields = serde_json::Map::new();
        for name in MISSING {
            let values = self.encode_events(&mut frames, name);
            let index = records.len();
            records.push(json!({"run_id":"inventory-id","field":name,"value":values}));
            fields.insert(name.into(), json!({"status":"Available","completeness":"complete",
                "value":values,"evidence":{"artifact":"observer-events","pointer":format!("/records/{index}")}}));
            let mut named_members = vec![json!({"theory":"HOL.HOL",
                "fact_group_name":"HOL.TrueI","member_index":0})];
            if self.extra_named_member {
                named_members.push(json!({"theory":"HOL.HOL",
                    "fact_group_name":NAMED_PAIR,"member_index":1}));
            }
            if self.extra_named_member && !self.omit_second_coverage {
                named_members.push(json!({"theory":"HOL.HOL",
                    "fact_group_name":NAMED_PAIR,"member_index":2}));
            }
            if self.duplicate_named_coverage {
                named_members.push(named_members[0].clone());
            }
            let seal = json!({"named_members":named_members,
                "executed_commands":[],"bootstrap_loads":[{"run_id":"build-id","load_id":"root0"}]});
            let original = self
                .seal_override
                .as_ref()
                .filter(|(field, _)| *field == name)
                .map_or(&seal, |(_, value)| value);
            let mut item = push_frame(
                &mut frames,
                "observer",
                "seal",
                "inventory-id",
                "command-root",
                &encode_observation(name, "original_target", original),
            );
            item["run_id"] = json!("inventory-id");
            item["field"] = json!(name);
            for key in ["named_members", "executed_commands", "bootstrap_loads"] {
                item[key] = seal[key].clone();
            }
            coverage.push(item);
        }
        let observer = json!({"schema_version":2,"source_commit":COMMIT,"overlay_id":digest(b"overlay"),"records":records,"coverage":coverage});
        let closure = json!({"schema_version":2,"source_commit":COMMIT,"fields":fields});
        for (name, document) in [
            ("bootstrap-events", bootstrap),
            ("observer-events", observer),
            ("closure-evidence", closure),
        ] {
            self.base.artifacts.insert(name.into(), serde_json::to_vec(&document).unwrap());
        }
        self.base.artifacts.insert("observer-raw".into(), frames.concat());
    }

    fn verify(&mut self) -> Result<VerifiedReferenceEvidence, EvidenceError> {
        self.assemble_observations();
        self.verify_assembled()
    }

    fn verify_assembled(&mut self) -> Result<VerifiedReferenceEvidence, EvidenceError> {
        self.base.manifest["artifacts"] = self.base.artifacts.iter().filter(|(name, _)| *name != "closure.json")
            .map(|(name, bytes)| json!({"name":name,"path":format!("inventory/{name}"),"bytes":bytes.len(),"sha256":digest(bytes)})).collect();
        let manifest = &self.base.manifest;
        let manifest_hash = digest(&serde_json::to_vec(manifest).unwrap());
        let approval = json!({"schema_version":1,"purpose":"offline_reference_approval",
            "producer":{"kind":"independent_official","identity":"synthetic test authority"},
            "source_commit":COMMIT,"p0_manifest_sha256":manifest["p0_manifest_sha256"],
            "overlay_id":manifest["overlay"]["id"],"observer_sha256":manifest["overlay"]["observer_sha256"],
            "generator_sha256":manifest["overlay"]["generator_sha256"],"approved_patch_sha256":manifest["overlay"]["patches"],
            "isabelle_binary_sha256":digest(b"binary"),"resource_budget":self.limits,
            "manifest_sha256":manifest_hash,"receipt_sha256":digest(b"receipt"),
            "approved_run_root":"/synthetic/run","runs":manifest["runs"],"source_files":manifest["source_files"]});
        let sources = manifest["source_files"]
            .as_array()
            .unwrap()
            .iter()
            .map(|file| {
                (file["path"].as_str().unwrap().into(), file["sha256"].as_str().unwrap().into())
            })
            .collect();
        let approved = ApprovedObserverIdentity::from_offline_host(
            &approval,
            manifest,
            &manifest_hash,
            &digest(b"receipt"),
            "/synthetic/run",
            sources,
        )?;
        verify_reference_v2(manifest, &self.base.artifacts, &approved)
    }
}

#[test]
fn compare_v2_complete_observed_members_matches_without_proof_authority() {
    let mut fixture = ObservedFixture::new();
    let reference = fixture.verify().unwrap();
    let comparison = compare_candidate(&reference, &fixture.base.candidate).unwrap();
    assert!(matches!(comparison, Comparison::Matched), "{comparison:?}");
    let report = OfficialCompatibilityResult::from_comparison(comparison).as_json();
    assert_eq!(report["result"], "Succeeded");
    assert_eq!(report["purpose"], "official_compatibility_result");
    assert_eq!(report["authorization"], "none");
}

#[test]
fn verify_v2_raw_event_mismatch_rejects_approved_self_consistent_hashes() {
    let mut fixture = ObservedFixture::new();
    fixture.raw_override = Some(("declaration_origin", b"not-an-observation".to_vec()));
    assert!(fixture.verify().unwrap_err().to_string().contains("YXML observation"));
}

#[test]
fn verify_v2_well_formed_altered_event_value_rejects() {
    let mut fixture = ObservedFixture::new();
    fixture.raw_override = Some((
        "declaration_origin",
        encode_observation(
            "declaration_origin",
            "original_target",
            &json!({"theory":"HOL.HOL","fact_group_name":"HOL.TrueI",
                "member_index":0,"value":"changed"}),
        ),
    ));
    assert!(fixture.verify().unwrap_err().to_string().contains("payload differs from decoded"));
}

#[test]
fn verify_v2_raw_seal_mismatch_rejects_decoded_coverage() {
    let mut fixture = ObservedFixture::new();
    fixture.seal_override = Some((
        "declaration_origin",
        json!({"named_members":[],"executed_commands":[],"bootstrap_loads":[]}),
    ));
    assert!(
        fixture.verify().unwrap_err().to_string().contains("original observation seal differs")
    );
}

#[test]
fn verify_v2_duplicate_named_coverage_rejects() {
    let mut fixture = ObservedFixture::new();
    fixture.duplicate_named_coverage = true;
    assert!(fixture.verify().unwrap_err().to_string().contains("duplicate covered named member"));
}

#[test]
fn compare_v2_missing_named_events_remains_incomplete() {
    for name in
        ["full_axiom_extension_dependencies", "unresolved_sort_obligations", "declaration_origin"]
    {
        let mut fixture = ObservedFixture::new();
        fixture.events.get_mut(name).unwrap().clear();
        let reference = fixture.verify().unwrap();
        let comparison = compare_candidate(&reference, &fixture.base.candidate).unwrap();
        assert!(matches!(comparison, Comparison::Incomplete(_)), "{name}: {comparison:?}");
    }
}

#[test]
fn compare_v2_missing_one_of_two_named_members_remains_incomplete() {
    let mut fixture = ObservedFixture::new();
    fixture.extra_named_member = true;
    let reference = fixture.verify().unwrap();
    let comparison = compare_candidate(&reference, &fixture.base.candidate).unwrap();
    assert!(matches!(comparison, Comparison::Incomplete(_)), "{comparison:?}");
    let report = OfficialCompatibilityResult::from_comparison(comparison).as_json();
    assert_eq!(report["result"], "BlockedPrerequisite");
}

#[test]
fn validate_entities_invalid_multifact_indexes_rejects() {
    let mut fixture = ObservedFixture::new();
    fixture.add_named_pair();
    let mut inventory: Value =
        serde_json::from_slice(&fixture.base.artifacts["inventory"]).unwrap();
    let theory = inventory["theories"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|theory| theory["name"] == "HOL.HOL")
        .unwrap();
    let group = theory["fact_groups"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|group| group["name"] == NAMED_PAIR)
        .unwrap();
    group["theorems"][0]["index"] = json!(0);
    let error = isabelle_evidence::validate_entities(inventory["theories"].as_array().unwrap())
        .unwrap_err();
    assert!(error.to_string().contains("invalid official theorem index sequence"));
}

#[test]
fn compare_v2_missing_second_named_coverage_remains_incomplete() {
    let mut fixture = ObservedFixture::new();
    fixture.extra_named_member = true;
    for name in
        ["full_axiom_extension_dependencies", "unresolved_sort_obligations", "declaration_origin"]
    {
        fixture.events.get_mut(name).unwrap().push(json!({"phase":"original_target",
        "value":{"theory":"HOL.HOL","fact_group_name":NAMED_PAIR,
            "member_index":2,"value":if name == "declaration_origin" {
                json!("HOL.HOL")
            } else {
                json!([])
            }}}));
    }
    fixture.omit_second_coverage = true;
    let reference = fixture.verify().unwrap();
    let comparison = compare_candidate(&reference, &fixture.base.candidate).unwrap();
    assert!(matches!(comparison, Comparison::Incomplete(_)), "{comparison:?}");
    let report = OfficialCompatibilityResult::from_comparison(comparison).as_json();
    assert_eq!(report["result"], "BlockedPrerequisite");
}

#[test]
fn compare_v2_export_only_named_events_remains_incomplete() {
    let mut fixture = ObservedFixture::new();
    fixture.events.get_mut("declaration_origin").unwrap()[0]["phase"] = json!("reference_export");
    let reference = fixture.verify().unwrap();
    let comparison = compare_candidate(&reference, &fixture.base.candidate).unwrap();
    assert!(matches!(comparison, Comparison::Incomplete(_)), "{comparison:?}");
    let report = OfficialCompatibilityResult::from_comparison(comparison).as_json();
    assert_eq!(report["result"], "BlockedPrerequisite");
}

#[test]
fn verify_v2_approved_event_limit_rejects_excess_frames() {
    let mut fixture = ObservedFixture::new();
    fixture.limits["max_events"] = json!(1);
    assert!(fixture.verify().unwrap_err().to_string().contains("event count exceeds approved"));
}

#[test]
fn verify_v2_approved_depth_limit_rejects_deep_artifact() {
    let mut fixture = ObservedFixture::new();
    fixture.limits["max_depth"] = json!(1);
    assert!(fixture.verify().unwrap_err().to_string().contains("nesting limit exceeded"));
}

#[test]
fn verify_v2_approved_decoded_limit_rejects_before_json_decode() {
    let mut fixture = ObservedFixture::new();
    fixture.limits["decoded_total_bytes"] = json!(1);
    assert!(fixture.verify().unwrap_err().to_string().contains("artifact bytes exceed approved"));
}
