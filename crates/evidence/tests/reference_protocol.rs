use std::collections::BTreeMap;

#[path = "reference_protocol/observed.rs"]
mod observed;

use isabelle_evidence::{
    Comparison, OfficialCompatibilityResult, compare_candidate, verify_reference,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const COMMIT: &str = "765fb2460a57eb46e8490283241ad46f1fac857f";
const ROOTS: [&str; 9] = [
    "HOL.HOL",
    "HOL.Orderings",
    "HOL.Set",
    "HOL.Nat",
    "HOL.List",
    "HOL.Fun",
    "HOL.Product_Type",
    "HOL.Sum_Type",
    "HOL.Option",
];
const MISSING: [&str; 6] = [
    "full_axiom_extension_dependencies",
    "unresolved_sort_obligations",
    "declaration_origin",
    "anonymous_ephemeral_facts",
    "dynamic_fact_evaluations",
    "runtime_registration_effects",
];

fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
fn available(value: Value) -> Value {
    json!({"status":"Available","value":value,"evidence":"synthetic internal test input","completeness":"complete"})
}
fn make_theory(name: &str) -> Value {
    let parents = if name == "Pure" { json!([]) } else { json!(["Pure"]) };
    let mut theory = json!({"name":name,"source":format!("src/{}.thy", name.replace('.', "/")),
        "parents":parents,"import_specifications":parents});
    for section in [
        "types",
        "classes",
        "constants",
        "axioms",
        "fact_indexes",
        "class_relations",
        "arities",
        "specifications",
        "constant_definitions",
        "oracle_registrations",
        "fact_groups",
        "named_derivations",
        "default_sort",
    ] {
        theory[section] = json!([]);
    }
    if name == "Pure" {
        theory["types"] = json!([{"name":"prop","storage_kind":"logical","arity":0}]);
    }
    if name == "HOL.HOL" {
        theory["fact_indexes"] = json!([{"name":"HOL.TrueI","dynamic":false,"origin":name}]);
        theory["types"] = json!([{"name":"HOL.bool","storage_kind":"logical","arity":0}]);
        theory["classes"] = json!([{"name":"HOL.type","info_available":true,
            "parameters":[],"class_axioms":[]}]);
        theory["constants"] = json!([{"name":"HOL.True",
            "type":{"kind":"Type","name":"HOL.bool","args":[]}}]);
        theory["fact_groups"] = json!([{"name":"HOL.TrueI","theorems":[{
            "name":"HOL.TrueI","index":0,"owner":name,"dependencies":[],
            "proposition":{"kind":"Const","name":"HOL.True","type":{"kind":"Type","name":"HOL.bool","args":[]}},
            "hypotheses":[],"tpairs":[],"shyps":[],"has_skip_proof":false,"oracle_footprint":[]
        }]}]);
    }
    theory
}

fn make_observed_dependency(proposition: Value) -> Value {
    json!({"kind":"AcceptedFact","name":"HOL.TrueI","owner":"HOL.HOL",
        "statement":{"proposition":proposition.clone(),"hypotheses":[],"shyps":[],
            "tpairs":[],"sort_obligations":[]},
        "certificate":{"kind":"AcceptedFact","owner":"HOL.HOL",
            "goal":proposition,"premises":[]}})
}

fn make_proposition_variable(name: &str, index: u64, typ: Value) -> Value {
    json!({"kind":"Var","name":name,"index":index,"type":typ})
}

struct Fixture {
    manifest: Value,
    artifacts: BTreeMap<String, Vec<u8>>,
    candidate: Value,
}
impl Fixture {
    fn new() -> Self {
        let extras: Vec<_> = (0..57).map(|index| format!("HOL.Dependency{index}")).collect();
        let mut names = std::iter::once("Pure".to_owned())
            .chain(ROOTS.map(str::to_owned))
            .chain(extras.iter().cloned())
            .collect::<Vec<_>>();
        names.sort();
        let mut theories = names.iter().map(|name| make_theory(name)).collect::<Vec<_>>();
        let hol = theories.iter_mut().find(|item| item["name"] == "HOL.HOL").unwrap();
        hol["parents"].as_array_mut().unwrap().extend(extras.into_iter().map(Value::String));
        let sources = theories
            .iter()
            .map(|item| (item["source"].as_str().unwrap().to_owned(), json!("a".repeat(64))))
            .collect::<serde_json::Map<_, _>>();
        let inventory = json!({"reference":"Isabelle2025","roots":ROOTS,
            "source_sha256":sources,"theories":theories});
        let executed = theories
            .iter()
            .filter(|item| item["name"] != "Pure")
            .map(|item| json!({"name":item["name"],"commands":[]}))
            .collect::<Vec<_>>();
        let execution = json!({"reference":"Isabelle2025","roots":ROOTS,"theories":executed});
        let mut fields = serde_json::Map::new();
        for name in MISSING {
            fields.insert(
                name.to_owned(),
                json!({"status":"Unavailable","reason":"observer field unavailable in this run"}),
            );
        }
        let closure = json!({"schema_version":1,"source_commit":COMMIT,"fields":fields});
        let mut candidate = json!({"schema_version":1,"purpose":"native_closure_diagnostics",
            "source_commit":COMMIT,"requested_roots":ROOTS,
            "source_files":sources.iter().map(|(path, hash)| json!({"path":path,"sha256":hash})).collect::<Vec<_>>(),
            "theories":theories,"execution":{"theories":executed,"status":"Complete","pending_tasks":0},
            "effects":{"phase":"closed","pending":0}});
        for theory in candidate["theories"].as_array_mut().unwrap() {
            for group in theory["fact_groups"].as_array_mut().unwrap() {
                for fact in group["theorems"].as_array_mut().unwrap() {
                    let owner = fact.as_object_mut().unwrap().remove("owner").unwrap();
                    fact["observed_in"] = owner;
                    fact["authorization_kind"] = json!("KernelTrustedClosed");
                    for name in [
                        "unresolved_sort_obligations",
                        "oracle_footprint",
                        "pending",
                        "futures",
                        "full_axiom_extension_dependencies",
                    ] {
                        fact[name] = available(json!([]));
                    }
                    fact["accepted_in"] = available(json!("HOL.HOL"));
                    fact["declaration_origin"] = available(json!("HOL.HOL"));
                }
            }
        }
        let mut artifacts = BTreeMap::new();
        for (name, document) in
            [("inventory", inventory), ("execution", execution), ("closure-evidence", closure)]
        {
            artifacts.insert(name.into(), serde_json::to_vec(&document).unwrap());
        }
        let p0 = json!({"purpose":"isabelle2025_p0_reference_snapshot",
            "source":{"git_commit":COMMIT},
            "reference_runs":{"artifacts":{
                "inventory":{"sha256":digest(&artifacts["inventory"]),"bytes":artifacts["inventory"].len()},
                "execution":{"sha256":digest(&artifacts["execution"]),"bytes":artifacts["execution"].len()}}},
            "session_graph":{"bootstrap":{"sources":[],"prelude_sources":[]}},
            "observed_fixed_source_files":[]});
        artifacts.insert("closure.json".into(), serde_json::to_vec(&p0).unwrap());
        let entries = ["inventory", "execution", "closure-evidence"]
            .into_iter()
            .map(|name| {
                json!({"name":name,"path":format!("inventory/{name}.json"),
                "sha256":digest(&artifacts[name]),"bytes":artifacts[name].len()})
            })
            .collect::<Vec<_>>();
        let manifest = json!({"schema_version":1,"purpose":"native_reference_evidence",
            "source_commit":COMMIT,"p0_manifest_sha256":digest(&artifacts["closure.json"]),
            "source_files":sources.iter().map(|(path, hash)| json!({"path":path,"sha256":hash})).collect::<Vec<_>>(),
            "artifacts":entries});
        Self { manifest, artifacts, candidate }
    }
    fn verify(
        &self,
    ) -> Result<isabelle_evidence::VerifiedReferenceEvidence, isabelle_evidence::EvidenceError>
    {
        verify_reference(&self.manifest, &self.artifacts)
    }
    fn set_closure(&mut self, closure: &Value) {
        self.artifacts.insert("closure-evidence".into(), serde_json::to_vec(closure).unwrap());
        self.manifest["artifacts"][2]["bytes"] = json!(self.artifacts["closure-evidence"].len());
        self.manifest["artifacts"][2]["sha256"] =
            json!(digest(&self.artifacts["closure-evidence"]));
    }
    fn add_declaration_observation(&mut self, index: i64) {
        let origin = json!({"owner":"HOL.HOL","source":"src/HOL/HOL.thy",
            "command_sequence":0,"operation":"theorem","fact_name":"HOL.TrueI",
            "member_index":index});
        let value = json!([{"theory":"HOL.HOL","fact_group_name":"HOL.TrueI",
            "member_index":index,"value":origin.clone()}]);
        self.attach_observation("declaration_origin", value);
        let hol = self.candidate["theories"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|theory| theory["name"] == "HOL.HOL")
            .unwrap();
        hol["fact_groups"][0]["theorems"][0]["declaration_origin"]["value"] = origin;
    }
    fn attach_observation(&mut self, name: &str, value: Value) {
        let observation = json!({"records":[{"field":name,"value":value.clone()}]});
        self.artifacts.insert("observer".into(), serde_json::to_vec(&observation).unwrap());
        self.manifest["artifacts"].as_array_mut().unwrap().push(json!({
            "name":"observer","path":"observations/observer.json",
            "sha256":digest(&self.artifacts["observer"]),"bytes":self.artifacts["observer"].len()
        }));
        let mut closure: Value =
            serde_json::from_slice(&self.artifacts["closure-evidence"]).unwrap();
        closure["fields"][name] = json!({"status":"Available","value":value,
            "evidence":{"artifact":"observer","pointer":"/records/0"},"completeness":"complete"});
        self.set_closure(&closure);
    }

    fn add_named_dependency(&mut self, dependency: Value) {
        let value = json!([{"theory":"HOL.HOL","fact_group_name":"HOL.TrueI",
            "member_index":0,"value":[dependency.clone()]}]);
        self.attach_observation("full_axiom_extension_dependencies", value);
        let hol = self.candidate["theories"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|theory| theory["name"] == "HOL.HOL")
            .unwrap();
        hol["fact_groups"][0]["theorems"][0]["full_axiom_extension_dependencies"]["value"] =
            json!([dependency]);
    }

    fn add_event_observation(&mut self, name: &str, value: Value) {
        self.attach_observation(name, value.clone());
        self.candidate["execution"][name] = value;
    }

    fn add_hol_command(&mut self) {
        let mut execution: Value = serde_json::from_slice(&self.artifacts["execution"]).unwrap();
        let theories = execution["theories"].as_array_mut().unwrap();
        let hol = theories.iter_mut().find(|theory| theory["name"] == "HOL.HOL").unwrap();
        hol["commands"] = json!([{"sequence":0,"name":"theorem","source":"src/HOL/HOL.thy",
            "line":1,"offset":0,"skipped":false,"files":[]}]);
        self.candidate["execution"]["theories"] = execution["theories"].clone();
        self.artifacts.insert("execution".into(), serde_json::to_vec(&execution).unwrap());
        let record = &mut self.manifest["artifacts"][1];
        record["sha256"] = json!(digest(&self.artifacts["execution"]));
        record["bytes"] = json!(self.artifacts["execution"].len());
        let mut frozen: Value = serde_json::from_slice(&self.artifacts["closure.json"]).unwrap();
        frozen["reference_runs"]["artifacts"]["execution"] = json!({
            "sha256":digest(&self.artifacts["execution"]),"bytes":self.artifacts["execution"].len()
        });
        self.artifacts.insert("closure.json".into(), serde_json::to_vec(&frozen).unwrap());
        self.manifest["p0_manifest_sha256"] = json!(digest(&self.artifacts["closure.json"]));
    }
}

#[test]
fn verify_reference_fresh_manifest_bytes_preserve_frozen_anchor() {
    let mut fixture = Fixture::new();
    fixture.artifacts.get_mut("execution").unwrap().push(b' ');
    fixture.manifest["artifacts"][1]["bytes"] = json!(fixture.artifacts["execution"].len());
    fixture.manifest["artifacts"][1]["sha256"] = json!(digest(&fixture.artifacts["execution"]));
    let verified = fixture.verify().unwrap();
    assert!(matches!(
        compare_candidate(&verified, &fixture.candidate).unwrap(),
        Comparison::Incomplete(_)
    ));
}

#[test]
fn verify_reference_declaration_missing_execution_event_rejects() {
    let mut fixture = Fixture::new();
    fixture.add_declaration_observation(0);
    assert!(fixture.verify().is_err());
}

#[test]
fn compare_candidate_invalid_accepted_owner_rejects() {
    let mut fixture = Fixture::new();
    let reference = fixture.verify().unwrap();
    let hol = fixture.candidate["theories"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|theory| theory["name"] == "HOL.HOL")
        .unwrap();
    hol["fact_groups"][0]["theorems"][0]["accepted_in"]["value"] = Value::Null;
    assert!(compare_candidate(&reference, &fixture.candidate).is_err());
}

#[test]
fn compare_candidate_foreign_accepted_owner_rejects() {
    let mut fixture = Fixture::new();
    let reference = fixture.verify().unwrap();
    let hol = fixture.candidate["theories"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|theory| theory["name"] == "HOL.HOL")
        .unwrap();
    hol["fact_groups"][0]["theorems"][0]["accepted_in"]["value"] = json!("HOL.Nonexistent");
    assert!(compare_candidate(&reference, &fixture.candidate).is_err());
}

#[test]
fn verify_reference_unavailable_field_retains_blocked_prerequisite() {
    let fixture = Fixture::new();
    let verified = fixture.verify().unwrap();
    let Comparison::Incomplete(report) = compare_candidate(&verified, &fixture.candidate).unwrap()
    else {
        panic!("missing observation cannot match")
    };
    assert_eq!(report["result"], "BlockedPrerequisite");
    assert_eq!(report["unavailable"].as_array().unwrap().len(), MISSING.len());
}

#[test]
fn offline_result_incomplete_v1_diagnostics_never_claims_compatibility() {
    let fixture = Fixture::new();
    let verified = fixture.verify().unwrap();
    let comparison = compare_candidate(&verified, &fixture.candidate).unwrap();
    let report = OfficialCompatibilityResult::from_comparison(comparison).as_json();
    assert_eq!(report["purpose"], "official_compatibility_result");
    assert_eq!(report["result"], "BlockedPrerequisite");
    assert_eq!(report["diagnostics"]["unavailable"].as_array().unwrap().len(), MISSING.len());
    assert_eq!(report["authorization"], "none");
}

#[test]
fn verify_reference_mismatched_bytes_and_paths_reject() {
    let mut fixture = Fixture::new();
    fixture.artifacts.get_mut("execution").unwrap().push(b' ');
    assert!(fixture.verify().is_err());
    let mut fixture = Fixture::new();
    fixture.manifest["artifacts"][0]["path"] = json!("../inventory.json");
    assert!(fixture.verify().is_err());
    let mut fixture = Fixture::new();
    fixture.manifest["source_files"][0]["sha256"] = json!("b".repeat(64));
    assert!(fixture.verify().is_err());
    let mut fixture = Fixture::new();
    fixture.manifest["artifacts"][1]["name"] = json!("inventory");
    assert!(fixture.verify().is_err());
    let mut fixture = Fixture::new();
    fixture.manifest["p0_manifest_sha256"] = json!("b".repeat(64));
    assert!(fixture.verify().is_err());
    let mut fixture = Fixture::new();
    fixture.manifest["artifacts"][0]["bytes"] = json!(1);
    assert!(fixture.verify().is_err());
}

#[test]
fn verify_reference_forged_available_provenance_rejects() {
    let mut fixture = Fixture::new();
    let mut closure: Value =
        serde_json::from_slice(&fixture.artifacts["closure-evidence"]).unwrap();
    closure["fields"]["declaration_origin"] = json!({"status":"Available", "value":[],
        "evidence":{"artifact":"closure-evidence","pointer":"/fields/declaration_origin"},
        "completeness":"complete"});
    fixture.set_closure(&closure);
    assert!(fixture.verify().is_err());
}

#[test]
fn compare_candidate_final_result_and_open_effects_reject() {
    let mut fixture = Fixture::new();
    let verified = fixture.verify().unwrap();
    fixture.candidate["result"] = json!("Succeeded");
    assert!(compare_candidate(&verified, &fixture.candidate).is_err());
    fixture.candidate.as_object_mut().unwrap().remove("result");
    fixture.candidate["effects"]["pending"] = json!(1);
    assert!(matches!(
        compare_candidate(&verified, &fixture.candidate).unwrap(),
        Comparison::Different(_)
    ));
}

#[test]
fn verify_reference_duplicate_json_member_rejects() {
    let mut fixture = Fixture::new();
    let duplicate = format!(
        r#"{{"schema_version":1,"schema_version":1,"source_commit":"{COMMIT}","fields":{{}}}}"#
    );
    fixture.artifacts.insert("closure-evidence".into(), duplicate.into_bytes());
    fixture.manifest["artifacts"][2]["bytes"] = json!(fixture.artifacts["closure-evidence"].len());
    fixture.manifest["artifacts"][2]["sha256"] =
        json!(digest(&fixture.artifacts["closure-evidence"]));
    assert!(fixture.verify().is_err());
}

#[test]
fn compare_candidate_named_observation_mismatch_is_different() {
    let mut fixture = Fixture::new();
    fixture.add_hol_command();
    fixture.add_declaration_observation(0);
    let verified = fixture.verify().unwrap();
    assert!(matches!(
        compare_candidate(&verified, &fixture.candidate).unwrap(),
        Comparison::Incomplete(_)
    ));
    let hol = fixture.candidate["theories"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|theory| theory["name"] == "HOL.HOL")
        .unwrap();
    hol["fact_groups"][0]["theorems"][0]["declaration_origin"]["value"] = json!("HOL.Other");
    assert!(matches!(
        compare_candidate(&verified, &fixture.candidate).unwrap(),
        Comparison::Different(_)
    ));
}

#[test]
fn verify_reference_foreign_or_negative_member_rejects() {
    for member_index in [-1, 3] {
        let mut fixture = Fixture::new();
        fixture.add_hol_command();
        fixture.add_declaration_observation(member_index);
        assert!(fixture.verify().is_err());
    }
}

#[test]
fn compare_candidate_available_without_command_and_fact_coverage_is_incomplete() {
    let mut fixture = Fixture::new();
    fixture.add_hol_command();
    fixture.add_declaration_observation(0);
    let verified = fixture.verify().unwrap();
    let Comparison::Incomplete(report) = compare_candidate(&verified, &fixture.candidate).unwrap()
    else {
        panic!("self-consistent record without independent coverage must not match")
    };
    assert!(
        report["unavailable"]
            .as_array()
            .unwrap()
            .iter()
            .any(|record| record["field"] == "declaration_origin"
                && record["reason"] == "independent observation coverage not established")
    );
}

#[test]
fn verify_reference_summary_dependency_cannot_claim_available() {
    let mut fixture = Fixture::new();
    let value = json!([{"theory":"HOL.HOL","fact_group_name":"HOL.TrueI",
        "member_index":0,"value":[{"name":"HOL.TrueI","owner":"HOL.HOL","dependencies":[]}]}]);
    let observation =
        json!({"records":[{"field":"full_axiom_extension_dependencies","value":value.clone()}]});
    fixture.artifacts.insert("observer".into(), serde_json::to_vec(&observation).unwrap());
    fixture.manifest["artifacts"].as_array_mut().unwrap().push(json!({
        "name":"observer","path":"observations/observer.json",
        "sha256":digest(&fixture.artifacts["observer"]),
        "bytes":fixture.artifacts["observer"].len()
    }));
    let mut closure: Value =
        serde_json::from_slice(&fixture.artifacts["closure-evidence"]).unwrap();
    closure["fields"]["full_axiom_extension_dependencies"] = json!({
        "status":"Available","value":value,
        "evidence":{"artifact":"observer","pointer":"/records/0"},"completeness":"complete"
    });
    fixture.set_closure(&closure);
    assert!(fixture.verify().is_err());
}

#[test]
fn verify_reference_unbound_observer_claim_rejects() {
    let mut fixture = Fixture::new();
    fixture.add_hol_command();
    fixture.add_declaration_observation(0);
    let mut observation: Value = serde_json::from_slice(&fixture.artifacts["observer"]).unwrap();
    observation["coverage"] = json!([{"field":"declaration_origin","named_members":[],
        "executed_commands":[]}]);
    observation["schema_version"] = json!(1);
    observation["source_commit"] = json!(COMMIT);
    fixture.artifacts.insert("observer".into(), serde_json::to_vec(&observation).unwrap());
    let record = fixture.manifest["artifacts"].as_array_mut().unwrap().last_mut().unwrap();
    record["bytes"] = json!(fixture.artifacts["observer"].len());
    record["sha256"] = json!(digest(&fixture.artifacts["observer"]));
    assert!(fixture.verify().is_err());
}

#[test]
fn verify_reference_declaration_from_unrelated_owner_rejects() {
    let mut fixture = Fixture::new();
    fixture.add_hol_command();
    fixture.add_declaration_observation(0);
    let mut observation: Value = serde_json::from_slice(&fixture.artifacts["observer"]).unwrap();
    observation["records"][0]["value"][0]["value"]["owner"] = json!("HOL.Option");
    let mut closure: Value =
        serde_json::from_slice(&fixture.artifacts["closure-evidence"]).unwrap();
    closure["fields"]["declaration_origin"]["value"][0]["value"]["owner"] = json!("HOL.Option");
    fixture.set_closure(&closure);
    fixture.artifacts.insert("observer".into(), serde_json::to_vec(&observation).unwrap());
    let record = fixture.manifest["artifacts"].as_array_mut().unwrap().last_mut().unwrap();
    record["bytes"] = json!(fixture.artifacts["observer"].len());
    record["sha256"] = json!(digest(&fixture.artifacts["observer"]));
    assert!(fixture.verify().is_err());
}

#[test]
fn compare_candidate_dependency_alpha_rename_retains_incomplete() {
    let mut fixture = Fixture::new();
    let prop = json!({"kind":"Type","name":"prop","args":[]});
    fixture.add_named_dependency(make_observed_dependency(make_proposition_variable(
        "x",
        0,
        prop.clone(),
    )));
    let verified = fixture.verify().unwrap();
    let hol = fixture.candidate["theories"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|theory| theory["name"] == "HOL.HOL")
        .unwrap();
    let dependency =
        &mut hol["fact_groups"][0]["theorems"][0]["full_axiom_extension_dependencies"]["value"][0];
    let renamed = make_proposition_variable("u", 7, prop);
    dependency["statement"]["proposition"] = renamed.clone();
    dependency["certificate"]["goal"] = renamed;
    assert!(matches!(
        compare_candidate(&verified, &fixture.candidate).unwrap(),
        Comparison::Incomplete(_)
    ));
}

#[test]
fn compare_candidate_anonymous_alpha_rename_retains_incomplete() {
    let mut fixture = Fixture::new();
    fixture.add_hol_command();
    let prop = json!({"kind":"Type","name":"prop","args":[]});
    let statement =
        make_observed_dependency(make_proposition_variable("x", 0, prop.clone()))["statement"]
            .clone();
    fixture.add_event_observation(
        "anonymous_ephemeral_facts",
        json!([{
            "theory":"HOL.HOL","execution_event":0,"local_id":"fact-0",
            "value":{"owner":"HOL.HOL","statement":statement,"dependencies":[],
                "authorization_kind":"KernelTrustedClosed"}
        }]),
    );
    let verified = fixture.verify().unwrap();
    fixture.candidate["execution"]["anonymous_ephemeral_facts"][0]["value"]["statement"]["proposition"] =
        make_proposition_variable("u", 7, prop);
    assert!(matches!(
        compare_candidate(&verified, &fixture.candidate).unwrap(),
        Comparison::Incomplete(_)
    ));
}

#[test]
fn verify_reference_event_with_foreign_owner_rejects() {
    let mut fixture = Fixture::new();
    fixture.add_hol_command();
    fixture.add_event_observation(
        "runtime_registration_effects",
        json!([{
            "theory":"HOL.HOL","execution_event":0,"local_id":"method-0",
            "value":{"kind":"Method","name":"review_method","owner":"NoSuchTheory",
                "source":"src/HOL/HOL.thy","action":"Registered",
                "signature":{"domain":"unit","range":"unit"}}
        }]),
    );
    assert!(fixture.verify().is_err());
}

#[test]
fn verify_reference_dependency_undeclared_const_or_wrong_arity_rejects() {
    for proposition in [
        json!({"kind":"Const","name":"HOL.Unknown",
            "type":{"kind":"Type","name":"HOL.bool","args":[]}}),
        json!({"kind":"Const","name":"HOL.True",
            "type":{"kind":"Type","name":"HOL.bool",
                "args":[{"kind":"Type","name":"HOL.bool","args":[]}]}}),
    ] {
        let mut fixture = Fixture::new();
        fixture.add_named_dependency(make_observed_dependency(proposition));
        assert!(fixture.verify().is_err());
    }
}

#[test]
fn compare_candidate_wrong_declared_type_arity_rejects_input() {
    let fixture = Fixture::new();
    let verified = fixture.verify().unwrap();
    let mut candidate = fixture.candidate;
    let hol = candidate["theories"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|theory| theory["name"] == "HOL.HOL")
        .unwrap();
    hol["fact_groups"][0]["theorems"][0]["proposition"]["type"] = json!({
        "kind":"Type","name":"HOL.bool",
        "args":[{"kind":"Type","name":"HOL.bool","args":[]}]
    });
    assert!(compare_candidate(&verified, &candidate).is_err());
}

#[test]
fn compare_candidate_dependency_wrong_declared_type_arity_rejects_input() {
    let mut fixture = Fixture::new();
    let proposition = json!({"kind":"Const","name":"HOL.True",
        "type":{"kind":"Type","name":"HOL.bool","args":[]}});
    fixture.add_named_dependency(make_observed_dependency(proposition));
    let verified = fixture.verify().unwrap();
    let hol = fixture.candidate["theories"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|theory| theory["name"] == "HOL.HOL")
        .unwrap();
    let dependency =
        &mut hol["fact_groups"][0]["theorems"][0]["full_axiom_extension_dependencies"]["value"][0];
    let wrong = json!({"kind":"Const","name":"HOL.True",
        "type":{"kind":"Type","name":"HOL.bool",
            "args":[{"kind":"Type","name":"HOL.bool","args":[]}]}});
    dependency["statement"]["proposition"] = wrong.clone();
    dependency["certificate"]["goal"] = wrong;
    assert!(compare_candidate(&verified, &fixture.candidate).is_err());
}

#[test]
fn verify_reference_inherited_declarations_use_incremental_inventory() {
    let mut fixture = Fixture::new();
    fixture.add_named_dependency(make_observed_dependency(json!({
        "kind":"Var","name":"x","index":0,
        "type":{"kind":"Type","name":"prop","args":[]}
    })));
    let verified = fixture.verify().unwrap();
    assert!(matches!(
        compare_candidate(&verified, &fixture.candidate).unwrap(),
        Comparison::Incomplete(_)
    ));
}

#[test]
fn verify_reference_dependency_split_type_variable_sort_rejects() {
    let mut fixture = Fixture::new();
    let unsorted = json!({"kind":"TVar","name":"a","index":0,"sort":[]});
    let mut dependency = make_observed_dependency(make_proposition_variable("x", 0, unsorted));
    dependency["statement"]["sort_obligations"] = json!([{
        "type":{"kind":"TVar","name":"a","index":0,"sort":["HOL.type"]},
        "required_sort":["HOL.type"],"source_owner":"HOL.HOL",
        "occurrence":{"source":"P","path":[]}
    }]);
    fixture.add_named_dependency(dependency);
    assert!(fixture.verify().is_err());
}

#[test]
fn compare_candidate_dependency_premise_mutation_is_different() {
    let mut fixture = Fixture::new();
    let proposition = json!({"kind":"Const","name":"HOL.True",
        "type":{"kind":"Type","name":"HOL.bool","args":[]}});
    fixture.add_named_dependency(make_observed_dependency(proposition.clone()));
    let verified = fixture.verify().unwrap();
    assert!(matches!(
        compare_candidate(&verified, &fixture.candidate).unwrap(),
        Comparison::Incomplete(_)
    ));
    let hol = fixture.candidate["theories"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|theory| theory["name"] == "HOL.HOL")
        .unwrap();
    hol["fact_groups"][0]["theorems"][0]["full_axiom_extension_dependencies"]["value"][0]["certificate"]
        ["premises"] = json!([proposition]);
    assert!(matches!(
        compare_candidate(&verified, &fixture.candidate).unwrap(),
        Comparison::Different(_)
    ));
}

#[test]
fn verify_reference_duplicate_coverage_field_rejects() {
    let mut fixture = Fixture::new();
    fixture.add_hol_command();
    fixture.add_declaration_observation(0);
    let mut observer: Value = serde_json::from_slice(&fixture.artifacts["observer"]).unwrap();
    let named = json!([{"theory":"HOL.HOL","fact_group_name":"HOL.TrueI","member_index":0}]);
    let command = json!({"theory":"HOL.HOL","sequence":0,"source":"src/HOL/HOL.thy",
        "observed_local_ids":[]});
    observer["schema_version"] = json!(1);
    observer["source_commit"] = json!(COMMIT);
    observer["coverage"] = json!([
        {"field":"declaration_origin","named_members":named.clone(),
            "executed_commands":[command.clone()]},
        {"field":"declaration_origin","named_members":named,
            "executed_commands":[command]}
    ]);
    fixture.artifacts.insert("observer".into(), serde_json::to_vec(&observer).unwrap());
    let record = fixture.manifest["artifacts"].as_array_mut().unwrap().last_mut().unwrap();
    record["sha256"] = json!(digest(&fixture.artifacts["observer"]));
    record["bytes"] = json!(fixture.artifacts["observer"].len());
    assert!(fixture.verify().is_err());
}
