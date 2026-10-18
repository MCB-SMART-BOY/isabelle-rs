use isabelle_evidence::{P0_MISSING, collect_required_sources, compare_reports};
use serde_json::{Value, json};
use xtask::reference::common::{COMMIT, read_json};
use xtask::reference::compare::load_frozen_artifact;
use xtask::reference::decode_inventory::{EXPECTED_THEORY_COUNT, ROOTS};

fn make_fact(index: u64) -> Value {
    json!({"name":"HOL.TrueI","index":index,"owner":"HOL.HOL",
        "proposition":{"kind":"Const","name":"HOL.True","type":{"kind":"Type","name":"HOL.bool","args":[]}},
        "hypotheses":[],"tpairs":[],"shyps":[],"has_skip_proof":false,"oracle_footprint":[],"dependencies":[]})
}

fn make_evidence(value: Value) -> Value {
    json!({"status":"Available","value":value,"evidence":"synthetic test input","completeness":"complete"})
}

fn make_native_fact(mut original: Value) -> Value {
    let owner = original.as_object_mut().unwrap().remove("owner").unwrap();
    original["observed_in"] = owner;
    original["authorization_kind"] = json!("KernelTrustedClosed");
    for field in [
        "oracle_footprint",
        "unresolved_sort_obligations",
        "pending",
        "futures",
        "full_axiom_extension_dependencies",
    ] {
        original[field] = make_evidence(json!([]));
    }
    original["accepted_in"] = make_evidence(json!("HOL.HOL"));
    original["declaration_origin"] = make_evidence(json!("HOL.HOL"));
    original
}

fn make_theory(name: &str) -> Value {
    let parents = if name == "Pure" { json!([]) } else { json!(["Pure"]) };
    let mut theory = json!({"name":name,"source":format!("src/{}.thy",name.replace('.',"/")),
        "parents":parents,"import_specifications":parents});
    for field in [
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
        theory[field] = json!([]);
    }
    if name == "HOL.HOL" {
        theory["types"] = json!([{"name":"HOL.bool","storage_kind":"logical","arity":0}]);
        theory["constants"] = json!([{"name":"HOL.True",
            "type":{"kind":"Type","name":"HOL.bool","args":[]}}]);
        theory["fact_indexes"] =
            json!([{"name":"HOL.TrueI","dynamic":false,"concealed":false,"origin":name}]);
        theory["fact_groups"] = json!([{"name":"HOL.TrueI","theorems":[make_fact(0)]}]);
    }
    theory
}

struct Reports {
    reference: Value,
    execution: Value,
    native: Value,
    manifest: Value,
}

impl Reports {
    fn create() -> Self {
        let extras: Vec<_> = (0..EXPECTED_THEORY_COUNT - ROOTS.len() - 1)
            .map(|i| format!("HOL.Dependency{i}"))
            .collect();
        let mut names: Vec<_> = ["Pure"]
            .into_iter()
            .chain(ROOTS)
            .map(str::to_owned)
            .chain(extras.iter().cloned())
            .collect();
        names.sort();
        let mut theories: Vec<_> = names.iter().map(|name| make_theory(name)).collect();
        theories.iter_mut().find(|theory| theory["name"] == "HOL.HOL").unwrap()["parents"]
            .as_array_mut()
            .unwrap()
            .extend(extras.into_iter().map(Value::String));
        let sources: serde_json::Map<_, _> = theories
            .iter()
            .map(|theory| (theory["source"].as_str().unwrap().into(), json!("a".repeat(64))))
            .collect();
        let reference = json!({"reference":"Isabelle2025","roots":ROOTS,"theories":theories,"source_sha256":sources});
        let executed: Vec<_> = theories
            .iter()
            .filter(|theory| theory["name"] != "Pure")
            .map(|theory| json!({"name":theory["name"],"commands":[]}))
            .collect();
        let execution = json!({"theories":executed});
        let source_files: Vec<_> =
            sources.iter().map(|(path, digest)| json!({"path":path,"sha256":digest})).collect();
        let mut native = json!({"schema_version":1,"purpose":"native_closure_diagnostics","source_commit":COMMIT,
            "requested_roots":ROOTS,"theories":theories,"source_files":source_files,
            "execution":{"theories":executed,"status":"Complete","pending_tasks":0},
            "effects":{"phase":"closed","pending":0},"result":"Succeeded"});
        for theory in native["theories"].as_array_mut().unwrap() {
            for group in theory["fact_groups"].as_array_mut().unwrap() {
                for fact in group["theorems"].as_array_mut().unwrap() {
                    *fact = make_native_fact(fact.take());
                }
            }
        }
        let manifest = json!({"session_graph":{"bootstrap":{"sources":[],"prelude_sources":[]}},"observed_fixed_source_files":[]});
        Self { reference, execution, native, manifest }
    }

    fn compare(&self) -> Result<Value, isabelle_evidence::EvidenceError> {
        compare_reports(&self.reference, &self.execution, self.native.clone(), &self.manifest)
    }

    fn native_fact(&mut self) -> &mut Value {
        &mut self.native["theories"]
            .as_array_mut()
            .unwrap()
            .iter_mut()
            .find(|theory| theory["name"] == "HOL.HOL")
            .unwrap()["fact_groups"][0]["theorems"][0]
    }
}

#[test]
fn comparison_matching_snapshot_retains_unavailable_evidence_and_no_authority() {
    let report = Reports::create().compare().unwrap();
    assert_eq!(report["result"], "BlockedPrerequisite");
    assert_eq!(report["matched_named_facts"], 1);
    assert_eq!(report["differences"], json!([]));
    let missing: Vec<_> = report["unavailable"]
        .as_array()
        .unwrap()
        .iter()
        .map(|item| item["field"].as_str().unwrap())
        .collect();
    assert_eq!(missing, P0_MISSING);
    assert_eq!(report["authorization"], "none");
}

#[test]
fn comparison_incomplete_execution_or_effects_fails() {
    for (section, field, value, label) in [
        ("execution", "status", json!("Failed"), "execution status"),
        ("execution", "pending_tasks", json!(1), "pending tasks"),
        ("effects", "phase", json!("draining"), "runtime phase"),
        ("effects", "pending", json!(1), "pending effects"),
    ] {
        let mut reports = Reports::create();
        reports.native[section][field] = value;
        let result = reports.compare().unwrap();
        assert_eq!(result["result"], "Failed");
        assert_eq!(result["differences"], json!([{"input":label,"reason":"structural mismatch"}]));
    }
}

#[test]
fn comparison_missing_root_fails() {
    let mut reports = Reports::create();
    reports.native["theories"]
        .as_array_mut()
        .unwrap()
        .retain(|theory| theory["name"] != "HOL.List");
    let result = reports.compare().unwrap();
    assert_eq!(result["result"], "Failed");
    assert_eq!(
        result["differences"],
        json!([{"input":"theory identities","reason":"structural mismatch"}])
    );
}

#[test]
fn comparison_changed_source_fails() {
    let mut reports = Reports::create();
    reports.native["source_files"][0]["sha256"] = json!("b".repeat(64));
    let result = reports.compare().unwrap();
    assert_eq!(result["result"], "Failed");
    assert!(result["differences"][0]["input"].as_str().unwrap().starts_with("source:"));
}

#[test]
fn comparison_reordered_fact_indices_fail() {
    let mut reports = Reports::create();
    let facts: Vec<_> = (1..=2)
        .map(|index| {
            let mut fact = make_fact(index);
            fact["name"] = json!("HOL.ordered_facts");
            fact
        })
        .collect();
    let reference = reports.reference["theories"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|theory| theory["name"] == "HOL.HOL")
        .unwrap();
    reference["fact_indexes"].as_array_mut().unwrap().push(
        json!({"name":"HOL.ordered_facts","dynamic":false,"concealed":false,"origin":"HOL.HOL"}),
    );
    reference["fact_groups"]
        .as_array_mut()
        .unwrap()
        .push(json!({"name":"HOL.ordered_facts","theorems":facts}));
    let native = reports.native["theories"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|theory| theory["name"] == "HOL.HOL")
        .unwrap();
    native["fact_indexes"] = reference["fact_indexes"].clone();
    native["fact_groups"].as_array_mut().unwrap().push(json!({"name":"HOL.ordered_facts","theorems":facts.into_iter().map(make_native_fact).collect::<Vec<_>>()}));
    assert_eq!(reports.compare().unwrap()["result"], "BlockedPrerequisite");
    let native = reports.native["theories"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|theory| theory["name"] == "HOL.HOL")
        .unwrap();
    native["fact_groups"][1]["theorems"].as_array_mut().unwrap().reverse();
    let result = reports.compare().unwrap();
    assert_eq!(result["result"], "Failed");
    assert_eq!(
        result["differences"],
        json!([{"input":"HOL.HOL:HOL.ordered_facts:members","reason":"structural mismatch"}])
    );
}

#[test]
fn comparison_hidden_burdens_missing_provenance_and_unavailable_evidence_reject() {
    for field in ["oracle_footprint", "unresolved_sort_obligations", "pending", "futures"] {
        let mut reports = Reports::create();
        reports.native_fact()[field]["value"] = json!(["unresolved"]);
        assert!(reports.compare().is_err(), "{field}");
    }
    let mut reports = Reports::create();
    reports.native_fact().as_object_mut().unwrap().remove("accepted_in");
    assert!(reports.compare().is_err());
    let mut reports = Reports::create();
    reports.native_fact()["declaration_origin"]["status"] = json!("Unavailable");
    assert!(reports.compare().is_err());
}

#[test]
fn comparison_bootstrap_prelude_and_ml_inputs_are_required_sources() {
    let mut reports = Reports::create();
    let digest = "a".repeat(64);
    reports.manifest["session_graph"]["bootstrap"]["sources"] = json!([{"source":"src/Pure/ROOT.ML","sha256":digest,
        "statements":[{"kind":"load","file":{"source":"src/Pure/context.ML","sha256":digest}}]}]);
    reports.manifest["session_graph"]["bootstrap"]["prelude_sources"] =
        json!([{"source":"src/Pure/ML/ml_process.scala","sha256":digest}]);
    reports.execution["theories"][0]["commands"] =
        json!([{"files":[{"path":"src/HOL/Tools/typedef.ML","sha256":digest}]}]);
    let sources =
        collect_required_sources(&reports.reference, &reports.execution, &reports.manifest)
            .unwrap();
    let extra: Vec<_> = sources.keys().filter(|path| !path.ends_with(".thy")).copied().collect();
    assert_eq!(
        extra,
        [
            "src/HOL/Tools/typedef.ML",
            "src/Pure/ML/ml_process.scala",
            "src/Pure/ROOT.ML",
            "src/Pure/context.ML"
        ]
    );
}

#[test]
fn comparison_known_non_source_resource_is_diagnostic_input() {
    let mut reports = Reports::create();
    let digest = "a".repeat(64);
    reports.manifest["observed_fixed_source_files"] =
        json!([{"source":"Admin/etc/build.props","sha256":digest}]);
    reports.native["source_files"]
        .as_array_mut()
        .unwrap()
        .push(json!({"path":"Admin/etc/build.props","sha256":digest}));
    assert_eq!(reports.compare().unwrap()["result"], "BlockedPrerequisite");
    reports.native["source_files"].as_array_mut().unwrap().last_mut().unwrap()["sha256"] =
        json!("b".repeat(64));
    let result = reports.compare().unwrap();
    assert_eq!(result["result"], "Failed");
    assert_eq!(
        result["differences"],
        json!([{"input":"additional source:Admin/etc/build.props","reason":"structural mismatch"}])
    );
}

#[test]
fn comparison_duplicate_json_fields_and_changed_frozen_bytes_reject() {
    let directory = tempfile::tempdir().unwrap();
    let duplicate = directory.path().join("duplicate.json");
    std::fs::write(&duplicate, r#"{"result":"Failed","result":"Succeeded"}"#).unwrap();
    assert!(read_json(&duplicate).is_err());
    std::fs::create_dir(directory.path().join("inventory")).unwrap();
    std::fs::write(directory.path().join("inventory/inventory.json"), "{}").unwrap();
    let manifest = json!({"reference_runs":{"artifacts":{"inventory":{"path":"inventory/inventory.json","bytes":2,"sha256":"a".repeat(64)}}}});
    assert!(load_frozen_artifact(&manifest, directory.path(), "inventory").is_err());
}

#[test]
fn comparison_native_abs_preserves_type_and_rejects_unknown_fields() {
    let typ = json!({"kind":"Type","name":"HOL.bool","args":[]});
    let mut native = json!({"kind":"Abs","binder_type":typ,"body":{"kind":"Bound","index":0}});
    let reference = json!({"kind":"Abs","name":"x","type":typ,"body":{"kind":"Bound","index":0}});
    assert!(isabelle_evidence::compare_syntax::match_terms(&reference, &native).unwrap());
    native["unresolved"] = json!(true);
    assert!(isabelle_evidence::compare_syntax::match_terms(&reference, &native).is_err());
}

#[cfg(unix)]
#[test]
fn comparison_symlinked_manifest_component_rejects_before_open() {
    use std::os::unix::fs::symlink;
    let directory = tempfile::tempdir().unwrap();
    let real = directory.path().join("real");
    std::fs::create_dir(&real).unwrap();
    std::fs::write(real.join("manifest.json"), "{}").unwrap();
    let alias = directory.path().join("alias");
    symlink(&real, &alias).unwrap();
    assert!(
        xtask::reference::compare::run(
            &real.join("frozen.json"),
            &real,
            &real.join("native.json"),
            Some(&alias.join("manifest.json")),
            Some(&directory.path().join("approval.json")),
        )
        .is_err()
    );
}
