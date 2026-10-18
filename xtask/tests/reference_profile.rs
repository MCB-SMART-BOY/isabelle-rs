use std::fs;
use std::path::{Path, PathBuf};

use serde_json::{Value, json};
use sha1::{Digest as _, Sha1};
use xtask::reference::{decode_inventory::ROOTS, profile::build_reference_profile};

fn digest(bytes: &[u8]) -> String {
    xtask::reference::common::digest_bytes(bytes)
}
fn make_source(root: &Path, relative: &str, bytes: &[u8]) {
    let path = root.join(relative);
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, bytes).unwrap();
}
fn command(name: &str, source: &str, line: u64, offset: u64, sequence: u64, files: Value) -> Value {
    json!({"name": name, "source": source, "line": line, "offset": offset, "sequence": sequence, "skipped": false, "files": files})
}
fn executed_theory(name: &str, source: &str, sha256: &str) -> Value {
    json!({"name": name, "source": source, "sha256": sha256, "commands": [command("section", source, 1, 1, 1, json!([])), command("theory", source, 2, 8, 2, json!([])), command("end", source, 3, 20, 3, json!([]))]})
}
struct Fixture {
    _directory: tempfile::TempDir,
    root: PathBuf,
    inventory: Value,
    execution: Value,
}
fn fixture() -> Fixture {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path().join("fixed-source");
    let names: Vec<String> = std::iter::once("Pure".to_owned())
        .chain((0..57).map(|index| format!("HOL.Dependency_{index}")))
        .chain(ROOTS.map(str::to_owned))
        .collect();
    let mut theories = Vec::new();
    let mut manifest = serde_json::Map::new();
    let mut executed = Vec::new();
    for (index, name) in names.iter().enumerate() {
        let relative = format!("src/{}.thy", name.replace('.', "/"));
        let content = format!("theory {name}\nbegin\nend\n");
        make_source(&root, &relative, content.as_bytes());
        let hash = digest(content.as_bytes());
        manifest.insert(relative.clone(), json!(hash));
        let parents = if index == 0 {
            vec![]
        } else if name.starts_with("HOL.Dependency_") {
            vec![names[index - 1].clone()]
        } else if name == "HOL.HOL" {
            vec!["HOL.Dependency_56".to_owned()]
        } else {
            vec!["HOL.HOL".to_owned()]
        };
        theories.push(json!({"name": name, "parents": parents, "import_specifications": parents, "source": relative}));
        if name != "Pure" {
            executed.push(executed_theory(name, &relative, &hash));
        }
    }
    theories
        .sort_by(|left, right| left["name"].as_str().unwrap().cmp(right["name"].as_str().unwrap()));
    let inventory = json!({"schema_version": 1, "reference": "Isabelle2025", "roots": ROOTS, "source_sha256": manifest, "theories": theories});
    let execution = json!({"schema": 1, "reference": "Isabelle2025", "session": "Reference_Execution", "roots": ROOTS, "initial_theories": ["Pure", "ML_Bootstrap", "Pure.Sessions"], "coverage": {"observed": ["executed_theory_commands", "resolved_ML_file_inputs"], "unavailable": ["Pure_bootstrap_command_spans", "anonymous_ephemeral_facts", "unregistered_proof_steps", "dynamic_fact_evaluations", "ML_runtime_call_graph", "implicit_ML_load_events"], "ordering": "per_theory_source_segments_not_global_thread_order", "excluded_observer_theory": "Reference_Execution.Reference_Observer"}, "theories": executed});
    Fixture { _directory: directory, root, inventory, execution }
}
fn event(path: &str, result: &str, sequence: u64, syscall: &str, resolved: Option<&str>) -> Value {
    let mut event = json!({"tid": 39, "timestamp": format!("100.{sequence:06}"), "syscall": syscall, "path": path, "result": result, "sequence": sequence});
    if let Some(path) = resolved {
        event["resolved_path"] = json!(path);
    }
    event
}
fn trace(phase: &str, events: Vec<Value>) -> Value {
    let unresolved = events
        .iter()
        .filter(|entry| {
            !entry["path"].as_str().unwrap().starts_with('/')
                && entry.get("resolved_path").is_none()
        })
        .count();
    json!({"phase": phase, "summary": {"complete": true, "error_count": 0, "event_count": events.len(), "scope": ["execve", "execveat", "open", "openat"], "unresolved_relative_paths": unresolved, "relative_paths_resolved": unresolved == 0}, "events": events})
}
fn traces(build: Vec<Value>) -> Vec<Value> {
    vec![trace("build", build), trace("inventory", vec![])]
}
fn build(fixture: &Fixture, traces: &[Value]) -> Result<Value, xtask::runner::StepError> {
    build_reference_profile(&fixture.inventory, &fixture.execution, &fixture.root, traces)
}
fn add_file_command(fixture: &mut Fixture, name: &str, relative: &str, position: u64) {
    let bytes = format!("val {} = true;\n", name.replace('.', "_"));
    make_source(&fixture.root, relative, bytes.as_bytes());
    let theory = fixture.execution["theories"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|theory| theory["name"] == name)
        .unwrap();
    let source = theory["source"].as_str().unwrap().to_owned();
    let sha1 = format!("{:x}", Sha1::digest(bytes.as_bytes()));
    theory["commands"].as_array_mut().unwrap().insert(
        2,
        command(
            "ML_file",
            &source,
            2,
            10 + position,
            3,
            json!([{"path": relative, "sha1": sha1, "sha256": digest(bytes.as_bytes())}]),
        ),
    );
    theory["commands"][3] = command("end", &source, 3, 20 + position, 4, json!([]));
}
fn assert_rejected(fixture: &Fixture, traces: &[Value], message: &str) {
    let error = build(fixture, traces).unwrap_err();
    assert!(error.to_string().contains(message), "{error}");
}

#[test]
fn reference_profile_observations_preserve_occurrences_and_scopes() {
    let mut sample = fixture();
    let source_a = "src/HOL/Tools/probe.ML";
    let source_b = "src/Pure/Tools/probe.ML";
    add_file_command(&mut sample, "HOL.HOL", source_a, 0);
    add_file_command(&mut sample, "HOL.List", source_b, 1);
    let events = vec![
        event("probe.ML", "3", 1, "openat", Some(&format!("/work/fixed-source/{source_a}"))),
        event(&format!("/work/fixed-source/{source_b}"), "4", 2, "openat", None),
        event(
            "/work/fixed-source/lib/classes/New.class",
            "5",
            3,
            "openat",
            Some("/work/fixed-source/lib/classes/New.class"),
        ),
        event("/work/fixed-source/bin/isabelle", "0", 4, "execve", None),
        event("relative/unknown.ML", "-1", 5, "openat", None),
        event(&format!("/work/fixed-source/{source_a}"), "-1", 6, "openat", None),
        event("/bin/unavailable", "-2", 7, "execve", None),
    ];
    let result = build(&sample, &traces(events)).unwrap();
    let hol = result["theory_graph"]["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|node| node["name"] == "HOL.HOL")
        .unwrap();
    assert_eq!(hol["parents"], json!(["HOL.Dependency_56"]));
    assert_eq!(hol["sha256"], sample.inventory["source_sha256"][hol["source"].as_str().unwrap()]);
    let ml = result["command_requirements"]
        .as_array()
        .unwrap()
        .iter()
        .find(|requirement| requirement["name"] == "ML_file")
        .unwrap();
    assert_eq!(
        ml["occurrences"]
            .as_array()
            .unwrap()
            .iter()
            .map(|item| (
                item["theory"].as_str().unwrap(),
                item["offset"].as_u64().unwrap(),
                item["sequence"].as_u64().unwrap()
            ))
            .collect::<Vec<_>>(),
        [("HOL.HOL", 10, 3), ("HOL.List", 11, 3)]
    );
    assert_eq!(ml["native_rust_status"], "Unsupported");
    assert_eq!(ml["scope"], "general_official_source_execution");
    assert_eq!(
        result["ml_file_bindings"]
            .as_array()
            .unwrap()
            .iter()
            .map(|binding| binding["file"]["path"].as_str().unwrap())
            .collect::<Vec<_>>(),
        [source_a, source_b]
    );
    assert_eq!(
        result["fixed_source_reads"]
            .as_array()
            .unwrap()
            .iter()
            .map(|input| input["source"].as_str().unwrap())
            .collect::<Vec<_>>(),
        [source_a, source_b]
    );
    assert_eq!(result["generated_inputs"][0]["sequence"], 3);
    assert_eq!(result["external_executables"][0]["sequence"], 4);
    assert_eq!(result["unresolved_resources"][0]["credited_as_input"], false);
    assert_eq!(result["unresolved_resources"][0]["path"], "relative/unknown.ML");
}

#[test]
fn reference_profile_non_theory_source_read_hashed() {
    let sample = fixture();
    let relative = "etc/settings";
    let bytes = b"ISABELLE_SETTING=literal\n";
    make_source(&sample.root, relative, bytes);
    let result = build(
        &sample,
        &traces(vec![event(&format!("/work/fixed-source/{relative}"), "3", 1, "openat", None)]),
    )
    .unwrap();
    assert_eq!(
        result["fixed_source_reads"],
        json!([{"phase": "build", "tid": 39, "sequence": 1, "timestamp": "100.000001", "syscall": "openat", "path": "/work/fixed-source/etc/settings", "result": "3", "source": relative, "sha256": digest(bytes)}])
    );
}

#[test]
fn reference_profile_incomplete_graph_rejected() {
    let mut sample = fixture();
    sample.inventory["roots"].as_array_mut().unwrap().pop();
    assert_rejected(&sample, &traces(vec![]), "roots");
    let mut sample = fixture();
    sample.execution["theories"].as_array_mut().unwrap().pop();
    assert_rejected(&sample, &traces(vec![]), "Executed theory set");
    let mut sample = fixture();
    sample.inventory["theories"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|node| node["name"] == "HOL.HOL")
        .unwrap()["parents"] = json!(["Missing"]);
    assert_rejected(&sample, &traces(vec![]), "parent");
}

#[test]
fn reference_profile_escaping_source_rejected() {
    let sample = fixture();
    assert_rejected(
        &sample,
        &traces(vec![event("/work/fixed-source/src/HOL/../../outside.ML", "3", 1, "openat", None)]),
        "unsafe",
    );
    let external = sample._directory.path().join("outside.ML");
    fs::write(&external, b"outside").unwrap();
    let link = sample.root.join("src/HOL/Tools/escape.ML");
    fs::create_dir_all(link.parent().unwrap()).unwrap();
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink(&external, &link).unwrap();
        assert!(
            build(
                &sample,
                &traces(vec![event(
                    "/work/fixed-source/src/HOL/Tools/escape.ML",
                    "3",
                    1,
                    "openat",
                    None
                )])
            )
            .is_err()
        );
    }
}

#[test]
fn reference_profile_failed_syscalls_are_not_credited() {
    let sample = fixture();
    let events = vec![
        event("/work/fixed-source/src/Pure/Pure.thy", "-1", 1, "openat", None),
        event("/usr/bin/no-such-executable", "-1", 2, "execve", None),
        event("unresolved/data", "3", 3, "openat", None),
    ];
    let result = build(&sample, &traces(events)).unwrap();
    assert_eq!(result["fixed_source_reads"], json!([]));
    assert_eq!(result["external_executables"], json!([]));
    assert_eq!(result["unresolved_resources"][0]["path"], "unresolved/data");
}

#[test]
fn reference_profile_changed_inventory_source_rejected() {
    let sample = fixture();
    let source = sample.inventory["theories"][0]["source"].as_str().unwrap();
    fs::write(sample.root.join(source), b"changed after observation\n").unwrap();
    assert_rejected(&sample, &traces(vec![]), "SHA256");
}

#[test]
fn reference_profile_incomplete_trace_rejected() {
    let sample = fixture();
    let mut observations = traces(vec![]);
    observations[1]["summary"]["complete"] = json!(false);
    assert_rejected(&sample, &observations, "incomplete syscall observation");
}

#[cfg(unix)]
#[test]
fn reference_profile_in_root_alias_rejects_changed_file_identity() {
    let mut sample = fixture();
    let relative = "src/HOL/Tools/probe.ML";
    add_file_command(&mut sample, "HOL.HOL", relative, 0);
    assert!(build(&sample, &traces(vec![])).is_ok());
    let alias = "src/HOL/Tools/alias.ML";
    std::os::unix::fs::symlink("probe.ML", sample.root.join(alias)).unwrap();
    let theory = sample.execution["theories"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|theory| theory["name"] == "HOL.HOL")
        .unwrap();
    theory["commands"][2]["files"][0]["path"] = json!(alias);
    assert_rejected(&sample, &traces(vec![]), "identity");
}
