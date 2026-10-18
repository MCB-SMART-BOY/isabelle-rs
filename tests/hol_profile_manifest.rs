use isabelle_rs::hol::theory_graph::TheoryGraph;
use std::{
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT_FIXTURE: AtomicUsize = AtomicUsize::new(0);

struct Fixture {
    dir: PathBuf,
    source_root: PathBuf,
    context_root: PathBuf,
}

impl Fixture {
    fn new() -> Self {
        let dir = std::env::temp_dir().join(format!(
            "isabelle-hol-profile-{}-{}",
            std::process::id(),
            NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed)
        ));
        let source_root = dir.join("source");
        let context_root = dir.join("context");
        fs::create_dir_all(&source_root).expect("create source fixture directory");
        fs::create_dir(&context_root).expect("create context fixture directory");
        fs::write(
            source_root.join("Tiny.thy"),
            "theory Tiny imports Main begin\nlemma sample: \"True\"\n  by simp\nend\n",
        )
        .expect("write theory source");
        fs::write(context_root.join("Context.thy"), "theory Context imports Main begin\nend\n")
            .expect("write context source");
        Self { dir, source_root, context_root }
    }

    fn manifest(&self) -> PathBuf {
        self.dir.join("manifest.json")
    }

    fn run(
        &self,
        mode: &str,
        manifest: &Path,
        theory: &str,
        lemma: &str,
        budget: Option<&str>,
    ) -> Output {
        let mut command = Command::new(env!("CARGO_BIN_EXE_isabelle-profile-hol"));
        command
            .args([
                "--source-root",
                self.source_root.to_str().expect("source path is UTF-8"),
                "--context-root",
                self.context_root.to_str().expect("context path is UTF-8"),
                "--theory",
                theory,
                "--lemma",
                lemma,
                mode,
            ])
            .arg(manifest);
        if let Some(limit) = budget {
            command.args(["--auto-limit", limit]);
        }
        command.output().expect("execute profile worker")
    }

    fn create_manifest(&self) -> serde_json::Value {
        let output = self.run("--manifest-out", &self.manifest(), "Tiny", "sample", Some("1"));
        assert_eq!(output.status.code(), Some(0), "{}", String::from_utf8_lossy(&output.stderr));
        let events: Vec<serde_json::Value> = output
            .stdout
            .split(|byte| *byte == b'\n')
            .filter(|line| !line.is_empty())
            .map(|line| serde_json::from_slice(line).expect("one JSON event per line"))
            .collect();
        events.into_iter().find(|event| event["event"] == "result").expect("completed diagnostic")
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.dir).expect("remove fixture directory");
    }
}

#[test]
fn manifest_replay_unchanged_source_keeps_original_target_and_budget() {
    let fixture = Fixture::new();
    let original = fixture.create_manifest();
    let replay = fixture.run("--manifest-in", &fixture.manifest(), "Tiny", "sample", None);
    assert_eq!(replay.status.code(), Some(0), "{}", String::from_utf8_lossy(&replay.stderr));
    let events: Vec<serde_json::Value> = replay
        .stdout
        .split(|byte| *byte == b'\n')
        .filter(|line| !line.is_empty())
        .map(|line| serde_json::from_slice(line).unwrap())
        .collect();
    let result =
        events.iter().find(|event| event["event"] == "result").expect("completed diagnostic");
    assert_eq!(result["auto_limit"], 1);
    assert_eq!(result["theory"], "Tiny");
    assert_eq!(result["lemma"], "sample");
    assert_eq!(result["outcome"], original["outcome"]);
}

#[test]
fn manifest_replay_quoted_context_keeps_legacy_theory_identity() {
    let fixture = Fixture::new();
    fs::write(
        fixture.context_root.join("Context.thy"),
        "theory \"Context\" imports Main begin\nend\n",
    )
    .expect("write quoted theory header");
    let original = fixture.create_manifest();
    let replay = fixture.run("--manifest-in", &fixture.manifest(), "Tiny", "sample", None);
    assert_eq!(replay.status.code(), Some(0), "{}", String::from_utf8_lossy(&replay.stderr));
    let result = replay
        .stdout
        .split(|byte| *byte == b'\n')
        .filter(|line| !line.is_empty())
        .map(|line| serde_json::from_slice::<serde_json::Value>(line).unwrap())
        .find(|event| event["event"] == "result")
        .expect("completed replay");
    assert_eq!(result["outcome"], original["outcome"]);
}

#[test]
fn manifest_replay_modified_source_rejects_changed_hash() {
    let fixture = Fixture::new();
    fixture.create_manifest();
    fs::write(
        fixture.source_root.join("Tiny.thy"),
        "theory Tiny imports Main begin\nlemma sample: \"False\" by simp\nend\n",
    )
    .expect("alter source");
    let replay = fixture.run("--manifest-in", &fixture.manifest(), "Tiny", "sample", None);
    assert_eq!(replay.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&replay.stderr).contains("source hash changed"));
    assert!(!String::from_utf8_lossy(&replay.stdout).contains("\"event\":\"result\""));
}
#[test]
fn manifest_replay_modified_context_rejects_changed_hash() {
    let fixture = Fixture::new();
    fixture.create_manifest();
    fs::write(
        fixture.context_root.join("Context.thy"),
        "theory Context imports Main begin\nlemma changed: \"True\" by simp\nend\n",
    )
    .expect("alter context source");
    let replay = fixture.run("--manifest-in", &fixture.manifest(), "Tiny", "sample", None);
    assert_eq!(replay.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&replay.stderr).contains("source hash changed"));
    assert!(!String::from_utf8_lossy(&replay.stdout).contains("\"event\":\"result\""));
}

#[test]
fn manifest_replay_missing_context_does_not_use_ambient_fallback() {
    let fixture = Fixture::new();
    fixture.create_manifest();
    fs::remove_file(fixture.context_root.join("Context.thy")).expect("remove context source");
    let replay = fixture.run("--manifest-in", &fixture.manifest(), "Tiny", "sample", None);
    assert_eq!(replay.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&replay.stderr).contains("failed to read diagnostic input"));
    assert!(!String::from_utf8_lossy(&replay.stdout).contains("\"event\":\"result\""));
}

#[test]
fn manifest_replay_conflicting_budget_or_target_rejects_input() {
    let fixture = Fixture::new();
    fixture.create_manifest();
    let bad_budget = fixture.run("--manifest-in", &fixture.manifest(), "Tiny", "sample", Some("2"));
    assert_eq!(bad_budget.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&bad_budget.stderr).contains("auto-limit conflicts"));
    let bad_target = fixture.run("--manifest-in", &fixture.manifest(), "Tiny", "other", None);
    assert_eq!(bad_target.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&bad_target.stderr).contains("target disagrees"));
}

#[test]
fn manifest_replay_escape_path_rejects_input() {
    let fixture = Fixture::new();
    fixture.create_manifest();
    let mut manifest: serde_json::Value =
        serde_json::from_slice(&fs::read(fixture.manifest()).expect("read manifest"))
            .expect("parse manifest");
    manifest["target"]["path"] = serde_json::json!("../outside.thy");
    fs::write(fixture.manifest(), serde_json::to_vec(&manifest).expect("serialize manifest"))
        .expect("replace test manifest");
    let replay = fixture.run("--manifest-in", &fixture.manifest(), "Tiny", "sample", None);
    assert_eq!(replay.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&replay.stderr).contains("invalid root-relative theory path"));
}

#[test]
fn manifest_replay_conflicting_theory_source_rejects_input() {
    let fixture = Fixture::new();
    fixture.create_manifest();
    fs::create_dir(fixture.source_root.join("alternate")).expect("create alternate directory");
    fs::copy(fixture.source_root.join("Tiny.thy"), fixture.source_root.join("alternate/Tiny.thy"))
        .expect("copy a separately valid source for the same theory");
    let mut manifest: serde_json::Value =
        serde_json::from_slice(&fs::read(fixture.manifest()).expect("read manifest")).unwrap();
    manifest["target"]["path"] = serde_json::json!("alternate/Tiny.thy");
    fs::write(fixture.manifest(), serde_json::to_vec(&manifest).unwrap()).unwrap();
    let replay = fixture.run("--manifest-in", &fixture.manifest(), "Tiny", "sample", None);
    assert_eq!(replay.status.code(), Some(2));
    assert!(!String::from_utf8_lossy(&replay.stdout).contains("\"event\":\"result\""));
}

#[test]
fn manifest_create_missing_proof_bearing_lemma_rejects_input() {
    let fixture = Fixture::new();
    let output = fixture.run("--manifest-out", &fixture.manifest(), "Tiny", "absent", Some("1"));
    assert_eq!(output.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("proof-bearing lemma absent not found")
    );
    assert!(!String::from_utf8_lossy(&output.stdout).contains("\"event\":\"result\""));
}

#[test]
fn manifest_duplicate_theory_records_scan_winner_and_discarded_path() {
    let fixture = Fixture::new();
    let first = fixture.source_root.join("first");
    let second = fixture.source_root.join("second");
    fs::create_dir(&first).expect("create first directory");
    fs::create_dir(&second).expect("create second directory");
    let source = "theory Duplicate imports Main begin\nlemma sample: \"True\"\n  by simp\nend\n";
    fs::write(first.join("Duplicate.thy"), source).expect("write first duplicate");
    fs::write(second.join("Duplicate.thy"), source).expect("write second duplicate");
    let mut graph = TheoryGraph::new();
    graph.scan(&fixture.source_root).expect("scan fixture with production graph");
    let winner = graph.nodes.get("Duplicate").expect("production graph winner").path.clone();

    let output =
        fixture.run("--manifest-out", &fixture.manifest(), "Duplicate", "sample", Some("1"));
    assert_eq!(output.status.code(), Some(0), "{}", String::from_utf8_lossy(&output.stderr));
    let manifest: serde_json::Value =
        serde_json::from_slice(&fs::read(fixture.manifest()).expect("read manifest"))
            .expect("parse manifest");
    let selected = manifest["target"]["path"].as_str().expect("selected target path");
    assert_eq!(fixture.source_root.join(selected), winner);
    let overrides = manifest["source_overrides"].as_array().expect("source overrides");
    let duplicate = overrides
        .iter()
        .find(|entry| entry["selected"]["theory"] == "Duplicate")
        .expect("duplicate selection");
    assert_eq!(duplicate["selected"]["path"], selected);
    assert_ne!(duplicate["discarded"]["path"], duplicate["selected"]["path"]);
}
