#![cfg(unix)]

use std::fs;
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};

use serde_json::json;

use super::{build_options, validate};
use crate::reference::{artifacts, common, prepare};

fn create_build_run(workspace: &Path) -> PathBuf {
    let run = workspace.join("runs/build-example");
    let heaps = run.join("home/.isabelle/p0-reference/heaps/platform");
    fs::create_dir_all(&heaps).unwrap();
    fs::write(heaps.join("Pure"), b"Pure observation input").unwrap();
    fs::write(heaps.join("HOL"), b"HOL observation input").unwrap();
    let config = run.join("home/.isabelle/p0-reference/etc");
    fs::create_dir_all(&config).unwrap();
    fs::write(config.join("settings"), prepare::SETTINGS).unwrap();
    fs::write(config.join("components"), "").unwrap();
    fs::create_dir(run.join("generated-classes")).unwrap();
    fs::write(run.join("generated-classes/isabelle.jar"), b"generated reference classes").unwrap();
    fs::create_dir(run.join("generated-demo")).unwrap();
    fs::write(run.join("stdout.log"), "Building Pure ...\nFinished Pure (\nBuilding HOL ...\nHOL: theory Tools.Code_Generator\nHOL: theory HOL.HOL\nFinished HOL (").unwrap();
    common::write_json_exclusive(&run.join("command.json"), &json!({"arguments":build_options()}))
        .unwrap();
    fs::write(run.join("events.jsonl"), "").unwrap();
    common::write_json_exclusive(
        &run.join(artifacts::INPUT_MANIFEST),
        &artifacts::collect_build_inputs(&run).unwrap(),
    )
    .unwrap();
    let result = json!({"operation":"build","exit_code":0,"interruption":null,"trace":{"complete":true},"prepared_sha256":"example-preparation","stdout_sha256":common::digest_file(&run.join("stdout.log")).unwrap(),"command_sha256":common::digest_file(&run.join("command.json")).unwrap(),"events_sha256":common::digest_file(&run.join("events.jsonl")).unwrap(),"build_inputs_sha256":common::digest_file(&run.join(artifacts::INPUT_MANIFEST)).unwrap()});
    common::write_json_exclusive(&run.join("result.json"), &result).unwrap();
    run
}

#[test]
fn require_build_run_mutated_inputs_rejects_reuse() {
    for relative in [
        "home/.isabelle/p0-reference/heaps/platform/HOL",
        "generated-classes/isabelle.jar",
        "home/.isabelle/p0-reference/etc/settings",
        "events.jsonl",
    ] {
        let workspace = tempfile::tempdir().unwrap();
        let run = create_build_run(workspace.path());
        assert!(
            validate::require_build_run(&run, workspace.path(), "example-preparation", "").is_ok()
        );
        fs::write(run.join(relative), b"changed execution input").unwrap();
        assert!(
            validate::require_build_run(&run, workspace.path(), "example-preparation", "").is_err(),
            "{relative}"
        );
    }
}

#[test]
fn make_run_directory_symlink_rejects_without_writing_outside() {
    let root = tempfile::tempdir().unwrap();
    let workspace = root.path().join("workspace");
    let outside = root.path().join("outside");
    fs::create_dir(&workspace).unwrap();
    fs::create_dir(&outside).unwrap();
    symlink(&outside, workspace.join("runs")).unwrap();
    assert!(validate::make_run_directory(&workspace, "build").is_err());
    assert_eq!(fs::read_dir(outside).unwrap().count(), 0);
}

#[test]
fn require_build_run_symlinked_home_rejects_reuse() {
    let root = tempfile::tempdir().unwrap();
    let run = create_build_run(root.path());
    let outside = root.path().join("outside-home");
    fs::rename(run.join("home"), &outside).unwrap();
    symlink(outside, run.join("home")).unwrap();
    assert!(validate::require_build_run(&run, root.path(), "example-preparation", "").is_err());
}

#[test]
fn collect_build_inputs_symlinked_generated_classes_rejects() {
    let root = tempfile::tempdir().unwrap();
    let run = create_build_run(root.path());
    let outside = root.path().join("outside");
    fs::rename(run.join("generated-classes"), &outside).unwrap();
    symlink(outside, run.join("generated-classes")).unwrap();
    assert!(artifacts::collect_build_inputs(&run).is_err());
}

#[test]
fn publish_existing_evidence_rejects_overwrite() {
    let root = tempfile::tempdir().unwrap();
    let result =
        super::finalize::publish(root.path(), "execution", &json!({"observed": true})).unwrap();
    assert!(result["execution_sha256"].is_string());
    assert!(
        super::finalize::publish(root.path(), "execution", &json!({"observed": false})).is_err()
    );
    assert_eq!(
        common::read_json(&root.path().join("execution.json")).unwrap(),
        json!({"observed": true})
    );
}

#[test]
fn decode_malformed_execution_creates_no_evidence() {
    let root = tempfile::tempdir().unwrap();
    let output = root.path().join("execution.json");
    let decoded = crate::reference::decode_execution::decode_execution(
        "not a YXML document",
        root.path(),
        &json!({}),
    );
    assert!(decoded.is_err());
    assert!(!output.exists());
}

#[test]
fn collect_build_inputs_nested_directories_have_unique_paths() {
    let root = tempfile::tempdir().unwrap();
    let run = create_build_run(root.path());
    let manifest = artifacts::collect_build_inputs(&run).unwrap();
    let entries = manifest["entries"].as_array().unwrap();
    let mut paths = std::collections::BTreeSet::new();
    for entry in entries {
        assert!(paths.insert(entry["path"].as_str().unwrap()), "duplicate build input {entry}");
    }
}

#[test]
fn require_build_run_single_record_directory_manifest_accepts_reuse() {
    let root = tempfile::tempdir().unwrap();
    let run = create_build_run(root.path());
    let manifest_path = run.join(artifacts::INPUT_MANIFEST);
    let mut manifest = common::read_json(&manifest_path).unwrap();
    let entries = manifest["entries"].as_array_mut().unwrap();
    entries.dedup_by(|left, right| left["path"] == right["path"]);
    fs::write(&manifest_path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    let result_path = run.join("result.json");
    let mut result = common::read_json(&result_path).unwrap();
    result["build_inputs_sha256"] = json!(common::digest_file(&manifest_path).unwrap());
    fs::write(result_path, serde_json::to_vec(&result).unwrap()).unwrap();
    validate::require_build_run(&run, root.path(), "example-preparation", "").unwrap();
}
