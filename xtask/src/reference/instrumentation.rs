//! Construct a run-private B/P/R snapshot from attested original and fixed patch bytes.
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};

use serde_json::{Value, json};

use super::{
    approved_identity::{Preapproval, is_safe_relative},
    artifacts, common, compare, prepare,
};
use crate::runner::{StepError, io_error};

const PATCH_NAMES: [&str; 21] = [
    "pure-root0",
    "pure-root",
    "pure-compiler0",
    "pure-ml-context",
    "pure-resources",
    "pure-build",
    "pure-toplevel",
    "pure-thy-info",
    "pure-thm",
    "pure-proofterm",
    "pure-facts",
    "pure-global-theory",
    "pure-outer-syntax",
    "pure-entity",
    "pure-method",
    "pure-attrib",
    "pure-context",
    "pure-theory",
    "pure-ml-env",
    "pure-future",
    "pure-context-rules",
];
const MAX_PATCH: u64 = 4 * 1024 * 1024;
const MAX_SOURCE: u64 = 512 * 1024 * 1024;

pub struct Overlay {
    pub root: PathBuf,
    pub source_snapshot_sha256: String,
    pub source_map_sha256: String,
    pub patches: Vec<Value>,
}

fn source_path(patch: &str) -> Result<String, StepError> {
    let file = patch
        .lines()
        .find_map(|line| line.strip_prefix("+++ b/"))
        .ok_or_else(|| StepError::Input("overlay patch missing destination".into()))?;
    common::require(
        is_safe_relative(file) && file.starts_with("src/Pure/"),
        format!("unsafe overlay patch destination {file}"),
    )?;
    Ok(file.into())
}

fn hunk_position(header: &str) -> Result<usize, StepError> {
    let old = header
        .strip_prefix("@@ -")
        .ok_or_else(|| StepError::Input("invalid overlay hunk header".into()))?;
    let first = old.split([',', ' ']).next().unwrap_or("");
    let position =
        first.parse::<usize>().map_err(|_| StepError::Input("invalid hunk offset".into()))?;
    Ok(position.saturating_sub(1))
}

fn apply_hunks(original: &[u8], patch: &str) -> Result<Vec<u8>, StepError> {
    let mut result = Vec::with_capacity(original.len());
    let mut source = original.split_inclusive(|byte| *byte == b'\n');
    let mut line_number = 0usize;
    let mut has_hunk = false;
    for line in patch.lines() {
        if line.starts_with("@@ -") {
            let target = hunk_position(line)?;
            common::require(target >= line_number, "overlapping overlay patch hunks")?;
            for _ in line_number..target {
                result.extend_from_slice(source.next().ok_or_else(|| {
                    StepError::Input("patch hunk exceeds original source".into())
                })?);
            }
            line_number = target;
            has_hunk = true;
            continue;
        }
        if !has_hunk || line.starts_with("\\ No newline at end of file") {
            continue;
        }
        let (action, text) = line.split_at(1);
        if !matches!(action, " " | "-" | "+") {
            return Err(StepError::Input("unexpected line in overlay hunk".into()));
        }
        let mut expected = text.as_bytes().to_vec();
        expected.push(b'\n');
        if action != "+" {
            let old = source
                .next()
                .ok_or_else(|| StepError::Input("overlay source ended early".into()))?;
            common::require(old == expected, "overlay patch context differs from original bytes")?;
            line_number += 1;
        }
        if action != "-" {
            result.extend_from_slice(&expected);
        }
    }
    common::require(has_hunk, "overlay patch contains no hunks")?;
    for old in source {
        result.extend_from_slice(old);
    }
    Ok(result)
}

fn write_patched(path: &Path, bytes: &[u8]) -> Result<(), StepError> {
    let original_mode = fs::metadata(path)
        .map_err(|source| io_error(format!("stat overlay {}", path.display()), source))?
        .permissions()
        .mode();
    let mut file = OpenOptions::new()
        .write(true)
        .truncate(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)
        .map_err(|source| io_error(format!("open overlay {}", path.display()), source))?;
    file.write_all(bytes)
        .map_err(|source| io_error(format!("write overlay {}", path.display()), source))?;
    file.set_permissions(fs::Permissions::from_mode(original_mode)).map_err(|source| {
        io_error(format!("restore overlay permissions {}", path.display()), source)
    })
}

fn patch_snapshot(
    root: &Path,
    original: &Path,
    patch_text: &str,
    approved: &super::approved_identity::ApprovedPatch,
    patch_sha256: &str,
) -> Result<Value, StepError> {
    let path = source_path(patch_text)?;
    common::require(path == approved.path, format!("patch destination differs: {path}"))?;
    let original_bytes = compare::read_checked_bytes(&original.join(&path), MAX_SOURCE)?;
    common::require(
        approved.original_sha256.as_deref() == Some(&common::digest_bytes(&original_bytes)),
        format!("overlay original bytes differ: {path}"),
    )?;
    let patched = apply_hunks(&original_bytes, patch_text)?;
    common::require(
        common::digest_bytes(&patched) == approved.patched_sha256,
        format!("overlay patched bytes differ: {path}"),
    )?;
    write_patched(&root.join(&path), &patched)?;
    Ok(json!({"path":path,"original_sha256":approved.original_sha256,
        "patched_sha256":approved.patched_sha256,"patch_sha256":patch_sha256}))
}

fn write_new_observer(
    root: &Path,
    approved: &super::approved_identity::ApprovedPatch,
    bytes: &[u8],
) -> Result<Value, StepError> {
    let path = "src/Pure/reference_observation.ML";
    common::require(
        approved.path == path
            && approved.original_sha256.is_none()
            && common::digest_bytes(bytes) == approved.patched_sha256,
        "new observer source is not preapproved",
    )?;
    let path = root.join(path);
    let mut file = OpenOptions::new()
        .create_new(true)
        .write(true)
        .mode(0o600)
        .open(&path)
        .map_err(|source| io_error("create approved overlay observer", source))?;
    file.write_all(bytes).map_err(|source| io_error("write approved overlay observer", source))?;
    Ok(json!({"path":approved.path,"original_sha256":Value::Null,
        "patched_sha256":approved.patched_sha256,"patch_sha256":approved.patch_sha256}))
}

fn collect_original_sources(
    report: &Value,
    original: &Path,
) -> Result<BTreeMap<String, String>, StepError> {
    let entries = report["source_files"]
        .as_array()
        .ok_or_else(|| StepError::Input("prepared original source list missing".into()))?;
    let mut files = BTreeMap::new();
    for entry in entries {
        let path = entry["path"]
            .as_str()
            .ok_or_else(|| StepError::Input("invalid original path".into()))?;
        let expected = entry["sha256"]
            .as_str()
            .ok_or_else(|| StepError::Input("invalid original SHA256".into()))?;
        common::require(
            is_safe_relative(path)
                && files.insert(path.into(), expected.into()).is_none()
                && common::digest_bytes(&compare::read_checked_bytes(
                    &original.join(path),
                    MAX_SOURCE,
                )?) == expected,
            format!("original frozen source differs: {path}"),
        )?;
    }
    Ok(files)
}

fn hash_snapshot(
    root: &Path,
    original: &BTreeMap<String, String>,
    patches: &[Value],
) -> Result<String, StepError> {
    let changes: BTreeMap<_, _> = patches
        .iter()
        .map(|patch| {
            (
                patch["path"].as_str().unwrap_or_default(),
                patch["patched_sha256"].as_str().unwrap_or_default(),
            )
        })
        .collect();
    let mut expected = original.clone();
    for (&path, &hash) in &changes {
        let old = expected.insert(path.into(), hash.into());
        common::require(
            !hash.is_empty() && old.as_deref() == original.get(path).map(String::as_str),
            format!("overlay source map conflict: {path}"),
        )?;
    }
    let mut lines = String::new();
    for (path, hash) in &expected {
        let actual_path = if let Some(name) = path.strip_prefix("session/") {
            root.parent()
                .ok_or_else(|| StepError::Input("overlay has no run root".into()))?
                .join("session")
                .join(name)
        } else {
            root.join(path)
        };
        common::require(
            !path.contains('\t')
                && !path.contains('\n')
                && common::digest_bytes(&compare::read_checked_bytes(&actual_path, MAX_SOURCE)?)
                    == *hash,
            format!("overlay source identity differs: {path}"),
        )?;
        lines.push_str(&format!("{path}\t{hash}\n"));
    }
    prepare::exclusive_text(
        &root
            .parent()
            .ok_or_else(|| StepError::Input("overlay has no run root".into()))?
            .join("source-hashes.tsv"),
        &lines,
    )?;
    Ok(common::digest_bytes(lines.as_bytes()))
}

fn append_identity(
    entries: &mut BTreeMap<String, Vec<u8>>,
    name: String,
    bytes: Vec<u8>,
) -> Result<(), StepError> {
    common::require(
        entries.insert(name.clone(), bytes).is_none(),
        format!("duplicate overlay byte input {name}"),
    )
}

fn overlay_id(entries: &BTreeMap<String, Vec<u8>>) -> String {
    let mut bytes = Vec::new();
    for (name, content) in entries {
        bytes.extend_from_slice(format!("{name}\0{}\0", content.len()).as_bytes());
        bytes.extend_from_slice(content);
    }
    common::digest_bytes(&bytes)
}

fn copy_session_sources(
    repository: &Path,
    run: &Path,
    approved: &Preapproval,
    seen: &mut BTreeSet<String>,
    patches: &mut Vec<Value>,
    inputs: &mut BTreeMap<String, Vec<u8>>,
) -> Result<(), StepError> {
    let destination = run.join("session");
    fs::create_dir(&destination)
        .map_err(|source| io_error("create isolated observer inputs", source))?;
    for name in super::execute::OBSERVER_FILES {
        let path = format!("session/{name}");
        let bytes = compare::read_checked_bytes(
            &repository.join("scripts/reference").join(name),
            MAX_PATCH,
        )?;
        let hash = common::digest_bytes(&bytes);
        let expected = approved
            .approved_patch_sha256
            .iter()
            .find(|patch| patch.path == path)
            .ok_or_else(|| StepError::Input(format!("unapproved observer input {path}")))?;
        common::require(
            expected.original_sha256.is_none()
                && expected.patched_sha256 == hash
                && expected.patch_sha256 == hash
                && seen.insert(path.clone()),
            format!("observer source differs from approval: {path}"),
        )?;
        let mut file = OpenOptions::new()
            .create_new(true)
            .write(true)
            .mode(0o600)
            .open(destination.join(name))
            .map_err(|source| io_error("create isolated observer source", source))?;
        file.write_all(&bytes)
            .map_err(|source| io_error("write isolated observer source", source))?;
        patches.push(json!({"path":path,"original_sha256":Value::Null,
            "patched_sha256":hash,"patch_sha256":hash}));
        append_identity(inputs, format!("scripts/reference/{name}"), bytes)?;
    }
    Ok(())
}

pub fn prepare_overlay(
    repository: &Path,
    workspace: &Path,
    run: &Path,
    report: &Value,
    approved: &Preapproval,
    bwrap: &Path,
    strace: &Path,
) -> Result<Overlay, StepError> {
    let original = workspace.join("fixed-source");
    let source_files = collect_original_sources(report, &original)?;
    let root = run.join("fixed-source");
    prepare::archive::verify_tree(
        &workspace.join("fixed-source.tar"),
        &root,
        false,
        "",
        &["lib/classes", "src/Tools/Demo/lib"],
    )?;
    let inputs = repository.join("scripts/reference/instrumentation");
    let mut patches = Vec::new();
    let mut identity = BTreeMap::new();
    let mut seen = BTreeSet::new();
    for name in PATCH_NAMES {
        let path = inputs.join(format!("{name}.patch"));
        let bytes = compare::read_checked_bytes(&path, MAX_PATCH)?;
        let patch_sha256 = common::digest_bytes(&bytes);
        let text = std::str::from_utf8(&bytes)
            .map_err(|_| StepError::Input(format!("non-UTF8 patch {}", path.display())))?;
        let destination = source_path(text)?;
        let approved_patch = approved
            .approved_patch_sha256
            .iter()
            .find(|item| item.path == destination)
            .ok_or_else(|| StepError::Input(format!("unapproved patch {destination}")))?;
        common::require(
            patch_sha256 == approved_patch.patch_sha256 && seen.insert(destination.clone()),
            format!("overlay patch bytes are not preapproved: {}", path.display()),
        )?;
        let patch = patch_snapshot(&root, &original, text, approved_patch, &patch_sha256)?;
        append_identity(
            &mut identity,
            format!("scripts/reference/instrumentation/{name}.patch"),
            bytes,
        )?;
        patches.push(patch);
    }
    let observer =
        compare::read_checked_bytes(&inputs.join("reference_observation.ML"), MAX_PATCH)?;
    let observer_patch = approved
        .approved_patch_sha256
        .iter()
        .find(|patch| patch.path == "src/Pure/reference_observation.ML")
        .ok_or_else(|| StepError::Input("observer source is not preapproved".into()))?;
    common::require(
        common::digest_bytes(&observer) == approved.observer_sha256
            && observer_patch.patch_sha256 == approved.observer_sha256
            && seen.insert(observer_patch.path.clone()),
        "overlay observer differs from approval",
    )?;
    append_identity(
        &mut identity,
        "scripts/reference/instrumentation/reference_observation.ML".into(),
        observer.clone(),
    )?;
    patches.push(write_new_observer(&root, observer_patch, &observer)?);
    copy_session_sources(repository, run, approved, &mut seen, &mut patches, &mut identity)?;
    common::require(
        seen.len() == approved.approved_patch_sha256.len(),
        "overlay patch set differs from preapproval",
    )?;
    let generator =
        std::env::current_exe().map_err(|source| io_error("locate executing generator", source))?;
    let bytes = compare::read_checked_bytes(&generator, MAX_SOURCE)?;
    common::require(
        common::digest_bytes(&bytes) == approved.generator_sha256,
        "generator executable differs from preapproved bytes",
    )?;
    append_identity(&mut identity, "tools/xtask-executable".into(), bytes)?;
    append_identity(
        &mut identity,
        "tools/bwrap".into(),
        compare::read_checked_bytes(bwrap, MAX_SOURCE)?,
    )?;
    append_identity(
        &mut identity,
        "tools/strace".into(),
        compare::read_checked_bytes(strace, MAX_SOURCE)?,
    )?;
    common::require(
        overlay_id(&identity) == approved.overlay_id,
        "overlay complete sorted tool and patch bytes differ from approval",
    )?;
    let source_map_sha256 = hash_snapshot(&root, &source_files, &patches)?;
    let source_snapshot_sha256 = snapshot_sha256(run)?;
    Ok(Overlay { root, source_snapshot_sha256, source_map_sha256, patches })
}

pub fn snapshot_sha256(run: &Path) -> Result<String, StepError> {
    let source = artifacts::source_tree_sha256(&run.join("fixed-source"))?;
    let session = artifacts::source_tree_sha256(&run.join("session"))?;
    Ok(common::digest_bytes(format!("fixed-source:{source}\nsession:{session}\n").as_bytes()))
}

pub fn attest_overlay(
    run: &Path,
    expected_snapshot: &str,
    expected_map: &str,
) -> Result<(), StepError> {
    common::require(
        snapshot_sha256(run)? == expected_snapshot,
        "complete immutable reference snapshot differs before and after execution",
    )?;
    let bytes = compare::read_checked_bytes(&run.join("source-hashes.tsv"), MAX_SOURCE)?;
    common::require(
        common::digest_bytes(&bytes) == expected_map,
        "reference source map changed after preparation",
    )?;
    let text = std::str::from_utf8(&bytes)
        .map_err(|_| StepError::Input("invalid source hash map UTF-8".into()))?;
    let mut prior = "";
    for line in text.lines() {
        let (path, expected) = line
            .split_once('\t')
            .ok_or_else(|| StepError::Input("invalid source map entry".into()))?;
        common::require(
            is_safe_relative(path) && path > prior && super::approved_identity::is_hash(expected),
            format!("noncanonical source map path {path}"),
        )?;
        prior = path;
        let source = if let Some(name) = path.strip_prefix("session/") {
            run.join("session").join(name)
        } else {
            run.join("fixed-source").join(path)
        };
        common::require(
            compare::digest_checked_file(&source, MAX_SOURCE)? == expected,
            format!("executed reference source changed: {path}"),
        )?;
    }
    Ok(())
}
