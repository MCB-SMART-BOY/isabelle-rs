//! Compare native observations against frozen reference evidence, without accepting proofs.
#[cfg(unix)]
use rustix::fs::{CWD, FileType, Mode, OFlags, fstat, openat};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::io::{Read, Write};
#[cfg(unix)]
use std::path::Component;
use std::path::Path;

use super::{
    approved_identity,
    common::{COMMIT, as_str, decode_json, digest_bytes, field, require},
};
use crate::runner::{StepError, io_error};
use isabelle_evidence::{
    Comparison, EvidenceError, OfficialCompatibilityResult, compare_candidate, compare_reports,
    compare_syntax::require_index, verify_reference_v2,
};

const MAX_ARTIFACT_BYTES: u64 = 512 * 1024 * 1024;
const HASH_BUFFER_BYTES: usize = 64 * 1024;
const MAX_TOTAL_BYTES: u64 = 512 * 1024 * 1024;
const MAX_MANIFEST_BYTES: u64 = 16 * 1024 * 1024;
const MAX_OFFLINE_ARTIFACTS: usize = 16;
const REQUIRED_OBSERVATION_ARTIFACTS: [&str; 6] = [
    "inventory",
    "execution",
    "closure-evidence",
    "observer-events",
    "observer-raw",
    "bootstrap-events",
];

pub(super) fn read_budgeted_bytes(
    path: &Path,
    limit: u64,
    remaining: &mut u64,
) -> Result<Vec<u8>, StepError> {
    let budget = limit.min(*remaining);
    let bytes = read_checked_bytes(path, budget)?;
    *remaining -= bytes.len() as u64;
    Ok(bytes)
}

pub(super) fn digest_budgeted_file(
    path: &Path,
    limit: u64,
    remaining: &mut u64,
) -> Result<String, StepError> {
    use sha2::{Digest, Sha256};
    let mut file = open_checked_file(path, limit.min(*remaining))?;
    let mut hash = Sha256::new();
    let mut buffer = [0u8; HASH_BUFFER_BYTES];
    loop {
        let count = file
            .read(&mut buffer)
            .map_err(|source| io_error(format!("hash reference {}", path.display()), source))?;
        if count == 0 {
            return Ok(base16ct::lower::encode_string(&hash.finalize()));
        }
        require(count as u64 <= *remaining, "reference total byte budget exceeded")?;
        *remaining -= count as u64;
        hash.update(&buffer[..count]);
    }
}

pub(super) fn digest_checked_file(path: &Path, limit: u64) -> Result<String, StepError> {
    use sha2::{Digest, Sha256};
    let mut file = open_checked_file(path, limit)?;
    let mut hash = Sha256::new();
    let mut total = 0u64;
    let mut buffer = [0u8; HASH_BUFFER_BYTES];
    loop {
        let count = file
            .read(&mut buffer)
            .map_err(|source| io_error(format!("hash reference {}", path.display()), source))?;
        if count == 0 {
            return Ok(base16ct::lower::encode_string(&hash.finalize()));
        }
        total += count as u64;
        require(total <= limit, format!("reference hash exceeded limit: {}", path.display()))?;
        hash.update(&buffer[..count]);
    }
}

fn evidence_error(source: EvidenceError) -> StepError {
    match source {
        EvidenceError::Input(detail) => StepError::Input(detail),
        EvidenceError::Json { name, source } => {
            StepError::Json { operation: format!("decode reference artifact {name}"), source }
        },
    }
}

pub fn load_frozen_artifact(manifest: &Value, run: &Path, name: &str) -> Result<Value, StepError> {
    let record = field(field(field(manifest, "reference_runs")?, "artifacts")?, name)?;
    let relative = format!("inventory/{name}.json");
    require(
        field(record, "path")? == &Value::String(relative.clone()),
        format!("unsafe artifact path: {name}"),
    )?;
    let path = run.join(relative);
    let size = require_index(field(record, "bytes")?, "artifact bytes").map_err(evidence_error)?;
    require(
        size <= MAX_ARTIFACT_BYTES,
        format!("artifact size exceeds limit: {}", path.display()),
    )?;
    let content = read_checked_bytes(&path, size)?;
    require(
        content.len() as u64 == size
            && digest_bytes(&content) == as_str(field(record, "sha256")?, "artifact hash")?,
        format!("changed reference artifact: {}", path.display()),
    )?;
    decode_json(&content, &format!("decode frozen artifact {}", path.display()))
}

pub(super) fn read_checked_bytes(path: &Path, limit: u64) -> Result<Vec<u8>, StepError> {
    let mut content = Vec::new();
    open_checked_file(path, limit)?
        .take(limit + 1)
        .read_to_end(&mut content)
        .map_err(|source| io_error(format!("read reference {}", path.display()), source))?;
    require(
        content.len() as u64 <= limit,
        format!("reference file exceeds limit: {}", path.display()),
    )?;
    Ok(content)
}

#[cfg(not(unix))]
pub(super) fn open_checked_file(path: &Path, _limit: u64) -> Result<File, StepError> {
    Err(StepError::Input(format!(
        "secure reference file reads require Unix descriptor-relative no-follow opening: {}",
        path.display()
    )))
}

#[cfg(unix)]
pub(super) fn open_checked_file(path: &Path, limit: u64) -> Result<File, StepError> {
    let absolute = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .map_err(|source| io_error("resolve working directory", source))?
            .join(path)
    };
    let operation = format!("open reference {}", absolute.display());
    let mut directory =
        openat(CWD, "/", OFlags::RDONLY | OFlags::DIRECTORY | OFlags::CLOEXEC, Mode::empty())
            .map_err(|source| io_error(&operation, source.into()))?;
    let mut components =
        absolute.components().filter(|part| !matches!(part, Component::RootDir)).peekable();
    require(components.peek().is_some(), "reference path must name a regular file")?;
    while let Some(component) = components.next() {
        let Component::Normal(name) = component else {
            return Err(StepError::Input(format!("unsafe reference path {}", absolute.display())));
        };
        let flags = if components.peek().is_some() {
            OFlags::RDONLY | OFlags::DIRECTORY | OFlags::NOFOLLOW | OFlags::CLOEXEC
        } else {
            OFlags::RDONLY | OFlags::NOFOLLOW | OFlags::NONBLOCK | OFlags::CLOEXEC
        };
        directory = openat(&directory, name, flags, Mode::empty())
            .map_err(|source| io_error(&operation, source.into()))?;
    }
    let stat = fstat(&directory).map_err(|source| io_error(&operation, source.into()))?;
    require(
        FileType::from_raw_mode(stat.st_mode).is_file()
            && stat.st_size >= 0
            && stat.st_size as u64 <= limit,
        format!("reference file is not ordinary or exceeds limit: {}", absolute.display()),
    )?;
    Ok(File::from(directory))
}

fn blocked_offline(reason: impl Into<String>) -> Value {
    OfficialCompatibilityResult::from_comparison(Comparison::Incomplete(json!({
        "unavailable":[{"field":"independent_reference","reason":reason.into()}],
        "differences":[]
    })))
    .as_json()
}

fn read_exact_budgeted_artifact(
    path: &Path,
    expected: u64,
    remaining: &mut u64,
) -> Result<Vec<u8>, StepError> {
    require(expected <= *remaining, "reference total byte budget exceeded")?;
    let file = open_checked_file(path, expected)?;
    let actual = file
        .metadata()
        .map_err(|source| io_error(format!("inspect opened reference {}", path.display()), source))?
        .len();
    require(
        actual == expected,
        format!("reference artifact length differs from manifest: {}", path.display()),
    )?;
    let mut bytes = Vec::new();
    file.take(expected + 1)
        .read_to_end(&mut bytes)
        .map_err(|source| io_error(format!("read reference {}", path.display()), source))?;
    require(
        bytes.len() as u64 == expected,
        format!("reference artifact changed during read: {}", path.display()),
    )?;
    *remaining -= expected;
    Ok(bytes)
}

fn plan_offline_artifacts(
    manifest: &Value,
    limits: isabelle_evidence::ObservationLimits,
) -> Result<Vec<(&str, &str, u64)>, StepError> {
    let entries = manifest
        .get("artifacts")
        .ok_or_else(|| {
            approved_identity::missing_offline_prerequisite(
                "offline observation artifacts are absent",
            )
        })?
        .as_array()
        .ok_or_else(|| StepError::Input("reference run artifacts: expected array".into()))?;
    require(
        entries.len() <= limits.max_artifacts.min(MAX_OFFLINE_ARTIFACTS),
        "too many offline artifacts",
    )?;
    let mut planned = Vec::with_capacity(entries.len());
    let mut paths = BTreeSet::new();
    let mut names = BTreeSet::new();
    let (mut raw_bytes, mut decoded_bytes) = (0u64, 0u64);
    for record in entries {
        let name = as_str(field(record, "name")?, "artifact name")?;
        let relative = as_str(field(record, "path")?, "artifact path")?;
        require(
            !relative.is_empty()
                && !relative.contains('\\')
                && !relative.contains(':')
                && !relative.contains('\0')
                && relative.split('/').all(|part| !matches!(part, "" | "." | ".."))
                && paths.insert(relative),
            format!("unsafe or duplicate artifact path {relative}"),
        )?;
        require(
            !name.is_empty()
                && name.bytes().all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
                && name != "closure.json"
                && names.insert(name),
            format!("invalid or duplicate reference artifact {name}"),
        )?;
        let bytes =
            require_index(field(record, "bytes")?, "artifact bytes").map_err(evidence_error)?;
        require(bytes <= MAX_ARTIFACT_BYTES, format!("{name}: artifact size exceeds limit"))?;
        let subtotal = if name == "observer-raw" { &mut raw_bytes } else { &mut decoded_bytes };
        *subtotal = subtotal
            .checked_add(bytes)
            .ok_or_else(|| StepError::Input("offline artifact byte count overflow".into()))?;
        planned.push((name, relative, bytes));
    }
    require(
        raw_bytes <= limits.raw_total_bytes && decoded_bytes <= limits.decoded_total_bytes,
        "offline artifacts exceed approved raw/decoded read budgets",
    )?;
    if !REQUIRED_OBSERVATION_ARTIFACTS.iter().all(|name| names.contains(*name)) {
        return Err(approved_identity::missing_offline_prerequisite(
            "required independent observation artifacts are absent",
        ));
    }
    Ok(planned)
}
fn read_offline_artifacts(
    manifest: &Value,
    run: &Path,
    frozen_bytes: Vec<u8>,
    remaining: &mut u64,
    approval: &isabelle_evidence::ApprovedObserverIdentity,
) -> Result<BTreeMap<String, Vec<u8>>, StepError> {
    let planned = plan_offline_artifacts(manifest, approval.import_limits())?;
    let total = planned.iter().try_fold(0u64, |total, (_, _, bytes)| {
        total
            .checked_add(*bytes)
            .ok_or_else(|| StepError::Input("offline artifact total byte count overflow".into()))
    })?;
    require(total <= *remaining, "offline artifacts exceed remaining total read budget")?;
    let mut artifacts = BTreeMap::new();
    artifacts.insert("closure.json".into(), frozen_bytes);
    for (name, relative, expected) in planned {
        artifacts.insert(
            name.into(),
            read_exact_budgeted_artifact(&run.join(relative), expected, remaining)?,
        );
    }
    Ok(artifacts)
}

fn compare_observed_run(
    frozen_manifest: &Path,
    run: &Path,
    native_path: &Path,
    manifest_path: &Path,
    approval_path: Option<&Path>,
) -> Result<Value, StepError> {
    let Some(approval_path) = approval_path else {
        return Ok(blocked_offline("trusted external approval is absent"));
    };
    let mut remaining = MAX_TOTAL_BYTES;
    let manifest_bytes =
        match read_budgeted_bytes(manifest_path, MAX_MANIFEST_BYTES, &mut remaining) {
            Err(StepError::Io { source, .. }) if source.kind() == std::io::ErrorKind::NotFound => {
                return Ok(blocked_offline("reference run manifest is absent"));
            },
            other => other?,
        };
    let manifest = decode_json(&manifest_bytes, "decode offline reference run manifest")?;
    let runs = manifest["runs"].as_array();
    if runs.is_none_or(|runs| {
        runs.len() != 2
            || !["build", "inventory"].iter().all(|phase| {
                runs.iter()
                    .filter(|run| {
                        run["phase"] == *phase
                            && run["run_id"].as_str().is_some_and(|id| !id.is_empty())
                    })
                    .count()
                    == 1
            })
    }) {
        return Ok(blocked_offline("independent build and inventory run records are absent"));
    }
    let approval = match approved_identity::load_offline_identity(
        approval_path,
        manifest_path,
        run,
        &manifest,
        &manifest_bytes,
        &mut remaining,
    ) {
        Ok(approval) => approval,
        Err(StepError::Protocol { operation, detail })
            if operation == approved_identity::OFFLINE_PREREQUISITE =>
        {
            return Ok(blocked_offline(detail));
        },
        Err(StepError::Io { source, .. }) if source.kind() == std::io::ErrorKind::NotFound => {
            return Ok(blocked_offline("external approval, receipt or original source is absent"));
        },
        Err(error) => return Err(error),
    };
    let frozen_bytes = read_budgeted_bytes(frozen_manifest, MAX_MANIFEST_BYTES, &mut remaining)?;
    let artifacts =
        match read_offline_artifacts(&manifest, run, frozen_bytes, &mut remaining, &approval) {
            Err(StepError::Protocol { operation, detail })
                if operation == approved_identity::OFFLINE_PREREQUISITE =>
            {
                return Ok(blocked_offline(detail));
            },
            Err(StepError::Io { source, .. }) if source.kind() == std::io::ErrorKind::NotFound => {
                return Ok(blocked_offline("approved reference artifact is absent"));
            },
            other => other?,
        };
    let reference =
        verify_reference_v2(&manifest, &artifacts, &approval).map_err(evidence_error)?;
    let native_bytes = read_budgeted_bytes(native_path, MAX_MANIFEST_BYTES, &mut remaining)?;
    let mut native = decode_json(&native_bytes, "decode native build result")?;
    require(
        native["result"] == "Succeeded" && native["purpose"] == "native_build_result",
        "official compatibility requires a completed native_build_result",
    )?;
    native
        .as_object_mut()
        .ok_or_else(|| StepError::Input("native result must be an object".into()))?
        .remove("result");
    let comparison = compare_candidate(&reference, &native).map_err(evidence_error)?;
    Ok(OfficialCompatibilityResult::from_comparison(comparison).as_json())
}

pub fn run(
    manifest_path: &Path,
    reference_run: &Path,
    native_path: &Path,
    reference_manifest: Option<&Path>,
    reference_approval: Option<&Path>,
) -> Result<(), StepError> {
    let report = if let Some(reference_manifest) = reference_manifest {
        compare_observed_run(
            manifest_path,
            reference_run,
            native_path,
            reference_manifest,
            reference_approval,
        )?
    } else {
        require(reference_approval.is_none(), "approval requires a reference manifest")?;
        let manifest = decode_json(
            &read_checked_bytes(manifest_path, MAX_MANIFEST_BYTES)?,
            "decode frozen P0 manifest",
        )?;
        require(
            field(field(&manifest, "source")?, "git_commit")? == COMMIT,
            "manifest source commit",
        )?;
        let reference = load_frozen_artifact(&manifest, reference_run, "inventory")?;
        let execution = load_frozen_artifact(&manifest, reference_run, "execution")?;
        let native = decode_json(
            &read_checked_bytes(native_path, MAX_MANIFEST_BYTES)?,
            "decode legacy native diagnostic",
        )?;
        compare_reports(&reference, &execution, native, &manifest).map_err(evidence_error)?
    };
    let stdout = std::io::stdout();
    let mut output = stdout.lock();
    serde_json::to_writer(&mut output, &report).map_err(|source| StepError::Json {
        operation: "write reference comparison report".into(),
        source,
    })?;
    output
        .write_all(b"\n")
        .map_err(|source| io_error("finish reference comparison report", source))?;
    if report["result"] == "Succeeded" {
        return Ok(());
    }
    Err(StepError::Protocol {
        operation: "reference comparison".into(),
        detail: format!("{}; diagnostic observations do not authorize proof", report["result"]),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use isabelle_evidence::ObservationLimits;

    #[test]
    fn plan_offline_artifacts_excess_raw_or_decoded_bytes_rejects_before_io() {
        let limits = ObservationLimits {
            raw_total_bytes: 2,
            decoded_total_bytes: 3,
            max_artifacts: 6,
            max_events: 1,
            max_depth: 1,
        };
        let raw = json!({"artifacts":[{"name":"observer-raw","path":"raw.bin","bytes":3}]});
        let decoded = json!({"artifacts":[{"name":"inventory","path":"inventory.json","bytes":4}]});
        assert!(plan_offline_artifacts(&raw, limits).is_err());
        assert!(plan_offline_artifacts(&decoded, limits).is_err());
    }

    #[test]
    fn plan_offline_artifacts_duplicate_paths_and_count_rejects() {
        let limits = ObservationLimits {
            raw_total_bytes: 10,
            decoded_total_bytes: 10,
            max_artifacts: 1,
            max_events: 1,
            max_depth: 1,
        };
        let records = json!({"artifacts":[
            {"name":"inventory","path":"same.json","bytes":1},
            {"name":"execution","path":"same.json","bytes":1}
        ]});
        assert!(plan_offline_artifacts(&records, limits).is_err());
        let limits = ObservationLimits { max_artifacts: 2, ..limits };
        assert!(plan_offline_artifacts(&records, limits).is_err());
    }
    #[cfg(unix)]
    #[test]
    fn read_exact_budgeted_artifact_wrong_declared_length_rejects_before_copy() {
        let directory = tempfile::tempdir().unwrap();
        let artifact = directory.path().join("artifact.json");
        std::fs::write(&artifact, b"changed").unwrap();
        let mut remaining = 10;
        assert!(read_exact_budgeted_artifact(&artifact, 2, &mut remaining).is_err());
        assert_eq!(remaining, 10);
    }

    #[cfg(unix)]
    #[test]
    fn read_checked_bytes_symlinked_parent_rejects_without_following() {
        let directory = tempfile::tempdir().unwrap();
        let real = directory.path().join("real");
        std::fs::create_dir(&real).unwrap();
        std::fs::write(real.join("artifact.json"), b"private").unwrap();
        std::os::unix::fs::symlink(&real, directory.path().join("link")).unwrap();
        assert!(read_checked_bytes(&directory.path().join("link/artifact.json"), 7).is_err());
    }

    #[cfg(not(unix))]
    #[test]
    fn read_checked_bytes_without_secure_open_rejects_explicitly() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("artifact.json");
        std::fs::write(&path, b"private").unwrap();
        let error = read_checked_bytes(&path, 7).unwrap_err();
        assert!(matches!(error, StepError::Input(_)));
        assert!(error.to_string().contains("no-follow"));
    }

    #[test]
    fn plan_offline_artifacts_unsafe_path_rejects() {
        let limits = ObservationLimits {
            raw_total_bytes: 10,
            decoded_total_bytes: 10,
            max_artifacts: 6,
            max_events: 1,
            max_depth: 1,
        };
        let records = json!({"artifacts":[{"name":"inventory","path":"../outside","bytes":1}]});
        assert!(plan_offline_artifacts(&records, limits).is_err());
    }
}
