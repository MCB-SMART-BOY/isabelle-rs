//! Trusted coordinator input, kept outside the VM capability registry.
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use isabelle_evidence::{
    EvidenceError, VerifiedReferenceEvidence, decode_json_reader, verify_reference,
};
use serde_json::Value;
use thiserror::Error;

use crate::ml::host::files::HostIoError;
use crate::ml::host::input::read_supervisor_input;
use crate::ml::host::lifecycle::{BuildLifecycle, TaskLease};

const MAX_ARTIFACT_BYTES: usize = 512 * 1024 * 1024;
const FROZEN_MANIFEST: &[u8] = include_bytes!("../../../tests/fixtures/isabelle2025/closure.json");

/// User-fixable reference input failure, never a proof or a published build result.
#[derive(Debug, Error)]
pub enum ReferenceInputError {
    /// Missing files are prerequisites; other filesystem errors retain their cause.
    #[error("read reference input {path}: {source}")]
    Read {
        path: PathBuf,
        #[source]
        source: Box<HostIoError>,
    },
    /// A manifest or opened artifact violates the shared diagnostic evidence contract.
    #[error("validate reference input {path}: {source}")]
    Evidence {
        path: PathBuf,
        #[source]
        source: EvidenceError,
    },
}

impl ReferenceInputError {
    pub fn is_missing_prerequisite(&self) -> bool {
        matches!(self, Self::Read { source, .. }
            if matches!(source.as_ref(), HostIoError::Io { source, .. }
                if source.kind() == std::io::ErrorKind::NotFound))
    }
}

/// Read each artifact once, then verify exactly those bytes using the pure evidence crate.
/// This function grants neither source execution rights nor theorem acceptance authority.
pub fn load_reference_inputs(
    lifecycle: &BuildLifecycle,
    lease: &TaskLease,
    manifest_path: &Path,
    run: &Path,
) -> Result<VerifiedReferenceEvidence, ReferenceInputError> {
    let bytes = read_input(lifecycle, lease, manifest_path, MAX_ARTIFACT_BYTES)?;
    let evidence_error =
        |source| ReferenceInputError::Evidence { path: manifest_path.to_owned(), source };
    let manifest =
        decode_json_reader(bytes.as_slice(), "reference manifest").map_err(evidence_error)?;
    let records = manifest
        .get("artifacts")
        .and_then(Value::as_array)
        .ok_or_else(|| evidence_error(EvidenceError::Input("artifacts must be an array".into())))?;
    let mut artifacts = BTreeMap::new();
    artifacts.insert("closure.json".to_owned(), FROZEN_MANIFEST.to_vec());
    for record in records {
        let (name, relative, length) = parse_artifact(record).map_err(evidence_error)?;
        if artifacts.contains_key(name) {
            return Err(evidence_error(EvidenceError::Input(format!("duplicate artifact {name}"))));
        }
        let content = read_input(lifecycle, lease, &run.join(relative), length)?;
        artifacts.insert(name.to_owned(), content);
    }
    verify_reference(&manifest, &artifacts).map_err(evidence_error)
}

fn parse_artifact(record: &Value) -> Result<(&str, &str, usize), EvidenceError> {
    let name = record
        .get("name")
        .and_then(Value::as_str)
        .ok_or_else(|| EvidenceError::Input("artifact name must be a string".into()))?;
    let path = record
        .get("path")
        .and_then(Value::as_str)
        .ok_or_else(|| EvidenceError::Input(format!("{name}: artifact path must be a string")))?;
    let length = record
        .get("bytes")
        .and_then(Value::as_u64)
        .filter(|length| *length <= MAX_ARTIFACT_BYTES as u64)
        .ok_or_else(|| EvidenceError::Input(format!("{name}: invalid artifact byte limit")))?;
    if name.is_empty() || !name.bytes().all(|byte| byte.is_ascii_alphanumeric() || byte == b'-') {
        return Err(EvidenceError::Input(format!("invalid artifact name {name:?}")));
    }
    if path.is_empty()
        || path.contains(['\\', '\0', ':'])
        || path.split('/').any(|part| matches!(part, "" | "." | ".."))
    {
        return Err(EvidenceError::Input(format!("unsafe artifact path {path:?}")));
    }
    Ok((name, path, length as usize))
}

fn read_input(
    lifecycle: &BuildLifecycle,
    lease: &TaskLease,
    path: &Path,
    limit: usize,
) -> Result<Vec<u8>, ReferenceInputError> {
    read_supervisor_input(lifecycle, lease, path, limit).map_err(|source| {
        ReferenceInputError::Read { path: path.to_owned(), source: Box::new(source) }
    })
}
