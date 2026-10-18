//! Pure diagnostic evidence validation and comparison. No theorem authority or I/O.
mod common;
mod compare;
mod compare_sources;
pub mod compare_syntax;
mod json;
mod observation;
mod observation_match;
mod protocol;
mod protocol_v2;
mod signature;
mod validate;
pub use compare::{P0_MISSING, compare_reports};
pub use compare_sources::collect_required_sources;
pub use protocol::{
    Comparison, OfficialCompatibilityResult, VerifiedReferenceEvidence, compare_candidate,
    verify_reference,
};
pub use protocol_v2::{
    ApprovedObserverIdentity, ObservationLimits, ObserverHostInputs, verify_reference_v2,
};
pub use validate::{validate_entities, validate_graph};

use thiserror::Error;

/// Decode an opened reference byte stream, rejecting duplicate fields and excess nesting.
pub fn decode_json_reader(
    reader: impl std::io::Read,
    name: &str,
) -> Result<serde_json::Value, EvidenceError> {
    json::decode_reader(reader).map_err(|source| EvidenceError::Json { name: name.into(), source })
}

/// Malformed or contradictory input evidence; the caller can correct the input.
#[derive(Debug, Error)]
pub enum EvidenceError {
    /// A user-supplied report, manifest, or observation violates its structural contract.
    #[error("invalid reference evidence: {0}")]
    Input(String),
    /// The already-opened artifact does not contain valid strict JSON.
    #[error("decode reference artifact {name}: {source}")]
    Json {
        name: String,
        #[source]
        source: serde_json::Error,
    },
}
