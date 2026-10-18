use std::collections::{BTreeMap, BTreeSet};

use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use crate::common::{COMMIT, ROOTS, as_array, as_object, as_str, field, require, require_fields};
use crate::compare::{ComparisonDiagnostics, P0_MISSING, compare_candidate_observations};
use crate::compare_sources::collect_required_sources;
use crate::compare_syntax::{match_judgments_with_constraints, require_index};
use crate::{EvidenceError, validate_entities, validate_graph};

const SCHEMA_VERSION: u64 = 1;
const MAX_ARTIFACT_BYTES: u64 = 512 * 1024 * 1024;
const REQUIRED_ARTIFACTS: [&str; 3] = ["inventory", "execution", "closure-evidence"];

/// Diagnostic comparison only; no variant contains or authorizes a theorem token.
#[derive(Debug, PartialEq)]
pub enum Comparison {
    Matched,
    Different(Value),
    Incomplete(Value),
}

/// Offline compatibility result, never a native build or theorem acceptance result.
#[derive(Debug)]
pub struct OfficialCompatibilityResult {
    result: &'static str,
    diagnostics: Value,
}

impl OfficialCompatibilityResult {
    /// Preserve the existing comparer while publishing an explicitly separate result purpose.
    pub fn from_comparison(comparison: Comparison) -> Self {
        match comparison {
            Comparison::Matched => Self {
                result: "Succeeded",
                diagnostics: json!({"differences":[],"unavailable":[]}),
            },
            Comparison::Different(diagnostics) => Self { result: "Failed", diagnostics },
            Comparison::Incomplete(diagnostics) => {
                Self { result: "BlockedPrerequisite", diagnostics }
            },
        }
    }

    pub fn as_json(&self) -> Value {
        json!({"schema_version":1,"purpose":"official_compatibility_result",
            "authorization":"none","result":self.result,"diagnostics":self.diagnostics})
    }
}

/// Validated byte identities and structural reference observations, not logical authority.
#[derive(Debug)]
pub struct VerifiedReferenceEvidence {
    pub(crate) inventory: Value,
    pub(crate) execution: Value,
    pub(crate) closure: Value,
    pub(crate) frozen: Value,
    pub(crate) version_two: Option<crate::protocol_v2::VerifiedV2>,
    pub(crate) incomplete_observations: Vec<&'static str>,
}

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn validate_sha256<'a>(value: &'a Value, context: &str) -> Result<&'a str, EvidenceError> {
    let digest = as_str(value, context)?;
    require(
        digest.len() == 64
            && digest.bytes().all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        format!("{context}: invalid SHA256"),
    )?;
    Ok(digest)
}

pub(super) fn validate_relative_path(path: &str) -> Result<(), EvidenceError> {
    require(
        !path.is_empty()
            && !path.starts_with('/')
            && !path.contains('\\')
            && !path.contains('\0')
            && path.split('/').all(|part| !matches!(part, "" | "." | ".."))
            && !path.contains(':'),
        format!("unsafe reference path {path:?}"),
    )
}

fn decode_artifact(name: &str, bytes: &[u8]) -> Result<Value, EvidenceError> {
    crate::decode_json_reader(bytes, name)
}

fn validate_manifest_artifacts(
    manifest: &Value,
    artifacts: &BTreeMap<String, Vec<u8>>,
) -> Result<BTreeMap<String, Value>, EvidenceError> {
    let mut decoded = BTreeMap::new();
    let mut paths = BTreeSet::new();
    for record in as_array(field(manifest, "artifacts")?, "reference artifacts")? {
        require_fields(record, &["name", "path", "sha256", "bytes"], "artifact record")?;
        let name = as_str(field(record, "name")?, "artifact name")?;
        require(
            !name.is_empty()
                && name.bytes().all(|byte| byte.is_ascii_alphanumeric() || byte == b'-'),
            format!("invalid artifact name {name:?}"),
        )?;
        let path = as_str(field(record, "path")?, "artifact path")?;
        validate_relative_path(path)?;
        require(paths.insert(path), format!("duplicate artifact path {path:?}"))?;
        let bytes = artifacts.get(name).ok_or_else(|| {
            EvidenceError::Input(format!("missing opened reference artifact {name}"))
        })?;
        let length = require_index(field(record, "bytes")?, "artifact bytes")?;
        require(
            length <= MAX_ARTIFACT_BYTES && bytes.len() as u64 == length,
            format!("{name}: artifact length differs from manifest or exceeds limit"),
        )?;
        require(
            sha256(bytes) == validate_sha256(field(record, "sha256")?, name)?,
            format!("{name}: artifact hash differs from opened bytes"),
        )?;
        require(
            decoded.insert(name.to_owned(), decode_artifact(name, bytes)?).is_none(),
            format!("duplicate artifact name {name:?}"),
        )?;
    }
    require(
        REQUIRED_ARTIFACTS.iter().all(|name| decoded.contains_key(*name)),
        "missing inventory, execution, or closure-evidence artifact",
    )?;
    require(
        artifacts.len() == decoded.len() + 1
            && artifacts.keys().all(|name| name == "closure.json" || decoded.contains_key(name)),
        "opened reference artifact set differs from manifest",
    )?;
    Ok(decoded)
}

fn validate_source_files(
    manifest: &Value,
    inventory: &Value,
    execution: &Value,
    frozen: &Value,
) -> Result<(), EvidenceError> {
    let required = collect_required_sources(inventory, execution, frozen)?;
    let mut listed = BTreeMap::new();
    for entry in as_array(field(manifest, "source_files")?, "source files")? {
        require_fields(entry, &["path", "sha256"], "source file")?;
        let path = as_str(field(entry, "path")?, "source path")?;
        validate_relative_path(path)?;
        let digest = validate_sha256(field(entry, "sha256")?, path)?;
        require(listed.insert(path, digest).is_none(), format!("duplicate source path {path}"))?;
    }
    require(
        required == listed,
        "reference source set/hash differs from fixed inventory and execution",
    )
}

/// Verify a same-version run manifest against bytes already opened by the caller.
/// The caller must parse manifest bytes with `decode_json_reader` to reject duplicate JSON fields.
/// The reserved `closure.json` key contains the original frozen P0 manifest bytes.
pub fn verify_reference(
    manifest: &Value,
    artifacts: &BTreeMap<String, Vec<u8>>,
) -> Result<VerifiedReferenceEvidence, EvidenceError> {
    require_fields(
        manifest,
        &[
            "schema_version",
            "purpose",
            "source_commit",
            "p0_manifest_sha256",
            "source_files",
            "artifacts",
        ],
        "reference run manifest",
    )?;
    require(
        manifest["schema_version"] == SCHEMA_VERSION
            && manifest["purpose"] == "native_reference_evidence"
            && manifest["source_commit"] == COMMIT,
        "reference run identity",
    )?;
    let p0 = artifacts
        .get("closure.json")
        .ok_or_else(|| EvidenceError::Input("missing original closure.json bytes".into()))?;
    require(
        sha256(p0)
            == validate_sha256(field(manifest, "p0_manifest_sha256")?, "frozen manifest hash")?,
        "original closure.json hash differs from run manifest",
    )?;
    let frozen = decode_artifact("closure.json", p0)?;
    require(
        frozen["source"]["git_commit"] == COMMIT
            && frozen["purpose"] == "isabelle2025_p0_reference_snapshot",
        "frozen P0 identity",
    )?;
    let mut decoded = validate_manifest_artifacts(manifest, artifacts)?;
    let incomplete_observations = {
        let inventory = decoded
            .get("inventory")
            .ok_or_else(|| EvidenceError::Input("missing inventory".into()))?;
        let execution = decoded
            .get("execution")
            .ok_or_else(|| EvidenceError::Input("missing execution".into()))?;
        let closure = decoded
            .get("closure-evidence")
            .ok_or_else(|| EvidenceError::Input("missing closure-evidence".into()))?;
        require(
            inventory["roots"] == json!(ROOTS)
                && inventory["reference"] == "Isabelle2025"
                && execution["roots"] == json!(ROOTS)
                && execution["reference"] == "Isabelle2025",
            "inventory/execution fixed roots or reference identity differs",
        )?;
        validate_graph(as_array(field(inventory, "theories")?, "inventory theories")?)?;
        validate_entities(as_array(&inventory["theories"], "inventory theories")?)?;
        validate_source_files(manifest, inventory, execution, &frozen)?;
        require_fields(
            closure,
            &["schema_version", "source_commit", "fields"],
            "closure evidence",
        )?;
        require(
            closure["schema_version"] == SCHEMA_VERSION && closure["source_commit"] == COMMIT,
            "closure evidence identity differs",
        )?;
        validate_closure_fields(closure, &decoded, inventory, execution, manifest)?
    };
    let inventory = decoded
        .remove("inventory")
        .ok_or_else(|| EvidenceError::Input("missing inventory".into()))?;
    let execution = decoded
        .remove("execution")
        .ok_or_else(|| EvidenceError::Input("missing execution".into()))?;
    let closure = decoded
        .remove("closure-evidence")
        .ok_or_else(|| EvidenceError::Input("missing closure-evidence".into()))?;
    Ok(VerifiedReferenceEvidence {
        inventory,
        execution,
        closure,
        frozen,
        incomplete_observations,
        version_two: None,
    })
}

fn locate_pointer<'a>(artifact: &'a Value, pointer: &str) -> Result<&'a Value, EvidenceError> {
    require(
        pointer.starts_with('/') && pointer.len() > 1,
        "observation requires a concrete JSON pointer",
    )?;
    artifact
        .pointer(pointer)
        .ok_or_else(|| EvidenceError::Input(format!("observation pointer not found: {pointer}")))
}

fn validate_provenance<'a>(
    wrapper: &Value,
    field_name: &str,
    observations: &'a BTreeMap<String, Value>,
) -> Result<&'a Value, EvidenceError> {
    let provenance = field(wrapper, "evidence")?;
    require_fields(provenance, &["artifact", "pointer"], "observation provenance")?;
    let artifact = as_str(&provenance["artifact"], "observation artifact")?;
    require(artifact != "closure-evidence", format!("{field_name}: self-referential observation"))?;
    let pointer = as_str(&provenance["pointer"], "observation pointer")?;
    let observed = observations.get(artifact).ok_or_else(|| {
        EvidenceError::Input(format!(
            "{field_name}: observation artifact {artifact:?} not independently supplied"
        ))
    })?;
    let record = locate_pointer(observed, pointer)?;
    require_fields(record, &["field", "value"], "observation record")?;
    require(
        record["field"] == field_name && record["value"] == wrapper["value"],
        format!("{field_name}: observation record value or field differs"),
    )?;
    Ok(observed)
}

fn is_ancestor(
    theories: &[Value],
    theory: &str,
    owner: &str,
    depth: usize,
) -> Result<bool, EvidenceError> {
    require(depth < theories.len(), "theory owner graph has a cycle")?;
    let node = theories
        .iter()
        .find(|item| item["name"] == theory)
        .ok_or_else(|| EvidenceError::Input(format!("unknown reference theory {theory}")))?;
    if node["name"] == owner {
        return Ok(true);
    }
    for parent in as_array(field(node, "parents")?, "theory parents")? {
        if is_ancestor(theories, as_str(parent, "theory parent")?, owner, depth + 1)? {
            return Ok(true);
        }
    }
    Ok(false)
}

pub(crate) fn validate_observation_owner(
    inventory: &Value,
    theory: &str,
    owner: &str,
) -> Result<(), EvidenceError> {
    let theories = as_array(field(inventory, "theories")?, "inventory theories")?;
    require(
        is_ancestor(theories, theory, owner, 0)?,
        format!("owner {owner} is not an ancestor of {theory}"),
    )
}

fn validate_observation_source(manifest: &Value, path: &Value) -> Result<(), EvidenceError> {
    let source = as_str(path, "observation source")?;
    require(
        as_array(field(manifest, "source_files")?, "source files")?
            .iter()
            .any(|entry| entry["path"] == source),
        format!("observation uses unknown source {source}"),
    )
}

fn validate_declaration_event(origin: &Value, execution: &Value) -> Result<(), EvidenceError> {
    let owner = as_str(field(origin, "owner")?, "origin owner")?;
    let theories = as_array(field(execution, "theories")?, "executed theories")?;
    let theory = theories
        .iter()
        .find(|item| item["name"] == owner)
        .ok_or_else(|| EvidenceError::Input(format!("unobserved declaration owner {owner}")))?;
    let sequence = require_index(field(origin, "command_sequence")?, "declaration command")?;
    let commands = as_array(field(theory, "commands")?, "executed commands")?;
    let command =
        commands.iter().find(|item| item["sequence"].as_u64() == Some(sequence)).ok_or_else(
            || EvidenceError::Input(format!("missing declaration command {owner}:{sequence}")),
        )?;
    require(
        field(command, "source")? == field(origin, "source")?
            && field(command, "name")? == field(origin, "operation")?,
        format!("declaration origin differs from executed command {owner}:{sequence}"),
    )
}

fn validate_named_payload_owners(
    inventory: &Value,
    execution: &Value,
    manifest: &Value,
    theory: &str,
    field_name: &str,
    payload: &Value,
) -> Result<(), EvidenceError> {
    if field_name == "declaration_origin" {
        validate_observation_owner(
            inventory,
            theory,
            as_str(field(payload, "owner")?, "origin owner")?,
        )?;
        validate_observation_source(manifest, field(payload, "source")?)?;
        validate_declaration_event(payload, execution)?;
    } else if field_name == "full_axiom_extension_dependencies" {
        for dependency in as_array(payload, "dependencies")? {
            validate_observation_owner(
                inventory,
                theory,
                as_str(field(dependency, "owner")?, "dependency owner")?,
            )?;
        }
    } else {
        for obligation in as_array(payload, "obligations")? {
            validate_observation_owner(
                inventory,
                theory,
                as_str(field(obligation, "source_owner")?, "sort owner")?,
            )?;
        }
    }
    Ok(())
}

fn validate_named_observation_syntax(
    inventory: &Value,
    theory: &str,
    group: &str,
    index: u64,
    field_name: &str,
    payload: &Value,
    signatures: &mut crate::signature::SignatureCache<'_>,
) -> Result<(), EvidenceError> {
    if field_name == "declaration_origin" {
        return Ok(());
    }
    if field_name == "full_axiom_extension_dependencies" {
        for dependency in as_array(payload, "observed dependencies")? {
            let owner = as_str(field(dependency, "owner")?, "dependency owner")?;
            let signature = signatures.get(owner)?;
            crate::observation::validate_dependency_signature(dependency, signature)?;
        }
        return Ok(());
    }
    let reference_theories = as_array(field(inventory, "theories")?, "inventory theories")?;
    let theorem = find_named_member(reference_theories, theory, group, index).ok_or_else(|| {
        EvidenceError::Input(format!("missing sort reference {theory}:{group}:{index}"))
    })?;
    crate::observation::validate_sort_obligations(payload, theorem)?;
    let signature = signatures.get(theory)?;
    signature.validate_judgment(theorem)?;
    for obligation in as_array(payload, "sort obligations")? {
        signature.validate_type(field(obligation, "type")?)?;
        signature.validate_declared_sort(field(obligation, "required_sort")?)?;
    }
    Ok(())
}

fn validate_named_members(
    value: &Value,
    inventory: &Value,
    execution: &Value,
    manifest: &Value,
    field_name: &str,
) -> Result<(), EvidenceError> {
    let mut signatures = crate::signature::SignatureCache::new(inventory);
    let mut expected = BTreeSet::new();
    for theory in as_array(field(inventory, "theories")?, "inventory theories")? {
        let theory_name = as_str(field(theory, "name")?, "theory")?;
        for group in as_array(field(theory, "fact_groups")?, "fact groups")? {
            let group_name = as_str(field(group, "name")?, "fact group")?;
            for member in as_array(field(group, "theorems")?, "fact members")? {
                expected.insert((
                    theory_name,
                    group_name,
                    require_index(field(member, "index")?, "member index")?,
                ));
            }
        }
    }
    let mut observed = BTreeSet::new();
    for record in as_array(value, field_name)? {
        let theory = as_str(field(record, "theory")?, field_name)?;
        let group = as_str(field(record, "fact_group_name")?, field_name)?;
        let index = require_index(field(record, "member_index")?, field_name)?;
        require(
            observed.insert((theory, group, index)),
            format!("{field_name}: duplicate named theorem member"),
        )?;
        let payload = field(record, "value")?;
        crate::observation::validate_named_payload(field_name, payload)?;
        validate_named_observation_syntax(
            inventory,
            theory,
            group,
            index,
            field_name,
            payload,
            &mut signatures,
        )?;
        validate_named_payload_owners(inventory, execution, manifest, theory, field_name, payload)?;
    }
    require(
        expected == observed,
        format!("{field_name}: incomplete or foreign named theorem membership"),
    )
}

fn validate_observed_fact(
    inventory: &Value,
    event_theory: &str,
    fact: &Value,
    signatures: &mut crate::signature::SignatureCache<'_>,
) -> Result<(), EvidenceError> {
    let owner = as_str(field(fact, "owner")?, "event fact owner")?;
    validate_observation_owner(inventory, event_theory, owner)?;
    let signature = signatures.get(owner)?;
    crate::observation::validate_statement_signature(field(fact, "statement")?, signature)?;
    for dependency in as_array(field(fact, "dependencies")?, "event fact dependencies")? {
        let dependency_owner = as_str(field(dependency, "owner")?, "event dependency owner")?;
        validate_observation_owner(inventory, owner, dependency_owner)?;
        let signature = signatures.get(dependency_owner)?;
        crate::observation::validate_dependency_signature(dependency, signature)?;
    }
    Ok(())
}

fn validate_event_owners_and_syntax(
    inventory: &Value,
    event_theory: &str,
    field_name: &str,
    value: &Value,
    signatures: &mut crate::signature::SignatureCache<'_>,
) -> Result<(), EvidenceError> {
    match field_name {
        "anonymous_ephemeral_facts" => {
            validate_observed_fact(inventory, event_theory, value, signatures)
        },
        "dynamic_fact_evaluations" => {
            for result in as_array(field(value, "results")?, "dynamic results")? {
                validate_observed_fact(inventory, event_theory, result, signatures)?;
            }
            Ok(())
        },
        "runtime_registration_effects" => {
            let owner = as_str(field(value, "owner")?, "registration owner")?;
            validate_observation_owner(inventory, event_theory, owner)
        },
        _ => Err(EvidenceError::Input(format!("unknown event field {field_name}"))),
    }
}

fn validate_event_members(
    value: &Value,
    inventory: &Value,
    execution: &Value,
    manifest: &Value,
    field_name: &str,
) -> Result<(), EvidenceError> {
    let mut signatures = crate::signature::SignatureCache::new(inventory);
    let mut seen = BTreeSet::new();
    for record in as_array(value, field_name)? {
        let theory_name = as_str(field(record, "theory")?, field_name)?;
        let event = require_index(field(record, "execution_event")?, field_name)?;
        let local_id = as_str(field(record, "local_id")?, field_name)?;
        require(
            !local_id.is_empty() && seen.insert((theory_name, event, local_id)),
            format!("{field_name}: empty or duplicate local event identity"),
        )?;
        let theories = as_array(field(execution, "theories")?, "executed theories")?;
        let theory = theories.iter().find(|item| item["name"] == theory_name).ok_or_else(|| {
            EvidenceError::Input(format!("{field_name}: foreign theory {theory_name}"))
        })?;
        require(
            as_array(field(theory, "commands")?, "executed commands")?
                .iter()
                .any(|command| command["sequence"].as_u64() == Some(event)),
            format!("{field_name}: nonexistent execution event {event}"),
        )?;
        let payload = field(record, "value")?;
        crate::observation::validate_event_payload(field_name, payload)?;
        validate_event_owners_and_syntax(
            inventory,
            theory_name,
            field_name,
            payload,
            &mut signatures,
        )?;
        if let Some(source) = payload.get("source") {
            validate_observation_source(manifest, source)?;
        }
    }
    Ok(())
}

fn validate_closure_fields(
    closure: &Value,
    observations: &BTreeMap<String, Value>,
    inventory: &Value,
    execution: &Value,
    manifest: &Value,
) -> Result<Vec<&'static str>, EvidenceError> {
    let fields = as_object(field(closure, "fields")?, "closure fields")?;
    require(
        fields.len() == P0_MISSING.len()
            && P0_MISSING.iter().all(|name| fields.contains_key(*name)),
        "closure fields differ from six required observations",
    )?;
    let mut incomplete = Vec::new();
    for field_name in P0_MISSING {
        let wrapper = &fields[field_name];
        match as_str(field(wrapper, "status")?, field_name)? {
            "Unavailable" => {
                let object = as_object(wrapper, field_name)?;
                require(
                    (object.len() == 2 || (object.len() == 3 && object.contains_key("evidence")))
                        && object.contains_key("reason")
                        && !as_str(field(wrapper, "reason")?, field_name)?.is_empty(),
                    format!("{field_name}: missing concrete unavailability reason"),
                )?;
                if let Some(evidence) = object.get("evidence") {
                    require_fields(
                        evidence,
                        &["artifact", "pointer"],
                        "unavailability provenance",
                    )?;
                    let artifact = as_str(&evidence["artifact"], field_name)?;
                    require(
                        artifact != "closure-evidence",
                        "unavailability evidence cannot self-reference",
                    )?;
                    let reference = observations.get(artifact).ok_or_else(|| {
                        EvidenceError::Input(format!(
                            "{field_name}: unknown provenance artifact {artifact}"
                        ))
                    })?;
                    let record =
                        locate_pointer(reference, as_str(&evidence["pointer"], field_name)?)?;
                    require(
                        record["field"] == field_name && record["reason"] == wrapper["reason"],
                        format!("{field_name}: unavailability reason differs from observation"),
                    )?;
                }
            },
            "Available" => {
                require_fields(
                    wrapper,
                    &["status", "value", "evidence", "completeness"],
                    field_name,
                )?;
                require(
                    wrapper["completeness"] == "complete",
                    format!("{field_name}: incomplete observation"),
                )?;
                let artifact = validate_provenance(wrapper, field_name, observations)?;
                if matches!(
                    field_name,
                    "anonymous_ephemeral_facts"
                        | "dynamic_fact_evaluations"
                        | "runtime_registration_effects"
                ) {
                    validate_event_members(
                        &wrapper["value"],
                        inventory,
                        execution,
                        manifest,
                        field_name,
                    )?;
                } else {
                    validate_named_members(
                        &wrapper["value"],
                        inventory,
                        execution,
                        manifest,
                        field_name,
                    )?;
                }
                if !crate::observation::has_complete_coverage(
                    artifact,
                    field_name,
                    &wrapper["value"],
                    inventory,
                    execution,
                )? {
                    incomplete.push(field_name);
                }
            },
            _ => {
                return Err(EvidenceError::Input(format!("{field_name}: unknown evidence status")));
            },
        }
    }
    Ok(incomplete)
}

fn find_named_member<'a>(
    theories: &'a [Value],
    theory: &str,
    group: &str,
    index: u64,
) -> Option<&'a Value> {
    theories
        .iter()
        .find(|item| item["name"] == theory)
        .and_then(|item| item["fact_groups"].as_array())
        .and_then(|groups| groups.iter().find(|item| item["name"] == group))
        .and_then(|item| item["theorems"].as_array())
        .and_then(|members| members.iter().find(|item| item["index"].as_u64() == Some(index)))
}

fn compare_named_observations(
    differences: &mut ComparisonDiagnostics,
    inventory: &Value,
    candidate: &Value,
    name: &str,
    observed: &Value,
) -> Result<(), EvidenceError> {
    let reference_theories = as_array(field(inventory, "theories")?, "inventory theories")?;
    let theories = as_array(field(candidate, "theories")?, "candidate theories")?;
    let mut signatures = crate::signature::SignatureCache::new(inventory);
    for record in as_array(observed, name)? {
        let theory = as_str(field(record, "theory")?, name)?;
        let group = as_str(field(record, "fact_group_name")?, name)?;
        let member = require_index(field(record, "member_index")?, name)?;
        let source = find_named_member(reference_theories, theory, group, member);
        let native = find_named_member(theories, theory, group, member);
        let identity = format!("{theory}:{group}:{member}:{name}");
        if name == "unresolved_sort_obligations" {
            let is_match = match (source, native) {
                (Some(original), Some(actual)) => match_judgments_with_constraints(
                    original,
                    actual,
                    as_array(field(record, "value")?, name)?,
                    as_array(field(field(actual, name)?, "value")?, name)?,
                )?,
                _ => false,
            };
            differences.compare_value(identity, &true, &is_match);
        } else if name == "full_axiom_extension_dependencies" {
            let actual =
                native.and_then(|item| item.get(name)).and_then(|wrapper| wrapper.get("value"));
            let is_match = match actual {
                Some(actual) => crate::observation_match::match_dependency_records(
                    field(record, "value")?,
                    actual,
                    &mut signatures,
                )?,
                None => false,
            };
            differences.compare_value(identity, &true, &is_match);
        } else {
            let actual =
                native.and_then(|item| item.get(name)).and_then(|wrapper| wrapper.get("value"));
            differences.compare_value(identity, &Some(field(record, "value")?), &actual);
        }
    }
    Ok(())
}

fn compare_event_observations(
    differences: &mut ComparisonDiagnostics,
    inventory: &Value,
    candidate: &Value,
    name: &str,
    observed: &Value,
) -> Result<(), EvidenceError> {
    let mut signatures = crate::signature::SignatureCache::new(inventory);
    let actual = field(candidate, "execution")?.get(name);
    let is_match = match actual {
        Some(actual) => {
            crate::observation_match::match_event_records(name, observed, actual, &mut signatures)?
        },
        None => false,
    };
    differences.compare_value(format!("execution:{name}"), &true, &is_match);
    Ok(())
}

/// Compare a private candidate (no final `result`) before publication.
pub fn compare_candidate(
    reference: &VerifiedReferenceEvidence,
    candidate: &Value,
) -> Result<Comparison, EvidenceError> {
    if let Some(v2) = &reference.version_two {
        return crate::protocol_v2::compare_candidate_v2(reference, v2, candidate);
    }
    let mut differences = compare_candidate_observations(
        &reference.inventory,
        &reference.execution,
        candidate,
        &reference.frozen,
    )?;
    let fields = as_object(field(&reference.closure, "fields")?, "closure fields")?;
    for name in P0_MISSING {
        if fields[name]["status"] == "Unavailable" {
            differences.blocked.push(json!({"field":name,"status":"Unavailable",
                "reason":fields[name]["reason"]}));
        } else if matches!(
            name,
            "anonymous_ephemeral_facts"
                | "dynamic_fact_evaluations"
                | "runtime_registration_effects"
        ) {
            compare_event_observations(
                &mut differences,
                &reference.inventory,
                candidate,
                name,
                &fields[name]["value"],
            )?;
        } else {
            compare_named_observations(
                &mut differences,
                &reference.inventory,
                candidate,
                name,
                &fields[name]["value"],
            )?;
        }
        if reference.incomplete_observations.contains(&name) {
            differences.blocked.push(json!({"field":name,"status":"Unavailable",
                "reason":"independent observation coverage not established"}));
        }
    }
    if !differences.differences.is_empty() {
        return Ok(Comparison::Different(differences.report()));
    }
    if !differences.blocked.is_empty() {
        return Ok(Comparison::Incomplete(differences.report()));
    }
    Ok(Comparison::Matched)
}
