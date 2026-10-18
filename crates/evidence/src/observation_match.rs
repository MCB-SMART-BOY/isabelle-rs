//! Identity-aligned comparison of independently observed theorem payloads.
use std::collections::BTreeMap;

use serde_json::Value;

use crate::EvidenceError;
use crate::common::{as_array, as_str, field, require};
use crate::compare_syntax::match_judgments_with_premises;
use crate::observation::{validate_event_payload, validate_named_payload};
use crate::signature::SignatureCache;

type DependencyKey<'a> = (&'a str, &'a str, &'a str);
type EventKey<'a> = (&'a str, u64, &'a str);

fn index_dependencies<'a>(
    value: &'a Value,
) -> Result<BTreeMap<DependencyKey<'a>, &'a Value>, EvidenceError> {
    let mut indexed = BTreeMap::new();
    for dependency in as_array(value, "full dependencies")? {
        let key = (
            as_str(field(dependency, "kind")?, "dependency kind")?,
            as_str(field(dependency, "name")?, "dependency name")?,
            as_str(field(dependency, "owner")?, "dependency owner")?,
        );
        require(
            indexed.insert(key, dependency).is_none(),
            format!("duplicate dependency {key:?}"),
        )?;
    }
    Ok(indexed)
}

fn match_statement(
    left: &Value,
    right: &Value,
    left_premises: &[Value],
    right_premises: &[Value],
) -> Result<bool, EvidenceError> {
    match_judgments_with_premises(
        left,
        right,
        as_array(field(left, "sort_obligations")?, "left sort obligations")?,
        as_array(field(right, "sort_obligations")?, "right sort obligations")?,
        left_premises,
        right_premises,
    )
}

pub(crate) fn match_dependency_records(
    left: &Value,
    right: &Value,
    signatures: &mut SignatureCache<'_>,
) -> Result<bool, EvidenceError> {
    validate_named_payload("full_axiom_extension_dependencies", right)?;
    for dependency in as_array(right, "candidate dependencies")? {
        let owner = as_str(field(dependency, "owner")?, "candidate dependency owner")?;
        crate::observation::validate_dependency_signature(dependency, signatures.get(owner)?)?;
    }
    let left = index_dependencies(left)?;
    let right = index_dependencies(right)?;
    if left.keys().ne(right.keys()) {
        return Ok(false);
    }
    for (key, original) in left {
        let Some(actual) = right.get(&key) else {
            return Ok(false);
        };
        let original_certificate = field(original, "certificate")?;
        let actual_certificate = field(actual, "certificate")?;
        if !match_statement(
            field(original, "statement")?,
            field(actual, "statement")?,
            as_array(field(original_certificate, "premises")?, "left certificate premises")?,
            as_array(field(actual_certificate, "premises")?, "right certificate premises")?,
        )? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn match_anonymous_fact(
    original: &Value,
    actual: &Value,
    signatures: &mut SignatureCache<'_>,
) -> Result<bool, EvidenceError> {
    let owner = as_str(field(actual, "owner")?, "candidate fact owner")?;
    crate::observation::validate_statement_signature(
        field(actual, "statement")?,
        signatures.get(owner)?,
    )?;
    if original["owner"] != actual["owner"]
        || original["authorization_kind"] != actual["authorization_kind"]
    {
        return Ok(false);
    }
    let left = field(original, "statement")?;
    let right = field(actual, "statement")?;
    if !match_statement(left, right, &[], &[])? {
        return Ok(false);
    }
    match_dependency_records(
        field(original, "dependencies")?,
        field(actual, "dependencies")?,
        signatures,
    )
}

fn match_dynamic_evaluation(
    original: &Value,
    actual: &Value,
    signatures: &mut SignatureCache<'_>,
) -> Result<bool, EvidenceError> {
    if original["source"] != actual["source"] || original["expression"] != actual["expression"] {
        return Ok(false);
    }
    let left = as_array(field(original, "results")?, "reference dynamic results")?;
    let right = as_array(field(actual, "results")?, "native dynamic results")?;
    if left.len() != right.len() {
        return Ok(false);
    }
    for (reference, native) in left.iter().zip(right) {
        if !match_anonymous_fact(reference, native, signatures)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn index_events<'a>(
    value: &'a Value,
    context: &str,
) -> Result<BTreeMap<EventKey<'a>, &'a Value>, EvidenceError> {
    let mut indexed = BTreeMap::new();
    for record in as_array(value, context)? {
        let key = (
            as_str(field(record, "theory")?, context)?,
            field(record, "execution_event")?
                .as_u64()
                .ok_or_else(|| EvidenceError::Input(format!("{context}: negative event index")))?,
            as_str(field(record, "local_id")?, context)?,
        );
        require(
            !key.2.is_empty() && indexed.insert(key, record).is_none(),
            format!("{context}: empty or duplicate event identity {key:?}"),
        )?;
    }
    Ok(indexed)
}

pub(crate) fn match_event_records(
    field_name: &str,
    left: &Value,
    right: &Value,
    signatures: &mut SignatureCache<'_>,
) -> Result<bool, EvidenceError> {
    let left = index_events(left, "reference events")?;
    let right = index_events(right, "candidate events")?;
    if left.keys().ne(right.keys()) {
        return Ok(false);
    }
    for (key, original) in left {
        let Some(actual) = right.get(&key) else {
            return Ok(false);
        };
        let left_value = field(original, "value")?;
        let right_value = field(actual, "value")?;
        validate_event_payload(field_name, right_value)?;
        let is_match = match field_name {
            "anonymous_ephemeral_facts" => {
                match_anonymous_fact(left_value, right_value, signatures)?
            },
            "dynamic_fact_evaluations" => {
                match_dynamic_evaluation(left_value, right_value, signatures)?
            },
            "runtime_registration_effects" => left_value == right_value,
            _ => return Err(EvidenceError::Input(format!("unknown event field {field_name}"))),
        };
        if !is_match {
            return Ok(false);
        }
    }
    Ok(true)
}
