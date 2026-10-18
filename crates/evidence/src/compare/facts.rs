use std::collections::BTreeMap;

use serde_json::Value;

use super::{ComparisonDiagnostics, index_named, require_keys};
use crate::EvidenceError as StepError;
use crate::common::{as_array, as_str, field, require, require_fields};
use crate::compare_syntax::{match_judgments, require_index};
use crate::signature::SignatureCache;

type FactIdentity<'a> = (&'a str, u64);

fn require_evidence<'a>(
    record: &'a Value,
    name: &str,
    context: &str,
) -> Result<&'a Value, StepError> {
    require_keys(record, &[name], context)?;
    let evidence = &record[name];
    require_fields(
        evidence,
        &["status", "value", "evidence", "completeness"],
        &format!("{context}:{name}"),
    )?;
    require(
        evidence["status"] == "Available",
        format!("{context}:{name}: native evidence unavailable"),
    )?;
    require(
        evidence["completeness"] == "complete",
        format!("{context}:{name}: incomplete native evidence"),
    )?;
    require(
        !as_str(&evidence["evidence"], "evidence provenance")?.is_empty(),
        format!("{context}:{name}: missing provenance"),
    )?;
    Ok(&evidence["value"])
}

fn validate_native_fact(
    fact: &Value,
    reference: &Value,
    theory: &str,
    context: &str,
) -> Result<(), StepError> {
    for field_name in ["unresolved_sort_obligations", "oracle_footprint", "pending", "futures"] {
        require(
            require_evidence(fact, field_name, context)?.as_array().is_some_and(Vec::is_empty),
            format!("{context}:{field_name}: unresolved burden"),
        )?;
    }
    require(
        field(fact, "has_skip_proof")?.as_bool() == Some(false),
        format!("{context}: skipped proof"),
    )?;
    require(
        field(fact, "authorization_kind")? == "KernelTrustedClosed",
        format!("{context}: not accepted"),
    )?;
    require(
        as_array(field(fact, "hypotheses")?, "hypotheses")?.is_empty()
            && as_array(field(fact, "tpairs")?, "tpairs")?.is_empty(),
        format!("{context}: open accepted theorem"),
    )?;
    let accepted = as_str(require_evidence(fact, "accepted_in", context)?, "accepted owner")?;
    crate::common::require(!accepted.is_empty(), format!("{context}: empty accepted owner"))?;
    crate::protocol::validate_observation_owner(reference, theory, accepted)?;
    for name in ["full_axiom_extension_dependencies", "declaration_origin"] {
        require_evidence(fact, name, context)?;
    }
    Ok(())
}

fn fact_identity<'a>(fact: &'a Value, context: &str) -> Result<FactIdentity<'a>, StepError> {
    Ok((as_str(field(fact, "name")?, context)?, require_index(field(fact, "index")?, context)?))
}

fn index_facts<'a>(
    facts: &'a [Value],
    context: &str,
) -> Result<BTreeMap<FactIdentity<'a>, &'a Value>, StepError> {
    let mut indexed = BTreeMap::new();
    for fact in facts {
        let key = fact_identity(fact, context)?;
        require(indexed.insert(key, fact).is_none(), format!("{context}: duplicate {key:?}"))?;
    }
    Ok(indexed)
}

fn compare_group(
    result: &mut ComparisonDiagnostics,
    theory: &str,
    name: &str,
    expected: &Value,
    actual: &Value,
    reference: &Value,
    signatures: &mut SignatureCache<'_>,
) -> Result<(), StepError> {
    let context = format!("{theory}:{name}");
    let a = as_array(expected, &context)?;
    let b = as_array(actual, &context)?;
    let left = index_facts(a, &context)?;
    let right = index_facts(b, &context)?;
    let same_order = a.len() == b.len()
        && a.iter().zip(b).all(|(a, b)| a["name"] == b["name"] && a["index"] == b["index"]);
    if !same_order {
        result.add_difference(format!("{context}:members"), "structural mismatch");
    }
    for (identity, original) in left {
        let Some(native) = right.get(&identity) else {
            continue;
        };
        let context = format!("{context}:{}", identity.1);
        validate_native_fact(native, reference, theory, &context)?;
        signatures.get(theory)?.validate_judgment(native)?;
        result.compare_value(
            format!("{context}:observed_in"),
            field(original, "owner")?,
            field(native, "observed_in")?,
        );
        result.compare_value(
            format!("{context}:skip"),
            field(original, "has_skip_proof")?,
            field(native, "has_skip_proof")?,
        );
        result.compare_value(
            format!("{context}:oracle"),
            field(original, "oracle_footprint")?,
            &native["oracle_footprint"]["value"],
        );
        if match_judgments(original, native)? {
            result.matched_facts += 1;
        } else {
            result.add_difference(context, "P/H/S/F mismatch");
        }
    }
    Ok(())
}

pub(super) fn compare_fact_groups(
    result: &mut ComparisonDiagnostics,
    expected: &Value,
    actual: &Value,
    reference: &Value,
) -> Result<(), StepError> {
    let context = as_str(field(expected, "name")?, "theory name")?;
    let mut signatures = SignatureCache::new(reference);
    let left = index_named(field(expected, "fact_groups")?, context)?;
    let right = index_named(field(actual, "fact_groups")?, context)?;
    if left.keys().ne(right.keys()) {
        result.add_difference(format!("{context}:fact_groups"), "structural mismatch");
    }
    for (name, group) in left {
        if let Some(candidate) = right.get(name) {
            compare_group(
                result,
                context,
                name,
                field(group, "theorems")?,
                field(candidate, "theorems")?,
                reference,
                &mut signatures,
            )?;
        }
    }
    Ok(())
}
