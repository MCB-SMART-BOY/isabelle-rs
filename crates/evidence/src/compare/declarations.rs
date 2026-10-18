use serde_json::Value;

use super::{ComparisonDiagnostics, index_named};
use crate::EvidenceError as StepError;
use crate::common::{as_array, as_str, field};
use crate::compare_syntax::{match_validated_records, validate_sort};

const NAMED_DECLARATIONS: [&str; 5] = ["types", "classes", "constants", "axioms", "fact_indexes"];
const SET_DECLARATIONS: [&str; 5] = [
    "class_relations",
    "arities",
    "specifications",
    "constant_definitions",
    "oracle_registrations",
];

fn compare_named_records(
    result: &mut ComparisonDiagnostics,
    context: &str,
    expected: &Value,
    actual: &Value,
) -> Result<(), StepError> {
    let left = index_named(expected, context)?;
    let right = index_named(actual, context)?;
    if left.keys().ne(right.keys()) {
        result.add_difference(format!("{context}: names"), "structural mismatch");
    }
    for (name, record) in left {
        if let Some(candidate) = right.get(name)
            && !match_validated_records(record, candidate)?
        {
            result.add_difference(format!("{context}:{name}"), "structural mismatch");
        }
    }
    Ok(())
}

fn compare_set_records(
    result: &mut ComparisonDiagnostics,
    context: &str,
    expected: &Value,
    actual: &Value,
) -> Result<(), StepError> {
    let actual = as_array(actual, context)?;
    let mut used = vec![false; actual.len()];
    for record in as_array(expected, context)? {
        let mut found = None;
        for (index, candidate) in actual.iter().enumerate() {
            if !used[index] && match_validated_records(record, candidate)? {
                found = Some(index);
                break;
            }
        }
        if let Some(index) = found {
            used[index] = true;
        } else {
            result.add_difference(context, "missing set member");
        }
    }
    if used.iter().any(|is_used| !is_used) {
        result.add_difference(context, "unexpected set members");
    }
    Ok(())
}

pub(super) fn compare_declarations(
    result: &mut ComparisonDiagnostics,
    expected: &Value,
    actual: &Value,
) -> Result<(), StepError> {
    let context = as_str(field(expected, "name")?, "theory name")?;
    let a = field(expected, "default_sort")?;
    let b = field(actual, "default_sort")?;
    validate_sort(a)?;
    validate_sort(b)?;
    for section in NAMED_DECLARATIONS {
        compare_named_records(
            result,
            &format!("{context}:{section}"),
            field(expected, section)?,
            field(actual, section)?,
        )?;
    }
    for section in SET_DECLARATIONS {
        compare_set_records(
            result,
            &format!("{context}:{section}"),
            field(expected, section)?,
            field(actual, section)?,
        )?;
    }
    let a = as_array(a, "default sort")?;
    let b = as_array(b, "default sort")?;
    if a.len() != b.len() || a.iter().any(|value| !b.contains(value)) {
        result.add_difference(format!("{context}:default_sort"), "structural mismatch");
    }
    Ok(())
}
