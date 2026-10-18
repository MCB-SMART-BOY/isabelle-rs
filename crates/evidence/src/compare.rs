//! Pure comparison of fixed reference observations and native candidate reports.
mod declarations;
mod facts;

use crate::common::{COMMIT, ROOTS, as_array, as_object, as_str, field, require};
use crate::compare_sources::compare_sources;
use crate::compare_syntax::require_index;
use crate::{EvidenceError as StepError, validate_entities, validate_graph};
use serde_json::{Value, json};
use std::collections::BTreeMap;

pub const P0_MISSING: [&str; 6] = [
    "full_axiom_extension_dependencies",
    "unresolved_sort_obligations",
    "declaration_origin",
    "anonymous_ephemeral_facts",
    "dynamic_fact_evaluations",
    "runtime_registration_effects",
];
const SCHEMA_VERSION: u64 = 1;

#[derive(Default)]
pub(crate) struct ComparisonDiagnostics {
    pub(crate) differences: Vec<Value>,
    pub(crate) blocked: Vec<Value>,
    matched_facts: usize,
}

impl ComparisonDiagnostics {
    pub fn compare_value<T: PartialEq + ?Sized>(
        &mut self,
        context: impl Into<String>,
        expected: &T,
        actual: &T,
    ) {
        if expected != actual {
            self.add_difference(context, "structural mismatch");
        }
    }

    pub fn add_difference(&mut self, context: impl Into<String>, reason: &str) {
        self.differences.push(json!({"input":context.into(),"reason":reason}));
    }

    pub fn report(self) -> Value {
        let status = if !self.differences.is_empty() {
            "Failed"
        } else if !self.blocked.is_empty() {
            "BlockedPrerequisite"
        } else {
            "Succeeded"
        };
        json!({"schema_version":SCHEMA_VERSION,"purpose":"reference_comparison_diagnostics",
            "authorization":"none","result":status,"matched_named_facts":self.matched_facts,
            "differences":self.differences,"unavailable":self.blocked})
    }
}

pub fn require_keys(value: &Value, keys: &[&str], context: &str) -> Result<(), StepError> {
    let object = as_object(value, context)?;
    require(keys.iter().all(|key| object.contains_key(*key)), format!("{context}: missing fields"))
}

fn index_named<'a>(
    records: &'a Value,
    context: &str,
) -> Result<BTreeMap<&'a str, &'a Value>, StepError> {
    let mut index = BTreeMap::new();
    for record in as_array(records, context)? {
        let name = as_str(field(record, "name")?, context)?;
        require(index.insert(name, record).is_none(), format!("{context}: duplicate {name:?}"))?;
    }
    Ok(index)
}

fn compare_theories(
    result: &mut ComparisonDiagnostics,
    reference: &Value,
    native: &Value,
) -> Result<(), StepError> {
    let expected = index_named(field(reference, "theories")?, "reference theories")?;
    let actual = index_named(field(native, "theories")?, "native theories")?;
    if expected.keys().ne(actual.keys()) {
        result.add_difference("theory identities", "structural mismatch");
    }
    for (name, left) in expected {
        let Some(right) = actual.get(name) else {
            continue;
        };
        require_keys(
            right,
            &["source", "parents", "import_specifications", "default_sort", "fact_groups"],
            name,
        )?;
        for key in ["source", "parents", "import_specifications"] {
            result.compare_value(format!("{name}:{key}"), field(left, key)?, field(right, key)?);
        }
        declarations::compare_declarations(result, left, right)?;
        facts::compare_fact_groups(result, left, right, reference)?;
    }
    Ok(())
}

fn compare_execution(
    result: &mut ComparisonDiagnostics,
    reference: &Value,
    native: &Value,
) -> Result<(), StepError> {
    require_keys(native, &["theories", "status", "pending_tasks"], "native execution")?;
    require_index(&native["pending_tasks"], "native execution: pending tasks")?;
    result.compare_value("execution status", &json!("Complete"), &native["status"]);
    result.compare_value("pending tasks", &json!(0), &native["pending_tasks"]);
    let expected = index_named(field(reference, "theories")?, "reference execution")?;
    let actual = index_named(&native["theories"], "native execution")?;
    if expected.keys().ne(actual.keys()) {
        result.add_difference("executed theories", "structural mismatch");
    }
    for (name, left) in expected {
        if let Some(right) = actual.get(name) {
            result.compare_value(format!("{name}:executed commands"), left, *right);
        }
    }
    Ok(())
}

fn validate_report_identity(
    reference: &Value,
    native: &Value,
    is_candidate: bool,
    is_v2: bool,
) -> Result<(), StepError> {
    let required = [
        "schema_version",
        "purpose",
        "source_commit",
        "source_files",
        "requested_roots",
        "theories",
        "execution",
        "effects",
    ];
    require_keys(native, &required, "native report")?;
    require(
        native.get("result").is_some() != is_candidate,
        "native candidate must not carry a final result",
    )?;
    require(native["schema_version"].as_u64() == Some(SCHEMA_VERSION), "native schema version")?;
    require(
        native["purpose"]
            == if is_v2 { "native_build_result" } else { "native_closure_diagnostics" },
        "native report purpose",
    )?;
    require(native["source_commit"] == COMMIT, "native source commit")?;
    let roots = json!(ROOTS);
    require(native["requested_roots"] == roots, "native root identities/order")?;
    require(
        reference["roots"] == roots && reference["reference"] == "Isabelle2025",
        "reference identities",
    )?;
    if !is_candidate {
        let theories = as_array(field(reference, "theories")?, "reference theories")?;
        validate_graph(theories)?;
        validate_entities(theories)?;
    }
    Ok(())
}

pub fn compare_reports(
    reference: &Value,
    execution: &Value,
    native: Value,
    manifest: &Value,
) -> Result<Value, StepError> {
    validate_report_identity(reference, &native, false, false)?;
    let mut result = compare_observations(reference, execution, &native, manifest)?;
    result.compare_value("native result", &json!("Succeeded"), &native["result"]);
    result.blocked = P0_MISSING
        .iter()
        .map(|name| {
            json!({"field":name,"status":"Unavailable",
            "reason":"not observed by the frozen P0 reference"})
        })
        .collect();
    Ok(result.report())
}

pub(crate) fn compare_candidate_observations(
    reference: &Value,
    execution: &Value,
    candidate: &Value,
    frozen: &Value,
) -> Result<ComparisonDiagnostics, StepError> {
    validate_report_identity(reference, candidate, true, false)?;
    compare_observations(reference, execution, candidate, frozen)
}
pub(crate) fn compare_candidate_observations_v2(
    reference: &Value,
    execution: &Value,
    candidate: &Value,
    frozen_sources: &BTreeMap<String, String>,
) -> Result<ComparisonDiagnostics, StepError> {
    validate_report_identity(reference, candidate, true, true)?;
    let mut result = ComparisonDiagnostics::default();
    let mut actual = BTreeMap::new();
    for entry in as_array(field(candidate, "source_files")?, "native source files")? {
        let path = as_str(field(entry, "path")?, "native source path")?;
        crate::protocol::validate_relative_path(path)?;
        let hash = as_str(field(entry, "sha256")?, "native source hash")?;
        require(
            actual.insert(path.to_owned(), hash.to_owned()).is_none(),
            format!("duplicate native source {path}"),
        )?;
    }
    result.compare_value("frozen original source bytes", frozen_sources, &actual);
    compare_theories(&mut result, reference, candidate)?;
    compare_execution(&mut result, execution, &candidate["execution"])?;
    let effects = field(candidate, "effects")?;
    require_keys(effects, &["phase", "pending"], "native effects")?;
    require_index(field(effects, "pending")?, "native pending effects")?;
    result.compare_value("native phase", &json!("closed"), &effects["phase"]);
    result.compare_value("native pending effects", &json!(0), &effects["pending"]);
    Ok(result)
}

fn compare_observations(
    reference: &Value,
    execution: &Value,
    native: &Value,
    manifest: &Value,
) -> Result<ComparisonDiagnostics, StepError> {
    let mut result = ComparisonDiagnostics::default();
    compare_sources(&mut result, reference, execution, native, manifest)?;
    compare_theories(&mut result, reference, native)?;
    compare_execution(&mut result, execution, &native["execution"])?;
    let effects = &native["effects"];
    require_keys(effects, &["phase", "pending"], "native effects")?;
    require_index(&effects["pending"], "native effects: pending")?;
    result.compare_value("runtime phase", &json!("closed"), &effects["phase"]);
    result.compare_value("pending effects", &json!(0), &effects["pending"]);
    Ok(result)
}
