//! Reference-only observed closure: never native Rust theorem authorization.
mod coverage;
mod execution;
mod trace_events;

use std::fs;
use std::path::Path;

use serde_json::{Value, json};

use super::common::require;
use crate::runner::{StepError, io_error};
use execution::{catalog_commands, inspect_execution, inspect_inventory};
use trace_events::catalog_traces;

/// Bind decoded fixed inventory, executed commands, and sanitized syscall events.
pub fn build_reference_profile(
    inventory: &Value,
    execution: &Value,
    source_root: &Path,
    traces: &[Value],
) -> Result<Value, StepError> {
    let root = fs::canonicalize(source_root).map_err(|cause| {
        io_error(
            format!("resolve fixed source root {} for reference profile", source_root.display()),
            cause,
        )
    })?;
    require(root.is_dir(), format!("Not a fixed source directory: {}", source_root.display()))?;
    let inventory_sources = inspect_inventory(inventory, &root)?;
    let theories = inspect_execution(execution, &inventory_sources)?;
    let (requirements, bindings) = catalog_commands(theories, &root)?;
    let catalog = catalog_traces(traces, &root)?;
    let nodes: Vec<Value> = inventory["theories"].as_array().ok_or_else(|| StepError::Input("Missing inventory theories".into()))?
        .iter().map(|theory| {
            let source = theory["source"].as_str().ok_or_else(|| StepError::Input("Missing theory source".into()))?;
            let digest = inventory_sources.manifest.get(source).ok_or_else(|| StepError::Input(format!("Missing theory source SHA256 for {source}")))?;
            Ok(json!({"name": theory["name"], "parents": theory["parents"], "import_specifications": theory["import_specifications"], "source": source, "sha256": digest}))
        }).collect::<Result<_, StepError>>()?;
    Ok(json!({
        "schema_version": 1,
        "reference": "Isabelle2025",
        "authorization": "none_reference_requirements_only",
        "theory_graph": { "roots": inventory["roots"], "nodes": nodes },
        "command_requirements": requirements,
        "ml_file_bindings": bindings,
        "fixed_source_reads": catalog.reads,
        "generated_inputs": catalog.generated,
        "external_executables": catalog.executables,
        "unresolved_resources": catalog.unresolved,
        "coverage": coverage::describe_coverage(),
    }))
}
