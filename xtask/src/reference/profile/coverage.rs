use serde_json::{Value, json};

pub(super) fn describe_coverage() -> Value {
    json!({
        "observed": [
            "inventory_theory_graph", "executed_theory_command_occurrences",
            "executed_file_command_bindings", "successful_fixed_source_open_observations",
            "successful_generated_mount_open_observations", "successful_exec_observations",
            "unresolved_relative_open_observations"
        ],
        "unavailable": [
            "Pure_bootstrap_command_spans", "anonymous_ephemeral_facts", "unregistered_proof_steps",
            "dynamic_fact_evaluations", "ML_runtime_call_graph", "implicit_ML_load_events"
        ],
        "ordering": "Per-theory source order and per-trace/per-thread syscall evidence; no global logical order",
        "limits": {
            "theory_graph": "Decoded static inventory parents/imports; not a runtime resource graph",
            "command_requirements": "Official executed theory command positions, not native support or proof",
            "ml_file_bindings": "Official file-command parser binding, not implicit ML runtime loads",
            "fixed_source_reads": "Successful selected syscalls on current verified fixed-source bytes; not bytes at syscall time or complete language execution",
            "generated_inputs": "Successful generated mount accesses; no immutable source hash",
            "external_executables": "Successful exec paths only; not permission, argv or environment",
            "unresolved_resources": "Relative paths and source directories are not credited as file inputs, regardless of syscall outcome"
        },
        "provenance": {
            "theory_graph": "strict decoded official inventory and fixed-source SHA256 manifest",
            "command_requirements": "strict decoded official execution command occurrences; trusted_loader.rs frontend scope",
            "ml_file_bindings": "strict decoded official execution resolved file-command inputs and verified fixed-source bytes",
            "fixed_source_reads": "build/inventory strace -yy open/openat results plus fixed-source current bytes",
            "generated_inputs": "build/inventory strace -yy open/openat results and isolated writable mount configuration",
            "external_executables": "build/inventory strace execve/execveat results",
            "unresolved_resources": "build/inventory strace unresolved relative open/openat or source directory observation"
        }
    })
}
