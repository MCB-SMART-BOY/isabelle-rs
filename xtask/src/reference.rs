//! Native Rust reference orchestration and diagnostic comparison.
pub mod approved_identity;
pub mod artifacts;
pub mod classify_axioms;
pub mod common;
pub mod compare;
pub mod decode_bootstrap;
pub mod decode_bootstrap_events;
pub mod decode_execution;
pub mod decode_interfaces;
pub mod decode_inventory;
pub mod decode_observations;
pub mod execute;
pub mod instrumentation;
pub mod observe;
pub mod prepare;
pub mod profile;
pub mod trace;
pub mod yxml;

use std::path::{Path, PathBuf};

use crate::runner::StepError;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operation {
    Prepare,
    Build,
    Inventory,
    Compare,
}

impl Operation {
    pub fn name(self) -> &'static str {
        match self {
            Self::Prepare => "prepare",
            Self::Build => "build",
            Self::Inventory => "inventory",
            Self::Compare => "compare",
        }
    }
}

#[derive(Debug)]
pub struct Options {
    pub operation: Operation,
    pub workspace: Option<PathBuf>,
    pub source_root: Option<PathBuf>,
    pub build_run: Option<PathBuf>,
    pub rust_report: Option<PathBuf>,
    pub reference_run: Option<PathBuf>,
    pub reference_manifest: Option<PathBuf>,
    pub reference_preapproval: Option<PathBuf>,
    pub reference_approval: Option<PathBuf>,
}

impl Options {
    pub(crate) fn validate(&self) -> Result<(), StepError> {
        if self.operation != Operation::Compare {
            return Err(StepError::Input(
                "local official reference execution is disabled by the JVM-free policy; only offline comparison is available".into(),
            ));
        }
        if self.rust_report.is_none() || self.reference_run.is_none() {
            return Err(StepError::Input(
                "reference compare requires --rust-report PATH --reference-run PATH".into(),
            ));
        }
        if self.reference_preapproval.is_some() {
            return Err(StepError::Input(
                "--reference-preapproval is unavailable under the JVM-free policy".into(),
            ));
        }
        if self.reference_approval.is_some() && self.reference_manifest.is_none() {
            return Err(StepError::Input(
                "--reference-approval requires reference compare with --reference-manifest PATH"
                    .into(),
            ));
        }
        Ok(())
    }
}

pub fn run(root: &Path, options: Options) -> Result<(), StepError> {
    options.validate()?;
    let report = options
        .rust_report
        .ok_or_else(|| StepError::Input("reference compare requires --rust-report PATH".into()))?;
    let run = options.reference_run.ok_or_else(|| {
        StepError::Input("reference compare requires --reference-run PATH".into())
    })?;
    compare::run(
        &root.join("tests/fixtures/isabelle2025/closure.json"),
        &run,
        &report,
        options.reference_manifest.as_deref(),
        options.reference_approval.as_deref(),
    )
}
