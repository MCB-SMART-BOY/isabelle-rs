//! Linux PID-namespace supervision for HOL diagnostics.
use std::path::Path;

use crate::runner::StepError;

#[cfg(target_os = "linux")]
mod linux;

/// Run a selected diagnostic worker with the same options as `supervise`.
pub fn run(root: &Path, worker: &Path, args: &[String]) -> Result<(), StepError> {
    #[cfg(target_os = "linux")]
    {
        linux::run(root, worker, args)
    }
    #[cfg(not(target_os = "linux"))]
    {
        let _ = (root, worker, args);
        Err(StepError::Input("HOL supervision requires Linux PID and user namespaces".into()))
    }
}

/// CLI entry point; unlike `run`, accepts a `--worker PATH` option.
pub fn run_cli(root: &Path, args: &[String]) -> Result<(), StepError> {
    #[cfg(target_os = "linux")]
    {
        linux::run_cli(root, args)
    }
    #[cfg(not(target_os = "linux"))]
    {
        let _ = (root, args);
        Err(StepError::Input("HOL supervision requires Linux PID and user namespaces".into()))
    }
}

/// Dispatch the PID-namespace init process before parsing regular xtask options.
/// `Some(code)` must become the process' exact exit code (including worker errors).
pub fn run_internal(args: &[String]) -> Result<Option<i32>, StepError> {
    if args.first().map(String::as_str) != Some("__supervisor-child") {
        return Ok(None);
    }
    #[cfg(target_os = "linux")]
    {
        linux::run_internal(args).map(Some)
    }
    #[cfg(not(target_os = "linux"))]
    {
        Err(StepError::Input("HOL supervision requires Linux PID and user namespaces".into()))
    }
}
