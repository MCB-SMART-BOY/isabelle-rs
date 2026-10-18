use super::{SolverConfig, SolverError, SolverErrorKind, SolverOutput, SolverRequest};
use crate::ml::host::lifecycle::{BuildLifecycle, Cancellation, LifecycleErrorKind, TaskLease};

fn unavailable(operation: &'static str) -> SolverError {
    SolverError::new(
        SolverErrorKind::BlockedPrerequisite,
        operation,
        "fixed veriT isolation requires Linux x86_64",
    )
}

pub(super) fn check_config(_config: &SolverConfig) -> Result<(), SolverError> {
    Err(unavailable("validate solver configuration"))
}

pub(super) fn run(
    _config: &SolverConfig,
    _args: &[String],
    _request: SolverRequest,
    _cancellation: &Cancellation,
    lifecycle: &BuildLifecycle,
    process: TaskLease,
) -> Result<SolverOutput, SolverError> {
    let error = unavailable("run solver");
    if let Err(source) = lifecycle.cancel(error.to_string()) {
        tracing::error!(kind = ?source.kind, "failed to record unsupported solver failure");
    }
    if let Err(source) = process.complete()
        && source.kind != LifecycleErrorKind::Cancelled
    {
        return Err(SolverError::lifecycle(source));
    }
    Err(error)
}

pub(super) fn run_launcher_if_requested() -> Result<Option<i32>, SolverError> {
    if std::env::args_os().nth(1).as_deref()
        == Some(std::ffi::OsStr::new("--internal-solver-launcher"))
    {
        return Err(unavailable("start solver launcher"));
    }
    Ok(None)
}
