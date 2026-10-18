//! Fixed, fail-closed veriT execution boundary. No shell command is ever evaluated.
mod argv;
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[path = "solver/linux.rs"]
mod platform;
#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
#[path = "solver/unsupported.rs"]
mod platform;

use std::path::PathBuf;
use std::time::Duration;

use super::files::{HostIoError, RestrictedHost};
use super::lifecycle::{LifecycleError, TaskLease, WorkKind};

pub const MAX_WALL: Duration = Duration::from_secs(300);
pub const MAX_INPUT: usize = 64 * 1024 * 1024;
pub const MAX_OUTPUT: usize = 256 * 1024 * 1024;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverErrorKind {
    /// Invocation asks for an unapproved effect or malformed solver arguments (user-fixable).
    Permission,
    /// A required OS isolation or pinned executable prerequisite is absent (user-fixable).
    BlockedPrerequisite,
    /// The build was cancelled (recoverable, but not proof success).
    Cancelled,
    /// The supervised execution exceeded a hard resource bound (fatal for this build).
    ResourceLimit,
    /// The process or its domain could not be completely cleaned up (fatal).
    CleanupFailure,
    /// OS operation failed (fatal for this invocation; source retained).
    System,
}

#[derive(Debug, thiserror::Error)]
#[error("solver {operation}: {reason}")]
pub struct SolverError {
    pub kind: SolverErrorKind,
    pub operation: &'static str,
    pub reason: String,
    #[source]
    pub source: Option<std::io::Error>,
}

impl SolverError {
    fn new(kind: SolverErrorKind, operation: &'static str, reason: impl Into<String>) -> Self {
        Self { kind, operation, reason: reason.into(), source: None }
    }
    fn io(
        kind: SolverErrorKind,
        operation: &'static str,
        reason: impl Into<String>,
        source: std::io::Error,
    ) -> Self {
        Self { kind, operation, reason: reason.into(), source: Some(source) }
    }
    fn host(error: HostIoError) -> Self {
        let kind = match &error {
            HostIoError::Lifecycle { .. } => SolverErrorKind::Cancelled,
            _ => SolverErrorKind::Permission,
        };
        Self::io(kind, "authorize fixed veriT", error.to_string(), std::io::Error::other(error))
    }

    fn lifecycle(error: LifecycleError) -> Self {
        Self::io(
            SolverErrorKind::Cancelled,
            "complete supervised solver task",
            error.to_string(),
            std::io::Error::other(error),
        )
    }
}

pub struct SolverRequest {
    pub script: String,
    pub input: Vec<u8>,
    pub cwd: Option<PathBuf>,
    pub environment: Vec<(String, String)>,
    pub timeout: Duration,
    pub redirect: bool,
}

pub struct SolverOutput {
    pub code: i32,
    pub output: Vec<u8>,
}

pub struct SolverConfig {
    pub executable: PathBuf,
    pub delegated_cgroup_root: PathBuf,
    pub staging_root: PathBuf,
    pub bubblewrap: PathBuf,
    pub elf_loader: PathBuf,
    pub libc: PathBuf,
    pub libm: PathBuf,
    pub libgmp: PathBuf,
}

pub struct FixedSolver {
    config: SolverConfig,
    is_running: bool,
}

impl FixedSolver {
    pub fn new(config: SolverConfig) -> Result<Self, SolverError> {
        platform::check_config(&config)?;
        Ok(Self { config, is_running: false })
    }

    /// Pure input validation; the configured executable is a request, never authority.
    pub fn validate_request(
        config: &SolverConfig,
        request: &SolverRequest,
    ) -> Result<Vec<String>, SolverError> {
        if !request.environment.is_empty() {
            return Err(SolverError::new(
                SolverErrorKind::Permission,
                "validate putenv",
                "environment overrides forbidden",
            ));
        }
        if !request.redirect {
            return Err(SolverError::new(
                SolverErrorKind::Permission,
                "validate redirection",
                "stderr must be merged at descriptor level",
            ));
        }
        if request.input.len() > MAX_INPUT {
            return Err(SolverError::new(
                SolverErrorKind::Permission,
                "validate stdin",
                "64 MiB input bound exceeded",
            ));
        }
        if request.cwd.as_ref().is_some_and(|cwd| cwd != &config.staging_root) {
            return Err(SolverError::new(
                SolverErrorKind::Permission,
                "validate cwd",
                "only solver staging directory is permitted",
            ));
        }
        argv::parse_script(&request.script, &config.executable)
    }

    pub fn run(
        &mut self,
        request: SolverRequest,
        host: &RestrictedHost,
        lease: &TaskLease,
    ) -> Result<SolverOutput, SolverError> {
        host.authorize_fixed_solver(lease).map_err(SolverError::host)?;
        if self.is_running {
            let error = SolverError::new(
                SolverErrorKind::Permission,
                "run solver",
                "solver call already active",
            );
            Self::revoke_build(host, &error);
            return Err(error);
        }
        let args = Self::validate_request(&self.config, &request).inspect_err(|error| {
            Self::revoke_build(host, error);
        })?;
        let process = lease
            .start_child(WorkKind::Process, "fixed veriT execution")
            .map_err(SolverError::lifecycle)?;
        self.is_running = true;
        let result = platform::run(
            &self.config,
            &args,
            request,
            &host.lifecycle().cancellation(),
            host.lifecycle(),
            process,
        );
        self.is_running = false;
        result
    }
    fn revoke_build(host: &RestrictedHost, error: &SolverError) {
        if let Err(source) = host.lifecycle().cancel(error.to_string()) {
            tracing::error!(kind = ?source.kind, "failed to record solver failure");
        }
    }
}

/// Called before any normal product command dispatch in the current trusted executable.
/// Returns `Some(exit_code)` only after the internal launcher branch has completed.
pub fn run_launcher_if_requested() -> Result<Option<i32>, SolverError> {
    platform::run_launcher_if_requested()
}
