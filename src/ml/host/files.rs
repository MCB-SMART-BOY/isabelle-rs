//! Supervisor-issued filesystem and environment effects for one build domain.
//! Root descriptors and an unforgeable live task lease, never source text or hashes, grant access.
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::time::{Duration, Instant, SystemTime};

use super::anchored_fs::DirectoryRoot;
use super::lifecycle::{BuildLifecycle, LifecycleError, RuntimePhase, TaskLease, WorkKind};
use crate::ml::{HostBridge, HostFailure, Value, Vm};

/// Maximum bytes per source read or staging write (including dynamically compiled source).
pub const MAX_FILE_BYTES: usize = 64 * 1024 * 1024;
const IO_CHUNK_BYTES: usize = 8192;
/// Upper bound on each wait before rechecking cancellation and phase permissions.
const SLEEP_CHECK_INTERVAL: Duration = Duration::from_millis(10);

/// A key and its intended use; a snapshot value cannot be reused for a different purpose.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct EnvironmentUse {
    pub key: String,
    pub purpose: String,
}

/// Capabilities independently approved by the caller, requested by the manifest, and allowed in a phase.
#[derive(Clone, Debug, Default)]
pub struct EffectSet {
    pub read_source: bool,
    pub read_resources: BTreeSet<String>,
    pub write_staging: bool,
    pub run_fixed_verit: bool,
    /// Read the real system clock; this never permits setting it.
    pub read_clock: bool,
    /// Wait on the current evaluation thread with cancellation and phase checks.
    pub sleep: bool,
    pub environment: BTreeSet<EnvironmentUse>,
}

#[derive(Clone, Debug, Default)]
pub struct PhaseEffects {
    pub active: EffectSet,
    pub draining: EffectSet,
}

/// Absolute fixed roots are selected by the supervisor, not by ML input or a source hash.
/// `staging_name` is exclusively created beneath `staging_parent` for this authority.
#[derive(Clone, Debug)]
pub struct HostRoots {
    pub source: PathBuf,
    pub resources: BTreeMap<String, PathBuf>,
    pub staging_parent: PathBuf,
    pub staging_name: PathBuf,
}

/// Redirected native diagnostic stream; bytes stay inside the authorized build staging area.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DiagnosticChannel {
    Stdout,
    Stderr,
}

/// Typed host failure; source chains preserve the original filesystem, UTF-8, or lifecycle cause.
#[derive(Debug)]
pub enum HostIoError {
    /// Input path was not a strict relative path, or a configured root was not absolute.
    InvalidPath(PathBuf),
    /// A relative path exceeded its byte length, component byte length, or traversal depth bound.
    PathLimit { path: PathBuf, constraint: &'static str, limit: usize },
    /// A capability, file type, or private-staging requirement was not met.
    Permission { operation: &'static str, path: PathBuf, reason: &'static str },
    /// The input exceeded the host's fixed per-operation byte bound.
    TooLarge { operation: &'static str, path: PathBuf, limit: usize },
    /// Filesystem operation failed; its operating-system error is preserved.
    Io { operation: &'static str, path: PathBuf, source: std::io::Error },
    /// A verified regular-file parent produced a recoverable NotADirectory error.
    OrdinaryIo { operation: &'static str, path: PathBuf, source: std::io::Error },
    /// Text decoding failed; invalid UTF-8 is never silently replaced.
    Utf8 { path: PathBuf, source: std::string::FromUtf8Error },
    /// A task lease or lifecycle phase failed validation.
    Lifecycle { operation: &'static str, source: LifecycleError },
    /// A VM adapter task lease has already been explicitly completed.
    LeaseCompleted,
    /// A host lease lock was poisoned and authority must be revoked.
    PoisonedLease,
    /// Fatal diagnostic-state corruption; output ordering is no longer reliable.
    PoisonedOutput,
    /// Fatal exhaustion of the monotonic diagnostic sequence.
    OutputSequenceExhausted,
}
impl HostIoError {
    /// An already-authorized filesystem operation can fail as an ordinary SML IO exception.
    /// The NativeFunction adapter must preserve the SML exception identity and source chain.
    pub fn is_ordinary_ml_io(&self) -> bool {
        matches!(self, Self::OrdinaryIo { .. })
            || matches!(
                self,
                Self::Io { source, .. }
                    if matches!(source.kind(), std::io::ErrorKind::NotFound | std::io::ErrorKind::AlreadyExists)
            )
    }
}

impl fmt::Display for HostIoError {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidPath(path) => write!(out, "invalid anchored path {}", path.display()),
            Self::PathLimit { path, constraint, limit } => {
                write!(
                    out,
                    "invalid anchored path {}: {constraint} exceeds {limit}",
                    path.display()
                )
            },
            Self::Permission { operation, path, reason } => {
                write!(out, "{operation} {}: {reason}", path.display())
            },
            Self::TooLarge { operation, path, limit } => {
                write!(out, "{operation} {}: exceeds {limit} bytes", path.display())
            },
            Self::Io { operation, path, source } | Self::OrdinaryIo { operation, path, source } => {
                write!(out, "{operation} {}: {source}", path.display())
            },
            Self::Utf8 { path, source } => {
                write!(out, "decode source {}: {source}", path.display())
            },
            Self::Lifecycle { operation, source } => write!(out, "{operation}: {source}"),
            Self::LeaseCompleted => write!(out, "host task lease already completed"),
            Self::PoisonedLease => write!(out, "host task lease lock poisoned"),
            Self::PoisonedOutput => write!(out, "write diagnostic output: sequence lock poisoned"),
            Self::OutputSequenceExhausted => {
                write!(out, "write diagnostic output: sequence exhausted")
            },
        }
    }
}

impl Error for HostIoError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Io { source, .. } | Self::OrdinaryIo { source, .. } => Some(source),
            Self::Utf8 { source, .. } => Some(source),
            Self::Lifecycle { source, .. } => Some(source),
            _ => None,
        }
    }
}

/// Supervisor-configured, immutable authority; every effect also requires a live same-build lease.
pub struct RestrictedHost {
    lifecycle: BuildLifecycle,
    source_path: PathBuf,
    source: DirectoryRoot,
    resources: BTreeMap<String, DirectoryRoot>,
    pub(super) staging: DirectoryRoot,
    staging_parent: PathBuf,
    staging_name: PathBuf,
    caller: EffectSet,
    manifest: EffectSet,
    phases: PhaseEffects,
    environment: BTreeMap<EnvironmentUse, Option<String>>,
    #[cfg(test)]
    sleep_entry: Option<std::sync::Arc<(std::sync::Barrier, std::sync::Barrier)>>,
}

impl RestrictedHost {
    pub fn new(
        lifecycle: BuildLifecycle,
        lease: &TaskLease,
        roots: HostRoots,
        caller: EffectSet,
        manifest: EffectSet,
        phases: PhaseEffects,
        environment: BTreeMap<EnvironmentUse, Option<String>>,
    ) -> Result<Self, HostIoError> {
        let result: Result<Self, HostIoError> = (|| {
            Self::validate_setup(&lifecycle, lease, &roots)?;
            let source = DirectoryRoot::open(&roots.source)?;
            let resources = roots
                .resources
                .iter()
                .map(|(name, path)| {
                    DirectoryRoot::open(path).map(|directory| (name.clone(), directory))
                })
                .collect::<Result<_, _>>()?;
            let staging = Self::open_authorized_staging(&lifecycle, lease, &roots)?;
            lifecycle.check_task(lease).map_err(|source| HostIoError::Lifecycle {
                operation: "initialize file host",
                source,
            })?;
            Ok(Self {
                lifecycle: lifecycle.clone(),
                source_path: roots.source,
                source,
                resources,
                staging,
                staging_parent: roots.staging_parent,
                staging_name: roots.staging_name,
                caller,
                manifest,
                phases,
                environment,
                #[cfg(test)]
                sleep_entry: None,
            })
        })();
        if let Err(error) = &result
            && let Err(source) = lifecycle.cancel(error.to_string())
        {
            tracing::error!(kind = ?source.kind, "failed to record host initialization failure");
        }
        result
    }
    fn validate_setup(
        lifecycle: &BuildLifecycle,
        lease: &TaskLease,
        roots: &HostRoots,
    ) -> Result<(), HostIoError> {
        lifecycle.check_task(lease).map_err(|source| HostIoError::Lifecycle {
            operation: "initialize file host",
            source,
        })?;
        if lifecycle.phase().map_err(|source| HostIoError::Lifecycle {
            operation: "initialize file host",
            source,
        })? != RuntimePhase::Active
        {
            return Err(HostIoError::Permission {
                operation: "initialize file host",
                path: roots.staging_name.clone(),
                reason: "staging must be created in active phase",
            });
        }
        super::anchored_fs::validate_relative(&roots.staging_name)?;
        if roots.staging_name.components().count() != 1 {
            return Err(HostIoError::InvalidPath(roots.staging_name.clone()));
        }
        Ok(())
    }

    fn open_authorized_staging(
        lifecycle: &BuildLifecycle,
        lease: &TaskLease,
        roots: &HostRoots,
    ) -> Result<DirectoryRoot, HostIoError> {
        DirectoryRoot::create_staging(&roots.staging_parent, &roots.staging_name, &mut || {
            lifecycle.check_task(lease).map_err(|source| HostIoError::Lifecycle {
                operation: "create staging root",
                source,
            })
        })
    }

    pub fn lifecycle(&self) -> &BuildLifecycle {
        &self.lifecycle
    }

    pub fn source_root_path(&self) -> &Path {
        // The configured root is diagnostic only; reads always use the anchored descriptor.
        &self.source_path
    }

    pub fn staging_parent_path(&self) -> &Path {
        &self.staging_parent
    }

    pub fn staging_name(&self) -> &Path {
        &self.staging_name
    }

    pub fn authorize_fixed_solver(&self, lease: &TaskLease) -> Result<(), HostIoError> {
        self.authorize(lease, "run fixed veriT", Path::new("verit-2021.06.2-rmx-1"), |set| {
            set.run_fixed_verit
        })
    }
    fn authorize(
        &self,
        lease: &TaskLease,
        operation: &'static str,
        path: &Path,
        is_allowed: impl Fn(&EffectSet) -> bool,
    ) -> Result<(), HostIoError> {
        self.check_result(Self::check_authority(
            &self.lifecycle,
            lease,
            (&self.caller, &self.manifest, &self.phases),
            operation,
            path,
            is_allowed,
        ))
    }

    fn check_authority(
        lifecycle: &BuildLifecycle,
        lease: &TaskLease,
        authority: (&EffectSet, &EffectSet, &PhaseEffects),
        operation: &'static str,
        path: &Path,
        is_allowed: impl Fn(&EffectSet) -> bool,
    ) -> Result<(), HostIoError> {
        let (caller, manifest, phases) = authority;
        lifecycle
            .check_task(lease)
            .map_err(|source| HostIoError::Lifecycle { operation, source })?;
        let phase =
            lifecycle.phase().map_err(|source| HostIoError::Lifecycle { operation, source })?;
        let current = match phase {
            RuntimePhase::Active => &phases.active,
            RuntimePhase::Draining => &phases.draining,
            _ => {
                return Err(HostIoError::Permission {
                    operation,
                    path: path.to_owned(),
                    reason: "phase prohibits effects",
                });
            },
        };
        if is_allowed(caller) && is_allowed(manifest) && is_allowed(current) {
            return Ok(());
        }
        Err(HostIoError::Permission {
            operation,
            path: path.to_owned(),
            reason: "caller, manifest, or phase did not grant capability",
        })
    }

    fn deny<T>(
        &self,
        operation: &'static str,
        path: &Path,
        reason: &'static str,
    ) -> Result<T, HostIoError> {
        let error = HostIoError::Permission { operation, path: path.to_owned(), reason };
        self.record_failure(&error);
        Err(error)
    }

    fn check_result<T>(&self, result: Result<T, HostIoError>) -> Result<T, HostIoError> {
        if let Err(error) = &result
            && !error.is_ordinary_ml_io()
        {
            self.record_failure(error);
        }
        result
    }

    fn record_failure(&self, error: &HostIoError) {
        if let Err(source) = self.lifecycle.cancel(error.to_string()) {
            tracing::error!(kind = ?source.kind, "failed to record host failure");
        }
    }

    fn read_file(
        &self,
        lease: &TaskLease,
        root: &DirectoryRoot,
        path: &Path,
        limit: usize,
        is_allowed: impl Fn(&EffectSet) -> bool + Copy,
    ) -> Result<Vec<u8>, HostIoError> {
        let limit = limit.min(MAX_FILE_BYTES);
        let mut authorize = || self.authorize(lease, "read source", path, is_allowed);
        let mut file = root.open_file(path, &mut authorize)?;
        let metadata = file.metadata().map_err(|source| HostIoError::Io {
            operation: "inspect source",
            path: path.to_owned(),
            source,
        })?;
        if metadata.len() > limit as u64 {
            return Err(HostIoError::TooLarge {
                operation: "read source",
                path: path.to_owned(),
                limit,
            });
        }
        let mut bytes = Vec::with_capacity(metadata.len() as usize);
        let mut chunk = [0u8; IO_CHUNK_BYTES];
        loop {
            self.authorize(lease, "read source", path, is_allowed)?;
            let remaining = limit - bytes.len();
            let read_limit = IO_CHUNK_BYTES.min(remaining + 1);
            let count = file.read(&mut chunk[..read_limit]).map_err(|source| HostIoError::Io {
                operation: "read source",
                path: path.to_owned(),
                source,
            })?;
            if count == 0 {
                break;
            }
            if count > remaining {
                return Err(HostIoError::TooLarge {
                    operation: "read source",
                    path: path.to_owned(),
                    limit,
                });
            }
            bytes.extend_from_slice(&chunk[..count]);
        }
        self.authorize(lease, "read source", path, is_allowed)?;
        Ok(bytes)
    }

    /// Read bytes only below the fixed source root; dynamic source compilation must use this entry.
    pub fn read_source(&self, lease: &TaskLease, path: &Path) -> Result<Vec<u8>, HostIoError> {
        self.read_source_bounded(lease, path, MAX_FILE_BYTES)
    }

    /// Enforce the caller's narrower byte budget before allocating source contents.
    pub fn read_source_bounded(
        &self,
        lease: &TaskLease,
        path: &Path,
        limit: usize,
    ) -> Result<Vec<u8>, HostIoError> {
        self.authorize(lease, "read source", path, |effects| effects.read_source)?;
        self.check_result(
            self.read_file(lease, &self.source, path, limit, |effects| effects.read_source),
        )
    }

    pub fn read_source_text(&self, lease: &TaskLease, path: &Path) -> Result<String, HostIoError> {
        let bytes = self.read_source(lease, path)?;
        self.check_result(
            String::from_utf8(bytes)
                .map_err(|source| HostIoError::Utf8 { path: path.to_owned(), source }),
        )
    }

    pub fn read_resource(
        &self,
        lease: &TaskLease,
        root: &str,
        path: &Path,
    ) -> Result<Vec<u8>, HostIoError> {
        self.read_resource_bounded(lease, root, path, MAX_FILE_BYTES)
    }

    /// Enforce a narrower byte budget using the same anchored resource descriptor.
    pub fn read_resource_bounded(
        &self,
        lease: &TaskLease,
        root: &str,
        path: &Path,
        limit: usize,
    ) -> Result<Vec<u8>, HostIoError> {
        self.authorize(lease, "read resource", path, |effects| {
            effects.read_resources.contains(root)
        })?;
        let directory = self.resources.get(root).ok_or_else(|| HostIoError::Permission {
            operation: "read resource",
            path: path.to_owned(),
            reason: "unknown fixed resource root",
        });
        self.check_result(directory.and_then(|directory| {
            self.read_file(lease, directory, path, limit, |effects| {
                effects.read_resources.contains(root)
            })
        }))
    }

    pub fn read_resource_text(
        &self,
        lease: &TaskLease,
        root: &str,
        path: &Path,
    ) -> Result<String, HostIoError> {
        let bytes = self.read_resource(lease, root, path)?;
        self.check_result(
            String::from_utf8(bytes)
                .map_err(|source| HostIoError::Utf8 { path: path.to_owned(), source }),
        )
    }

    /// Create a new private file, never overwrite an existing staging entry or write outside it.
    pub fn write_staging(
        &self,
        lease: &TaskLease,
        path: &Path,
        bytes: &[u8],
    ) -> Result<(), HostIoError> {
        self.authorize(lease, "write staging", path, |effects| effects.write_staging)?;
        self.check_result(self.write_file(lease, path, bytes))
    }

    fn write_file(&self, lease: &TaskLease, path: &Path, bytes: &[u8]) -> Result<(), HostIoError> {
        if bytes.len() > MAX_FILE_BYTES {
            return Err(HostIoError::TooLarge {
                operation: "write staging",
                path: path.to_owned(),
                limit: MAX_FILE_BYTES,
            });
        }
        let mut file = self.staging.create_file(path, &mut || {
            self.authorize(lease, "write staging", path, |effects| effects.write_staging)
        })?;
        for chunk in bytes.chunks(IO_CHUNK_BYTES) {
            self.authorize(lease, "write staging", path, |effects| effects.write_staging)?;
            file.write_all(chunk).map_err(|source| HostIoError::Io {
                operation: "write staging",
                path: path.to_owned(),
                source,
            })?;
        }
        file.sync_all().map_err(|source| HostIoError::Io {
            operation: "sync staging",
            path: path.to_owned(),
            source,
        })?;
        self.authorize(lease, "write staging", path, |effects| effects.write_staging)
    }

    /// Return real wall time only under this build's three-way clock permission.
    pub fn read_clock(&self, lease: &TaskLease) -> Result<SystemTime, HostIoError> {
        let identity = Path::new("Time.now");
        self.authorize(lease, "read clock", identity, |effects| effects.read_clock)?;
        let time = SystemTime::now();
        self.authorize(lease, "read clock", identity, |effects| effects.read_clock)?;
        Ok(time)
    }

    /// Wait for a real monotonic duration without disabling cancellation.
    /// Zero waits still require authority. Long waits cannot overflow an absolute deadline.
    pub fn sleep(&self, lease: &TaskLease, duration: Duration) -> Result<(), HostIoError> {
        let start = Instant::now();
        loop {
            self.authorize(lease, "sleep", Path::new("OS.Process.sleep"), |effects| effects.sleep)?;
            let remaining = duration.saturating_sub(start.elapsed());
            if remaining.is_zero() {
                return Ok(());
            }
            #[cfg(test)]
            if let Some(entry) = &self.sleep_entry {
                entry.0.wait();
                entry.1.wait();
            }
            std::thread::sleep(remaining.min(SLEEP_CHECK_INTERVAL));
        }
    }

    /// Read only a caller-provided immutable snapshot, never the ambient process environment.
    /// An explicit `None` means approved absence; a missing snapshot entry remains forbidden.
    pub fn read_environment(
        &self,
        lease: &TaskLease,
        key: &str,
        purpose: &str,
    ) -> Result<Option<String>, HostIoError> {
        self.check_result(
            self.lifecycle
                .check_task(lease)
                .map_err(|source| HostIoError::Lifecycle { operation: "read environment", source }),
        )?;
        let usage = EnvironmentUse { key: key.to_owned(), purpose: purpose.to_owned() };
        let identity = Path::new(key);
        if key == "HOME" || key.is_empty() || purpose.is_empty() {
            return self.deny(
                "read environment",
                identity,
                "ambient HOME or empty key/purpose is forbidden",
            );
        }
        self.authorize(lease, "read environment", identity, |effects| {
            effects.environment.contains(&usage)
        })?;
        let result = self.environment.get(&usage).cloned().ok_or_else(|| HostIoError::Permission {
            operation: "read environment",
            path: identity.to_owned(),
            reason: "approved snapshot has no entry",
        });
        self.check_result(result)
    }
}

/// VM adapter bound to one uncloneable task lease; `complete` returns accounting to lifecycle.
pub struct FileHostBridge {
    authority: RestrictedHost,
    lease: Mutex<Option<TaskLease>>,
    output_sequence: Mutex<u64>,
}

impl FileHostBridge {
    pub fn new(authority: RestrictedHost, lease: TaskLease) -> Self {
        Self { authority, lease: Mutex::new(Some(lease)), output_sequence: Mutex::new(0) }
    }

    /// Identify this build without exposing its mutable authority or task lease.
    pub fn shares_build(&self, lifecycle: &BuildLifecycle) -> bool {
        self.authority.lifecycle.shares_build(lifecycle)
    }

    /// Run a linked, trusted plugin under a registered child task of this live build.
    /// The parent mutex is released before the callback, allowing nested host calls.
    pub fn with_plugin_task<T>(
        &self,
        vm: &Vm,
        kind: WorkKind,
        operation: &str,
        invoke: impl FnOnce(&RestrictedHost, &TaskLease) -> Result<T, HostIoError>,
    ) -> Result<T, HostIoError> {
        let child = self.reserve_plugin_task(vm, kind, operation)?;
        self.execute_plugin_task(child, invoke)
    }

    /// Continue an already authenticated request without sending its non-Send VM
    /// across threads. A live same-build reservation may drain after evaluation ends.
    /// The caller retains and must complete the reservation after this child returns.
    pub fn with_reserved_plugin_task<T>(
        &self,
        reservation: &TaskLease,
        kind: WorkKind,
        operation: &str,
        invoke: impl FnOnce(&RestrictedHost, &TaskLease) -> Result<T, HostIoError>,
    ) -> Result<T, HostIoError> {
        self.authority.check_result(self.authority.lifecycle.check_task(reservation).map_err(
            |source| HostIoError::Lifecycle { operation: "check plugin reservation", source },
        ))?;
        let child =
            self.authority.check_result(reservation.start_child(kind, operation).map_err(
                |source| HostIoError::Lifecycle { operation: "start reserved plugin task", source },
            ))?;
        self.execute_plugin_task(child, invoke)
    }

    fn execute_plugin_task<T>(
        &self,
        child: TaskLease,
        invoke: impl FnOnce(&RestrictedHost, &TaskLease) -> Result<T, HostIoError>,
    ) -> Result<T, HostIoError> {
        let result = self.authority.check_result(invoke(&self.authority, &child));
        let completion = self.authority.check_result(child.complete().map_err(|source| {
            HostIoError::Lifecycle { operation: "complete plugin task", source }
        }));
        match result {
            Ok(value) => completion.map(|()| value),
            Err(error) => {
                if let Err(completion_error) = completion {
                    tracing::error!(error = %completion_error, "plugin task completion failed after service error");
                }
                Err(error)
            },
        }
    }

    /// Reserve one supervised call before its result/cancellation becomes observable.
    /// A queued call keeps the build open until its lease is explicitly completed.
    pub fn reserve_plugin_task(
        &self,
        vm: &Vm,
        kind: WorkKind,
        origin: &str,
    ) -> Result<TaskLease, HostIoError> {
        self.check_vm(vm)?;
        self.with_live_lease(|parent| {
            parent.start_child(kind, origin).map_err(|source| HostIoError::Lifecycle {
                operation: "reserve plugin task",
                source,
            })
        })
    }

    /// Bind native Basis operations to this bridge's actual VM cancellation domain.
    pub fn check_vm(&self, vm: &Vm) -> Result<(), HostIoError> {
        if !self.authority.lifecycle.matches_stop_handle(&vm.stop_handle()) {
            // A mismatched caller must not retain a live capability domain.
            vm.request_stop();
            return self.authority.deny(
                "bind file host",
                Path::new("VM"),
                "foreign cancellation domain",
            );
        }
        self.with_live_lease(|_| Ok(()))
    }

    /// Read the clock only in the bridge's own live VM/build domain.
    pub fn read_clock(&self, vm: &Vm) -> Result<SystemTime, HostIoError> {
        self.check_vm(vm)?;
        self.with_live_lease(|lease| self.authority.read_clock(lease))
    }

    /// Perform an authorized, cancellable wait in this VM's evaluation lease.
    pub fn sleep(&self, vm: &Vm, duration: Duration) -> Result<(), HostIoError> {
        self.check_vm(vm)?;
        self.with_live_lease(|lease| self.authority.sleep(lease, duration))
    }

    /// Return the exact source bytes for hashing and evaluation by native Basis code.
    pub fn read_source_bytes(&self, path: &Path) -> Result<Vec<u8>, HostIoError> {
        self.with_live_lease(|lease| self.authority.read_source(lease, path))
    }

    /// Snapshot a permitted source and retain a managed stream until the caller closes it.
    pub fn open_source_stream(&self, path: &Path) -> Result<(Vec<u8>, TaskLease), HostIoError> {
        self.with_live_lease(|parent| {
            let bytes = self.authority.read_source(parent, path)?;
            let stream = parent
                .start_child(super::lifecycle::WorkKind::Stream, &path.to_string_lossy())
                .map_err(|source| HostIoError::Lifecycle {
                    operation: "open source stream",
                    source,
                })?;
            Ok((bytes, stream))
        })
    }

    /// Write a synchronous, ordered chunk without exposing ambient stdout or stderr.
    pub fn write_output(
        &self,
        channel: DiagnosticChannel,
        bytes: &[u8],
    ) -> Result<(), HostIoError> {
        self.with_live_lease(|lease| {
            let mut sequence =
                self.output_sequence.lock().map_err(|_| HostIoError::PoisonedOutput)?;
            let next = sequence.checked_add(1).ok_or(HostIoError::OutputSequenceExhausted)?;
            let extension = match channel {
                DiagnosticChannel::Stdout => "stdout",
                DiagnosticChannel::Stderr => "stderr",
            };
            let path = PathBuf::from(format!("diagnostics/{sequence}.{extension}"));
            self.authority.write_staging(lease, &path, bytes)?;
            *sequence = next;
            Ok(())
        })
    }

    /// Read only the supervisor-snapshotted value for the approved key and purpose.
    pub fn read_environment(
        &self,
        key: &str,
        purpose: &str,
    ) -> Result<Option<String>, HostIoError> {
        self.with_live_lease(|lease| self.authority.read_environment(lease, key, purpose))
    }

    fn with_live_lease<T>(
        &self,
        operation: impl FnOnce(&TaskLease) -> Result<T, HostIoError>,
    ) -> Result<T, HostIoError> {
        let result = (|| {
            let guard = self.lease.lock().map_err(|_| HostIoError::PoisonedLease)?;
            let lease = guard.as_ref().ok_or(HostIoError::LeaseCompleted)?;
            self.authority.lifecycle.check_task(lease).map_err(|source| {
                HostIoError::Lifecycle { operation: "invoke file host", source }
            })?;
            operation(lease)
        })();
        self.authority.check_result(result)
    }

    pub fn complete(&self) -> Result<(), HostIoError> {
        let mut guard = self.lease.lock().map_err(|_| {
            self.authority.record_failure(&HostIoError::PoisonedLease);
            HostIoError::PoisonedLease
        })?;
        let lease = guard.take().ok_or_else(|| {
            self.authority.record_failure(&HostIoError::LeaseCompleted);
            HostIoError::LeaseCompleted
        })?;
        lease
            .complete()
            .map_err(|source| HostIoError::Lifecycle { operation: "complete file host", source })
    }

    fn dispatch(
        &self,
        operation: &str,
        args: &[Value],
        lease: &TaskLease,
    ) -> Result<HostOutput, HostIoError> {
        let args = if args.len() == 1 { args[0].as_tuple().unwrap_or(args) } else { args };
        let argument = |index: usize| args.get(index).and_then(Value::as_text);
        match operation {
            "filesystem.read_source" if args.len() == 1 => self
                .authority
                .read_source_text(
                    lease,
                    Path::new(argument(0).ok_or_else(|| invalid_argument(operation))?),
                )
                .map(|value| HostOutput::Value(Value::text(value))),
            "filesystem.read_resource" if args.len() == 2 => self
                .authority
                .read_resource_text(
                    lease,
                    argument(0).ok_or_else(|| invalid_argument(operation))?,
                    Path::new(argument(1).ok_or_else(|| invalid_argument(operation))?),
                )
                .map(|value| HostOutput::Value(Value::text(value))),
            "filesystem.write_staging" if args.len() == 2 => {
                let path = Path::new(argument(0).ok_or_else(|| invalid_argument(operation))?);
                let content = argument(1).ok_or_else(|| invalid_argument(operation))?;
                self.authority
                    .write_staging(lease, path, content.as_bytes())
                    .map(|()| HostOutput::Value(Value::unit()))
            },
            "filesystem.read_environment" if args.len() == 2 => self
                .authority
                .read_environment(
                    lease,
                    argument(0).ok_or_else(|| invalid_argument(operation))?,
                    argument(1).ok_or_else(|| invalid_argument(operation))?,
                )
                .map(HostOutput::Environment),
            _ => self.authority.deny(
                "invoke unsupported host effect",
                Path::new(operation),
                "unrecognized or malformed host operation",
            ),
        }
    }
}

enum HostOutput {
    Value(Value),
    Environment(Option<String>),
}

fn invalid_argument(operation: &str) -> HostIoError {
    HostIoError::Permission {
        operation: "invoke host effect",
        path: PathBuf::from(operation),
        reason: "expected text arguments",
    }
}

impl HostBridge for FileHostBridge {
    fn invoke(&self, vm: &mut Vm, operation: &str, args: &[Value]) -> Result<Value, HostFailure> {
        let output = self
            .check_vm(vm)
            .and_then(|()| self.with_live_lease(|lease| self.dispatch(operation, args, lease)))
            .map_err(|error| {
                // Compatibility HostBridge has no SML exception channel. Ordinary I/O
                // must fail closed here; NativeFunction is the catchable Basis I/O route.
                if error.is_ordinary_ml_io() {
                    self.authority.record_failure(&error);
                }
                let resource = error.to_string();
                match error {
                    HostIoError::Permission { .. } | HostIoError::InvalidPath(_) => {
                        HostFailure::Permission {
                            operation: operation.to_owned(),
                            resource,
                            cause: "capability revoked".to_owned(),
                        }
                    },
                    HostIoError::Lifecycle { .. } => HostFailure::Stopped { cause: resource },
                    _ => HostFailure::Failed {
                        operation: operation.to_owned(),
                        resource,
                        cause: "host effect failed".to_owned(),
                    },
                }
            })?;
        match output {
            HostOutput::Value(value) => Ok(value),
            HostOutput::Environment(value) => vm
                .make_option(value.map(Value::text))
                .map_err(|error| HostFailure::Stopped { cause: error.to_string() }),
        }
    }
}

impl HostBridge for std::sync::Arc<FileHostBridge> {
    fn invoke(&self, vm: &mut Vm, operation: &str, args: &[Value]) -> Result<Value, HostFailure> {
        self.as_ref().invoke(vm, operation, args)
    }
}

#[cfg(test)]
#[path = "timing_tests.rs"]
mod timing_tests;
