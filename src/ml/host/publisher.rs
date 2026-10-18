//! Trusted publisher, separate from VM effects and bound to one private build directory.
use std::io::{self, Write};
use std::path::{Path, PathBuf};

use super::anchored_fs::{DirectoryRoot, validate_relative};
use super::files::{HostIoError, MAX_FILE_BYTES, RestrictedHost};
use super::lifecycle::{BuildLifecycle, LifecycleError, RuntimePhase, TaskLease};

const REPORT_FILE: &str = "report.json";
const REPORT_CHUNK_BYTES: usize = 8192;

/// Owns the single atomic publication of a previously frozen build report.
/// Neither the publisher nor its directory descriptors are exposed to ML.
pub struct BuildPublisher {
    lifecycle: BuildLifecycle,
    parent: DirectoryRoot,
    staging: DirectoryRoot,
    staging_name: PathBuf,
    output_dir: PathBuf,
    output_name: PathBuf,
    is_prepared: bool,
}

impl BuildPublisher {
    /// Construct while the matching build is active and the host still holds a live lease.
    pub fn new(
        host: &RestrictedHost,
        lease: &TaskLease,
        output_dir: &Path,
    ) -> Result<Self, HostIoError> {
        let lifecycle = host.lifecycle();
        lifecycle.check_task(lease).map_err(|source| HostIoError::Lifecycle {
            operation: "initialize publisher",
            source,
        })?;
        if lifecycle.phase().map_err(|source| HostIoError::Lifecycle {
            operation: "initialize publisher",
            source,
        })? != RuntimePhase::Active
        {
            return Err(HostIoError::Permission {
                operation: "initialize publisher",
                path: output_dir.to_owned(),
                reason: "publisher must be anchored while build is active",
            });
        }
        let output_name = Self::validate_destination(host, output_dir)?;
        let (parent, staging) = Self::anchor_directories(host, &output_name, output_dir)?;
        lifecycle.check_task(lease).map_err(|source| HostIoError::Lifecycle {
            operation: "initialize publisher",
            source,
        })?;
        Ok(Self {
            lifecycle: lifecycle.clone(),
            parent,
            staging,
            staging_name: host.staging_name().to_owned(),
            output_dir: output_dir.to_owned(),
            output_name,
            is_prepared: false,
        })
    }

    fn validate_destination(
        host: &RestrictedHost,
        output_dir: &Path,
    ) -> Result<PathBuf, HostIoError> {
        let output_name = output_dir
            .strip_prefix(host.staging_parent_path())
            .map_err(|_| HostIoError::InvalidPath(output_dir.to_owned()))?;
        validate_relative(output_name)?;
        if output_name.components().count() != 1 || output_name == host.staging_name() {
            return Err(HostIoError::InvalidPath(output_dir.to_owned()));
        }
        Ok(output_name.to_owned())
    }

    fn anchor_directories(
        host: &RestrictedHost,
        output_name: &Path,
        output_dir: &Path,
    ) -> Result<(DirectoryRoot, DirectoryRoot), HostIoError> {
        let parent = DirectoryRoot::open(host.staging_parent_path())?;
        if !parent.is_private()? {
            return Err(HostIoError::Permission {
                operation: "initialize publisher",
                path: host.staging_parent_path().to_owned(),
                reason: "publication parent must be private to its owner",
            });
        }
        if parent.child_exists(output_name)? {
            return Err(HostIoError::Permission {
                operation: "initialize publisher",
                path: output_dir.to_owned(),
                reason: "publication destination already exists",
            });
        }
        let staging = host.staging.duplicate().map_err(|source| HostIoError::Io {
            operation: "duplicate private staging descriptor",
            path: host.staging_name().to_owned(),
            source,
        })?;
        if !parent.is_child(host.staging_name(), &staging)? {
            return Err(HostIoError::Permission {
                operation: "initialize publisher",
                path: host.staging_name().to_owned(),
                reason: "private staging directory identity changed",
            });
        }
        Ok((parent, staging))
    }

    pub fn matches_lifecycle(&self, lifecycle: &BuildLifecycle) -> bool {
        self.lifecycle.shares_build(lifecycle)
    }

    pub fn validates_output_dir(&self, output_dir: &Path) -> bool {
        self.output_dir == output_dir
    }

    /// Write an immutable report only after all registered work drains and VM access is revoked.
    pub fn write_report(&mut self, bytes: &[u8]) -> Result<(), HostIoError> {
        self.check_closed("write frozen report").map_err(|error| self.revoke(error))?;
        if self.is_prepared || bytes.len() > MAX_FILE_BYTES {
            return Err(self.revoke(HostIoError::Permission {
                operation: "write frozen report",
                path: PathBuf::from(REPORT_FILE),
                reason: "report already prepared or exceeds fixed output bound",
            }));
        }
        self.write_report_file(bytes).map_err(|error| self.revoke(error))?;
        self.is_prepared = true;
        Ok(())
    }

    fn write_report_file(&self, bytes: &[u8]) -> Result<(), HostIoError> {
        let report = Path::new(REPORT_FILE);
        let mut file =
            self.staging.create_file(report, &mut || self.check_closed("write frozen report"))?;
        for chunk in bytes.chunks(REPORT_CHUNK_BYTES) {
            self.check_closed("write frozen report")?;
            file.write_all(chunk).map_err(|source| HostIoError::Io {
                operation: "write frozen report",
                path: report.to_owned(),
                source,
            })?;
        }
        file.sync_all().map_err(|source| HostIoError::Io {
            operation: "sync frozen report",
            path: report.to_owned(),
            source,
        })?;
        self.check_closed("write frozen report")
    }

    fn revoke(&self, error: HostIoError) -> HostIoError {
        // The original typed I/O failure remains primary; cancellation can lose a race
        // only after another actor has already stopped this build.
        if let Err(source) = self.lifecycle.cancel(error.to_string()) {
            tracing::error!(kind = ?source.kind, "failed to record publication failure");
        }
        error
    }

    /// Consumes the publisher; cancellation and the no-replace rename share one lifecycle lock.
    pub fn commit(self) -> Result<(), LifecycleError> {
        self.lifecycle.commit_publication(&self)
    }

    pub(super) fn rename_for_commit(&self) -> io::Result<()> {
        if !self.is_prepared {
            return Err(io::Error::new(io::ErrorKind::InvalidInput, "report not prepared"));
        }
        if !self.parent.is_child(&self.staging_name, &self.staging).map_err(io::Error::other)? {
            return Err(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "private staging identity changed",
            ));
        }
        self.parent.rename_child_noreplace(&self.staging_name, &self.output_name)
    }

    fn check_closed(&self, operation: &'static str) -> Result<(), HostIoError> {
        let phase = self
            .lifecycle
            .phase()
            .map_err(|source| HostIoError::Lifecycle { operation, source })?;
        let pending = self
            .lifecycle
            .pending_counts()
            .map_err(|source| HostIoError::Lifecycle { operation, source })?;
        if phase == RuntimePhase::Closed && pending.total() == 0 {
            return Ok(());
        }
        Err(HostIoError::Permission {
            operation,
            path: self.output_dir.clone(),
            reason: "build not closed with zero pending work",
        })
    }
}
