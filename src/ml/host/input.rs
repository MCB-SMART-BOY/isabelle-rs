//! Supervisor-only input reads; never registered as an ML capability.
//! A live build lease controls cancellation, not ML access to these paths.
use std::io::Read;
use std::path::Path;

use super::anchored_fs::DirectoryRoot;
use super::files::HostIoError;
use super::lifecycle::{BuildLifecycle, TaskLease};

const READ_CHUNK_BYTES: usize = 8192;

/// Read a regular file through anchored directories, rejecting symlinks and excess bytes.
pub(crate) fn read_supervisor_input(
    lifecycle: &BuildLifecycle,
    lease: &TaskLease,
    path: &Path,
    limit: usize,
) -> Result<Vec<u8>, HostIoError> {
    let mut authorize = || {
        lifecycle
            .check_task(lease)
            .map_err(|source| HostIoError::Lifecycle { operation: "read supervisor input", source })
    };
    authorize()?;
    if !path.is_absolute() {
        return Err(HostIoError::InvalidPath(path.to_owned()));
    }
    let parent = path.parent().ok_or_else(|| HostIoError::InvalidPath(path.to_owned()))?;
    let name = path.file_name().ok_or_else(|| HostIoError::InvalidPath(path.to_owned()))?;
    let directory = DirectoryRoot::open(parent)?;
    let mut file = directory.open_file(Path::new(name), &mut authorize)?;
    let metadata = file.metadata().map_err(|source| HostIoError::Io {
        operation: "inspect supervisor input",
        path: path.to_owned(),
        source,
    })?;
    if metadata.len() > limit as u64 {
        return Err(HostIoError::TooLarge {
            operation: "read supervisor input",
            path: path.to_owned(),
            limit,
        });
    }
    let mut content = Vec::new();
    let mut chunk = [0; READ_CHUNK_BYTES];
    loop {
        authorize()?;
        let count = file.read(&mut chunk).map_err(|source| HostIoError::Io {
            operation: "read supervisor input",
            path: path.to_owned(),
            source,
        })?;
        if count == 0 {
            authorize()?;
            return Ok(content);
        }
        if count > limit - content.len() {
            return Err(HostIoError::TooLarge {
                operation: "read supervisor input",
                path: path.to_owned(),
                limit,
            });
        }
        content.extend_from_slice(&chunk[..count]);
    }
}
