//! Linux directory-descriptor traversal; never follow an input-supplied symlink.
use std::ffi::{CString, OsStr, OsString};
use std::fs::{DirBuilder, File, OpenOptions};
use std::io;
use std::os::fd::AsRawFd;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Component, Path, PathBuf};

use super::files::HostIoError;

// Linux UAPI flags; all OS interaction remains in safe std::fs APIs.
const O_NOFOLLOW: i32 = 0o400000;
const O_DIRECTORY: i32 = 0o200000;
const O_NONBLOCK: i32 = 0o4000;
const PRIVATE_DIRECTORY_MODE: u32 = 0o700;
const PRIVATE_FILE_MODE: u32 = 0o600;
// Linux PATH_MAX includes the terminator; NAME_MAX bounds one directory entry.
// Limiting depth also bounds descriptor opens and authorization checks per request.
// Revocation is checked before each syscall, not atomically with it: one racing
// mkdir/open may finish, but a later directory or leaf cannot pass the next check.
pub(super) const MAX_RELATIVE_PATH_BYTES: usize = 4095;
pub(super) const MAX_COMPONENT_BYTES: usize = 255;
pub(super) const MAX_PATH_COMPONENTS: usize = 64;
const RENAME_NOREPLACE: u32 = 1;

unsafe extern "C" {
    fn renameat2(
        old_directory: i32,
        old_name: *const i8,
        new_directory: i32,
        new_name: *const i8,
        flags: u32,
    ) -> i32;
}

pub(super) struct DirectoryRoot {
    directory: File,
}

pub(super) fn validate_relative(path: &Path) -> Result<(), HostIoError> {
    let text = path.to_str().ok_or_else(|| HostIoError::InvalidPath(path.to_owned()))?;
    if text.len() > MAX_RELATIVE_PATH_BYTES {
        return Err(HostIoError::PathLimit {
            path: path.to_owned(),
            constraint: "relative path bytes",
            limit: MAX_RELATIVE_PATH_BYTES,
        });
    }
    if text.is_empty()
        || text.contains('\0')
        || text.split('/').any(|part| matches!(part, "" | "." | ".."))
        || path.components().any(|part| !matches!(part, Component::Normal(_)))
    {
        return Err(HostIoError::InvalidPath(path.to_owned()));
    }
    let mut count = 0;
    for component in text.split('/') {
        if component.len() > MAX_COMPONENT_BYTES {
            return Err(HostIoError::PathLimit {
                path: path.to_owned(),
                constraint: "component bytes",
                limit: MAX_COMPONENT_BYTES,
            });
        }
        count += 1;
        if count > MAX_PATH_COMPONENTS {
            return Err(HostIoError::PathLimit {
                path: path.to_owned(),
                constraint: "path components",
                limit: MAX_PATH_COMPONENTS,
            });
        }
    }
    Ok(())
}

fn descriptor_path(directory: &File, name: &OsStr) -> PathBuf {
    PathBuf::from(format!("/proc/self/fd/{}", directory.as_raw_fd())).join(name)
}

fn open_directory(path: &Path) -> Result<File, HostIoError> {
    OpenOptions::new()
        .read(true)
        .custom_flags(O_DIRECTORY | O_NOFOLLOW | O_NONBLOCK)
        .open(path)
        .map_err(|source| HostIoError::Io {
            operation: "open directory",
            path: path.to_owned(),
            source,
        })
}

impl DirectoryRoot {
    pub(super) fn open(path: &Path) -> Result<Self, HostIoError> {
        if !path.is_absolute() {
            return Err(HostIoError::InvalidPath(path.to_owned()));
        }
        let mut directory = open_directory(Path::new("/"))?;
        for component in path.components() {
            if let Component::Normal(name) = component {
                directory = Self::open_child_directory(&directory, name, false)?;
            } else if component != Component::RootDir {
                return Err(HostIoError::InvalidPath(path.to_owned()));
            }
        }
        Ok(Self { directory })
    }
    pub(super) fn duplicate(&self) -> io::Result<Self> {
        Ok(Self { directory: self.directory.try_clone()? })
    }
    pub(super) fn is_private(&self) -> Result<bool, HostIoError> {
        let metadata = self.directory.metadata().map_err(|source| HostIoError::Io {
            operation: "inspect publication parent",
            path: PathBuf::from("staging parent"),
            source,
        })?;
        Ok(metadata.permissions().mode() & 0o077 == 0)
    }
    pub(super) fn child_exists(&self, name: &Path) -> Result<bool, HostIoError> {
        validate_relative(name)?;
        if name.components().count() != 1 {
            return Err(HostIoError::InvalidPath(name.to_owned()));
        }
        match std::fs::symlink_metadata(descriptor_path(&self.directory, name.as_os_str())) {
            Ok(_) => Ok(true),
            Err(source) if source.kind() == io::ErrorKind::NotFound => Ok(false),
            Err(source) => Err(HostIoError::Io {
                operation: "inspect publication destination",
                path: name.to_owned(),
                source,
            }),
        }
    }

    pub(super) fn is_child(&self, name: &Path, child: &Self) -> Result<bool, HostIoError> {
        validate_relative(name)?;
        if name.components().count() != 1 {
            return Err(HostIoError::InvalidPath(name.to_owned()));
        }
        let opened = Self::open_child_directory(&self.directory, name.as_os_str(), false)?;
        let actual = opened.metadata().map_err(|source| HostIoError::Io {
            operation: "inspect staging identity",
            path: name.to_owned(),
            source,
        })?;
        let expected = child.directory.metadata().map_err(|source| HostIoError::Io {
            operation: "inspect staging identity",
            path: name.to_owned(),
            source,
        })?;
        Ok(actual.dev() == expected.dev() && actual.ino() == expected.ino())
    }

    pub(super) fn rename_child_noreplace(&self, old: &Path, new: &Path) -> io::Result<()> {
        if old.components().count() != 1 || new.components().count() != 1 {
            return Err(io::Error::from(io::ErrorKind::InvalidInput));
        }
        validate_relative(old).map_err(io::Error::other)?;
        validate_relative(new).map_err(io::Error::other)?;
        let old = CString::new(old.as_os_str().as_bytes())
            .map_err(|_| io::Error::from(io::ErrorKind::InvalidInput))?;
        let new = CString::new(new.as_os_str().as_bytes())
            .map_err(|_| io::Error::from(io::ErrorKind::InvalidInput))?;
        // SAFETY: both validated names are NUL-terminated, the owned parent fd stays live,
        // and Linux RENAME_NOREPLACE atomically refuses an existing file, symlink, or directory.
        let status = unsafe {
            renameat2(
                self.directory.as_raw_fd(),
                old.as_ptr(),
                self.directory.as_raw_fd(),
                new.as_ptr(),
                RENAME_NOREPLACE,
            )
        };
        if status == 0 { Ok(()) } else { Err(io::Error::last_os_error()) }
    }

    pub(super) fn create_staging(
        parent: &Path,
        name: &Path,
        authorize: &mut impl FnMut() -> Result<(), HostIoError>,
    ) -> Result<Self, HostIoError> {
        validate_relative(name)?;
        let parent = Self::open(parent)?;
        let (directory, leaf) = parent.resolve_parent(name, true, authorize)?;
        authorize()?;
        let path = descriptor_path(&directory, &leaf);
        DirBuilder::new().mode(PRIVATE_DIRECTORY_MODE).create(&path).map_err(|source| {
            HostIoError::Io {
                operation: "create private staging root",
                path: name.to_owned(),
                source,
            }
        })?;
        let root = Self { directory: open_directory(&path)? };
        let metadata = root.directory.metadata().map_err(|source| HostIoError::Io {
            operation: "inspect staging root",
            path: name.to_owned(),
            source,
        })?;
        if metadata.permissions().mode() & 0o077 != 0
            || metadata.uid()
                != parent
                    .directory
                    .metadata()
                    .map_err(|source| HostIoError::Io {
                        operation: "inspect staging parent",
                        path: name.to_owned(),
                        source,
                    })?
                    .uid()
        {
            return Err(HostIoError::Permission {
                operation: "create staging root",
                path: name.to_owned(),
                reason: "staging root is not private to the staging parent owner",
            });
        }
        Ok(root)
    }

    fn resolve_parent(
        &self,
        path: &Path,
        may_create: bool,
        authorize: &mut impl FnMut() -> Result<(), HostIoError>,
    ) -> Result<(File, OsString), HostIoError> {
        validate_relative(path)?;
        let mut components = path.iter().peekable();
        let mut directory = self.directory.try_clone().map_err(|source| HostIoError::Io {
            operation: "duplicate root descriptor",
            path: path.to_owned(),
            source,
        })?;
        while let Some(component) = components.next() {
            if components.peek().is_none() {
                return Ok((directory, component.to_owned()));
            }
            authorize()?;
            directory = Self::open_child_directory(&directory, component, may_create)?;
        }
        Err(HostIoError::InvalidPath(path.to_owned()))
    }

    fn open_child_directory(
        parent: &File,
        name: &OsStr,
        may_create: bool,
    ) -> Result<File, HostIoError> {
        let path = descriptor_path(parent, name);
        if may_create {
            match DirBuilder::new().mode(PRIVATE_DIRECTORY_MODE).create(&path) {
                Ok(()) => {},
                Err(source) if source.kind() == std::io::ErrorKind::AlreadyExists => {
                    // Existence is not authorization: the no-follow directory open below must succeed.
                },
                Err(source) => {
                    return Err(HostIoError::Io { operation: "create directory", path, source });
                },
            }
        }
        match open_directory(&path) {
            Err(HostIoError::Io { operation, path, source })
                if source.kind() == io::ErrorKind::NotADirectory =>
            {
                let metadata = std::fs::symlink_metadata(&path);
                match metadata {
                    Ok(metadata) if metadata.file_type().is_symlink() => {
                        Err(HostIoError::Permission {
                            operation,
                            path,
                            reason: "directory component is a symlink",
                        })
                    },
                    Ok(metadata) if metadata.is_file() => {
                        Err(HostIoError::OrdinaryIo { operation, path, source })
                    },
                    _ => Err(HostIoError::Io { operation, path, source }),
                }
            },
            result => result,
        }
    }

    pub(super) fn open_file(
        &self,
        path: &Path,
        authorize: &mut impl FnMut() -> Result<(), HostIoError>,
    ) -> Result<File, HostIoError> {
        let (directory, name) = self.resolve_parent(path, false, authorize)?;
        authorize()?;
        let file = OpenOptions::new()
            .read(true)
            .custom_flags(O_NOFOLLOW | O_NONBLOCK)
            .open(descriptor_path(&directory, &name))
            .map_err(|source| HostIoError::Io {
                operation: "open source",
                path: path.to_owned(),
                source,
            })?;
        let metadata = file.metadata().map_err(|source| HostIoError::Io {
            operation: "inspect source",
            path: path.to_owned(),
            source,
        })?;
        if !metadata.is_file() {
            return Err(HostIoError::Permission {
                operation: "read source",
                path: path.to_owned(),
                reason: "not a regular file",
            });
        }
        Ok(file)
    }

    pub(super) fn create_file(
        &self,
        path: &Path,
        authorize: &mut impl FnMut() -> Result<(), HostIoError>,
    ) -> Result<File, HostIoError> {
        let (directory, name) = self.resolve_parent(path, true, authorize)?;
        authorize()?;
        OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(PRIVATE_FILE_MODE)
            .custom_flags(O_NOFOLLOW)
            .open(descriptor_path(&directory, &name))
            .map_err(|source| HostIoError::Io {
                operation: "create output",
                path: path.to_owned(),
                source,
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ml::host::lifecycle::{BuildLifecycle, RuntimePhase, WorkKind};
    use crate::ml::{DenyHost, Vm};
    use std::error::Error;
    use std::fs;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT_ROOT: AtomicU64 = AtomicU64::new(0);

    #[test]
    fn create_file_revoked_during_parent_walk_stops_before_next_directory() {
        let base = std::env::temp_dir().join(format!(
            "native-fs-revoke-{}-{}",
            std::process::id(),
            NEXT_ROOT.fetch_add(1, Ordering::Relaxed),
        ));
        fs::create_dir(&base).unwrap();
        let root = DirectoryRoot::open(&base).unwrap();
        let vm = Vm::new(DenyHost);
        let lifecycle = BuildLifecycle::new(vm.stop_handle());
        let lease = lifecycle.start_root(WorkKind::Evaluation, "directory traversal").unwrap();
        let mut checks = 0;
        let error = root
            .create_file(Path::new("first/second/output"), &mut || {
                checks += 1;
                if checks == 2 {
                    lifecycle.cancel("cancel while traversing".to_owned()).unwrap();
                }
                lifecycle
                    .check_task(&lease)
                    .map_err(|source| HostIoError::Lifecycle { operation: "write staging", source })
            })
            .unwrap_err();
        assert!(matches!(error, HostIoError::Lifecycle { .. }));
        assert!(error.source().is_some());
        assert_eq!(checks, 2);
        assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
        assert!(base.join("first").is_dir());
        assert!(!base.join("first/second").exists());
        fs::remove_dir_all(&base).unwrap();
    }

    #[test]
    fn create_file_revoked_before_leaf_open_does_not_create_file() {
        let base = std::env::temp_dir().join(format!(
            "native-fs-revoke-{}-{}",
            std::process::id(),
            NEXT_ROOT.fetch_add(1, Ordering::Relaxed),
        ));
        fs::create_dir(&base).unwrap();
        let root = DirectoryRoot::open(&base).unwrap();
        let vm = Vm::new(DenyHost);
        let lifecycle = BuildLifecycle::new(vm.stop_handle());
        let lease = lifecycle.start_root(WorkKind::Evaluation, "leaf creation").unwrap();
        let mut checks = 0;
        let error = root
            .create_file(Path::new("first/output"), &mut || {
                checks += 1;
                if checks == 2 {
                    lifecycle.cancel("cancel before leaf".to_owned()).unwrap();
                }
                lifecycle
                    .check_task(&lease)
                    .map_err(|source| HostIoError::Lifecycle { operation: "write staging", source })
            })
            .unwrap_err();
        assert!(matches!(error, HostIoError::Lifecycle { .. }));
        assert_eq!(checks, 2);
        assert!(base.join("first").is_dir());
        assert!(!base.join("first/output").exists());
        fs::remove_dir_all(&base).unwrap();
    }
}
