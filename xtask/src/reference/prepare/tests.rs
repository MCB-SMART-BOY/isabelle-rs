#![cfg(unix)]

use std::fs;
use std::os::unix::fs::{PermissionsExt, symlink};

use super::{require_empty_directory, require_external_workspace, retrieve_archive};

#[test]
fn require_external_workspace_inside_repository_rejects() {
    let root = tempfile::tempdir().unwrap();
    let repository = root.path().join("checkout");
    fs::create_dir(&repository).unwrap();
    assert!(require_external_workspace(&repository.join("private/work"), &repository).is_err());
}

#[test]
fn require_external_workspace_symlink_rejects() {
    let root = tempfile::tempdir().unwrap();
    let repository = root.path().join("checkout");
    let outside = root.path().join("outside");
    fs::create_dir(&repository).unwrap();
    fs::create_dir(&outside).unwrap();
    let link = root.path().join("link");
    symlink(&outside, &link).unwrap();
    assert!(require_external_workspace(&link, &repository).is_err());
}

#[test]
fn require_external_workspace_shared_writable_rejects() {
    let root = tempfile::tempdir().unwrap();
    let repository = root.path().join("checkout");
    let workspace = root.path().join("workspace");
    fs::create_dir(&repository).unwrap();
    fs::create_dir(&workspace).unwrap();
    fs::set_permissions(&workspace, fs::Permissions::from_mode(0o777)).unwrap();
    assert!(require_external_workspace(&workspace, &repository).is_err());
}

#[test]
fn require_empty_directory_entry_rejects() {
    let root = tempfile::tempdir().unwrap();
    fs::write(root.path().join("injected"), b"payload").unwrap();
    assert!(require_empty_directory(root.path(), "verify empty heap root").is_err());
}

#[test]
fn retrieve_archive_orphaned_marker_rejects_before_network() {
    let root = tempfile::tempdir().unwrap();
    fs::write(root.path().join("download-state.json"), b"{}").unwrap();
    assert!(retrieve_archive(root.path()).is_err());
    assert!(!root.path().join(super::ARCHIVE_NAME).exists());
}
