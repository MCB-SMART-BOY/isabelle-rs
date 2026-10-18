use std::fs;
use std::path::Path;

use tar::{Builder, EntryType, Header};

use super::{inspect, verify_existing_tree, verify_tree};

fn add_member(
    archive: &mut Builder<fs::File>,
    path: &str,
    kind: EntryType,
    target: Option<&str>,
    data: &[u8],
) {
    let mut header = Header::new_gnu();
    header.set_entry_type(kind);
    header.set_size(data.len() as u64);
    header.set_mode(0o600);
    header.set_path(path).unwrap();
    if let Some(link) = target {
        header.set_link_name(link).unwrap();
    }
    header.set_cksum();
    archive.append(&header, data).unwrap();
}

fn create_tar(path: &Path, members: &[(&str, EntryType, Option<&str>, &[u8])]) {
    let mut archive = Builder::new(fs::File::create(path).unwrap());
    for (name, kind, target, data) in members {
        add_member(&mut archive, name, *kind, *target, data);
    }
    archive.finish().unwrap();
}

#[test]
fn inspect_duplicate_member_rejects_archive() {
    let temp = tempfile::tempdir().unwrap();
    let archive = temp.path().join("duplicate.tar");
    create_tar(
        &archive,
        &[("safe", EntryType::Regular, None, b"ok"), ("safe", EntryType::Regular, None, b"evil")],
    );
    assert!(inspect(&archive, false, "").is_err());
}

#[test]
fn inspect_parent_traversal_rejects_archive_before_extraction() {
    let temp = tempfile::tempdir().unwrap();
    let archive = temp.path().join("traversal.tar");
    let mut output = Builder::new(fs::File::create(&archive).unwrap());
    let mut header = Header::new_gnu();
    header.set_size(1);
    header.set_mode(0o600);
    header.as_mut_bytes()[..10].copy_from_slice(b"../outside");
    header.set_cksum();
    output.append(&header, b"x" as &[u8]).unwrap();
    output.finish().unwrap();
    let destination = temp.path().join("fixed-source");
    assert!(verify_tree(&archive, &destination, false, "", &[]).is_err());
    assert!(!temp.path().join("outside").exists());
    assert!(!destination.exists());
}

#[test]
fn inspect_link_escape_rejects_archive_before_extraction() {
    let temp = tempfile::tempdir().unwrap();
    let archive = temp.path().join("escape.tar");
    create_tar(
        &archive,
        &[("Isabelle2025/escape", EntryType::Symlink, Some("../../outside"), b"")],
    );
    let destination = temp.path().join("distribution");
    assert!(verify_tree(&archive, &destination, false, "Isabelle2025", &[]).is_err());
    assert!(!destination.exists());
}

#[test]
fn inspect_symlink_ancestor_rejects_archive() {
    let temp = tempfile::tempdir().unwrap();
    let archive = temp.path().join("ancestor.tar");
    create_tar(
        &archive,
        &[
            ("parent", EntryType::Symlink, Some("target"), b""),
            ("parent/file", EntryType::Regular, None, b"escape"),
        ],
    );
    assert!(inspect(&archive, false, "").is_err());
}

#[test]
fn verify_tree_mutated_file_rejects_cached_extraction() {
    let temp = tempfile::tempdir().unwrap();
    let archive = temp.path().join("fixed.tar");
    create_tar(&archive, &[("file", EntryType::Regular, None, b"original")]);
    let directory = temp.path().join("fixed-source");
    verify_tree(&archive, &directory, false, "", &[]).unwrap();
    fs::write(directory.join("file"), b"tampered").unwrap();
    assert!(verify_tree(&archive, &directory, false, "", &[]).is_err());
}

#[test]
fn verify_tree_unexpected_member_rejects_cached_extraction() {
    let temp = tempfile::tempdir().unwrap();
    let archive = temp.path().join("fixed.tar");
    create_tar(&archive, &[("file", EntryType::Regular, None, b"original")]);
    let directory = temp.path().join("fixed-source");
    verify_tree(&archive, &directory, false, "", &[]).unwrap();
    fs::write(directory.join("unexpected"), b"injected").unwrap();
    assert!(verify_tree(&archive, &directory, false, "", &[]).is_err());
}

#[test]
fn verify_existing_tree_missing_root_rejects_without_repair() {
    let temp = tempfile::tempdir().unwrap();
    let archive = temp.path().join("fixed.tar");
    create_tar(&archive, &[("file", EntryType::Regular, None, b"original")]);
    let missing = temp.path().join("fixed-source");
    assert!(verify_existing_tree(&archive, &missing, false, "", &[]).is_err());
    assert!(!missing.exists());
}

#[test]
fn verify_tree_global_comment_extracts_only_files_and_reuses_manifest() {
    let temp = tempfile::tempdir().unwrap();
    let archive = temp.path().join("git.tar");
    create_tar(
        &archive,
        &[
            ("pax_global_header", EntryType::XGlobalHeader, None, b"18 comment=source\n"),
            ("source", EntryType::Regular, None, b"theory"),
        ],
    );
    let destination = temp.path().join("fixed-source");
    let (count, manifest) = verify_tree(&archive, &destination, false, "", &[]).unwrap();
    assert_eq!(count, 1);
    assert_eq!(fs::read(destination.join("source")).unwrap(), b"theory");
    assert!(!destination.join("pax_global_header").exists());
    assert_eq!(
        verify_existing_tree(&archive, &destination, false, "", &[]).unwrap(),
        (count, manifest),
    );
}

#[test]
fn verify_tree_unsupported_global_overrides_reject_before_extraction() {
    let temp = tempfile::tempdir().unwrap();
    let archive = temp.path().join("override.tar");
    create_tar(
        &archive,
        &[
            ("pax_global_header", EntryType::XGlobalHeader, None, b"19 path=../outside\n"),
            ("source", EntryType::Regular, None, b"theory"),
        ],
    );
    let destination = temp.path().join("fixed-source");
    let error = verify_tree(&archive, &destination, false, "", &[]).unwrap_err();
    assert!(error.to_string().contains("unsupported global attribute"), "{error}");
    assert!(!destination.exists());
    assert!(!temp.path().join("outside").exists());
}
