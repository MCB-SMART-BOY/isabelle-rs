use std::fs;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Output};

use flate2::{Compression, write::ZlibEncoder};
use sha1::{Digest, Sha1};

// Construct isolated Git evidence without staging or committing the user's checkout.
fn write_git_object(root: &Path, kind: &str, body: &[u8]) -> [u8; 20] {
    let mut bytes = format!("{kind} {}\0", body.len()).into_bytes();
    bytes.extend_from_slice(body);
    let digest = Sha1::digest(&bytes);
    let hex = format!("{digest:x}");
    let directory = root.join(".git/objects").join(&hex[..2]);
    fs::create_dir_all(&directory).unwrap();
    let mut encoder = ZlibEncoder::new(Vec::new(), Compression::default());
    encoder.write_all(&bytes).unwrap();
    fs::write(directory.join(&hex[2..]), encoder.finish().unwrap()).unwrap();
    digest.into()
}

fn create_deleted_sources(count: usize) -> tempfile::TempDir {
    let root = tempfile::Builder::new().prefix("xtask hook 'quoted' ").tempdir().unwrap();
    fs::create_dir_all(root.path().join(".git/refs")).unwrap();
    let blob = write_git_object(root.path(), "blob", b"source\n");
    let mut names: Vec<_> = (0..count).map(|index| format!("file-{index:02}.rs")).collect();
    if let Some(name) = names.first_mut() {
        *name = "line\nbreak 'quoted' $(literal).rs".into();
    }
    names.sort_unstable();
    let mut sources = Vec::new();
    for name in names {
        sources.extend_from_slice(format!("100644 {name}\0").as_bytes());
        sources.extend_from_slice(&blob);
    }
    let source_tree = write_git_object(root.path(), "tree", &sources);
    let mut tree = b"40000 src\0".to_vec();
    tree.extend_from_slice(&source_tree);
    let tree = write_git_object(root.path(), "tree", &tree);
    let tree_hex = tree.iter().map(|byte| format!("{byte:02x}")).collect::<String>();
    let commit = format!(
        "tree {tree_hex}\nauthor Fixture <fixture@example.invalid> 0 +0000\ncommitter Fixture <fixture@example.invalid> 0 +0000\n\nFixture\n"
    );
    let commit = write_git_object(root.path(), "commit", commit.as_bytes());
    let commit_hex = commit.iter().map(|byte| format!("{byte:02x}")).collect::<String>();
    fs::write(root.path().join(".git/HEAD"), format!("{commit_hex}\n")).unwrap();
    root
}

fn run_hook(directory: &Path, event: &str, path: Option<&str>) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_xtask"));
    command.current_dir(directory).args(["hook", event]);
    command.env_remove("GIT_DIR").env_remove("GIT_WORK_TREE");
    command.env_remove("CLAUDE_TOOL_FILE_PATH");
    if let Some(path) = path {
        command.env("CLAUDE_TOOL_FILE_PATH", path);
    }
    command.output().unwrap()
}

#[test]
fn hook_pre_edit_special_characters_are_literal() {
    let root = tempfile::tempdir().unwrap();
    let path = "src/has space 'quote' $(touch injected).rs";
    let output = run_hook(root.path(), "pre-edit", Some(path));
    assert!(output.status.success(), "{output:?}");
    assert_eq!(String::from_utf8(output.stdout).unwrap(), format!("Editing file: {path}\n"));
    assert!(!root.path().join("injected").exists());
}

#[test]
fn hook_post_edit_unrelated_or_missing_path_skips_git() {
    let root = tempfile::tempdir().unwrap();
    for path in [None, Some("README.md"), Some("src-other/file.rs"), Some("/src/file.rs")] {
        let output = run_hook(root.path(), "post-edit", path);
        assert!(output.status.success(), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
    }
}

#[test]
fn hook_post_edit_at_threshold_is_quiet() {
    for count in [0, 10] {
        let root = create_deleted_sources(count);
        let output = run_hook(root.path(), "post-edit", Some("src/edited.rs"));
        assert!(output.status.success(), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
    }
}

#[test]
fn hook_post_edit_over_threshold_counts_paths_not_lines() {
    let root = create_deleted_sources(11);
    let output = run_hook(root.path(), "post-edit", Some("src/edited $(touch injected).rs"));
    assert!(output.status.success(), "{output:?}");
    let message = String::from_utf8(output.stdout).unwrap();
    assert!(message.contains("[doc-sync] 11 src files changed."), "{message}");
    assert!(message.contains("/sync-docs"), "{message}");
    assert!(!root.path().join("injected").exists());
}

#[test]
fn hook_post_edit_git_failure_is_reported() {
    let root = tempfile::tempdir().unwrap();
    let output = run_hook(root.path(), "post-edit", Some("src/edited.rs"));
    assert!(!output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(String::from_utf8(output.stderr).unwrap().contains("count changed src files"));
}
