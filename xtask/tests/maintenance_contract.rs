use std::fs::{self, File};
use std::io::Read;
use std::path::Path;
use std::process::Command;

const EXPECTED_ARCHIVE_ENTRIES: usize = 5;

fn create_artifacts(root: &Path) {
    for platform in ["linux", "macos", "windows"] {
        let directory = root.join(format!("isabelle-rs-{platform}-x86_64"));
        fs::create_dir(&directory).unwrap();
        for name in ["isabelle-rs", "isabelle-build"] {
            let name = if platform == "windows" { format!("{name}.exe") } else { name.into() };
            fs::write(directory.join(&name), format!("{platform}:{name}")).unwrap();
        }
    }
}

fn package(root: &Path) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_xtask"))
        .arg("package")
        .arg("--artifacts")
        .arg(root)
        .output()
        .unwrap()
}

fn read_tar_entries(path: &Path) -> Vec<(std::path::PathBuf, String, u32)> {
    let file = File::open(path).unwrap();
    let mut archive = tar::Archive::new(flate2::read::GzDecoder::new(file));
    archive
        .entries()
        .unwrap()
        .map(|entry| {
            let mut entry = entry.unwrap();
            let mut body = String::new();
            entry.read_to_string(&mut body).unwrap();
            (entry.path().unwrap().into_owned(), body, entry.header().mode().unwrap())
        })
        .collect()
}

fn read_expected_notice(name: &str) -> Vec<u8> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join(name);
    fs::read(path).unwrap()
}

fn check_tar_contents(root: &Path, platform: &str) {
    let folder = format!("isabelle-rs-{platform}-x86_64");
    let entries = read_tar_entries(&root.join(format!("{folder}.tar.gz")));
    assert_eq!(entries.len(), EXPECTED_ARCHIVE_ENTRIES);
    for name in ["isabelle-rs", "isabelle-build"] {
        let path = std::path::PathBuf::from(format!("{folder}/{name}"));
        let entry = entries.iter().find(|entry| entry.0 == path).unwrap();
        assert_eq!(entry.1, format!("{platform}:{name}"));
        assert_eq!(entry.2, 0o755);
    }
    for name in ["LICENSE", "NOTICE", "THIRD_PARTY_LICENSES"] {
        let path = std::path::PathBuf::from(format!("{folder}/{name}"));
        let entry = entries.iter().find(|entry| entry.0 == path).unwrap();
        assert_eq!(entry.2, 0o644, "{name} must not be executable");
        assert_eq!(entry.1.as_bytes(), read_expected_notice(name), "{name} must be complete");
    }
}

fn check_zip_contents(root: &Path) {
    let file = File::open(root.join("isabelle-rs-windows-x86_64.zip")).unwrap();
    let mut archive = zip::ZipArchive::new(file).unwrap();
    assert_eq!(archive.len(), EXPECTED_ARCHIVE_ENTRIES);
    for name in ["isabelle-rs", "isabelle-build"] {
        let mut entry = archive.by_name(&format!("isabelle-rs-windows-x86_64/{name}.exe")).unwrap();
        let mut body = String::new();
        entry.read_to_string(&mut body).unwrap();
        assert_eq!(body, format!("windows:{name}.exe"));
        assert_eq!(entry.unix_mode().unwrap() & 0o777, 0o755);
    }
    for name in ["LICENSE", "NOTICE", "THIRD_PARTY_LICENSES"] {
        let mut entry = archive.by_name(&format!("isabelle-rs-windows-x86_64/{name}")).unwrap();
        assert_eq!(entry.unix_mode().unwrap() & 0o777, 0o644, "{name} must not be executable");
        let mut body = Vec::new();
        entry.read_to_end(&mut body).unwrap();
        assert_eq!(body, read_expected_notice(name), "{name} must be complete");
    }
}

#[test]
fn package_complete_artifacts_preserve_binaries_and_include_nonexecutable_notices() {
    let directory = tempfile::tempdir().unwrap();
    create_artifacts(directory.path());
    let result = package(directory.path());
    assert!(result.status.success(), "{result:?}");
    for platform in ["linux", "macos"] {
        check_tar_contents(directory.path(), platform);
    }
    check_zip_contents(directory.path());
}

#[test]
fn package_existing_output_preserves_previous_archives() {
    let directory = tempfile::tempdir().unwrap();
    create_artifacts(directory.path());
    let existing = directory.path().join("isabelle-rs-windows-x86_64.zip");
    fs::write(&existing, b"preserve this artifact").unwrap();
    assert!(!package(directory.path()).status.success());
    assert_eq!(fs::read(existing).unwrap(), b"preserve this artifact");
    assert!(!directory.path().join("isabelle-rs-linux-x86_64.tar.gz").exists());
}

#[test]
fn package_missing_binary_does_not_publish_partial_archives() {
    let directory = tempfile::tempdir().unwrap();
    create_artifacts(directory.path());
    fs::remove_file(directory.path().join("isabelle-rs-windows-x86_64/isabelle-build.exe"))
        .unwrap();
    assert!(!package(directory.path()).status.success());
    assert!(!directory.path().join("isabelle-rs-linux-x86_64.tar.gz").exists());
}

#[cfg(unix)]
#[test]
fn package_symbolic_input_rejects() {
    let directory = tempfile::tempdir().unwrap();
    create_artifacts(directory.path());
    let binary = directory.path().join("isabelle-rs-linux-x86_64/isabelle-rs");
    fs::remove_file(&binary).unwrap();
    std::os::unix::fs::symlink("isabelle-build", binary).unwrap();
    assert!(!package(directory.path()).status.success());
    assert!(!directory.path().join("isabelle-rs-linux-x86_64.tar.gz").exists());
}

fn create_checkout(root: &Path) {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[workspace]\n[package]\nname = \"isabelle-rs\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(
        root.join("Cargo.lock"),
        "version = 4\n[[package]]\nname = \"isabelle-rs\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    fs::write(root.join("src/main.rs"), "fn main() {}\n").unwrap();
}

#[test]
fn install_check_relative_parent_path_builds_existing_checkout() {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path().join("checkout");
    create_checkout(&root);
    let result = Command::new(env!("CARGO_BIN_EXE_xtask"))
        .current_dir(root.join("src"))
        .args(["install", "--check", "--dir", ".."])
        .output()
        .unwrap();
    assert!(result.status.success(), "{result:?}");
}

#[cfg(unix)]
#[test]
fn install_check_symlink_path_builds_existing_checkout() {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path().join("checkout");
    create_checkout(&root);
    std::os::unix::fs::symlink(&root, directory.path().join("alias")).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_xtask"))
        .current_dir(directory.path())
        .args(["install", "--check", "--dir", "alias"])
        .output()
        .unwrap();
    assert!(result.status.success(), "{result:?}");
}
