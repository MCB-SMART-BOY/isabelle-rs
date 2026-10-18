use std::fs;
use std::path::Path;
use std::process::Command;

use tempfile::TempDir;
use xtask::cli::{Action, Gate};
use xtask::reference::common::COMMIT;
use xtask::reference::prepare::check_pinned_source;
use xtask::tasks;

const OTHER_COMMIT: &str = "0000000000000000000000000000000000000001";
const HOL_FILES: [&str; 9] =
    ["HOL", "Orderings", "Set", "Nat", "List", "Fun", "Product_Type", "Sum_Type", "Option"];

fn git(directory: &Path, args: &[&str]) -> String {
    let output = Command::new("git").arg("-C").arg(directory).args(args).output().unwrap();
    assert!(output.status.success(), "git {args:?}: {output:?}");
    String::from_utf8(output.stdout).unwrap().trim().to_owned()
}

fn stage_gitlink(root: &Path, revision: &str) {
    git(root, &["update-index", "--add", "--cacheinfo", "160000", revision, "isabelle-source"]);
}

fn commit_fixture(directory: &Path) {
    git(
        directory,
        &[
            "-c",
            "user.name=Fixture",
            "-c",
            "user.email=fixture@example.invalid",
            "commit",
            "-qm",
            "Fixture",
        ],
    );
}

fn make_checkout() -> TempDir {
    let fixture = tempfile::tempdir().unwrap();
    let root = fixture.path();
    git(root, &["init", "-q"]);
    let source = root.join("isabelle-source");
    fs::create_dir(&source).unwrap();
    git(&source, &["init", "-q"]);
    fs::create_dir_all(source.join("src/Pure")).unwrap();
    fs::create_dir_all(source.join("src/HOL")).unwrap();
    fs::write(source.join("src/Pure/ROOT.ML"), "(* fixture *)\n").unwrap();
    for name in HOL_FILES {
        fs::write(source.join(format!("src/HOL/{name}.thy")), format!("theory {name}\n")).unwrap();
    }
    git(&source, &["add", "src"]);
    commit_fixture(&source);
    let actual = git(&source, &["rev-parse", "HEAD"]);
    fs::create_dir_all(source.join(".git/refs/replace")).unwrap();
    fs::write(source.join(".git/refs/replace").join(COMMIT), format!("{actual}\n")).unwrap();
    fs::write(source.join(".git/HEAD"), format!("{COMMIT}\n")).unwrap();
    stage_gitlink(root, COMMIT);
    commit_fixture(root);
    fixture
}

#[test]
fn pinned_source_valid_checkout_passes() {
    let fixture = make_checkout();
    check_pinned_source(fixture.path()).unwrap();
    assert!(tasks::execute(Action::Gate(Gate::PinnedSource), fixture.path(), (0, 0)));
}

#[test]
fn pinned_source_missing_checkout_reports_path() {
    let fixture = tempfile::tempdir().unwrap();
    let error = check_pinned_source(fixture.path()).unwrap_err().to_string();
    assert!(error.contains("isabelle-source"), "{error}");
    assert!(!tasks::execute(Action::Gate(Gate::PinnedSource), fixture.path(), (0, 0)));
}

#[test]
fn pinned_source_missing_hol_file_reports_path() {
    let fixture = make_checkout();
    fs::remove_file(fixture.path().join("isabelle-source/src/HOL/List.thy")).unwrap();
    let error = check_pinned_source(fixture.path()).unwrap_err().to_string();
    assert!(error.contains("src/HOL/List.thy"), "{error}");
}

#[test]
fn pinned_source_wrong_checkout_fails() {
    let fixture = make_checkout();
    let source = fixture.path().join("isabelle-source");
    let actual = fs::read_to_string(source.join(".git/refs/replace").join(COMMIT)).unwrap();
    fs::write(source.join(".git/HEAD"), actual).unwrap();
    assert!(check_pinned_source(fixture.path()).is_err());
}

#[test]
fn pinned_source_wrong_index_gitlink_fails() {
    let fixture = make_checkout();
    stage_gitlink(fixture.path(), OTHER_COMMIT);
    assert!(check_pinned_source(fixture.path()).is_err());
}

#[test]
fn pinned_source_staged_rebaseline_passes_with_old_head_gitlink() {
    let fixture = make_checkout();
    stage_gitlink(fixture.path(), OTHER_COMMIT);
    commit_fixture(fixture.path());
    stage_gitlink(fixture.path(), COMMIT);
    check_pinned_source(fixture.path()).unwrap();
    assert!(tasks::execute(Action::Gate(Gate::PinnedSource), fixture.path(), (0, 0)));
}

#[test]
fn pinned_source_dirty_checkout_fails() {
    let fixture = make_checkout();
    fs::write(fixture.path().join("isabelle-source/src/Pure/ROOT.ML"), "modified\n").unwrap();
    assert!(check_pinned_source(fixture.path()).is_err());
}
