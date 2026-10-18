use std::{env, fs, path::Path, process::Command};

use tempfile::TempDir;
use xtask::{
    gates::{audit_compat, check_links, check_snippets, check_templates},
    runner::StepError,
};

fn create_fixture() -> TempDir {
    tempfile::tempdir().expect("create gate fixture")
}

fn write_file(root: &Path, relative: &str, content: &str) {
    let path = root.join(relative);
    fs::create_dir_all(path.parent().expect("fixture file parent"))
        .expect("create fixture directory");
    fs::write(path, content).expect("write fixture file");
}

#[test]
fn links_missing_local_target_reports_source_location() {
    let fixture = create_fixture();
    write_file(
        fixture.path(),
        "docs/guide.md",
        "[ok](#section) [remote](https://example.test) [bad](absent.md)\n",
    );
    let error = check_links(fixture.path()).expect_err("missing local link must fail");
    assert!(error.to_string().contains("guide.md:1 -> absent.md"), "{error}");
}

#[test]
fn links_existing_relative_target_accepts_and_skips_excluded_trees() {
    let fixture = create_fixture();
    write_file(fixture.path(), "docs/guide.md", "[child](sub/page.md#section)\n");
    write_file(fixture.path(), "docs/sub/page.md", "# Section\n");
    write_file(fixture.path(), "target/stale.md", "[bad](missing.md)\n");
    assert!(check_links(fixture.path()).is_ok());
}

#[test]
fn links_invalid_source_reports_read_failure() {
    let fixture = create_fixture();
    fs::write(fixture.path().join("invalid.md"), [0xff]).expect("create malformed markdown");
    let error = check_links(fixture.path()).expect_err("failed read cannot be clean");
    assert!(matches!(error, StepError::Io { .. }), "{error}");
}

#[test]
fn snippets_duplicate_body_across_files_reports_first_location() {
    let fixture = create_fixture();
    let snippet = format!("```rust\n{}\n```\n", "let n = 1;\n".repeat(12).trim_end());
    write_file(fixture.path(), "a.md", &snippet);
    write_file(fixture.path(), "b.md", &snippet);
    let error = check_snippets(fixture.path()).expect_err("duplicate executable block must fail");
    assert!(error.to_string().contains("b.md:1: duplicates rust fenced block at"), "{error}");
    assert!(error.to_string().contains("a.md:1 (12 lines)"), "{error}");
}

#[test]
fn snippets_oversized_block_and_unclosed_block_both_fail() {
    let fixture = create_fixture();
    write_file(
        fixture.path(),
        "too-long.md",
        &format!("```json\n{}\n```\n", "null\n".repeat(41).trim_end()),
    );
    write_file(fixture.path(), "unclosed.md", "```sh\nprintf hello\n");
    let error = check_snippets(fixture.path()).expect_err("invalid blocks must fail");
    assert!(error.to_string().contains("41 lines; explanatory limit is 40"), "{error}");
    assert!(error.to_string().contains("unclosed sh fenced block"), "{error}");
}

#[test]
fn snippets_custom_limits_reject_long_and_duplicate_blocks() {
    let output = Command::new(env::current_exe().expect("locate test binary"))
        .args(["--exact", "snippets_limit_child_checks_policy"])
        .env("XTASK_GATE_LIMIT_CHILD", "yes")
        .env("MAX_EXPLANATORY_LINES", "1")
        .env("DUPLICATE_MIN_LINES", "1")
        .output()
        .expect("run isolated limits check");
    assert!(output.status.success(), "{output:?}");
}

#[test]
fn snippets_limit_child_checks_policy() {
    if env::var_os("XTASK_GATE_LIMIT_CHILD").is_none() {
        return;
    }
    let fixture = create_fixture();
    write_file(fixture.path(), "a.md", "```json\n1\n2\n```\n```json\n1\n```\n```json\n1\n```\n");
    let error = check_snippets(fixture.path()).expect_err("configured limits must apply");
    assert!(error.to_string().contains("2 lines; explanatory limit is 1"), "{error}");
    assert!(error.to_string().contains("duplicates json fenced block"), "{error}");
}

#[test]
fn templates_missing_directory_reports_enumeration_failure() {
    let fixture = create_fixture();
    let error = check_templates(fixture.path()).expect_err("missing templates must fail");
    assert!(matches!(error, StepError::Io { .. }), "{error}");
}

#[test]
fn templates_missing_classification_rejects_source() {
    let fixture = create_fixture();
    write_file(fixture.path(), "scripts/templates/sample.rs", "pub fn sample() {}\n");
    let error = check_templates(fixture.path()).expect_err("template requires classification");
    assert!(error.to_string().contains("missing design-only classification"), "{error}");
}

#[test]
fn templates_formatted_standalone_source_compiles() {
    let fixture = create_fixture();
    write_file(
        fixture.path(),
        "scripts/templates/sample.rs",
        "// Classification: design-only standalone template; not production code.\npub fn sample() {}\n",
    );
    assert!(check_templates(fixture.path()).is_ok());
}

#[test]
fn templates_valid_syntax_with_unresolved_type_rejects_compilation() {
    let fixture = create_fixture();
    write_file(
        fixture.path(),
        "scripts/templates/sample.rs",
        "// Classification: design-only standalone template; not production code.\npub fn sample() -> UnknownType {\n    loop {}\n}\n",
    );
    let error = check_templates(fixture.path()).expect_err("independent rustc check must fail");
    assert!(matches!(error, StepError::Exit { .. }), "{error}");
}

#[test]
fn compat_report_groups_all_legacy_patterns_without_failing() {
    let fixture = create_fixture();
    write_file(fixture.path(), "src/legacy.rs", "assume_compat(\ncompat_alpha_eq\n");
    write_file(fixture.path(), "tests/legacy.rs", "CTerm::certify(\n");
    let output = Command::new(env::current_exe().expect("locate test binary"))
        .args(["--exact", "compat_report_child_emits_matches", "--nocapture"])
        .env("XTASK_COMPAT_FIXTURE", fixture.path())
        .output()
        .expect("run isolated compatibility audit");
    assert!(output.status.success(), "{output:?}");
    let report = String::from_utf8(output.stdout).expect("UTF-8 audit report");
    for (section, pattern) in [
        ("Compatibility theorem constructors", "src/legacy.rs:1:assume_compat("),
        ("Compatibility equality", "src/legacy.rs:2:compat_alpha_eq"),
        ("Unchecked legacy certification", "tests/legacy.rs:1:CTerm::certify("),
    ] {
        assert!(report.contains(section), "{report}");
        assert!(report.contains(pattern), "{report}");
    }
}

#[test]
fn compat_report_child_emits_matches() {
    let Some(root) = env::var_os("XTASK_COMPAT_FIXTURE") else { return };
    audit_compat(Path::new(&root)).expect("compatibility findings are informative");
}

#[test]
fn compat_missing_scan_root_reports_enumeration_failure() {
    let fixture = create_fixture();
    fs::create_dir(fixture.path().join("src")).expect("create source tree");
    let error = audit_compat(fixture.path()).expect_err("missing test tree must fail");
    assert!(matches!(error, StepError::Io { .. }), "{error}");
}

#[test]
fn compat_invalid_source_reports_read_failure() {
    let fixture = create_fixture();
    fs::create_dir(fixture.path().join("src")).expect("create source tree");
    fs::create_dir(fixture.path().join("tests")).expect("create test tree");
    fs::write(fixture.path().join("src/invalid.rs"), [0xff]).expect("write malformed source");
    let error = audit_compat(fixture.path()).expect_err("read failure must not be an empty report");
    assert!(matches!(error, StepError::Io { .. }), "{error}");
}
