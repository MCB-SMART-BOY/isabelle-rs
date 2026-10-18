use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

struct Scratch(PathBuf);

impl Scratch {
    fn create() -> Self {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        let path = std::env::temp_dir().join(format!("xtask cli {nonce} {}", std::process::id()));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn xtask() -> Command {
    Command::new(env!("CARGO_BIN_EXE_xtask"))
}

#[test]
fn cli_unknown_and_conflicting_options_fail_without_building() {
    let scratch = Scratch::create();
    for args in [
        vec!["nonesuch"],
        vec!["test", "--lib", "--test", "bnf_tests"],
        vec!["profile", "--worker", "other"],
        vec!["reference"],
        vec!["reference", "inventory"],
        vec!["reference", "inventory", "--build-run"],
        vec!["reference", "build", "--build-run", "old-run"],
        vec!["reference", "inventory", "--source-root", "different-source"],
        vec!["reference", "build", "--workspace", "one", "--workspace", "two"],
        vec!["reference", "prepare", "--workspace"],
        vec!["reference", "compare"],
        vec!["reference", "compare", "--rust-report", "native.json"],
        vec!["reference", "compare", "--reference-run", "reference"],
        vec!["reference", "compare", "--workspace", "reference"],
        vec!["reference", "prepare", "--reference-preapproval", "preapproval.json"],
        vec!["reference", "build", "--reference-approval", "approval.json"],
        vec![
            "reference",
            "inventory",
            "--build-run",
            "build",
            "--reference-approval",
            "approval.json",
        ],
        vec!["reference", "compare", "--reference-preapproval", "preapproval.json"],
        vec![
            "reference",
            "compare",
            "--rust-report",
            "native.json",
            "--reference-run",
            "run",
            "--reference-approval",
            "approval.json",
        ],
        vec![
            "reference",
            "build",
            "--reference-preapproval",
            "first.json",
            "--reference-preapproval",
            "second.json",
        ],
        vec!["install", "--dir"],
        vec!["install", "--release", "--release"],
        vec!["install", "--unknown"],
        vec!["package", "--artifacts", "--release"],
        vec!["package"],
        vec!["fix", "unknown"],
        vec!["hook"],
        vec!["hook", "unknown"],
        vec!["hook", "pre-edit", "extra"],
        vec!["supervise"],
    ] {
        let output = xtask().current_dir(&scratch.0).args(args).output().unwrap();
        assert_eq!(output.status.code(), Some(2), "{}", String::from_utf8_lossy(&output.stderr));
    }
}

#[test]
fn cli_reference_execution_policy_rejects_before_workspace_access() {
    let scratch = Scratch::create();
    let workspace = scratch.0.join("uncreated reference");
    for operation in ["prepare", "build", "inventory"] {
        let mut command = xtask();
        command
            .current_dir(&scratch.0)
            .env("PATH", "")
            .args(["reference", operation, "--workspace"])
            .arg(&workspace);
        if operation == "inventory" {
            command.args(["--build-run", "unavailable build"]);
        }
        let output = command.output().unwrap();
        assert_eq!(output.status.code(), Some(2), "operation {operation}");
        assert!(!workspace.exists(), "operation {operation} created a workspace");
    }
}

#[test]
fn cli_profile_invalid_limits_prevent_worker_build() {
    let scratch = Scratch::create();
    fs::create_dir(scratch.0.join("source with spaces")).unwrap();
    let output = xtask()
        .current_dir(&scratch.0)
        .env("CARGO", scratch.0.join("missing cargo"))
        .args([
            "profile",
            "--source-root",
            "source with spaces",
            "--theory",
            "Tiny",
            "--lemma",
            "sample",
            "--output-dir",
            "new output",
            "--timeout-secs",
            "0",
        ])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(!scratch.0.join("new output").exists());
    assert!(String::from_utf8_lossy(&output.stderr).contains("timeout-secs"));
}

#[test]
fn cli_tier_invalid_environment_limit_prevents_worker_build() {
    let scratch = Scratch::create();
    let output = xtask()
        .current_dir(&scratch.0)
        .env("CARGO", scratch.0.join("missing cargo"))
        .env("HOL_DIAGNOSTIC_TIMEOUT_SECS", "1")
        .env("HOL_DIAGNOSTIC_MEMORY_MIB", "65537")
        .arg("tier2")
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("memory-mib"));
}

#[test]
fn cli_install_check_ignores_unapproved_system_codec_overrides() {
    let scratch = Scratch::create();
    fs::create_dir(scratch.0.join("src")).unwrap();
    fs::write(
        scratch.0.join("Cargo.toml"),
        "[package]\nname = \"isabelle-rs\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(scratch.0.join("src/lib.rs"), "pub fn ready() -> bool { true }\n").unwrap();
    fs::write(
        scratch.0.join("build.rs"),
        r#"
        fn main() {
            assert!(std::env::var_os("ZSTD_SYS_USE_PKG_CONFIG").is_none());
            assert!(std::env::var_os("ZSTD_SYS_NO_HIDE_SYMBOLS").is_none());
        }
    "#,
    )
    .unwrap();
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let locked = Command::new(cargo)
        .current_dir(&scratch.0)
        .args(["generate-lockfile", "--offline"])
        .status()
        .unwrap();
    assert!(locked.success());
    let output = xtask()
        .current_dir(&scratch.0)
        .env("ZSTD_SYS_USE_PKG_CONFIG", "1")
        .env("ZSTD_SYS_NO_HIDE_SYMBOLS", "1")
        .args(["install", "--dir", scratch.0.to_str().unwrap(), "--check"])
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
}

#[test]
fn cli_version_mismatch_blocks_every_release_gate() {
    let scratch = Scratch::create();
    let output = xtask()
        .current_dir(&scratch.0)
        .env("HOL_DIAGNOSTIC_MEMORY_MIB", "invalid-but-must-not-run")
        .args(["release-check", "--tag", "not-a-version-tag"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{}", String::from_utf8_lossy(&output.stderr));
    let summary = String::from_utf8_lossy(&output.stderr);
    assert!(summary.contains("does not match root package version"), "{summary}");
    assert!(summary.contains("BLOCKED release verification"), "{summary}");
    assert!(!summary.contains("=== markdown snippets ==="), "{summary}");
}

#[test]
fn cli_matching_package_version_passes_without_release_gates() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap();
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let metadata = Command::new(cargo)
        .args(["metadata", "--locked", "--no-deps", "--format-version", "1"])
        .current_dir(root)
        .output()
        .unwrap();
    assert!(metadata.status.success(), "{metadata:?}");
    let metadata: serde_json::Value = serde_json::from_slice(&metadata.stdout).unwrap();
    let package = metadata["packages"]
        .as_array()
        .unwrap()
        .iter()
        .find(|package| package["name"] == "isabelle-rs")
        .unwrap();
    let tag = format!("v{}", package["version"].as_str().unwrap());
    let output = xtask().args(["version-check", "--tag", &tag]).output().unwrap();
    assert_eq!(output.status.code(), Some(0), "{output:?}");
}
