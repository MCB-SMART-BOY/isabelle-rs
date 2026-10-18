#![cfg(target_os = "linux")]

use std::{
    fs,
    path::{Path, PathBuf},
    process::{Child, Command, ExitStatus},
    sync::atomic::{AtomicU64, Ordering},
    thread,
    time::{Duration, Instant},
};

use serde_json::Value;

static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);
const WAIT_LIMIT: Duration = Duration::from_secs(90);

struct Fixture {
    root: PathBuf,
}

impl Fixture {
    fn create() -> Self {
        let number = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir()
            .join(format!("hol-product-supervisor-{}-{number}", std::process::id()));
        fs::create_dir(&root).expect("create isolated fixture");
        Self { root }
    }

    fn scale_command(&self, mode: &str, output_dir: &Path) -> Command {
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
        let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
        let mut command = Command::new(cargo);
        command
            .current_dir(&self.root)
            .arg("run")
            .args(["--locked", "--manifest-path"])
            .arg(manifest)
            .args([
                "-p",
                "xtask",
                "--",
                "supervise",
                "--timeout-secs",
                "10",
                "--memory-mib",
                "512",
                "--output-dir",
            ])
            .arg(output_dir)
            .arg("--worker")
            .arg(env!("CARGO_BIN_EXE_isabelle-scale-hol"))
            .args(["--scale-mode", mode]);
        command
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.root).expect("remove isolated fixture");
    }
}

fn wait_for_exit(child: &mut Child) -> ExitStatus {
    let deadline = Instant::now() + WAIT_LIMIT;
    loop {
        if let Some(status) = child.try_wait().expect("check supervised product") {
            return status;
        }
        if Instant::now() >= deadline {
            child.kill().expect("stop stalled product supervision");
            child.wait().expect("reap stalled product supervision");
            panic!("supervised product failed to exit within {WAIT_LIMIT:?}");
        }
        thread::yield_now();
    }
}

fn read_report(output_dir: &Path) -> Value {
    serde_json::from_slice(
        &fs::read(output_dir.join("supervisor.json")).expect("read supervisor report"),
    )
    .expect("valid supervisor JSON")
}

#[test]
fn supervisor_scale_mode_missing_sources_reports_error_instead_of_completion() {
    let fixture = Fixture::create();
    let output = fixture.root.join("missing-source");
    let mut command = fixture.scale_command("verify-batch-first-five", &output);
    assert_eq!(wait_for_exit(&mut command.spawn().unwrap()).code(), Some(2));
    let report = read_report(&output);
    assert_eq!(report["status"], "error");
    assert_eq!(report["scale_mode"], "verify-batch-first-five");
    assert!(!output.join("manifest.json").exists());
}

#[test]
fn supervisor_scale_mode_option_like_or_unknown_value_reports_error() {
    let fixture = Fixture::create();
    for (index, mode) in ["--help", "-h", "unknown", "$(touch injected)"].iter().enumerate() {
        let output = fixture.root.join(format!("invalid-mode-{index}"));
        let mut command = fixture.scale_command(mode, &output);
        assert_eq!(wait_for_exit(&mut command.spawn().unwrap()).code(), Some(2));
        assert_eq!(read_report(&output)["status"], "error");
    }
    assert!(!fixture.root.join("injected").exists());
}

#[test]
fn supervisor_scale_mode_directory_source_reports_error() {
    let fixture = Fixture::create();
    fs::create_dir_all(fixture.root.join("theories/HOL/HOL.thy")).unwrap();
    let output = fixture.root.join("directory-source");
    let mut command = fixture.scale_command("verify-batch-first-five", &output);
    assert_eq!(wait_for_exit(&mut command.spawn().unwrap()).code(), Some(2));
    assert_eq!(read_report(&output)["status"], "error");
}

#[test]
fn supervisor_tier_modes_without_readable_sources_report_error() {
    for (mode, unreadable_source) in [("tier2", None), ("tier3", Some("Set_Interval.thy"))] {
        let fixture = Fixture::create();
        if let Some(source) = unreadable_source {
            fs::create_dir_all(fixture.root.join("theories/HOL").join(source)).unwrap();
        }
        let output = fixture.root.join("no-readable-sources");
        let mut command = fixture.scale_command(mode, &output);
        assert_eq!(wait_for_exit(&mut command.spawn().unwrap()).code(), Some(2));
        let report = read_report(&output);
        assert_eq!(report["status"], "error");
        assert_eq!(report["scale_mode"], mode);
        assert!(!output.join("manifest.json").exists());
    }
}
