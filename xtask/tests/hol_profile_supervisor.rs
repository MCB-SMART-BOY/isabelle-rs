#![cfg(target_os = "linux")]

#[path = "support/supervisor.rs"]
mod support;

use std::{fs, os::unix::fs::FileTypeExt, path::Path, time::Instant};
use support::{
    CANCEL_LIMIT, Fixture, LOG_BYTES, assert_process_reaped, read_report, set_barrier_env,
    set_permissive_umask, signal_process, wait_for_exit, wait_for_file, wait_for_pid_file,
};

#[test]
fn supervisor_worker_errors_preserve_ordinary_and_timeout_like_codes() {
    let fixture = Fixture::create();
    let worker = fixture.worker();
    for code in [1, 42, 124, 137] {
        let output = fixture.root.join(format!("failed-{code}"));
        let mut command = fixture.command(&worker, &output, "failure");
        command.env("SUPERVISOR_WORKER_EXIT", code.to_string());
        let result = command.output().unwrap();
        assert_eq!(result.status.code(), Some(code));
        assert!(!String::from_utf8_lossy(&result.stderr).contains("namespace launcher failed"));
        assert_eq!(read_report(&output)["status"], "error");
        assert_eq!(read_report(&output)["exit_code"], code);
    }
}

#[test]
fn supervisor_namespace_denial_reports_prerequisite_without_running_worker() {
    let fixture = Fixture::create();
    let worker = fixture.worker();
    let output = fixture.root.join("namespace-denied");
    let (bin_dir, barrier, release) = fixture.install_barrier_unshare(&worker);
    let mut command = fixture.command(&worker, &output, "normal-descendant");
    set_barrier_env(&mut command, bin_dir, &barrier, &release);
    let result = command.env("PROFILE_DENY_NAMESPACE", "1").output().unwrap();
    assert_eq!(result.status.code(), Some(1));
    let diagnostic = String::from_utf8_lossy(&result.stderr);
    assert!(diagnostic.contains("user/PID namespace launcher failed"), "{diagnostic}");
    assert!(diagnostic.contains("Operation not permitted"), "{diagnostic}");
    assert_eq!(read_report(&output)["status"], "error");
    assert_eq!(read_report(&output)["exit_code"], 1);
    assert!(!fixture.root.join("worker-pid").exists());
}

#[test]
fn supervisor_replaced_launcher_log_preserves_exit_without_following_path() {
    let fixture = Fixture::create();
    let worker = fixture.worker();
    let target = fixture.root.join("unrelated.txt");
    let marker = "unshare: unshare failed: unrelated-file-marker";
    fs::write(&target, marker).unwrap();
    for replacement in ["fifo", "symlink"] {
        let output = fixture.root.join(replacement);
        let stderr_path = fixture.root.join(format!("{replacement}-stderr.log"));
        let mut command = fixture.command(&worker, &output, "replace-timeout-log");
        command
            .env("PROFILE_TIMEOUT_LOG", output.join("timeout.log"))
            .env("PROFILE_LOG_REPLACEMENT", replacement)
            .env("PROFILE_LOG_TARGET", &target)
            .stderr(fs::File::create(&stderr_path).unwrap());
        assert_eq!(wait_for_exit(&mut command.spawn().unwrap()).code(), Some(1));
        let file_type = fs::symlink_metadata(output.join("timeout.log")).unwrap().file_type();
        let is_expected_type =
            if replacement == "fifo" { file_type.is_fifo() } else { file_type.is_symlink() };
        assert!(is_expected_type, "worker must execute the {replacement} replacement");
        assert_eq!(read_report(&output)["status"], "error");
        assert_eq!(read_report(&output)["exit_code"], 1);
        assert!(!fs::read_to_string(stderr_path).unwrap().contains(marker));
    }
    assert_eq!(fs::read_to_string(target).unwrap(), marker);
}

#[test]
fn supervisor_permissive_umask_creates_private_output_directory() {
    let fixture = Fixture::create();
    let worker = fixture.worker();
    let output = fixture.root.join("private");
    let mut command = fixture.command(&worker, &output, "success");
    set_permissive_umask(&mut command);
    assert_eq!(wait_for_exit(&mut command.spawn().unwrap()).code(), Some(0));
    use std::os::unix::fs::PermissionsExt;
    assert_eq!(fs::metadata(output).unwrap().permissions().mode() & 0o077, 0);
}

#[test]
fn supervisor_existing_directory_is_not_overwritten() {
    let fixture = Fixture::create();
    let worker = fixture.worker();
    let output = fixture.root.join("existing");
    fs::create_dir(&output).unwrap();
    fs::write(output.join("user.txt"), b"keep me").unwrap();
    let status = wait_for_exit(&mut fixture.command(&worker, &output, "success").spawn().unwrap());
    assert_eq!(status.code(), Some(2));
    assert_eq!(fs::read(output.join("user.txt")).unwrap(), b"keep me");
    assert!(!output.join("supervisor.json").exists());
}

#[test]
fn supervisor_excessive_stderr_is_limited_and_reported_as_error() {
    let fixture = Fixture::create();
    let worker = fixture.worker();
    let output = fixture.root.join("limited");
    let mut command = fixture.command(&worker, &output, "stderr");
    command.args(["--timeout-secs", "10"]);
    let status = wait_for_exit(&mut command.spawn().unwrap());
    assert_ne!(status.code(), Some(0));
    assert_eq!(read_report(&output)["status"], "error");
    assert!(fs::metadata(output.join("stderr.log")).unwrap().len() <= LOG_BYTES);
}

#[test]
fn supervisor_normal_exit_reaps_leftover_descendant() {
    let fixture = Fixture::create();
    let worker = fixture.worker();
    let output = fixture.root.join("leftover");
    let mut supervisor = fixture.command(&worker, &output, "normal-descendant").spawn().unwrap();
    let worker_pid = wait_for_pid_file(&mut supervisor, &fixture.root.join("worker-pid"));
    let child_pid = wait_for_pid_file(&mut supervisor, &fixture.root.join("child-pid"));
    assert_eq!(wait_for_exit(&mut supervisor).code(), Some(0));
    assert_eq!(read_report(&output)["status"], "completed");
    assert_process_reaped(worker_pid);
    assert_process_reaped(child_pid);
}

#[test]
fn supervisor_hard_timeout_reaps_term_ignoring_processes_in_fixed_locale() {
    let fixture = Fixture::create();
    let worker = fixture.worker();
    let output = fixture.root.join("timeout");
    let mut command = fixture.command(&worker, &output, "waiting-descendant");
    command.env("LC_ALL", "C.UTF-8").env("LANGUAGE", "fr");
    let mut supervisor = command.spawn().unwrap();
    let worker_pid = wait_for_pid_file(&mut supervisor, &fixture.root.join("worker-pid"));
    let child_pid = wait_for_pid_file(&mut supervisor, &fixture.root.join("child-pid"));
    assert!(matches!(wait_for_exit(&mut supervisor).code(), Some(124 | 137)));
    assert_eq!(read_report(&output)["status"], "timed_out");
    assert_process_reaped(worker_pid);
    assert_process_reaped(child_pid);
}

fn run_interrupt_fixture(signal: i32, expected_code: i32, name: &str) {
    let fixture = Fixture::create();
    let worker = fixture.worker();
    let output = fixture.root.join(name);
    let mut command = fixture.command(&worker, &output, "waiting-descendant");
    command.args(["--timeout-secs", "10"]);
    let mut supervisor = command.spawn().unwrap();
    let worker_pid = wait_for_pid_file(&mut supervisor, &fixture.root.join("worker-pid"));
    let child_pid = wait_for_pid_file(&mut supervisor, &fixture.root.join("child-pid"));
    let started = Instant::now();
    signal_process(supervisor.id(), signal);
    assert_eq!(wait_for_exit(&mut supervisor).code(), Some(expected_code));
    assert!(started.elapsed() < CANCEL_LIMIT, "cancellation used wall timeout");
    assert_eq!(read_report(&output)["status"], "error");
    assert_eq!(read_report(&output)["exit_code"], expected_code);
    assert_process_reaped(worker_pid);
    assert_process_reaped(child_pid);
}

#[test]
fn supervisor_term_and_int_reap_processes_without_using_wall_budget() {
    run_interrupt_fixture(libc::SIGTERM, 143, "terminated");
    run_interrupt_fixture(libc::SIGINT, 130, "interrupted");
}

#[test]
fn supervisor_cancel_during_launcher_startup_is_not_lost() {
    let fixture = Fixture::create();
    let worker = fixture.worker();
    let output = fixture.root.join("startup-cancel");
    let (bin_dir, barrier, release) = fixture.install_barrier_unshare(&worker);
    let mut command = fixture.command(&worker, &output, "waiting-descendant");
    command.args(["--timeout-secs", "10"]);
    set_barrier_env(&mut command, bin_dir, &barrier, &release);
    let mut supervisor = command.spawn().unwrap();
    wait_for_file(&mut supervisor, &barrier);
    let started = Instant::now();
    signal_process(supervisor.id(), libc::SIGTERM);
    fs::write(&release, b"go").expect("release launcher");
    assert_eq!(wait_for_exit(&mut supervisor).code(), Some(143));
    assert!(started.elapsed() < CANCEL_LIMIT, "queued cancellation lost");
    assert_eq!(read_report(&output)["status"], "error");
}

#[test]
fn supervisor_scale_mode_with_single_lemma_arguments_rejects_before_running() {
    let fixture = Fixture::create();
    let worker = fixture.worker();
    let output = fixture.root.join("conflicting");
    let mut command = fixture.command(&worker, &output, "success");
    command.args(["--scale-mode", "verify-batch-first-five"]);
    assert_eq!(wait_for_exit(&mut command.spawn().unwrap()).code(), Some(2));
    assert!(!output.exists());
}

#[test]
fn supervisor_scale_mode_empty_or_missing_value_rejects_before_running() {
    let fixture = Fixture::create();
    let worker = fixture.worker();
    for has_value in [false, true] {
        let output = fixture.root.join(format!("invalid-value-{has_value}"));
        let mut command = fixture.scale_command(&worker, &output, "verify-batch-first-five");
        command.arg("--scale-mode");
        if has_value {
            command.arg("");
        }
        assert_eq!(wait_for_exit(&mut command.spawn().unwrap()).code(), Some(2));
        assert!(!output.exists());
    }
}

#[test]
fn supervisor_scale_mode_empty_single_lemma_argument_rejects_before_running() {
    let fixture = Fixture::create();
    let worker = fixture.worker();
    let options =
        ["--source-root", "--theory", "--lemma", "--context-root", "--manifest-in", "--auto-limit"];
    for (index, option) in options.iter().enumerate() {
        let output = fixture.root.join(format!("empty-conflict-{index}"));
        let mut command = fixture.scale_command(&worker, &output, "verify-batch-first-five");
        command.args([*option, ""]);
        assert_eq!(wait_for_exit(&mut command.spawn().unwrap()).code(), Some(2));
        assert!(!output.exists(), "{option} was silently ignored");
    }
}

#[test]
fn supervisor_scale_mode_hard_timeout_reaps_term_ignoring_processes() {
    let fixture = Fixture::create();
    let worker = fixture.worker();
    let output = fixture.root.join("scale-timeout");
    let mut supervisor =
        fixture.scale_command(&worker, &output, "verify-batch-first-five").spawn().unwrap();
    let worker_pid = wait_for_pid_file(&mut supervisor, &fixture.root.join("worker-pid"));
    let child_pid = wait_for_pid_file(&mut supervisor, &fixture.root.join("child-pid"));
    assert!(matches!(wait_for_exit(&mut supervisor).code(), Some(124 | 137)));
    assert_eq!(read_report(&output)["status"], "timed_out");
    assert_process_reaped(worker_pid);
    assert_process_reaped(child_pid);
}

#[test]
fn supervisor_report_declares_per_process_limits_and_exact_selection() {
    let fixture = Fixture::create();
    let worker = fixture.worker();
    let output = fixture.root.join("limits");
    assert_eq!(
        wait_for_exit(&mut fixture.command(&worker, &output, "success").spawn().unwrap()).code(),
        Some(0)
    );
    let report = read_report(&output);
    assert_eq!(report["resource_scope"], "per_process");
    assert_eq!(report["max_log_bytes"], LOG_BYTES);
    assert_eq!(report["memory_mib"], 512);
    assert_eq!(report["timeout_secs"], 1);
    assert_eq!(report["cpu_secs"], 4);
    assert_eq!(report["theory"], "Fixture");
    assert_eq!(report["lemma"], "lemma");
    assert_eq!(report["scale_mode"], "");
    assert!(Path::new(&output.join("events.jsonl")).exists());
}

#[test]
fn supervisor_invalid_limits_and_missing_worker_reject_before_output() {
    let fixture = Fixture::create();
    let worker = fixture.worker();
    for (index, (flag, value)) in [
        ("--timeout-secs", "0"),
        ("--timeout-secs", "86401"),
        ("--timeout-secs", "00000001"),
        ("--memory-mib", "65537"),
        ("--auto-limit", "10001"),
        ("--timeout-secs", "1; touch injected"),
    ]
    .iter()
    .enumerate()
    {
        let output = fixture.root.join(format!("invalid-limit-{index}"));
        let mut command = fixture.command(&worker, &output, "success");
        command.args([*flag, *value]);
        assert_eq!(wait_for_exit(&mut command.spawn().unwrap()).code(), Some(2));
        assert!(!output.exists());
    }
    let output = fixture.root.join("missing-worker");
    let mut command = fixture.command(&fixture.root.join("nonexistent-worker"), &output, "success");
    assert_eq!(wait_for_exit(&mut command.spawn().unwrap()).code(), Some(2));
    assert!(!output.exists());
    assert!(!fixture.root.join("injected").exists());
}
