use isabelle_rs::ml::host::solver::{FixedSolver, SolverConfig, SolverErrorKind, SolverRequest};
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
use std::fs;
use std::path::PathBuf;
#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
use std::process::Command;
use std::time::Duration;

const FLAGS: &str = "--proof-with-sharing --proof-define-skolems --proof-prune --proof-merge --disable-print-success --disable-banner";
const BEST: &str = "--index-sorts --index-fresh-sorts --triggers-new --triggers-sel-rm-specific";
const DEL_INSTS: &str = "--index-sorts --index-fresh-sorts --ccfv-breadth --inst-deletion --index-SAT-triggers --inst-deletion-loops --inst-deletion-track-vars --inst-deletion --index-SAT-triggers";

fn request(script: String) -> SolverRequest {
    SolverRequest {
        script,
        input: Vec::new(),
        cwd: None,
        environment: Vec::new(),
        timeout: Duration::ZERO,
        redirect: true,
    }
}

fn config() -> SolverConfig {
    SolverConfig {
        executable: PathBuf::from("/fixed/verit"),
        delegated_cgroup_root: PathBuf::from("/delegated/cgroup"),
        staging_root: PathBuf::from("/solver/staging"),
        bubblewrap: PathBuf::from("/fixed/bwrap"),
        elf_loader: PathBuf::from("/fixed/loader"),
        libc: PathBuf::from("/fixed/libc"),
        libm: PathBuf::from("/fixed/libm"),
        libgmp: PathBuf::from("/fixed/libgmp"),
    }
}

#[test]
fn solver_script_three_full_strategies_preserve_order() {
    for strategy in ["", BEST, DEL_INSTS] {
        let separator = if strategy.is_empty() { "" } else { " " };
        let script = format!("/fixed/verit {FLAGS}{separator}{strategy}");
        let arguments = FixedSolver::validate_request(&config(), &request(script)).unwrap();
        let expected: Vec<_> =
            format!("{FLAGS}{separator}{strategy}").split_whitespace().map(str::to_owned).collect();
        assert_eq!(arguments, expected);
    }
}

#[test]
fn solver_script_milliseconds_bounds_and_overflow_rejected() {
    for time in ["1", "300000"] {
        let script = format!("/fixed/verit {FLAGS} --max-time\\={time}");
        let arguments = FixedSolver::validate_request(&config(), &request(script)).unwrap();
        assert_eq!(
            arguments.last().map(String::as_str),
            Some(format!("--max-time={time}").as_str())
        );
    }
    for time in ["0", "0001", "300001", "18446744073709551616", "-1", "1;echo"] {
        let script = format!("/fixed/verit {FLAGS} --max-time\\={time}");
        assert_eq!(
            FixedSolver::validate_request(&config(), &request(script)).unwrap_err().kind,
            SolverErrorKind::Permission
        );
    }
    let noncanonical = format!("/fixed/verit {FLAGS} --max-time=1");
    assert_eq!(
        FixedSolver::validate_request(&config(), &request(noncanonical)).unwrap_err().kind,
        SolverErrorKind::Permission
    );
}

#[test]
fn solver_script_shell_injection_and_strategy_mutation_rejected() {
    for script in [
        format!("/fixed/verit {FLAGS}; /bin/sh"),
        format!("/fixed/verit {FLAGS} --inst-deletion"),
        format!("/fixed/verit {FLAGS} {BEST} --index-sorts"),
        format!(
            "/fixed/verit {FLAGS} --index-sorts --triggers-new --index-fresh-sorts --triggers-sel-rm-specific"
        ),
        format!("/fixed/verit {FLAGS} {DEL_INSTS} --inst-deletion"),
        format!("/fixed/verit {FLAGS}  --max-time=1"),
        format!("/fixed/verit {FLAGS} --max-time=1\n"),
        format!("/fixed/verit {FLAGS} --max-time=\\1"),
        format!("/fixed/verit {FLAGS} --max-time=$'\\x31'"),
        format!("/other/verit {FLAGS}"),
    ] {
        assert_eq!(
            FixedSolver::validate_request(&config(), &request(script.clone())).unwrap_err().kind,
            SolverErrorKind::Permission,
            "{script}"
        );
    }
}

#[test]
fn solver_script_excess_words_and_word_length_rejected_before_argv_copy() {
    let base = format!("/fixed/verit {FLAGS}");
    for script in [
        format!("{base} {}", "a ".repeat(11).trim_end()),
        format!("{base} --max-time\\={}", "1".repeat(80)),
        format!("{base} {}", "A".repeat(4096)),
    ] {
        let error = FixedSolver::validate_request(&config(), &request(script)).unwrap_err();
        assert_eq!(error.kind, SolverErrorKind::Permission);
    }
}

#[test]
fn solver_request_effects_and_input_bounds_rejected() {
    let base = format!("/fixed/verit {FLAGS}");
    let mut nonredirect = request(base.clone());
    nonredirect.redirect = false;
    let mut env = request(base.clone());
    env.environment.push(("LD_PRELOAD".into(), "payload".into()));
    let mut cwd = request(base.clone());
    cwd.cwd = Some("/tmp".into());
    let mut input = request(base);
    input.input.resize(64 * 1024 * 1024 + 1, 0);
    for case in [nonredirect, env, cwd, input] {
        assert_eq!(
            FixedSolver::validate_request(&config(), &case).unwrap_err().kind,
            SolverErrorKind::Permission
        );
    }
}

#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
#[test]
fn solver_unsupported_platform_rejects_configuration_before_execution() {
    assert_eq!(
        FixedSolver::new(config()).err().unwrap().kind,
        SolverErrorKind::BlockedPrerequisite
    );
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[test]
fn launcher_forged_flag_cannot_write_ordinary_cgroup_file() {
    let root = std::env::temp_dir().join(format!(
        "isabelle-solver-forged-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir(&root).unwrap();
    let victim = root.join("cgroup.procs");
    fs::write(&victim, "sentinel").unwrap();
    for (name, value) in [
        ("memory.max", "2147483648"),
        ("memory.swap.max", "0"),
        ("pids.max", "16"),
        ("cpu.max", "100000 100000"),
    ] {
        fs::write(root.join(name), value).unwrap();
    }
    let result = Command::new(env!("CARGO_BIN_EXE_isabelle-rs"))
        .arg("--internal-solver-launcher")
        .arg(&root)
        .args(["3", "4", "5", "6", "7", "8", "9", "10"])
        .output()
        .unwrap();
    assert!(!result.status.success());
    assert!(String::from_utf8_lossy(&result.stderr).contains("authenticate launcher"));
    assert_eq!(fs::read(&victim).unwrap(), b"sentinel");
    fs::remove_dir_all(root).unwrap();
}
