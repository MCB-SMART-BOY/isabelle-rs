use std::io::Write;
use std::path::{Path, PathBuf};

use crate::cargo::{build_worker, cargo_command, root_package_id, root_version};
use crate::cli::{Action, Gate, Profile, TestSelection, resource_limits};
use crate::runner::{Runner, StepError, io_error, report_line, run_command};

fn cargo_step(runner: &mut Runner, root: &Path, label: &str, args: &[&str]) -> usize {
    let mut command = cargo_command();
    command.args(args);
    runner.step(label, &[], || run_command(command, label, root))
}

fn format(runner: &mut Runner, root: &Path) {
    cargo_step(runner, root, "workspace format", &["fmt", "--all", "--", "--check"]);
}

fn verify(runner: &mut Runner, root: &Path) {
    runner.step("pinned official source", &[], || {
        crate::reference::prepare::check_pinned_source(root)
    });
    format(runner, root);
    lint(runner, root);
    cargo_step(
        runner,
        root,
        "workspace all-targets check",
        &["check", "--locked", "--workspace", "--all-targets"],
    );
    let mut kernel = cargo_command();
    kernel.args(["check", "--locked", "-p", "isabelle-kernel"]).env("RUSTFLAGS", "-D warnings");
    runner.step("kernel zero warnings", &[], || run_command(kernel, "kernel zero warnings", root));
    documentation_gates(runner, root);
    runner.step("kernel firewall", &[], || crate::gates::check_firewall(root));
    test(runner, root, TestSelection::Workspace, false);
}

fn check(runner: &mut Runner, root: &Path, all_targets: bool) {
    let mut args = vec!["check", "--locked", "-p", "isabelle-rs"];
    if all_targets {
        args.push("--all-targets");
    }
    cargo_step(runner, root, "root check", &args);
}

fn fast(runner: &mut Runner, root: &Path) {
    format(runner, root);
    check(runner, root, false);
}

fn strict_setup(runner: &mut Runner, root: &Path) {
    fast(runner, root);
    let mut kernel = cargo_command();
    kernel.args(["check", "--locked", "-p", "isabelle-kernel"]).env("RUSTFLAGS", "-D warnings");
    runner.step("kernel zero warnings", &[], || run_command(kernel, "kernel zero warnings", root));
    runner.step("kernel firewall", &[], || crate::gates::check_firewall(root));
}

fn strict_boundaries(runner: &mut Runner, root: &Path) {
    for target in
        ["kernel_rewrite_soundness", "kernel_context_identity", "kernel_trusted_acceptance"]
    {
        cargo_step(
            runner,
            root,
            target,
            &["test", "--locked", "-p", "isabelle-rs", "--test", target],
        );
    }
    cargo_step(
        runner,
        root,
        "kernel compile-fail doctests",
        &["test", "--locked", "-p", "isabelle-kernel", "--doc"],
    );
    cargo_step(
        runner,
        root,
        "kernel serde boundary doctests",
        &["test", "--locked", "-p", "isabelle-rs", "--doc", "kernel"],
    );
    cargo_step(
        runner,
        root,
        "kernel_declaration_boundary",
        &["test", "--locked", "-p", "isabelle-rs", "--test", "kernel_declaration_boundary"],
    );
    cargo_step(
        runner,
        root,
        "sampled source boundary",
        &[
            "test",
            "--locked",
            "-p",
            "isabelle-rs",
            "--test",
            "sampled_true_i",
            "--test",
            "source_term_elaboration",
        ],
    );
}

fn strict(runner: &mut Runner, root: &Path) {
    strict_setup(runner, root);
    strict_boundaries(runner, root);
    cargo_step(
        runner,
        root,
        "kernel_soundness",
        &["test", "--locked", "-p", "isabelle-rs", "--test", "kernel_soundness"],
    );
    cargo_step(
        runner,
        root,
        "isabelle-kernel package tests",
        &["test", "--locked", "-p", "isabelle-kernel", "--no-fail-fast"],
    );
    cargo_step(
        runner,
        root,
        "legacy core:: tests",
        &["test", "--locked", "-p", "isabelle-rs", "--lib", "core::"],
    );
}

fn checkpoint(runner: &mut Runner, root: &Path) {
    strict(runner, root);
    cargo_step(
        runner,
        root,
        "prove_true_i_succeeds",
        &[
            "test",
            "--locked",
            "-p",
            "isabelle-rs",
            "--lib",
            "prove_true_i_succeeds",
            "--",
            "--nocapture",
        ],
    );
    for filter in ["polytype_tests", "axiom_dep_tests", "definition_tests"] {
        cargo_step(
            runner,
            root,
            filter,
            &["test", "--locked", "-p", "isabelle-kernel", "--lib", filter, "--", "--nocapture"],
        );
    }
}

fn core(runner: &mut Runner, root: &Path) {
    cargo_step(
        runner,
        root,
        "sampled core trust snapshot",
        &[
            "test",
            "--locked",
            "-p",
            "isabelle-rs",
            "core_batch_snapshot_reports_one_kernel_trusted_and_zero_transitional",
            "--",
            "--nocapture",
        ],
    );
}

fn documentation_gates(runner: &mut Runner, root: &Path) {
    runner.step("markdown snippets", &[], || crate::gates::check_snippets(root));
    runner.step("documentation links", &[], || crate::gates::check_links(root));
    runner.step("Rust templates", &[], || crate::gates::check_templates(root));
}

fn docs(runner: &mut Runner, root: &Path) {
    documentation_gates(runner, root);
    fast(runner, root);
}

fn make_diagnostic_dir(mode: &str, _root: &Path) -> Result<PathBuf, StepError> {
    tempfile::Builder::new()
        .prefix(&format!("isabelle-{mode}-"))
        .tempdir()
        .map(tempfile::TempDir::keep)
        .map_err(|source| io_error(format!("create diagnostic directory for {mode}"), source))
}

fn supervise(root: &Path, label: &str, worker: &Path, args: &[String]) -> Result<(), StepError> {
    report_line(format_args!("Supervising {label}: {}", worker.display()))?;
    crate::supervisor::run(root, worker, args)
}

fn require_linux() -> Result<(), StepError> {
    if cfg!(target_os = "linux") {
        Ok(())
    } else {
        Err(StepError::Input("profile-hol diagnostics require Linux".into()))
    }
}

fn tier(runner: &mut Runner, root: &Path, mode: &str, limits: (u64, u64)) {
    let mut worker = None;
    let build = runner.step(format!("build {mode} worker"), &[], || {
        require_linux()?;
        let package_id = root_package_id(root)?;
        worker = Some(build_worker(root, &package_id, "isabelle-scale-hol")?);
        Ok(())
    });
    runner.step(format!("{mode} bounded diagnostic"), &[build], || {
        let directory = make_diagnostic_dir(mode, root)?;
        let output = directory.join("run");
        report_line(format_args!("Diagnostic output: {}", output.display()))?;
        let args = vec![
            "--scale-mode".into(),
            mode.into(),
            "--timeout-secs".into(),
            limits.0.to_string(),
            "--memory-mib".into(),
            limits.1.to_string(),
            "--output-dir".into(),
            output.display().to_string(),
        ];
        let worker = worker.as_deref().ok_or_else(|| StepError::Protocol {
            operation: format!("supervise {mode}"),
            detail: "successful build lacked worker".into(),
        })?;
        supervise(root, mode, worker, &args)
    });
}

fn profile(runner: &mut Runner, root: &Path, profile: Profile) {
    let mut worker = None;
    let build = runner.step("build profile worker", &[], || {
        require_linux()?;
        let package_id = root_package_id(root)?;
        worker = Some(build_worker(root, &package_id, "isabelle-profile-hol")?);
        Ok(())
    });
    runner.step("single-lemma bounded diagnostic", &[build], || {
        let mut args = vec![
            "--source-root".into(),
            profile.source_root.display().to_string(),
            "--theory".into(),
            profile.theory,
            "--lemma".into(),
            profile.lemma,
            "--output-dir".into(),
            profile.output_dir.display().to_string(),
            "--timeout-secs".into(),
            profile.timeout_secs.to_string(),
            "--memory-mib".into(),
            profile.memory_mib.to_string(),
        ];
        for (flag, path) in
            [("--context-root", profile.context_root), ("--manifest-in", profile.manifest_in)]
        {
            if let Some(path) = path {
                args.extend([flag.into(), path.display().to_string()]);
            }
        }
        if let Some(limit) = profile.auto_limit {
            args.extend(["--auto-limit".into(), limit.to_string()]);
        }
        let worker = worker.as_deref().ok_or_else(|| StepError::Protocol {
            operation: "supervise profile".into(),
            detail: "successful build lacked worker".into(),
        })?;
        supervise(root, "single-lemma profile", worker, &args)
    });
}

fn test(runner: &mut Runner, root: &Path, selection: TestSelection, ignored: bool) {
    let mut args = vec!["test", "--locked"];
    match &selection {
        TestSelection::Workspace => args.extend(["--workspace", "--no-fail-fast"]),
        TestSelection::Library(filter) => {
            args.extend(["-p", "isabelle-rs", "--lib"]);
            if let Some(filter) = filter {
                args.push(filter);
            }
        },
        TestSelection::Target(target) => args.extend(["-p", "isabelle-rs", "--test", target]),
        TestSelection::Doc => args.extend(["-p", "isabelle-rs", "--doc"]),
    }
    if ignored {
        args.extend(["--", "--ignored"]);
    }
    cargo_step(runner, root, "selected tests", &args);
}

fn version_check(root: &Path, tag: &str) -> Result<(), StepError> {
    let version = root_version(root)?;
    let expected = format!("v{version}");
    if tag != expected {
        return Err(StepError::Input(format!(
            "release tag {tag:?} does not match root package version {expected:?}"
        )));
    }
    report_line(format_args!("release tag matches root package version: {expected}"))?;
    Ok(())
}

fn all(runner: &mut Runner, root: &Path, limits: (u64, u64)) {
    docs(runner, root);
    strict(runner, root);
    core(runner, root);
    tier(runner, root, "tier2", limits);
    tier(runner, root, "tier3", limits);
}

fn build_root(runner: &mut Runner, root: &Path, release: bool) {
    let mut args = vec!["build", "--locked", "-p", "isabelle-rs"];
    if release {
        args.push("--release");
    }
    cargo_step(runner, root, "root build", &args);
}

fn lint(runner: &mut Runner, root: &Path) {
    cargo_step(
        runner,
        root,
        "workspace strict clippy",
        &["clippy", "--locked", "--workspace", "--all-targets", "--", "-D", "warnings"],
    );
}

fn broad(runner: &mut Runner, root: &Path, limits: (u64, u64)) {
    core(runner, root);
    tier(runner, root, "tier2", limits);
    tier(runner, root, "tier3", limits);
}

fn audit(runner: &mut Runner, root: &Path, rustsec_only: bool) {
    let mut audit = cargo_command();
    audit.arg("audit");
    runner.step("RustSec audit", &[], || run_command(audit, "cargo audit", root));
    if rustsec_only {
        return;
    }
    let mut deny = cargo_command();
    deny.args(["deny", "check"]);
    runner.step("cargo deny check", &[], || run_command(deny, "cargo deny check", root));
}

fn release_check(runner: &mut Runner, root: &Path, tag: String) {
    let check = runner.step("version check", &[], || version_check(root, &tag));
    runner.step("release verification", &[check], || {
        let mut nested = Runner::new();
        verify(&mut nested, root);
        if nested.finish() {
            Ok(())
        } else {
            Err(StepError::Protocol {
                operation: "release verification".into(),
                detail: "one or more independent gates failed".into(),
            })
        }
    });
}

pub fn preflight(action: &Action) -> Result<Option<(u64, u64)>, StepError> {
    match action {
        Action::Tier(_) | Action::Broad | Action::All => resource_limits().map(Some),
        _ => Ok(None),
    }
}

fn run_gate(gate: Gate, root: &Path) -> Result<(), StepError> {
    match gate {
        Gate::Links => crate::gates::check_links(root),
        Gate::Snippets => crate::gates::check_snippets(root),
        Gate::Templates => crate::gates::check_templates(root),
        Gate::Firewall => crate::gates::check_firewall(root),
        Gate::Compat => crate::gates::audit_compat(root),
        Gate::PinnedSource => crate::reference::prepare::check_pinned_source(root),
    }
}

fn show_help() -> Result<(), StepError> {
    std::io::stdout()
        .write_all(crate::cli::HELP.as_bytes())
        .map_err(|source| io_error("write xtask help", source))
}

pub fn execute(action: Action, root: &Path, limits: (u64, u64)) -> bool {
    let mut runner = Runner::new();
    match action {
        Action::Help => {
            runner.step("show help", &[], show_help);
        },
        Action::Build(release) => build_root(&mut runner, root, release),
        Action::Check(all_targets) => check(&mut runner, root, all_targets),
        Action::Fmt => format(&mut runner, root),
        Action::Verify => verify(&mut runner, root),
        Action::Lint => lint(&mut runner, root),
        Action::Fast => fast(&mut runner, root),
        Action::Strict => strict(&mut runner, root),
        Action::Checkpoint => checkpoint(&mut runner, root),
        Action::Core => core(&mut runner, root),
        Action::Lib => {
            cargo_step(
                &mut runner,
                root,
                "root library tests",
                &["test", "--locked", "-p", "isabelle-rs", "--lib"],
            );
        },
        Action::Docs => docs(&mut runner, root),
        Action::Gate(gate) => {
            runner.step("repository gate", &[], || run_gate(gate, root));
        },
        Action::Maintenance(options) => {
            runner.step("repository maintenance", &[], || crate::maintenance::run(root, options));
        },
        Action::Supervise(args) => {
            runner.step("bounded supervision", &[], || crate::supervisor::run_cli(root, &args));
        },
        Action::Tier(mode) => tier(&mut runner, root, mode, limits),
        Action::Profile(options) => profile(&mut runner, root, options),
        Action::Reference(options) => {
            runner.step("official reference", &[], || crate::reference::run(root, options));
        },
        Action::Broad => broad(&mut runner, root, limits),
        Action::All => all(&mut runner, root, limits),
        Action::Test(selection, ignored) => test(&mut runner, root, selection, ignored),
        Action::Selftest => {
            cargo_step(&mut runner, root, "xtask selftests", &["test", "--locked", "-p", "xtask"]);
        },
        Action::Rustdoc => {
            cargo_step(
                &mut runner,
                root,
                "root rustdoc",
                &["doc", "--locked", "-p", "isabelle-rs", "--no-deps", "--document-private-items"],
            );
        },
        Action::Audit(rustsec_only) => audit(&mut runner, root, rustsec_only),
        Action::VersionCheck(tag) => {
            runner.step("version check", &[], || version_check(root, &tag));
        },
        Action::ReleaseCheck(tag) => release_check(&mut runner, root, tag),
    }
    runner.finish()
}
