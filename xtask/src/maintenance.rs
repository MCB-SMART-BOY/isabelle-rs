//! Explicit source maintenance, checkout builds, and release packaging.
mod package;

use std::path::{Path, PathBuf};

use crate::cargo::{cargo_command, root_package_id};
use crate::hooks::HookEvent;
use crate::runner::{StepError, report_line, run_command};

pub struct InstallOptions {
    pub is_release: bool,
    pub is_check: bool,
    pub directory: Option<PathBuf>,
}

pub enum Maintenance {
    Install(InstallOptions),
    Fix { should_apply: bool },
    Package(PathBuf),
    Hook { event: HookEvent, directory: PathBuf },
}

pub fn parse(args: &[String], invocation: &Path) -> Result<Maintenance, StepError> {
    match args.split_first() {
        Some((command, rest)) if command == "install" => {
            parse_install(rest, invocation).map(Maintenance::Install)
        },
        Some((command, rest)) if command == "fix" => match rest {
            [mode] if mode == "check" => Ok(Maintenance::Fix { should_apply: false }),
            [mode] if mode == "apply" => Ok(Maintenance::Fix { should_apply: true }),
            _ => Err(StepError::Input("fix requires exactly check or apply".into())),
        },
        Some((command, rest)) if command == "package" => match rest {
            [flag, directory] if flag == "--artifacts" => {
                Ok(Maintenance::Package(resolve_path(directory, invocation)?))
            },
            _ => Err(StepError::Input("package requires --artifacts PATH".into())),
        },
        Some((command, rest)) if command == "hook" => Ok(Maintenance::Hook {
            event: HookEvent::parse(rest)?,
            directory: invocation.to_path_buf(),
        }),
        _ => Err(StepError::Input("expected install, fix, package, or hook".into())),
    }
}

fn resolve_path(value: &str, invocation: &Path) -> Result<PathBuf, StepError> {
    if value.is_empty() || value.starts_with("--") {
        return Err(StepError::Input("directory must not be empty or an option".into()));
    }
    Ok(invocation.join(value))
}

fn parse_install(args: &[String], invocation: &Path) -> Result<InstallOptions, StepError> {
    let mut options = InstallOptions { is_release: false, is_check: false, directory: None };
    let mut arguments = args.iter();
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--release" if !options.is_release => options.is_release = true,
            "--check" if !options.is_check => options.is_check = true,
            "--dir" if options.directory.is_none() => {
                let value = arguments
                    .next()
                    .ok_or_else(|| StepError::Input("missing value for --dir".into()))?;
                options.directory = Some(resolve_path(value, invocation)?);
            },
            _ => {
                return Err(StepError::Input(format!(
                    "unknown or duplicate install option: {argument}"
                )));
            },
        }
    }
    Ok(options)
}

fn run_install(root: &Path, options: InstallOptions) -> Result<(), StepError> {
    let checkout = options.directory.as_deref().unwrap_or(root);
    let checkout = checkout.canonicalize().map_err(|source| {
        crate::runner::io_error(format!("resolve install checkout {}", checkout.display()), source)
    })?;
    root_package_id(&checkout)?;
    let mut command = cargo_command();
    command.args([
        if options.is_check { "check" } else { "build" },
        "--locked",
        "-p",
        "isabelle-rs",
    ]);
    if options.is_release && !options.is_check {
        command.arg("--release");
    }
    report_line(format_args!(
        "Using existing checkout {}; no toolchain install or Git update",
        checkout.display()
    ))?;
    run_command(command, "build existing Isabelle-rs checkout", &checkout)
}

fn run_fix(root: &Path, should_apply: bool) -> Result<(), StepError> {
    if !should_apply {
        if crate::tasks::execute(crate::cli::Action::Fast, root, (0, 0)) {
            return Ok(());
        }
        return Err(StepError::Protocol {
            operation: "fix check".into(),
            detail: "read-only checks failed".into(),
        });
    }
    for arguments in [
        &["fix", "--locked", "--allow-dirty", "--allow-staged"][..],
        &["fmt", "--all"][..],
        &["clippy", "--locked", "--fix", "--allow-dirty", "--allow-staged"][..],
        &["check", "--locked", "-p", "isabelle-rs"][..],
    ] {
        let mut command = cargo_command();
        command.args(arguments);
        run_command(command, "apply explicit source maintenance", root)?;
    }
    Ok(())
}

pub fn run(root: &Path, options: Maintenance) -> Result<(), StepError> {
    match options {
        Maintenance::Install(options) => run_install(root, options),
        Maintenance::Fix { should_apply } => run_fix(root, should_apply),
        Maintenance::Package(directory) => package::create_archives(&directory),
        Maintenance::Hook { event, directory } => crate::hooks::run(event, &directory),
    }
}
