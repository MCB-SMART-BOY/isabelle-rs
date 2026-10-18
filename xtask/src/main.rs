use std::env;
use std::path::Path;
use std::process::ExitCode;

use runner::StepError;
use xtask::{cli, runner, supervisor, tasks};

fn execute() -> Result<i32, StepError> {
    let invocation = env::current_dir()
        .map_err(|source| runner::io_error("find invocation directory", source))?;
    let args = env::args_os()
        .skip(1)
        .map(|arg| {
            arg.into_string()
                .map_err(|_| StepError::Input("xtask options must be valid UTF-8".into()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    if let Some(code) = supervisor::run_internal(&args)? {
        return Ok(code);
    }
    let action = cli::parse(&args, &invocation)?;
    let limits = tasks::preflight(&action)?.unwrap_or_default();
    let root =
        Path::new(env!("CARGO_MANIFEST_DIR")).parent().ok_or_else(|| StepError::Protocol {
            operation: "find repository root".into(),
            detail: "xtask manifest has no parent".into(),
        })?;
    if !root.join("Cargo.toml").is_file() {
        return Err(StepError::Input(format!(
            "root manifest does not exist: {}",
            root.join("Cargo.toml").display()
        )));
    }
    if let cli::Action::Supervise(args) = action {
        supervisor::run_cli(root, &args)?;
        return Ok(0);
    }
    Ok(if tasks::execute(action, root, limits) { 0 } else { 1 })
}

fn report_terminal_error(error: impl std::fmt::Display) {
    // The process is already failing and has no remaining recovery channel if stderr is closed.
    let _ = runner::report_line(format_args!("xtask: {error}"));
}

fn main() -> ExitCode {
    match execute() {
        Ok(code) => ExitCode::from(u8::try_from(code).unwrap_or(1)),
        Err(StepError::Input(message)) => {
            report_terminal_error(message);
            ExitCode::from(2)
        },
        Err(StepError::Exit { operation, status }) => {
            report_terminal_error(format_args!("{operation}: {status}"));
            let code = status.code().unwrap_or(1);
            ExitCode::from(u8::try_from(code).unwrap_or(1))
        },
        Err(error) => {
            report_terminal_error(error);
            ExitCode::FAILURE
        },
    }
}
