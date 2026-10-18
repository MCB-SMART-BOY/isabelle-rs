//! Legacy HOL diagnostic worker. Use cargo xtask supervise for hard limits.

use std::{process::ExitCode, thread};

use clap::Parser;
use isabelle_rs::hol::{
    diagnostics::DIAGNOSTIC_STACK_BYTES,
    theory_graph::scale_diagnostics::{self, ScaleMode},
};

#[derive(Parser)]
#[command(about = "Run a legacy HOL diagnostic (supervise with cargo xtask supervise)")]
struct Cli {
    /// Workload to run; see --help for all modes.
    #[arg(value_enum)]
    mode: ScaleMode,
}

fn main() -> ExitCode {
    let args = Cli::parse();
    let worker = thread::Builder::new()
        .name("hol-scale-diagnostic".into())
        .stack_size(DIAGNOSTIC_STACK_BYTES)
        .spawn(move || scale_diagnostics::run(args.mode));
    let result = match worker {
        Ok(worker) => worker.join(),
        Err(error) => {
            eprintln!("failed to start scale diagnostic worker: {error}");
            return ExitCode::FAILURE;
        },
    };
    match result {
        Ok(Ok(())) => ExitCode::SUCCESS,
        Ok(Err(error)) => {
            eprintln!("{error}");
            ExitCode::from(2)
        },
        Err(_) => {
            eprintln!("scale diagnostic worker panicked");
            ExitCode::FAILURE
        },
    }
}
