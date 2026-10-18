//! One-shot legacy HOL diagnostic worker. Use cargo xtask profile for hard limits.

use std::{io, path::PathBuf, process::ExitCode, thread};

use clap::{ArgGroup, Parser};
use isabelle_rs::hol::diagnostics::{
    self, DIAGNOSTIC_STACK_BYTES, DiagnosticRequest, ManifestMode,
};

#[derive(Parser)]
#[command(group(ArgGroup::new("manifest").required(true).args(["manifest_out", "manifest_in"])))]
struct Cli {
    #[arg(long)]
    source_root: PathBuf,
    #[arg(long, default_value = "theories")]
    context_root: PathBuf,
    #[arg(long)]
    theory: String,
    #[arg(long)]
    lemma: String,
    #[arg(long)]
    manifest_out: Option<PathBuf>,
    #[arg(long)]
    manifest_in: Option<PathBuf>,
    #[arg(long)]
    auto_limit: Option<usize>,
}

fn main() -> ExitCode {
    let args = Cli::parse();
    let mode = match (args.manifest_out, args.manifest_in) {
        (Some(path), None) => ManifestMode::Create(path),
        (None, Some(path)) => ManifestMode::Replay(path),
        _ => return ExitCode::from(2),
    };
    let request = DiagnosticRequest {
        source_root: args.source_root,
        context_root: args.context_root,
        theory: args.theory,
        lemma: args.lemma,
        mode,
        auto_limit: args.auto_limit,
    };
    let worker = thread::Builder::new()
        .name("hol-diagnostic".into())
        .stack_size(DIAGNOSTIC_STACK_BYTES)
        .spawn(move || diagnostics::run(&request, &mut io::stdout().lock()));
    let result = match worker {
        Ok(worker) => worker.join(),
        Err(error) => {
            eprintln!("failed to start diagnostic worker: {error}");
            return ExitCode::FAILURE;
        },
    };
    match result {
        Ok(Ok(())) => ExitCode::SUCCESS,
        Ok(Err(error)) => {
            eprintln!("{error}");
            ExitCode::from(if error.is_input() { 2 } else { 1 })
        },
        Err(_) => {
            eprintln!("diagnostic worker panicked");
            ExitCode::FAILURE
        },
    }
}
