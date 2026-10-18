//! Fail-closed source-to-kernel compiler.

use std::{path::Path, path::PathBuf, process::ExitCode};

use clap::Parser;
use isabelle_rs::{
    hol::sampled_true_i::{SampledTrueIError, compile_sampled_true_i},
    isar::source_ast::SourceId,
    theory::trusted_loader::{TrustedLoadError, compile_trusted_source},
};
use thiserror::Error;

#[derive(Parser)]
#[command(name = "isabelle-build", version = env!("CARGO_PKG_VERSION"))]
struct Cli {
    /// One theory file to compile through the strict kernel.
    file: PathBuf,
    /// Audit the narrow HOL.TrueI projection, not the complete HOL theory.
    #[arg(long = "sampled-hol-true-i")]
    is_sampled_hol_true_i: bool,
}

#[derive(Debug, Error)]
enum BuildError {
    /// User-fixable input path or file contents.
    #[error(
        "E0401: failed to read theory `{path}`: {source}\n  = help: check the path and permissions"
    )]
    Read { path: PathBuf, source: std::io::Error },
    /// Rejected whole-file source, preserving the compiler cause.
    #[error(transparent)]
    WholeFile(#[from] TrustedLoadError),
    /// Rejected audited projection, preserving the compiler cause.
    #[error(transparent)]
    Projection(#[from] SampledTrueIError),
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match compile_file(&cli.file, cli.is_sampled_hol_true_i) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        },
    }
}

fn compile_file(path: &Path, is_sampled_hol_true_i: bool) -> Result<(), BuildError> {
    let source = std::fs::read_to_string(path)
        .map_err(|source| BuildError::Read { path: path.to_path_buf(), source })?;
    let source_id = SourceId::new(path.display().to_string());
    let result = if is_sampled_hol_true_i {
        compile_sampled_true_i(&source, source_id)?
    } else {
        compile_trusted_source(&source, source_id)?
    };
    if is_sampled_hol_true_i {
        println!("Audited HOL.TrueI projection only; the complete theory was not compiled.");
    }
    println!("KernelTrustedClosed: {} ({})", result.theorem.name().as_str(), path.display());
    Ok(())
}
