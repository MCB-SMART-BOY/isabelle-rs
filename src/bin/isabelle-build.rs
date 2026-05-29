//! `isabelle-build` — CLI tool for compiling Isabelle theory files.
//!
//! Usage:
//!   isabelle-build Foo.thy              # compile a single theory
//!   isabelle-build --dir theories/HOL/  # batch compile all .thy files in directory
//!   isabelle-build --stats              # show compilation statistics

use clap::Parser;
use std::path::PathBuf;

use isabelle_rs::core::theory::Theory;
use isabelle_rs::theory::loader::TheoryProcessor;
use isabelle_rs::theory::session_builder::SessionBuilder;

/// Isabelle-rs build tool — compile .thy files.
#[derive(Parser)]
#[command(name = "isabelle-build", version = env!("CARGO_PKG_VERSION"))]
struct Cli {
    /// Theory file(s) to compile.
    files: Vec<PathBuf>,

    /// Batch compile all .thy files in this directory.
    #[arg(long)]
    dir: Option<PathBuf>,

    /// Show statistics after compilation.
    #[arg(long)]
    stats: bool,

    /// Quiet mode (only show errors).
    #[arg(long)]
    quiet: bool,
}

fn main() {
    let cli = Cli::parse();

    if let Some(dir) = &cli.dir {
        batch_compile(dir, cli.quiet);
        return;
    }

    if cli.files.is_empty() {
        eprintln!("No files specified. Use --help for usage.");
        eprintln!("  isabelle-build Foo.thy          # compile one file");
        eprintln!("  isabelle-build --dir theories/  # batch compile directory");
        std::process::exit(1);
    }

    let mut total_ok = 0;
    let mut total_fail = 0;
    let mut total_thms = 0;

    for path in &cli.files {
        match compile_file(path) {
            Ok(thms) => {
                total_ok += 1;
                total_thms += thms;
                if !cli.quiet {
                    println!("✅ {} ({} theorems)", path.display(), thms);
                }
            }
            Err(errs) => {
                total_fail += 1;
                eprintln!("❌ {} ({} errors)", path.display(), errs.len());
                if !cli.quiet {
                    for err in &errs[..errs.len().min(5)] {
                        eprintln!("   {}", err);
                    }
                }
            }
        }
    }

    if cli.stats || cli.files.len() > 1 {
        println!(
            "Total: {} ok, {} failed, {} theorems",
            total_ok, total_fail, total_thms
        );
    }
}

fn compile_file(path: &PathBuf) -> Result<usize, Vec<String>> {
    let parent = Theory::pure();
    let file_name = path.file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("Unknown");
    let mut proc = TheoryProcessor::with_parent(parent, file_name);
    let source = std::fs::read_to_string(path)
        .map_err(|e| vec![format!("Cannot read: {e}")])?;
    let _thy = proc.process_source(&source);
    if proc.errors().is_empty() {
        Ok(proc.theorem_count())
    } else {
        Err(proc.errors().to_vec())
    }
}

fn batch_compile(dir: &PathBuf, quiet: bool) {
    let mut builder = SessionBuilder::new();
    match builder.scan(dir) {
        Ok(count) => {
            if !quiet {
                println!("Found {} .thy files in {}", count, dir.display());
            }
            let order = builder.resolve_dependencies();
            if !quiet {
                println!("Resolved {} theories in load order", order.len());
            }

            let result = builder.build();
            println!("╔══════════════════════════════════════╗");
            println!("║  Isabelle-rs Build Report            ║");
            println!("╠══════════════════════════════════════╣");
            println!("║  Total files:     {:<4}               ║", result.total);
            println!("║  Succeeded:       {:<4}               ║", result.loaded);
            println!("║  Failed:          {:<4}               ║", result.failed);
            println!("║  Theorems:        {:<4}               ║", result.theorems);
            println!("╚══════════════════════════════════════╝");

            if !result.error_messages.is_empty() && !quiet {
                println!("\nErrors:");
                for err in &result.error_messages[..result.error_messages.len().min(10)] {
                    println!("  {}", err);
                }
                if result.error_messages.len() > 10 {
                    println!("  ... and {} more", result.error_messages.len() - 10);
                }
            }
        }
        Err(e) => {
            eprintln!("Failed to scan {}: {}", dir.display(), e);
            std::process::exit(1);
        }
    }
}
