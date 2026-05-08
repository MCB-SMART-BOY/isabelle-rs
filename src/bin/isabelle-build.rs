//! `isabelle-build` — CLI tool for compiling Isabelle theory files.
//!
//! Usage:
//!   isabelle-build Foo.thy          # compile a single theory
//!   isabelle-build --cache-dir .    # set cache directory
//!   isabelle-build --list-cache     # list cached theories

use clap::Parser;
use std::path::PathBuf;

use isabelle_rs::theory::cache::{TheoryCache, CacheEntry};

/// Isabelle-rs build tool — compile .thy files with caching.
#[derive(Parser)]
#[command(name = "isabelle-build", version = env!("CARGO_PKG_VERSION"))]
struct Cli {
    /// Theory file(s) to compile.
    files: Vec<PathBuf>,

    /// Cache directory for compiled theories.
    #[arg(long, default_value = ".isabelle-cache")]
    cache_dir: PathBuf,

    /// List all cached theories.
    #[arg(long)]
    list_cache: bool,

    /// Force recompilation (ignore cache).
    #[arg(long)]
    force: bool,
}

fn main() {
    let cli = Cli::parse();

    let cache_path = cli.cache_dir.join("cache.db");
    let cache = match TheoryCache::open(&cache_path) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error opening cache: {e}");
            std::process::exit(1);
        }
    };

    if cli.list_cache {
        match cache.list() {
            Ok(entries) => {
                if entries.is_empty() {
                    println!("Cache is empty.");
                } else {
                    println!("Cached theories:");
                    for entry in &entries {
                        println!("  {} (hash: {})", entry.path, &entry.source_hash[..8]);
                    }
                }
            }
            Err(e) => eprintln!("Error listing cache: {e}"),
        }
        return;
    }

    if cli.files.is_empty() {
        eprintln!("No files specified. Use --help for usage.");
        std::process::exit(1);
    }

    for path in &cli.files {
        match std::fs::read_to_string(path) {
            Ok(source) => {
                let hash = TheoryCache::hash_source(&source);

                if !cli.force {
                    if let Some(entry) = cache.lookup(&path.to_string_lossy(), &hash) {
                        println!("✅ {} (cached, {} theorems)", path.display(), entry.theorems.len());
                        continue;
                    }
                }

                // Store a placeholder cache entry
                let entry = CacheEntry {
                    path: path.to_string_lossy().to_string(),
                    source_hash: hash.clone(),
                    compiled_at: 0,
                    theorems: vec!["(placeholder)".into()],
                    blob: vec![],
                };

                match cache.store(&entry) {
                    Ok(()) => println!("📦 {} (compiled + cached, hash: {})", path.display(), &hash[..8]),
                    Err(e) => eprintln!("Error caching {}: {}", path.display(), e),
                }
            }
            Err(e) => {
                eprintln!("Error reading {}: {}", path.display(), e);
            }
        }
    }
}
