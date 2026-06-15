//! Theory verification classifier — categorizes .thy files by verification status.
//!
//! ## Purpose
//!
//! As isabelle-rs scales from 5 core files to 1,849 full-library verification,
//! we need systematic classification of:
//! - Which files verify successfully (and at what rate)
//! - Which files fail (and why)
//! - Patterns in failures (to guide kernel/method improvements)
//!
//! ## Classification categories
//!
//! | Status | Meaning |
//! |--------|---------|
//! | `FullSuccess` | 100% of sampled lemmas verify |
//! | `PartialSuccess` | Some lemmas verify, some fail |
//! | `SyntaxError` | File cannot be parsed |
//! | `TypeError` | Type checking failure in lemmas |
//! | `ProofFailure` | All lemmas fail proof search |
//! | `Timeout` | File processing exceeds time budget |
//! | `NoLemmas` | File has no verifiable lemmas |

use std::{collections::HashMap, path::PathBuf, time::Duration};

// =========================================================================
// Types
// =========================================================================

/// Verification status for a single theory file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerifyStatus {
    /// All sampled lemmas verified successfully.
    FullSuccess,
    /// Some lemmas verified, some failed.
    PartialSuccess { verified: usize, attempted: usize, failed_names: Vec<String> },
    /// File could not be parsed at all.
    SyntaxError { message: String },
    /// Type checking failed on one or more lemmas.
    TypeError { message: String },
    /// All attempted lemmas failed proof search.
    ProofFailure { attempted: usize },
    /// Processing exceeded time budget.
    Timeout { budget: Duration },
    /// File contains no verifiable lemmas (only definitions/type declarations).
    NoLemmas,
    /// File not found or unreadable.
    IoError { message: String },
}

impl VerifyStatus {
    /// Whether this status indicates any verified lemmas.
    pub fn has_verified(&self) -> bool {
        matches!(self, VerifyStatus::FullSuccess | VerifyStatus::PartialSuccess { .. })
    }

    /// Verification rate as a fraction (0.0 to 1.0).
    pub fn rate(&self) -> f64 {
        match self {
            VerifyStatus::FullSuccess => 1.0,
            VerifyStatus::PartialSuccess { verified, attempted, .. } => {
                if *attempted == 0 {
                    0.0
                } else {
                    *verified as f64 / *attempted as f64
                }
            },
            _ => 0.0,
        }
    }

    /// Short label for reporting.
    pub fn label(&self) -> &'static str {
        match self {
            VerifyStatus::FullSuccess => "OK",
            VerifyStatus::PartialSuccess { .. } => "PARTIAL",
            VerifyStatus::SyntaxError { .. } => "SYNTAX",
            VerifyStatus::TypeError { .. } => "TYPE",
            VerifyStatus::ProofFailure { .. } => "PROOF",
            VerifyStatus::Timeout { .. } => "TIMEOUT",
            VerifyStatus::NoLemmas => "NO-LEMMA",
            VerifyStatus::IoError { .. } => "IO",
        }
    }
}

/// Result of verifying a single theory file.
#[derive(Debug, Clone)]
pub struct VerifyResult {
    /// Theory name
    pub name: String,
    /// Path to the .thy file
    pub path: PathBuf,
    /// Verification status
    pub status: VerifyStatus,
    /// Time taken to process
    pub elapsed: Duration,
    /// Number of theorems produced (if any)
    pub theorem_count: usize,
}

/// Aggregate statistics from a batch verification run.
#[derive(Debug, Clone)]
pub struct VerifyReport {
    /// Total number of files processed
    pub total: usize,
    /// Results categorized by status
    pub results: Vec<VerifyResult>,
    /// Count per status label
    pub counts: HashMap<&'static str, usize>,
    /// Overall verification rate
    pub overall_rate: f64,
    /// Total theorems generated
    pub total_theorems: usize,
    /// Total time
    pub total_time: Duration,
}

impl VerifyReport {
    /// Create a report from a list of results.
    pub fn new(results: Vec<VerifyResult>) -> Self {
        let total = results.len();
        let mut counts: HashMap<&'static str, usize> = HashMap::new();
        let mut total_verified = 0usize;
        let mut total_attempted = 0usize;
        let mut total_theorems = 0usize;
        let mut total_time = Duration::ZERO;

        for r in &results {
            *counts.entry(r.status.label()).or_insert(0) += 1;
            total_theorems += r.theorem_count;
            total_time += r.elapsed;

            match &r.status {
                VerifyStatus::FullSuccess => {
                    total_verified += 1;
                    total_attempted += 1;
                },
                VerifyStatus::PartialSuccess { verified, attempted, .. } => {
                    total_verified += verified;
                    total_attempted += attempted;
                },
                _ => {},
            }
        }

        let overall_rate =
            if total_attempted == 0 { 0.0 } else { total_verified as f64 / total_attempted as f64 };

        VerifyReport { total, results, counts, overall_rate, total_theorems, total_time }
    }

    /// Print a human-readable report.
    pub fn print(&self) {
        println!("\n╔══════════════════════════════════════════════════════╗");
        println!("║        Isabelle-rs Verification Report               ║");
        println!("╠══════════════════════════════════════════════════════╣");
        println!("║ Files processed:  {:>6}                              ║", self.total);
        println!(
            "║ Total time:       {:>8.2}s                           ║",
            self.total_time.as_secs_f64()
        );
        println!("║ Total theorems:   {:>6}                              ║", self.total_theorems);
        println!(
            "║ Overall rate:     {:>7.1}%                            ║",
            self.overall_rate * 100.0
        );
        println!("╠══════════════════════════════════════════════════════╣");

        let order = ["OK", "PARTIAL", "TIMEOUT", "PROOF", "TYPE", "SYNTAX", "NO-LEMMA", "IO"];
        for label in &order {
            if let Some(count) = self.counts.get(label) {
                let bar = "█".repeat((*count as f64 / self.total as f64 * 20.0) as usize);
                println!("║ {:>8}: {:>4}  {:<20} ║", label, count, bar);
            }
        }
        println!("╚══════════════════════════════════════════════════════╝");
    }

    /// Print a summary of the top failing files.
    pub fn print_failures(&self, top_n: usize) {
        println!("\n--- Top {} Failing Files ---", top_n);
        let mut failures: Vec<&VerifyResult> = self
            .results
            .iter()
            .filter(|r| !matches!(r.status, VerifyStatus::FullSuccess | VerifyStatus::NoLemmas))
            .collect();
        failures.sort_by(|a, b| {
            a.status.rate().partial_cmp(&b.status.rate()).unwrap_or(std::cmp::Ordering::Equal)
        });

        for (i, r) in failures.iter().take(top_n).enumerate() {
            let rate_pct = r.status.rate() * 100.0;
            let label = r.status.label();
            println!(
                "  {:>3}. [{:>7}] {:>5.1}% — {} ({})",
                i + 1,
                label,
                rate_pct,
                r.name,
                r.path.display(),
            );
        }
    }

    /// Export results as CSV for further analysis.
    pub fn to_csv(&self) -> String {
        let mut csv = String::from("name,status,rate,theorem_count,elapsed_ms,path\n");
        for r in &self.results {
            csv.push_str(&format!(
                "{},{},{:.4},{},{:.0},{}\n",
                r.name,
                r.status.label(),
                r.status.rate(),
                r.theorem_count,
                r.elapsed.as_millis(),
                r.path.display(),
            ));
        }
        csv
    }
}
