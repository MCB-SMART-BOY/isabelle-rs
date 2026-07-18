//! Legacy theory verification classifier — categorizes .thy files by the
//! transitional `is_strict_closed_proved()` metric.
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
//! | `SyntaxError` | A parse error prevented complete file processing |
//! | `TypeError` | Type checking failure in lemmas |
//! | `ProofFailure` | All lemmas fail proof search |
//! | `Timeout` | File processing exceeds time budget |
//! | `NoLemmas` | File has no verifiable lemmas |
//! | `IoError` | File not found or unreadable |
//! | `InternalError` | Outer panic prevented attempt-count recovery |

use std::{collections::HashMap, path::PathBuf, time::Duration};

// =========================================================================
// Types
// =========================================================================

/// Verification status for a single theory file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerifyStatus {
    /// All sampled lemmas reached the transitional strict-closed predicate.
    FullSuccess { attempted: usize },
    /// Some lemmas reached the transitional strict-closed predicate.
    PartialSuccess { verified: usize, attempted: usize, failed_names: Vec<String> },
    /// One or more parse errors prevented complete file processing.
    SyntaxError { message: String, attempted: usize },
    /// Type checking or proof-context certification failed on one or more lemmas.
    TypeError { message: String, attempted: usize },
    /// All attempted lemmas failed proof search.
    ProofFailure { attempted: usize },
    /// Processing exceeded time budget.
    Timeout { budget: Duration },
    /// File contains no verifiable lemmas (only definitions/type declarations).
    NoLemmas,
    /// File not found or unreadable.
    IoError { message: String },
    /// An outer processing panic prevented recovery of an attempt count.
    InternalError { message: String },
}

impl VerifyStatus {
    /// Whether this status includes any transitional strict-closed lemmas.
    pub fn has_verified(&self) -> bool {
        matches!(self, VerifyStatus::FullSuccess { .. } | VerifyStatus::PartialSuccess { .. })
    }

    /// Transitional strict-closed rate as a fraction (0.0 to 1.0).
    pub fn rate(&self) -> f64 {
        match self {
            VerifyStatus::FullSuccess { attempted } => {
                if *attempted == 0 {
                    0.0
                } else {
                    1.0
                }
            },
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
            VerifyStatus::FullSuccess { .. } => "OK",
            VerifyStatus::PartialSuccess { .. } => "PARTIAL",
            VerifyStatus::SyntaxError { .. } => "SYNTAX",
            VerifyStatus::TypeError { .. } => "TYPE",
            VerifyStatus::ProofFailure { .. } => "PROOF",
            VerifyStatus::Timeout { .. } => "TIMEOUT",
            VerifyStatus::InternalError { .. } => "INTERNAL",
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
    /// Overall transitional strict-closed rate
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
                VerifyStatus::FullSuccess { attempted } => {
                    total_verified += attempted;
                    total_attempted += attempted;
                },
                VerifyStatus::PartialSuccess { verified, attempted, .. } => {
                    total_verified += verified;
                    total_attempted += attempted;
                },
                VerifyStatus::ProofFailure { attempted } => {
                    total_attempted += attempted;
                },
                VerifyStatus::SyntaxError { attempted, .. } => {
                    total_attempted += attempted;
                },
                VerifyStatus::TypeError { attempted, .. } => {
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
        println!("║   Isabelle-rs Transitional Verification Report       ║");
        println!("╠══════════════════════════════════════════════════════╣");
        println!("║ Files processed:  {:>6}                              ║", self.total);
        println!(
            "║ Total time:       {:>8.2}s                           ║",
            self.total_time.as_secs_f64()
        );
        println!("║ Total theorems:   {:>6}                              ║", self.total_theorems);
        println!(
            "║ Transitional:    {:>7.1}%                            ║",
            self.overall_rate * 100.0
        );
        println!("╠══════════════════════════════════════════════════════╣");

        let order =
            ["OK", "PARTIAL", "TIMEOUT", "INTERNAL", "PROOF", "TYPE", "SYNTAX", "NO-LEMMA", "IO"];
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
            .filter(|r| {
                !matches!(r.status, VerifyStatus::FullSuccess { .. } | VerifyStatus::NoLemmas)
            })
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

#[cfg(test)]
mod tests {
    use super::*;

    fn result(name: &str, status: VerifyStatus) -> VerifyResult {
        VerifyResult {
            name: name.to_string(),
            path: PathBuf::from(format!("{name}.thy")),
            status,
            elapsed: Duration::ZERO,
            theorem_count: 0,
        }
    }

    #[test]
    fn overall_rate_weights_all_attempted_lemmas() {
        let report = VerifyReport::new(vec![
            result("large", VerifyStatus::FullSuccess { attempted: 100 }),
            result("failed", VerifyStatus::ProofFailure { attempted: 1 }),
        ]);

        assert!((report.overall_rate - 100.0 / 101.0).abs() < f64::EPSILON);
    }

    #[test]
    fn overall_rate_includes_attempts_before_syntax_failure() {
        let report = VerifyReport::new(vec![
            result("proved", VerifyStatus::FullSuccess { attempted: 1 }),
            result(
                "malformed",
                VerifyStatus::SyntaxError { message: "syntax error".into(), attempted: 1 },
            ),
        ]);

        assert!((report.overall_rate - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn overall_rate_includes_every_counted_failure_attempt() {
        let report = VerifyReport::new(vec![
            result("full", VerifyStatus::FullSuccess { attempted: 3 }),
            result(
                "partial",
                VerifyStatus::PartialSuccess {
                    verified: 1,
                    attempted: 2,
                    failed_names: vec!["partial_failure".into()],
                },
            ),
            result(
                "type",
                VerifyStatus::TypeError {
                    message: "proof-context certification failed".into(),
                    attempted: 4,
                },
            ),
            result(
                "syntax",
                VerifyStatus::SyntaxError { message: "parse error".into(), attempted: 5 },
            ),
            result("proof", VerifyStatus::ProofFailure { attempted: 6 }),
        ]);

        assert!((report.overall_rate - 4.0 / 20.0).abs() < f64::EPSILON);
    }
}
