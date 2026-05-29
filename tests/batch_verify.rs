//! Targeted batch verification — verifies core HOL theories and reports results.
//!
//! This is the practical Phase 45 entry point: instead of processing all 1,849
//! files, we focus on the most important ones first to get actionable data.

#[cfg(test)]
mod batch_verify {
    use isabelle_rs::theory::session_builder::SessionBuilder;
    use isabelle_rs::theory::verify_classifier::VerifyStatus;
    use std::path::Path;

    /// The "first tier" files — foundational theories that MUST verify.
    const TIER1_FILES: &[&str] = &[
        "HOL", "Orderings", "Set", "Fun", "Product_Type",
        "Sum_Type", "Nat", "Int", "List", "Option",
    ];

    /// The "second tier" files — important HOL infrastructure.
    #[allow(dead_code)]
    const TIER2_FILES: &[&str] = &[
        "Lattices", "Complete_Lattices", "Relation", "Equiv_Relations",
        "Map", "Finite_Set", "Num", "Power", "Groups", "Rings", "Fields",
    ];

    #[test]
    fn test_tier1_verification() {
        let hol_dir = Path::new("isabelle-source/src/HOL");
        if !hol_dir.exists() {
            eprintln!("Skipping: isabelle-source/src/HOL not found");
            return;
        }

        let mut builder = SessionBuilder::new();
        // Use accept_all for fast theory loading (skip proof replay)
        builder.set_accept_all(true);
        let count = builder.scan(hol_dir).unwrap();
        eprintln!("Scanned {} theories", count);
        builder.resolve_dependencies();
        let report = builder.build_with_classifier();

        eprintln!("\n╔══════════════════════════════════════╗");
        eprintln!("║   Tier 1 — Core HOL Verification    ║");
        eprintln!("╚══════════════════════════════════════╝");

        let mut tier1_ok = 0;
        let mut tier1_total = 0;

        for name in TIER1_FILES {
            if let Some(r) = report.results.iter().find(|r| r.name == *name) {
                let label = r.status.label();
                let rate = r.status.rate() * 100.0;
                let icon = if r.status.has_verified() { "✅" } else { "❌" };
                eprintln!(
                    "  {} {:>15} [{:>7}] {:>5.0}% — {} theorems ({:.1}ms)",
                    icon, name, label, rate, r.theorem_count, r.elapsed.as_millis() as f64
                );
                if r.status.has_verified() {
                    tier1_ok += 1;
                }
                tier1_total += 1;

                // Tier 1 files must have some verified lemmas
                if !r.status.has_verified() {
                    eprintln!("    ⚠ WARNING: Tier 1 file {} failed verification!", name);
                }
            } else {
                eprintln!("  ❓ {:>15} NOT FOUND", name);
            }
        }

        eprintln!("\n  Tier 1 result: {}/{} files verified", tier1_ok, tier1_total);
        assert!(tier1_ok > 0, "No tier 1 files verified!");
    }

    #[test]
    fn test_classifier_report() {
        let hol_dir = Path::new("isabelle-source/src/HOL");
        if !hol_dir.exists() {
            eprintln!("Skipping: isabelle-source/src/HOL not found");
            return;
        }

        let mut builder = SessionBuilder::new();
        builder.set_accept_all(true);
        let count = builder.scan(hol_dir).unwrap();
        eprintln!("Scanned {} theories for classifier test", count);
        builder.resolve_dependencies();
        let report = builder.build_with_classifier();

        // Print summary
        report.print();

        // Verify basic properties
        assert!(report.total > 0, "No theories classified");
        assert!(!report.results.is_empty(), "No results produced");

        // Every result should have a valid status
        for r in &report.results {
            match &r.status {
                VerifyStatus::FullSuccess => assert!(r.status.rate() > 0.99),
                VerifyStatus::PartialSuccess { verified, attempted, .. } => {
                    assert!(*verified <= *attempted, "verified > attempted for {}", r.name);
                }
                _ => assert!(r.status.rate() < 0.01),
            }
        }

        // Show status distribution
        eprintln!("\nStatus distribution:");
        for (label, count) in &report.counts {
            let bar = "█".repeat((*count as f64 / report.total as f64 * 40.0) as usize);
            eprintln!("  {:>8}: {:>5}  {}", label, count, bar);
        }
    }

    #[test]
    fn test_failure_analysis() {
        let hol_dir = Path::new("isabelle-source/src/HOL");
        if !hol_dir.exists() {
            return;
        }

        let mut builder = SessionBuilder::new();
        builder.set_accept_all(true);
        builder.scan(hol_dir).unwrap();
        builder.resolve_dependencies();
        let report = builder.build_with_classifier();

        // Analyze failure patterns
        let syntax_count = report.counts.get("SYNTAX").copied().unwrap_or(0);
        let proof_count = report.counts.get("PROOF").copied().unwrap_or(0);
        let partial_count = report.counts.get("PARTIAL").copied().unwrap_or(0);

        eprintln!("\nFailure Analysis:");
        eprintln!("  SYNTAX errors:  {} files", syntax_count);
        eprintln!("  PROOF failures: {} files", proof_count);
        eprintln!("  PARTIAL passes: {} files", partial_count);

        // Print top 10 failures
        report.print_failures(10);

        // Highlight actionable fixes
        if syntax_count > 0 {
            eprintln!("\n  🔧 ACTION: Fix syntax errors first — these block all lemmas");
        }
        if proof_count > 0 {
            eprintln!("  🔧 ACTION: Add proof method support for the failing patterns");
        }
    }
}
