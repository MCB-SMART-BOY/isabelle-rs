//! Fast batch verification — scans and classifies without full processing.
//! For Phase 47: getting actionable data quickly.

#[cfg(test)]
mod fast_verify {
    use std::{path::Path, time::Instant};

    use isabelle_rs::theory::session_builder::SessionBuilder;

    #[test]
    fn test_fast_scan_and_classify() {
        let hol_dir = Path::new("isabelle-source/src/HOL");
        if !hol_dir.exists() {
            eprintln!("Skipping: isabelle-source/src/HOL not found");
            return;
        }

        // Phase 1: Fast scan (just parse headers, no processing)
        let start = Instant::now();
        let mut builder = SessionBuilder::new();
        let count = builder.scan(hol_dir).unwrap();
        let scan_time = start.elapsed();
        eprintln!("Scan: {} theories in {:.1}s", count, scan_time.as_secs_f64());

        // Phase 2: Dependency resolution
        let order = builder.resolve_dependencies();
        eprintln!("DAG: {} theories in order", order.len());

        // Phase 3: Classify — process with accept_all for speed
        let start = Instant::now();
        builder.set_accept_all(true);
        let report = builder.build_with_classifier();
        let build_time = start.elapsed();
        eprintln!("Build+Classify: {:.1}s", build_time.as_secs_f64());

        // Print results
        report.print();

        // Show tier 1 status
        let tier1 = [
            "HOL",
            "Orderings",
            "Set",
            "Fun",
            "Product_Type",
            "Sum_Type",
            "Nat",
            "Int",
            "List",
            "Option",
        ];
        eprintln!("\n=== Tier 1 Core Files ===");
        for name in &tier1 {
            if let Some(r) = report.results.iter().find(|r| r.name == *name) {
                let icon = if r.status.has_verified() { "✅" } else { "❌" };
                eprintln!(
                    "  {} {:>15} [{}] {:.0}% — {} thms",
                    icon,
                    name,
                    r.status.label(),
                    r.status.rate() * 100.0,
                    r.theorem_count
                );
            }
        }

        // Verify basic invariants
        assert!(count > 1000, "Expected >1000 theories, got {}", count);
        assert!(report.total > 0, "No theories processed");

        eprintln!("\nTotal time: {:.1}s", (scan_time + build_time).as_secs_f64());
    }
}
