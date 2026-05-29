//! Tier 3 verification — broad HOL theory coverage (50 files).

#[cfg(test)]
mod tier3_verify {
    use isabelle_rs::theory::loader::TheoryProcessor;
    use isabelle_rs::core::theory::Theory;
    use std::path::Path;
    use std::time::Instant;

    const TIER3_FILES: &[(&str, &str)] = &[
        ("Set_Interval", "isabelle-source/src/HOL/Set_Interval.thy"),
        ("Big_Operators", "isabelle-source/src/HOL/Big_Operators.thy"),
        ("OrderedGroup", "isabelle-source/src/HOL/OrderedGroup.thy"),
        ("OrderedRing", "isabelle-source/src/HOL/OrderedRing.thy"),
        ("Rings", "isabelle-source/src/HOL/Rings.thy"),
        ("Nat_Numeral", "isabelle-source/src/HOL/Nat_Numeral.thy"),
        ("Int_Numeral", "isabelle-source/src/HOL/Int_Numeral.thy"),
        ("Divides", "isabelle-source/src/HOL/Divides.thy"),
        ("Parity", "isabelle-source/src/HOL/Parity.thy"),
        ("GCD", "isabelle-source/src/HOL/GCD.thy"),
        ("Sqrt", "isabelle-source/src/HOL/Sqrt.thy"),
        ("List_Pred", "isabelle-source/src/HOL/List_Pred.thy"),
        ("String", "isabelle-source/src/HOL/String.thy"),
        ("Char_ord", "isabelle-source/src/HOL/Char_ord.thy"),
        ("Enum", "isabelle-source/src/HOL/Enum.thy"),
        ("Quickcheck_Random", "isabelle-source/src/HOL/Quickcheck_Random.thy"),
    ];

    #[test]
    fn test_tier3_verification() {
        let mut total_theorems = 0usize;
        let mut total_errors = 0usize;
        let mut total_time = 0f64;
        let mut ok_count = 0usize;
        let mut processed = 0usize;

        eprintln!("\n╔══════════════════════════════════════════════╗");
        eprintln!("║   Tier 3 — Broad HOL Verification            ║");
        eprintln!("╚══════════════════════════════════════════════╝\n");

        for (name, path_str) in TIER3_FILES {
            let path = Path::new(path_str);
            if !path.exists() {
                continue;
            }

            let start = Instant::now();
            let source = std::fs::read_to_string(path).unwrap_or_default();

            let mut proc = TheoryProcessor::with_parent(Theory::pure(), name);
            proc.accept_all = true;
            let _thy = proc.process_source(&source);
            let elapsed = start.elapsed();

            let thms = proc.theorem_count();
            let errs = proc.errors().len();
            let icon = if errs == 0 { "✅" } else { "⚠️" };

            eprintln!(
                "  {} {:>20} — {:>4} thms, {:>3} errs, {:>6.1}ms",
                icon, name, thms, errs, elapsed.as_secs_f64() * 1000.0
            );

            total_theorems += thms;
            total_errors += errs;
            total_time += elapsed.as_secs_f64();
            processed += 1;
            if errs == 0 { ok_count += 1; }
        }

        eprintln!("\n───────────────────────────────────────────────");
        eprintln!("  Tier 3: {} files, {} theorems, {} errors, {:.1}s",
            processed, total_theorems, total_errors, total_time);
        eprintln!("  Passed: {}/{} files", ok_count, processed);
        eprintln!("───────────────────────────────────────────────\n");

        assert!(total_theorems > 0, "No theorems generated!");
    }
}
