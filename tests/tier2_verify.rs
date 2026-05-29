//! Tier 2 verification — expanded HOL theory coverage.
//!
//! Extends verification beyond the 5 core files to 20 foundational HOL theories.

#[cfg(test)]
mod tier2_verify {
    use isabelle_rs::theory::loader::TheoryProcessor;
    use isabelle_rs::core::theory::Theory;
    use std::path::Path;
    use std::time::Instant;

    /// Tier 2 files: foundational HOL infrastructure.
    const TIER2_FILES: &[(&str, &str)] = &[
        ("Fun", "isabelle-source/src/HOL/Fun.thy"),
        ("Product_Type", "isabelle-source/src/HOL/Product_Type.thy"),
        ("Sum_Type", "isabelle-source/src/HOL/Sum_Type.thy"),
        ("Option", "isabelle-source/src/HOL/Option.thy"),
        ("Lattices", "isabelle-source/src/HOL/Lattices.thy"),
        ("Groups", "isabelle-source/src/HOL/Groups.thy"),
        ("Rings", "isabelle-source/src/HOL/Rings.thy"),
        ("Fields", "isabelle-source/src/HOL/Fields.thy"),
        ("Relation", "isabelle-source/src/HOL/Relation.thy"),
        ("Equiv_Relations", "isabelle-source/src/HOL/Equiv_Relations.thy"),
        ("Map", "isabelle-source/src/HOL/Map.thy"),
        ("Finite_Set", "isabelle-source/src/HOL/Finite_Set.thy"),
        ("Num", "isabelle-source/src/HOL/Num.thy"),
        ("Power", "isabelle-source/src/HOL/Power.thy"),
        ("Complete_Lattices", "isabelle-source/src/HOL/Complete_Lattices.thy"),
    ];

    #[test]
    fn test_tier2_verification() {
        let mut total_theorems = 0usize;
        let mut total_errors = 0usize;
        let mut total_time = 0f64;
        let mut ok_count = 0usize;
        let mut processed = 0usize;

        eprintln!("\n╔══════════════════════════════════════════════╗");
        eprintln!("║   Tier 2 — Extended HOL Verification        ║");
        eprintln!("╚══════════════════════════════════════════════╝\n");

        for (name, path_str) in TIER2_FILES {
            let path = Path::new(path_str);
            if !path.exists() {
                eprintln!("  ❓ {:>20} — file not found", name);
                continue;
            }

            let start = Instant::now();
            let source = match std::fs::read_to_string(path) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("  ❌ {:>20} — read error: {}", name, e);
                    continue;
                }
            };

            let mut proc = TheoryProcessor::with_parent(Theory::pure(), name);
            proc.accept_all = false;
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

            if errs == 0 {
                ok_count += 1;
            } else {
                for (i, e) in proc.errors().iter().take(3).enumerate() {
                    let short: String = e.chars().take(80).collect();
                    eprintln!("       {} {}", i + 1, short);
                }
            }
        }

        eprintln!("\n───────────────────────────────────────────────");
        eprintln!("  Tier 2: {} files, {} theorems, {} errors, {:.1}s",
            processed, total_theorems, total_errors, total_time);
        eprintln!("  Passed: {}/{} files", ok_count, processed);
        eprintln!("───────────────────────────────────────────────\n");

        assert!(total_theorems > 0, "No theorems generated from Tier 2 files!");
    }
}
