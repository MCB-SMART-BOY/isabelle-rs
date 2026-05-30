//! Quick verification — processes only 10 core HOL theories.
//! Gives fast, actionable data for Phase 47.

#[cfg(test)]
mod quick_verify {
    use isabelle_rs::theory::loader::TheoryProcessor;
    use isabelle_rs::core::theory::Theory;
    use std::path::Path;
    
    use std::time::Instant;

    const CORE_FILES: &[(&str, &str)] = &[
        ("HOL", "isabelle-source/src/HOL/HOL.thy"),
        ("Orderings", "isabelle-source/src/HOL/Orderings.thy"),
        ("Set", "isabelle-source/src/HOL/Set.thy"),
        ("Fun", "isabelle-source/src/HOL/Fun.thy"),
        ("Product_Type", "isabelle-source/src/HOL/Product_Type.thy"),
        ("Nat", "isabelle-source/src/HOL/Nat.thy"),
        ("List", "isabelle-source/src/HOL/List.thy"),
        ("Option", "isabelle-source/src/HOL/Option.thy"),
        ("Lattices", "isabelle-source/src/HOL/Lattices.thy"),
        ("Groups", "isabelle-source/src/HOL/Groups.thy"),
    ];

    #[test]
    fn test_quick_verify_10_core() {
        let mut total_theorems = 0usize;
        let mut total_errors = 0usize;
        let mut total_time = 0f64;
        let mut ok_count = 0usize;

        eprintln!("\n╔══════════════════════════════════════════════╗");
        eprintln!("║   Quick Verify — 10 Core HOL Theories        ║");
        eprintln!("╚══════════════════════════════════════════════╝\n");

        for (name, path_str) in CORE_FILES {
            let path = Path::new(path_str);
            if !path.exists() {
                eprintln!("  ❓ {:>15} — file not found", name);
                continue;
            }

            let start = Instant::now();
            let source = match std::fs::read_to_string(path) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("  ❌ {:>15} — read error: {}", name, e);
                    total_errors += 1;
                    continue;
                }
            };

            let mut proc = TheoryProcessor::with_parent(Theory::pure(), name);
            proc.accept_all = true; // Full mode: accept + verify
            let _thy = proc.process_source(&source);
            let elapsed = start.elapsed();

            let thms = proc.theorem_count();
            let errs = proc.errors().len();
            let icon = if errs == 0 { "✅" } else { "⚠️" };

            eprintln!(
                "  {} {:>15} — {:>4} thms, {:>3} errs, {:>6.1}ms",
                icon, name, thms, errs, elapsed.as_secs_f64() * 1000.0
            );

            total_theorems += thms;
            total_errors += errs;
            total_time += elapsed.as_secs_f64();

            if errs == 0 {
                ok_count += 1;
            } else {
                // Show first few errors
                for (i, e) in proc.errors().iter().take(3).enumerate() {
                    let short: String = e.chars().take(100).collect();
                    eprintln!("       {} {}", i + 1, short);
                }
            }
        }

        eprintln!("\n───────────────────────────────────────────────");
        eprintln!("  Total: {} theorems, {} errors, {:.1}s",
            total_theorems, total_errors, total_time);
        eprintln!("  Passed: {}/{} files", ok_count, CORE_FILES.len());
        eprintln!("───────────────────────────────────────────────\n");

        // At minimum, some core files should verify
        assert!(total_theorems > 0, "No theorems generated from core files!");
    }
}
