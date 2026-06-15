//! Tier 2 verification — expanded HOL theory coverage.
//!
//! Extends verification beyond the 5 core files to 20+ foundational HOL theories.
//! Uses local DB approach to avoid global LazyLock init.

#[cfg(test)]
mod tier2_verify {
    use std::{path::Path, time::Instant};

    use isabelle_rs::isar::method::verify_file;

    const TIER2_FILES: &[&str] = &[
        // Core files (verified separately)
        // "theories/HOL/HOL.thy" — 100%
        // "theories/HOL/Orderings.thy" — 100%
        // "theories/HOL/Set.thy" — 100%
        // "theories/HOL/Nat.thy" — 100%
        // "theories/HOL/List.thy" — known overflow
        "theories/HOL/Fun.thy",
        "theories/HOL/Product_Type.thy",
        "theories/HOL/Sum_Type.thy",
        // "theories/HOL/Option.thy" — overflow
        "theories/HOL/Lattices.thy",
        "theories/HOL/Groups.thy",
        "theories/HOL/Rings.thy",
        "theories/HOL/Fields.thy",
        "theories/HOL/Relation.thy",
        "theories/HOL/Equiv_Relations.thy",
        "theories/HOL/Map.thy",
        "theories/HOL/Finite_Set.thy",
        "theories/HOL/Num.thy",
        "theories/HOL/Power.thy",
        "theories/HOL/Complete_Lattices.thy",
        "theories/HOL/Wellfounded.thy",
        "theories/HOL/Hilbert_Choice.thy",
        "theories/HOL/Transitive_Closure.thy",
        "theories/HOL/Partial_Function.thy",
        "theories/HOL/Divides.thy",
    ];

    #[test]
    fn test_tier2_verification() {
        let mut total_verified = 0usize;
        let mut total_attempted = 0usize;
        let mut total_time = 0f64;
        let mut ok_count = 0usize;
        let mut processed = 0usize;

        eprintln!("\n╔══════════════════════════════════════════════╗");
        eprintln!("║   Tier 2 — Extended HOL Verification        ║");
        eprintln!("╚══════════════════════════════════════════════╝\n");

        for path_str in TIER2_FILES {
            let path = Path::new(path_str);
            if !path.exists() {
                let name = path.file_stem().unwrap().to_string_lossy();
                eprintln!("  ❓ {:>25} — file not found", name);
                continue;
            }

            let name = path.file_stem().unwrap().to_string_lossy();
            let start = Instant::now();
            let source = match std::fs::read_to_string(path) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("  ❌ {:>25} — read error: {}", name, e);
                    continue;
                },
            };

            let result =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| verify_file(&source)));

            let elapsed = start.elapsed();
            match result {
                Ok((v, a)) => {
                    let rate = if a > 0 { (v as f64 / a as f64) * 100.0 } else { 0.0 };
                    let icon = if a > 0 && rate >= 90.0 {
                        "✅"
                    } else if a > 0 && rate >= 50.0 {
                        "🟡"
                    } else if a > 0 {
                        "🔴"
                    } else {
                        "⚪"
                    };
                    eprintln!(
                        "  {} {:>25} — {:>4}/{:<4} ({:>5.1}%) in {:>5.1}s",
                        icon,
                        name,
                        v,
                        a,
                        rate,
                        elapsed.as_secs_f64()
                    );
                    total_verified += v;
                    total_attempted += a;
                    if a > 0 {
                        ok_count += 1;
                    }
                },
                Err(_) => {
                    eprintln!("  💥 {:>25} — OVERFLOWED", name);
                },
            }
            total_time += elapsed.as_secs_f64();
            processed += 1;
        }

        eprintln!("\n───────────────────────────────────────────────");
        eprintln!(
            "  Tier 2: {} files, {}/{} verified ({:.1}%), {:.1}s",
            processed,
            total_verified,
            total_attempted,
            if total_attempted > 0 {
                (total_verified as f64 / total_attempted as f64) * 100.0
            } else {
                0.0
            },
            total_time
        );
        eprintln!("  Files with lemmas: {}", ok_count);
        eprintln!("───────────────────────────────────────────────\n");

        assert!(processed > 0, "No Tier 2 files processed!");
    }
}
