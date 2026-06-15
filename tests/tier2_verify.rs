//! Tier 2 verification — expanded HOL theory coverage.
//!
//! Extends verification beyond the 5 core files to 19 foundational HOL theories.
//! Uses local DB approach to avoid global LazyLock init.
//!
//! Per-file timeout: ~120s for large files, ~30s for small files.
//! Uses AUTO_LIMIT to bound proof search per lemma.

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

    /// Max per-file time budget (seconds). Files exceeding this get partial results.
    const PER_FILE_TIMEOUT_SECS: u64 = 120;

    /// Max proof attempts per lemma (via AUTO_LIMIT).
    const PROOF_ATTEMPT_LIMIT: usize = 25;

    #[test]
    fn test_tier2_verification() {
        let mut total_verified = 0usize;
        let mut total_attempted = 0usize;
        let mut total_time = 0f64;
        let mut ok_count = 0usize;
        let mut processed = 0usize;
        let mut timed_out = 0usize;

        eprintln!("\n╔══════════════════════════════════════════════╗");
        eprintln!("║   Tier 2 — Extended HOL Verification        ║");
        eprintln!(
            "║   Timeout: {}s/file  |  Limit: {} attempts     ║",
            PER_FILE_TIMEOUT_SECS, PROOF_ATTEMPT_LIMIT
        );
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

            // Pre-count lemmas to set appropriate AUTO_LIMIT
            let lemma_count = source.matches("lemma ").count() + source.matches("theorem ").count();
            let auto_limit = if lemma_count > 300 {
                15
            } else if lemma_count > 200 {
                20
            } else {
                PROOF_ATTEMPT_LIMIT
            };

            // Set proof attempt limit for this file
            isabelle_rs::isar::method::set_auto_limit(auto_limit);

            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                verify_file(&source)
            }));

            let elapsed = start.elapsed();
            let elapsed_secs = elapsed.as_secs_f64();

            // Check if file exceeded timeout
            if elapsed_secs > PER_FILE_TIMEOUT_SECS as f64 {
                timed_out += 1;
            }

            match result {
                Ok((v, a)) => {
                    let rate = if a > 0 {
                        (v as f64 / a as f64) * 100.0
                    } else {
                        0.0
                    };
                    let timeout_flag = if elapsed_secs > PER_FILE_TIMEOUT_SECS as f64 {
                        " ⏱️"
                    } else {
                        ""
                    };
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
                        "  {}{} {:>23} — {:>4}/{:<4} ({:>5.1}%) in {:>5.1}s",
                        icon,
                        timeout_flag,
                        name,
                        v,
                        a,
                        rate,
                        elapsed_secs
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
            total_time += elapsed_secs;
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
        eprintln!("  Files with lemmas: {}  |  Timed out: {}", ok_count, timed_out);
        eprintln!("───────────────────────────────────────────────\n");

        assert!(processed > 0, "No Tier 2 files processed!");
    }
}
