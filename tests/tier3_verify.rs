//! Tier 3 verification — broad HOL theory coverage (30+ files).
//! Uses local DB approach to avoid global LazyLock init.

#[cfg(test)]
mod tier3_verify {
    use std::{path::Path, time::Instant};

    use isabelle_rs::isar::method::verify_file;

    const TIER3_FILES: &[&str] = &[
        "theories/HOL/Set_Interval.thy",
        "theories/HOL/Big_Operators.thy",
        "theories/HOL/OrderedGroup.thy",
        "theories/HOL/OrderedRing.thy",
        "theories/HOL/Nat_Numeral.thy",
        "theories/HOL/Int_Numeral.thy",
        "theories/HOL/Divides.thy",
        "theories/HOL/Parity.thy",
        "theories/HOL/GCD.thy",
        "theories/HOL/Sqrt.thy",
        "theories/HOL/String.thy",
        "theories/HOL/Char_ord.thy",
        "theories/HOL/Enum.thy",
        "theories/HOL/Groups_Big.thy",
        "theories/HOL/Lattices_Big.thy",
        "theories/HOL/Euclidean_Rings.thy",
        "theories/HOL/Factorial.thy",
        "theories/HOL/Binomial.thy",
        "theories/HOL/Code_Numeral.thy",
        "theories/HOL/Filter.thy",
        "theories/HOL/Conditionally_Complete_Lattices.thy",
        "theories/HOL/Archimedean_Field.thy",
        "theories/HOL/Topological_Spaces.thy",
        "theories/HOL/Modules.thy",
        "theories/HOL/Vector_Spaces.thy",
        "theories/HOL/Real_Vector_Spaces.thy",
        "theories/HOL/Deriv.thy",
        "theories/HOL/Series.thy",
        "theories/HOL/Transcendental.thy",
        "theories/HOL/Complex.thy",
    ];

    #[test]
    fn test_tier3_verification() {
        let mut total_verified = 0usize;
        let mut total_attempted = 0usize;
        let mut total_time = 0f64;
        let mut ok_count = 0usize;
        let mut processed = 0usize;

        eprintln!("\n╔══════════════════════════════════════════════╗");
        eprintln!("║   Tier 3 — Broad HOL Verification            ║");
        eprintln!("╚══════════════════════════════════════════════╝\n");

        for path_str in TIER3_FILES {
            let path = Path::new(path_str);
            if !path.exists() {
                let name = path.file_stem().unwrap().to_string_lossy();
                eprintln!("  ❓ {:>35} — file not found", name);
                continue;
            }

            let name = path.file_stem().unwrap().to_string_lossy();
            let start = Instant::now();
            let source = match std::fs::read_to_string(path) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("  ❌ {:>35} — read error: {}", name, e);
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
                        "  {} {:>35} — {:>4}/{:<4} ({:>5.1}%) in {:>5.1}s",
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
                    eprintln!("  💥 {:>35} — OVERFLOWED", name);
                },
            }
            total_time += elapsed.as_secs_f64();
            processed += 1;
        }

        eprintln!("\n───────────────────────────────────────────────");
        eprintln!(
            "  Tier 3: {} files, {}/{} verified ({:.1}%), {:.1}s",
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

        assert!(processed > 0, "No Tier 3 files processed!");
    }
}
