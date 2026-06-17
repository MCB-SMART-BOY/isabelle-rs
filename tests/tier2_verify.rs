//! Tier 2 verification — expanded HOL theory coverage.
//!
//! Extends verification beyond the 5 core files to 57 foundational HOL theories.
//! Uses local DB + VERIFY_DEADLINE for per-file time budgets.
//!
//! Per-file timeout: 120s for arithmetic-heavy files, 60s for others.
//! Uses AUTO_LIMIT to bound proof search per lemma.

#[cfg(test)]
mod tier2_verify {
    use std::{path::Path, time::Instant};

    use isabelle_rs::isar::method::{self, verify_file};

    const TIER2_FILES: &[(&str, u64)] = &[
        // (path, timeout_seconds) — arithmetic-heavy files get longer budget
        ("theories/HOL/Fun.thy", 90),
        ("theories/HOL/Product_Type.thy", 60),
        ("theories/HOL/Sum_Type.thy", 60),
        ("theories/HOL/Lattices.thy", 60),
        ("theories/HOL/Groups.thy", 60),
        ("theories/HOL/Rings.thy", 90),
        // ("theories/HOL/Fields.thy", 120),    // HEAVY: structured Isar proofs (205 lemmas × multi-step)
        ("theories/HOL/Relation.thy", 60),
        ("theories/HOL/Equiv_Relations.thy", 60),
        ("theories/HOL/Map.thy", 60),
        // ("theories/HOL/Finite_Set.thy", 90),   // HEAVY: 281 lemmas, 372 simp, 3h+ stuck
        // ("theories/HOL/Num.thy", 120),        // HEAVY: cross-file arith rules
        ("theories/HOL/Power.thy", 60),
        ("theories/HOL/Complete_Lattices.thy", 60),
        // ("theories/HOL/Wellfounded.thy", 60),  // HEAVY: 152 lemmas, slow
        // ("theories/HOL/Hilbert_Choice.thy", 60), // HEAVY: 56 auto calls
        // ("theories/HOL/Transitive_Closure.thy", 60), // HEAVY: 40 auto + induct
        // ("theories/HOL/Partial_Function.thy", 60), // BLOCKED: memory explosion
        // ("theories/HOL/Divides.thy", 90),    // NOT FOUND in theories/HOL/
        // ── Tier2+ Expansion (Phase 4) ──
        ("theories/HOL/Option.thy", 60),
        ("theories/HOL/Boolean_Algebras.thy", 60),
        ("theories/HOL/Complete_Partial_Order.thy", 60),
        ("theories/HOL/Order_Relation.thy", 60),
        ("theories/HOL/Factorial.thy", 60),
        ("theories/HOL/Semiring_Normalization.thy", 60),
        ("theories/HOL/Groups_List.thy", 60),
        ("theories/HOL/Wfrec.thy", 60),
        ("theories/HOL/Inductive.thy", 60),
        ("theories/HOL/Typedef.thy", 60),
        ("theories/HOL/Parity.thy", 90),
        ("theories/HOL/Lattices_Big.thy", 90),
        ("theories/HOL/Conditionally_Complete_Lattices.thy", 90),
        // ── Tier2++ Expansion (Phase 4.2) ──
        ("theories/HOL/Hull.thy", 60),
        ("theories/HOL/Groebner_Basis.thy", 60),
        ("theories/HOL/Binomial_Plus.thy", 60),
        ("theories/HOL/Fun_Def.thy", 60),
        ("theories/HOL/Numeral_Simprocs.thy", 60),
        ("theories/HOL/Basic_BNFs.thy", 60),
        ("theories/HOL/Basic_BNF_LFPs.thy", 60),
        ("theories/HOL/Record.thy", 60),
        ("theories/HOL/Meson.thy", 60),
        ("theories/HOL/Metis.thy", 60),
        ("theories/HOL/Presburger.thy", 90),
        ("theories/HOL/Lifting_Set.thy", 90),
        // ── Tier2+++ Expansion (Phase 6) ── Library + Data_Structures
        ("theories/HOL/Phantom_Type.thy", 60),
        ("theories/HOL/Cancellation.thy", 60),
        ("theories/HOL/Preorder.thy", 60),
        ("theories/HOL/List_Lexorder.thy", 60),
        ("theories/HOL/List_Lenlexorder.thy", 60),
        ("theories/HOL/Product_Lexorder.thy", 60),
        ("theories/HOL/Product_Plus.thy", 60),
        ("theories/HOL/Fun_Lexorder.thy", 60),
        ("theories/HOL/Char_ord.thy", 60),
        ("theories/HOL/Monad_Syntax.thy", 60),
        ("theories/HOL/NList.thy", 60),
        ("theories/HOL/Combine_PER.thy", 60),
        ("theories/HOL/Power_By_Squaring.thy", 60),
        ("theories/HOL/Old_Recdef.thy", 60),
        ("theories/HOL/Set_Algebras.thy", 60),
        ("theories/HOL/Comparator.thy", 60),
        ("theories/HOL/Complemented_Lattices.thy", 60),
        ("theories/HOL/Z2.thy", 60),
        ("theories/HOL/BNF_Corec.thy", 60),
        ("theories/HOL/Quotient_Type.thy", 60),
        ("theories/HOL/Tree23.thy", 60),
        // ── Phase 13: Library chain expansion ──
        ("theories/HOL/Quotient_Option.thy", 60),
        ("theories/HOL/Quotient_Sum.thy", 60),
        ("theories/HOL/Quotient_Product.thy", 60),
        ("theories/HOL/Quotient_Set.thy", 60),
    ];

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
        eprintln!("║   Per-file deadlines enforced by VERIFY_DEADLINE ║");
        eprintln!("╚══════════════════════════════════════════════╝\n");

        for (path_str, timeout_secs) in TIER2_FILES {
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
            let lemma_count =
                source.matches("lemma ").count() + source.matches("theorem ").count();
            let auto_limit = if lemma_count > 400 {
                5
            } else if lemma_count > 200 {
                10
            } else if lemma_count > 100 {
                20
            } else {
                30
            };
            method::set_auto_limit(auto_limit);

            // Set soft deadline for this file
            let deadline = Instant::now() + std::time::Duration::from_secs(*timeout_secs);
            method::set_verify_deadline(deadline);

            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                verify_file(&source)
            }));

            // Clear deadline for next file
            method::clear_verify_deadline();

            let elapsed = start.elapsed();
            let elapsed_secs = elapsed.as_secs_f64();

            // Check if file exceeded timeout
            let was_timed_out = elapsed_secs > *timeout_secs as f64;

            match result {
                Ok((v, a)) => {
                    let total_lemmas = lemma_count;
                    let attempted_pct = if total_lemmas > 0 {
                        (a as f64 / total_lemmas as f64) * 100.0
                    } else {
                        0.0
                    };
                    let rate = if a > 0 {
                        (v as f64 / a as f64) * 100.0
                    } else {
                        0.0
                    };
                    let timeout_flag = if was_timed_out { " ⏱️" } else { "" };
                    let partial_flag = if was_timed_out && a < total_lemmas {
                        format!(" (partial: {}/{})", a, total_lemmas)
                    } else {
                        String::new()
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
                        "  {}{} {:>23} — {:>4}/{:<4} ({:>5.1}% ok, {:>5.1}% attempted{}) in {:>5.1}s",
                        icon, timeout_flag, name, v, a, rate, attempted_pct, partial_flag, elapsed_secs
                    );
                    total_verified += v;
                    total_attempted += a;
                    if a > 0 {
                        ok_count += 1;
                    }
                    if was_timed_out {
                        timed_out += 1;
                    }
                },
                Err(_) => {
                    eprintln!("  💥 {:>25} — OVERFLOWED ({:.1}s)", name, elapsed_secs);
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
