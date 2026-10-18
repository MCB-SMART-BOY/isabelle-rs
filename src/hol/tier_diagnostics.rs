//! Explicit, resource-supervised Tier 2 and Tier 3 HOL verification diagnostics.
//! Counts from `verify_file` are transitional, not kernel-certified proof counts.

use std::{
    path::Path,
    time::{Duration, Instant},
};

use super::ScaleDiagnosticError;
use crate::isar::method::{self, verify_file};

const TIER2_FILES: &[(&str, u64)] = &[
    ("theories/HOL/Fun.thy", 90),
    ("theories/HOL/Product_Type.thy", 60),
    ("theories/HOL/Sum_Type.thy", 60),
    ("theories/HOL/Lattices.thy", 60),
    ("theories/HOL/Groups.thy", 60),
    ("theories/HOL/Rings.thy", 90),
    ("theories/HOL/Relation.thy", 60),
    ("theories/HOL/Equiv_Relations.thy", 60),
    ("theories/HOL/Map.thy", 60),
    ("theories/HOL/Power.thy", 60),
    ("theories/HOL/Complete_Lattices.thy", 60),
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
    ("theories/HOL/Quotient_Option.thy", 60),
    ("theories/HOL/Quotient_Sum.thy", 60),
    ("theories/HOL/Quotient_Product.thy", 60),
    ("theories/HOL/Quotient_Set.thy", 60),
    ("theories/HOL/Cmp.thy", 60),
    ("theories/HOL/Base_FDS.thy", 60),
    ("theories/HOL/Lookup2.thy", 60),
    ("theories/HOL/Function_Division.thy", 60),
    ("theories/HOL/Type_Length.thy", 60),
    ("theories/HOL/Quotient_Syntax.thy", 60),
    ("theories/HOL/Queue_Spec.thy", 60),
    ("theories/HOL/Less_False.thy", 60),
    ("theories/HOL/Priority_Queue_Specs.thy", 60),
    ("theories/HOL/Library/Case_Converter.thy", 60),
    ("theories/HOL/Library/Centered_Division.thy", 90),
    ("theories/HOL/Library/Code_Bit_Shifts_for_Arithmetic.thy", 60),
    ("theories/HOL/Library/Code_Target_Int.thy", 90),
    ("theories/HOL/Library/Conditional_Parametricity.thy", 60),
    ("theories/HOL/Library/Confluence.thy", 60),
    ("theories/HOL/Library/Debug.thy", 60),
    ("theories/HOL/Library/Fraction_Field.thy", 90),
    ("theories/HOL/Library/Group_Closure.thy", 60),
    ("theories/HOL/Library/Groups_Big_Fun.thy", 90),
    ("theories/HOL/Library/ListVector.thy", 60),
    ("theories/HOL/Library/Order_Relation_More.thy", 90),
    ("theories/HOL/Library/Order_Union.thy", 60),
    ("theories/HOL/Library/Parallel.thy", 60),
    ("theories/HOL/Library/Rewrite.thy", 60),
    ("theories/HOL/Library/Signed_Division.thy", 90),
    ("theories/HOL/Library/Stirling.thy", 60),
    ("theories/HOL/Library/Transposition.thy", 90),
    ("theories/HOL/Library/Uprod.thy", 60),
    ("theories/HOL/Library/Diagonal_Subsequence.thy", 60),
    ("theories/HOL/Library/Fib.thy", 60),
    ("theories/HOL/Library/Going_To_Filter.thy", 60),
    ("theories/HOL/Library/Infinite_Typeclass.thy", 60),
    ("theories/HOL/Library/Nonpos_Ints.thy", 120),
    ("theories/HOL/Library/Periodic_Fun.thy", 60),
    ("theories/HOL/Library/Real_Mod.thy", 120),
    ("theories/HOL/Library/Code_Abstract_Char.thy", 60),
];

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

#[derive(Default)]
struct TierTotals {
    verified: usize,
    attempted: usize,
    seconds: f64,
    with_lemmas: usize,
    processed: usize,
    timed_out: usize,
}

impl TierTotals {
    fn record(&mut self, verified: usize, attempted: usize, seconds: f64, is_timed_out: bool) {
        self.verified += verified;
        self.attempted += attempted;
        if attempted > 0 {
            self.with_lemmas += 1;
        }
        if is_timed_out {
            self.timed_out += 1;
        }
        self.seconds += seconds;
        self.processed += 1;
    }

    fn record_panic(&mut self, seconds: f64) {
        self.seconds += seconds;
        self.processed += 1;
    }

    fn report(&self, tier: &str) {
        eprintln!("\n-----------------------------------------------");
        eprintln!(
            "  {tier}: {} files, {}/{} transitional closed ({:.1}%), {:.1}s",
            self.processed,
            self.verified,
            self.attempted,
            compute_percentage(self.verified, self.attempted),
            self.seconds
        );
        if tier == "Tier 2" {
            eprintln!(
                "  Files with lemmas: {}  |  Timed out: {}",
                self.with_lemmas, self.timed_out
            );
        } else {
            eprintln!("  Files with lemmas: {}", self.with_lemmas);
        }
        eprintln!("-----------------------------------------------");
    }
}

fn compute_percentage(numerator: usize, denominator: usize) -> f64 {
    if denominator == 0 { 0.0 } else { (numerator as f64 / denominator as f64) * 100.0 }
}

fn read_source(path: &Path, name: &str, width: usize) -> Option<String> {
    match std::fs::read_to_string(path) {
        Ok(source) => Some(source),
        Err(error) => {
            eprintln!("  {:>width$} — read error at {}: {error}", name, path.display());
            None
        },
    }
}

fn get_file_name<'a>(path: &'a Path, fallback: &'a str) -> &'a str {
    path.file_stem().and_then(|name| name.to_str()).unwrap_or(fallback)
}

fn count_lemmas(source: &str) -> usize {
    source.matches("lemma ").count() + source.matches("theorem ").count()
}

fn choose_auto_limit(lemma_count: usize) -> usize {
    const LIMITS_BY_LEMMA_THRESHOLD: [(usize, usize); 3] = [(400, 5), (200, 10), (100, 20)];
    const DEFAULT_TIER2_AUTO_LIMIT: usize = 30;
    LIMITS_BY_LEMMA_THRESHOLD
        .into_iter()
        .find_map(|(threshold, limit)| (lemma_count > threshold).then_some(limit))
        .unwrap_or(DEFAULT_TIER2_AUTO_LIMIT)
}

fn report_tier2_file(
    name: &str,
    verified: usize,
    attempted: usize,
    lemma_count: usize,
    (proved, accepted): (usize, usize),
    seconds: f64,
    is_timed_out: bool,
) {
    let is_partial = is_timed_out && attempted < lemma_count;
    let status = if is_timed_out { " timed out" } else { "" };
    if is_partial {
        eprintln!(
            "  {:>23} — {:>4}/{:<4} ({:>5.1}% transitional closed, {:>5.1}% attempted \
             (partial: {attempted}/{lemma_count}){status}) \
             [transitional strict {} / axiom accepted {}] in {:>5.1}s",
            name,
            verified,
            attempted,
            compute_percentage(verified, attempted),
            compute_percentage(attempted, lemma_count),
            proved,
            accepted,
            seconds
        );
    } else {
        eprintln!(
            "  {:>23} — {:>4}/{:<4} ({:>5.1}% transitional closed, {:>5.1}% attempted{status}) \
             [transitional strict {} / axiom accepted {}] in {:>5.1}s",
            name,
            verified,
            attempted,
            compute_percentage(verified, attempted),
            compute_percentage(attempted, lemma_count),
            proved,
            accepted,
            seconds
        );
    }
}

fn run_tier2_file(path_str: &str, timeout_secs: u64, totals: &mut TierTotals) {
    let path = Path::new(path_str);
    let name = get_file_name(path, path_str);
    if !path.exists() {
        eprintln!("  {:>25} — file not found: {}", name, path.display());
        return;
    }
    let started = Instant::now();
    let Some(source) = read_source(path, name, 25) else { return };
    let lemma_count = count_lemmas(&source);
    method::set_auto_limit(choose_auto_limit(lemma_count));
    method::set_verify_deadline(Instant::now() + Duration::from_secs(timeout_secs));
    let stats_before = method::verify_stats();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| verify_file(&source)));
    method::clear_verify_deadline();
    let stats_after = method::verify_stats();
    let proved = stats_after.0.saturating_sub(stats_before.0);
    let accepted = stats_after.1.saturating_sub(stats_before.1);
    let seconds = started.elapsed().as_secs_f64();
    let is_timed_out = seconds > timeout_secs as f64;
    match result {
        Ok((verified, attempted)) => {
            report_tier2_file(
                name,
                verified,
                attempted,
                lemma_count,
                (proved, accepted),
                seconds,
                is_timed_out,
            );
            totals.record(verified, attempted, seconds, is_timed_out);
        },
        Err(_) => {
            eprintln!("  {:>25} — panicked ({seconds:.1}s)", name);
            totals.record_panic(seconds);
        },
    }
}

fn report_tier2_trust() {
    let (proved, accepted) = method::verify_stats();
    let total = proved + accepted;
    let proved_pct = compute_percentage(proved, total);
    eprintln!("  Transitional strict closed: {proved}/{total} ({proved_pct:.1}%)");
    eprintln!("  Axiom-accepted (not proved): {accepted} ({:.1}%)", 100.0 - proved_pct);
    eprintln!("-----------------------------------------------\n");
}

pub(super) fn run_tier2() -> Result<(), ScaleDiagnosticError> {
    let mut totals = TierTotals::default();
    method::reset_verify_stats();
    eprintln!("\nTier 2 — extended HOL diagnostic; per-file VERIFY_DEADLINE enabled\n");
    for &(path, timeout_secs) in TIER2_FILES {
        run_tier2_file(path, timeout_secs, &mut totals);
    }
    totals.report("Tier 2");
    report_tier2_trust();
    if totals.processed == 0 {
        return Err(ScaleDiagnosticError::NoFilesProcessed { tier: "Tier 2" });
    }
    Ok(())
}

fn run_tier3_file(path_str: &str, totals: &mut TierTotals) {
    let path = Path::new(path_str);
    let name = get_file_name(path, path_str);
    if !path.exists() {
        eprintln!("  {:>35} — file not found: {}", name, path.display());
        return;
    }
    let started = Instant::now();
    let Some(source) = read_source(path, name, 35) else { return };
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| verify_file(&source)));
    let seconds = started.elapsed().as_secs_f64();
    match result {
        Ok((verified, attempted)) => {
            eprintln!(
                "  {:>35} — {:>4}/{:<4} ({:>5.1}% transitional closed) in {:>5.1}s",
                name,
                verified,
                attempted,
                compute_percentage(verified, attempted),
                seconds
            );
            totals.record(verified, attempted, seconds, false);
        },
        Err(_) => {
            eprintln!("  {:>35} — panicked", name);
            totals.record_panic(seconds);
        },
    }
}

pub(super) fn run_tier3() -> Result<(), ScaleDiagnosticError> {
    let mut totals = TierTotals::default();
    eprintln!("\nTier 3 — broad HOL diagnostic\n");
    for &path in TIER3_FILES {
        run_tier3_file(path, &mut totals);
    }
    totals.report("Tier 3");
    eprintln!();
    if totals.processed == 0 {
        return Err(ScaleDiagnosticError::NoFilesProcessed { tier: "Tier 3" });
    }
    Ok(())
}
