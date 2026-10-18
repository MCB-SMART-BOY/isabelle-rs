//! Explicit legacy method workloads, separate from assertion-backed regression tests.

use std::path::Path;

use super::{
    AUTO_LIMIT, HolTheoremDb, classify_verify_result, enrich_local_db_with_checked_sources,
    record_verify_outcome, verify_lemma, verify_lemmas_batch,
};
use crate::hol::{
    hol_loader::{ParsedLemma, parse_lemmas, scan_theory_files},
    theory_graph::scale_diagnostics::ScaleDiagnosticError,
};

const BATCH_FILE_LIMIT: usize = 5;
const LIST_SAMPLE_LIMIT: usize = 10;
const NAT_SAMPLE_LIMIT: usize = 35;
const LARGE_THEORY_THRESHOLD: usize = 500;
const MEDIUM_THEORY_THRESHOLD: usize = 200;
const LARGE_AUTO_LIMIT: usize = 50;
const MEDIUM_AUTO_LIMIT: usize = 80;
const SMALL_AUTO_LIMIT: usize = 200;
const PROOF_PREVIEW_BYTES: usize = 80;

pub(crate) fn run_batch_first_five() -> Result<(), ScaleDiagnosticError> {
    let files = scan_theory_files("theories/HOL");
    let mut grand_total = 0;
    let mut grand_verified = 0;
    for path in files.iter().take(BATCH_FILE_LIMIT) {
        let path = Path::new(path);
        eprintln!("Reading and verifying {}", path.display());
        let source = std::fs::read_to_string(path)
            .map_err(|source| ScaleDiagnosticError::Source { path: path.to_path_buf(), source })?;
        let name = path.file_stem().unwrap_or(path.as_os_str()).to_string_lossy();
        let lemmas = parse_lemmas(&source);
        let db = build_local_database(&name, &source, &lemmas);
        let (verified, attempted) = verify_lemmas_batch(&lemmas, &db);
        eprintln!("  {name} TransitionalStrictClosed: {verified}/{attempted}");
        grand_total += attempted;
        grand_verified += verified;
    }
    eprintln!(
        "Total ({} files) TransitionalStrictClosed: {}/{} ({:.1}%)",
        files.len(),
        grand_verified,
        grand_total,
        compute_percentage(grand_verified, grand_total)
    );
    Ok(())
}

fn build_local_database(name: &str, source: &str, lemmas: &[ParsedLemma]) -> HolTheoremDb {
    let mut db = HolTheoremDb::from_lemmas(lemmas);
    // Preserve the legacy diagnostic's partial database, but make rejection visible.
    if let Err(error) = enrich_local_db_with_checked_sources(&mut db, source) {
        eprintln!("checked-source enrichment failed for {name}: {error}");
    }
    HolTheoremDb::add_builtins(&mut db);
    db
}

fn compute_percentage(verified: usize, attempted: usize) -> f64 {
    if attempted == 0 { 0.0 } else { verified as f64 / attempted as f64 * 100.0 }
}

fn compute_auto_limit(total_lemmas: usize) -> usize {
    if total_lemmas > LARGE_THEORY_THRESHOLD {
        LARGE_AUTO_LIMIT
    } else if total_lemmas > MEDIUM_THEORY_THRESHOLD {
        MEDIUM_AUTO_LIMIT
    } else {
        SMALL_AUTO_LIMIT
    }
}

// Also used by the assertion-backed 125-theorem core regression; keep the
// original selection, AUTO_LIMIT policy, statistics and classification.
pub(crate) fn bench_file(name: &str, source: &str, limit: usize) -> (usize, usize, f64) {
    let lemmas = parse_lemmas(source);
    let db = build_local_database(name, source, &lemmas);
    AUTO_LIMIT.with(|cell| cell.set(compute_auto_limit(lemmas.len())));
    let with_proofs: Vec<_> = lemmas.iter().filter(|lemma| lemma.proof_script.is_some()).collect();
    let sample = with_proofs.len().min(limit);
    let mut verified = 0;
    let start = std::time::Instant::now();
    for lemma in with_proofs.iter().take(sample) {
        let result = verify_lemma(lemma, &db);
        let outcome = classify_verify_result(&lemma.name, &result);
        if outcome.is_transitional_strict_closed() {
            verified += 1;
        }
        record_verify_outcome(&outcome);
    }
    let elapsed = start.elapsed().as_secs_f64();
    eprintln!(
        "  {name} TransitionalStrictClosed: {verified}/{sample} ({:.1}%) in {elapsed:.1}s",
        compute_percentage(verified, sample)
    );
    (verified, sample, elapsed)
}

pub(crate) fn run_list_sample() {
    eprintln!("=== List.thy Benchmark ===");
    bench_file("List", include_str!("../../theories/HOL/List.thy"), LIST_SAMPLE_LIMIT);
}

pub(crate) fn run_nat_sample() {
    bench_file("Nat", include_str!("../../theories/HOL/Nat.thy"), NAT_SAMPLE_LIMIT);
}

pub(crate) fn run_induction_sample() {
    let lemmas = parse_lemmas(include_str!("../../theories/HOL/List.thy"));
    let db = HolTheoremDb::from_lemmas(&lemmas);
    eprintln!("Loaded {} lemmas from List.thy", lemmas.len());
    if let Some(lemma) = lemmas.iter().find(|lemma| lemma.name == "append_Nil2") {
        eprintln!("Found lemma: {} with proof: {:?}", lemma.name, lemma.proof_script);
        report_induction_result(lemma, &db);
    }
    for name in ["append_assoc", "append_self_conv", "map_append"] {
        if let Some(lemma) = lemmas.iter().find(|lemma| lemma.name == name) {
            let preview = lemma.proof_script.as_deref().map(|proof| {
                &proof[..proof.floor_char_boundary(PROOF_PREVIEW_BYTES.min(proof.len()))]
            });
            eprintln!("Trying {}: proof={preview:?}", lemma.name);
            report_induction_result(lemma, &db);
        }
    }
}

fn report_induction_result(lemma: &ParsedLemma, db: &HolTheoremDb) {
    let result = verify_lemma(lemma, db);
    match result.legacy() {
        Some((theorem, exit))
            if super::classify_proof_outcome("", None, Some((theorem, exit)))
                .is_transitional_strict_closed() =>
        {
            eprintln!("TRANSITIONAL STRICT CLOSED: {} -> {:?}", lemma.name, theorem.prop().term());
        },
        Some((theorem, _)) => {
            eprintln!("ACCEPTED/OPEN: {} -> {:?}", lemma.name, theorem.prop().term());
        },
        None => eprintln!("FAILED to verify: {}", lemma.name),
    }
}
