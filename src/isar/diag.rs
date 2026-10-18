//! Opt-in structured-proof diagnostics; results do not grant theorem authority.

use crate::{
    hol::hol_loader::{HolTheoremDb, ParsedLemma, parse_lemmas},
    isar::method::{classify_verify_result, verify_lemma},
};

const STRUCTURED_SAMPLE_LIMIT: usize = 3;
const PROOF_PREVIEW_BYTES: usize = 60;

pub(crate) fn run_structured_proofs() {
    eprintln!("=== Structured Proof Analysis: loading global HOL database ===");
    let db = HolTheoremDb::global();
    let files = [
        ("HOL", include_str!("../../theories/HOL/HOL.thy")),
        ("Orderings", include_str!("../../theories/HOL/Orderings.thy")),
        ("Nat", include_str!("../../theories/HOL/Nat.thy")),
        ("Set", include_str!("../../theories/HOL/Set.thy")),
        ("List", include_str!("../../theories/HOL/List.thy")),
    ];
    for (name, source) in files {
        analyze_structured_proofs(name, source, db);
    }
}

fn has_structured_proof(lemma: &ParsedLemma) -> bool {
    lemma.proof_script.as_ref().is_some_and(|proof| {
        proof.contains('\n')
            && (proof.contains("have ")
                || proof.contains("show ")
                || proof.contains("case ")
                || proof.contains("next"))
    })
}

fn analyze_structured_proofs(name: &str, source: &str, db: &HolTheoremDb) {
    eprintln!("--- {name} ---");
    let lemmas = parse_lemmas(source);
    let structured: Vec<_> = lemmas.iter().filter(|lemma| has_structured_proof(lemma)).collect();
    eprintln!("  Total: {} structured proofs", structured.len());
    let sample = structured.len().min(STRUCTURED_SAMPLE_LIMIT);
    let mut verified = 0;
    for (index, lemma) in structured.iter().take(sample).enumerate() {
        eprintln!("    [{}/{}] {} ...", index + 1, sample, lemma.name);
        let result = verify_lemma(lemma, db);
        let outcome = classify_verify_result(&lemma.name, &result);
        if outcome.is_transitional_strict_closed() {
            verified += 1;
            eprintln!("      TransitionalStrictClosed");
        } else {
            let proof = lemma.proof_script.as_deref().unwrap_or("");
            let preview = &proof[..proof.floor_char_boundary(PROOF_PREVIEW_BYTES.min(proof.len()))];
            eprintln!("      {}: {preview}", outcome.label());
        }
    }
    eprintln!("  TransitionalStrictClosed: {verified}/{sample}");
}
