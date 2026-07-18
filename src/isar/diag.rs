//! Diagnostic tool to analyze which structured proofs succeed/fail.

#[cfg(test)]
mod diag_tests {
    use crate::{
        hol::hol_loader::{HolTheoremDb, parse_lemmas},
        isar::method::{classify_verify_result, verify_lemma},
    };

    #[test]
    fn test_diag_structured_proofs() {
        let _db = HolTheoremDb::get(); // init

        let files: [(&str, &str); 5] = [
            ("HOL", include_str!("../../theories/HOL/HOL.thy")),
            ("Orderings", include_str!("../../theories/HOL/Orderings.thy")),
            ("Nat", include_str!("../../theories/HOL/Nat.thy")),
            ("Set", include_str!("../../theories/HOL/Set.thy")),
            ("List", include_str!("../../theories/HOL/List.thy")),
        ];

        eprintln!("=== Structured Proof Analysis ===");
        for (fname, source) in &files {
            eprintln!("--- {} ---", fname);
            let lemmas = parse_lemmas(source);
            let structured: Vec<_> = lemmas
                .iter()
                .filter(|l| {
                    l.proof_script.as_ref().map_or(false, |p| {
                        p.contains('\n')
                            && (p.contains("have ")
                                || p.contains("show ")
                                || p.contains("case ")
                                || p.contains("next"))
                    })
                })
                .collect();

            eprintln!("  Total: {} structured proofs", structured.len());

            let sample = structured.len().min(3);
            let mut ok = 0usize;
            for (i, lem) in structured.iter().take(sample).enumerate() {
                eprintln!("    [{}/{}] {} ...", i + 1, sample, lem.name);
                let result = verify_lemma(lem);
                let outcome = classify_verify_result(&lem.name, result.as_ref());
                if outcome.is_transitional_strict_closed() {
                    ok += 1;
                    eprintln!("      TransitionalStrictClosed");
                } else {
                    let preview =
                        lem.proof_script.as_ref().map(|p| &p[..p.len().min(60)]).unwrap_or("");
                    eprintln!("      {}: {}", outcome.label(), preview);
                }
            }
            eprintln!("  TransitionalStrictClosed: {}/{}", ok, sample);
        }
    }
}
