#[cfg(test)]
mod hol_diag {
    use crate::{
        hol::hol_loader::{HolTheoremDb, parse_lemmas},
        isar::method::{classify_verify_result, verify_lemma},
    };

    #[test]
    #[ignore = "overflow on full DB with 15K theorems — known issue"]
    fn test_hol_failures() {
        let _db = HolTheoremDb::get();
        let source = include_str!("../../theories/HOL/HOL.thy");
        let lemmas = parse_lemmas(source);
        let with_proof: Vec<_> = lemmas.iter().filter(|l| l.proof_script.is_some()).collect();
        eprintln!("HOL.thy: {} total, {} with proofs", lemmas.len(), with_proof.len());
        let mut ok = 0;
        for (idx, lem) in with_proof.iter().enumerate() {
            eprintln!("  [{}/{}] verifying: {}...", idx + 1, with_proof.len(), lem.name);
            let result = verify_lemma(lem);
            let outcome = classify_verify_result(&lem.name, &result);
            if outcome.is_transitional_strict_closed() {
                ok += 1;
            } else {
                let proof = lem.proof_script.as_ref().unwrap();
                let short = if proof.len() > 60 { &proof[..60] } else { proof };
                eprintln!("  {} {}: {}", outcome.label(), lem.name, short);
            }
        }
        eprintln!("TransitionalStrictClosed: {}/{}", ok, with_proof.len());
    }
}
