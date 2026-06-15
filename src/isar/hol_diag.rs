#[cfg(test)]
mod hol_diag {
    use crate::{
        hol::hol_loader::{HolTheoremDb, parse_lemmas},
        isar::method::verify_lemma,
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
            if verify_lemma(lem).is_some() {
                ok += 1;
            } else {
                let proof = lem.proof_script.as_ref().unwrap();
                let short = if proof.len() > 60 { &proof[..60] } else { proof };
                eprintln!("  FAIL {}: {}", lem.name, short);
            }
        }
        eprintln!("Verified: {}/{}", ok, with_proof.len());
    }
}
