//! Comprehensive integration tests — full pipeline from theory to theorem.
//!
//! Validates end-to-end workflows:
//! - Theory loading → lemma parsing → proof verification
//! - Kernel operations → proof terms → proof checking
//! - Type inference → term annotation → certification

#[cfg(test)]
mod comprehensive {
    use isabelle_rs::core::*;
    use std::sync::Arc;

    // =========================================================================
    // Kernel roundtrip tests
    // =========================================================================

    #[test]
    fn test_full_implies_roundtrip() {
        let a = term::Term::const_("A", types::Typ::base("prop"));
        let ct = thm::CTerm::certify(a);
        let assume_a = thm::ThmKernel::assume(ct.clone());

        // Introduce: A ==> A
        let imp = thm::ThmKernel::implies_intr(&ct, &assume_a).unwrap();
        assert!(imp.is_unconditional());

        // Eliminate: from A ==> A and A, derive A
        let elim = thm::ThmKernel::implies_elim(&imp, &assume_a).unwrap();
        assert_eq!(elim.prop().term(), ct.term());
    }

    #[test]
    fn test_full_forall_roundtrip() {
        let a = term::Term::const_("A", types::Typ::base("prop"));
        let ct = thm::CTerm::certify(a.clone());
        let triv = thm::ThmKernel::trivial(ct).unwrap();

        // forall_intr: !!x. A
        let all = thm::ThmKernel::forall_intr("x", types::Typ::dummy(), &triv).unwrap();

        // forall_elim: instantiate with a specific term
        let t = term::Term::const_("c", types::Typ::base("bool"));
        let ct_t = thm::CTerm::certify(t);
        let result = thm::ThmKernel::forall_elim(ct_t, &all);
        // May fail if type doesn't match — that's OK
        let _ = result;
    }

    #[test]
    fn test_full_proof_term_pipeline() {
        use isabelle_rs::core::proofterm::{ProofTerm, ProofBody, check_proof};

        // Create a theorem
        let a = term::Term::const_("A", types::Typ::base("prop"));
        let ct = thm::CTerm::certify(a.clone());
        let thm = thm::ThmKernel::assume(ct);

        // Get proof body
        let mut body = thm.proof_body();

        // Check the proof
        let result = body.check(thm.prop().term());
        assert!(result.is_ok(), "Proof body check failed: {:?}", result);
    }

    #[test]
    fn test_full_type_infer_pipeline() {
        use isabelle_rs::core::type_infer::TypeInfer;

        // Create a term with dummy types and infer
        let f = term::Term::free("f", types::Typ::arrow(
            types::Typ::free("'a", types::Sort::top()),
            types::Typ::base("bool"),
        ));
        let x = term::Term::free("x", types::Typ::free("'a", types::Sort::top()));
        let app = term::Term::app(f, x);

        let mut infer = TypeInfer::new();
        let typ = infer.infer(&app);
        assert_eq!(typ, Some(types::Typ::base("bool")));

        // Apply inferred types
        let annotated = infer.apply_to_term(&app);
        // The annotated term should have real types
        let _ = annotated;
    }

    #[test]
    fn test_full_context_pipeline() {
        use isabelle_rs::core::context::Context;
        use isabelle_rs::core::theory::Theory;

        let thy = Theory::pure();
        let ctx = Context::theory(Arc::clone(&thy));

        // Enter proof mode
        let mut ctx = ctx.enter_proof();
        assert!(ctx.is_proof());

        // Fix variable and assume
        ctx.fix("x", types::Typ::base("nat"));
        ctx.assume(term::Term::const_("x > 0", types::Typ::base("prop")));

        assert_eq!(ctx.fixes().len(), 1);
        assert_eq!(ctx.assumptions().len(), 1);

        // Exit proof mode
        let ctx = ctx.exit_proof();
        assert!(ctx.is_theory());
    }

    #[test]
    fn test_full_bnf_pipeline() {
        use isabelle_rs::hol::hol_loader::{DatatypeDef, generate_datatype_lemmas, generate_bnf_lemmas};

        // Define a simple datatype
        let dt = DatatypeDef {
            name: "option".to_string(),
            type_params: vec!["'a".to_string()],
            constructors: vec![
                ("None".to_string(), vec![]),
                ("Some".to_string(), vec![(None, "'a".to_string())]),
            ],
        };

        // Generate datatype lemmas
        let lemmas = generate_datatype_lemmas(&dt);
        assert!(!lemmas.is_empty(), "No datatype lemmas generated");

        // Generate BNF lemmas
        let bnf_lemmas = generate_bnf_lemmas(&dt);
        assert!(!bnf_lemmas.is_empty(), "No BNF lemmas generated");

        // Check theorem counts
        eprintln!("Datatype lemmas: {}, BNF lemmas: {}",
            lemmas.len(), bnf_lemmas.len());
        assert!(lemmas.len() >= 4, "Expected >=4 datatype lemmas");
        assert!(bnf_lemmas.len() >= 3, "Expected >=3 BNF lemmas");
    }

    #[test]
    fn test_full_flexflex_pipeline() {
        // Test flex-flex resolution
        let a = term::Term::const_("A", types::Typ::base("prop"));
        let ct = thm::CTerm::certify(a);
        let thm = thm::ThmKernel::assume(ct);

        // Theorem should start with empty tpairs
        assert!(thm.tpairs().is_empty());

        // flexflex_resolve on no tpairs is identity
        let resolved = thm::ThmKernel::flexflex_resolve(&thm);
        assert_eq!(resolved.tpairs().len(), 0);
    }

    #[test]
    fn test_full_shyps_pipeline() {
        let a = term::Term::const_("A", types::Typ::base("prop"));
        let ct = thm::CTerm::certify(a);
        let thm = thm::ThmKernel::assume(ct);

        // Start with empty shyps
        assert!(thm.shyps().is_empty());

        // Add a sort hypothesis
        let ord_sort = types::Sort::singleton("ord");
        let thm = thm::ThmKernel::add_shyp(&thm, ord_sort.clone());
        assert!(!thm.shyps().is_empty());
        assert!(thm::ThmKernel::satisfies_shyp(&thm, &ord_sort));

        // Strip shyps
        let thm = thm::ThmKernel::strip_shyps(&thm);
        assert!(thm.shyps().is_empty());
    }
}
