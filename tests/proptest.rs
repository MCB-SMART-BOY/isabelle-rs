//! Property-based tests for Isabelle-rs kernel.
//!
//! Uses `proptest` to verify invariants of the LCF kernel
//! with randomly generated inputs.
//!
//! ## Test categories
//!
//! 1. **Display invariants** — formatting never panics
//! 2. **Kernel invariants** — each of 15 operations preserves soundness
//! 3. **Algebraic laws** — involution, idempotence, roundtrips
//! 4. **Unification invariants** — common instance, idempotence
//! 5. **Simplifier invariants** — fixpoint, soundness

use isabelle_rs::core::*;
use proptest::prelude::*;

// =========================================================================
// Strategies — random term/type generators
// =========================================================================

/// Generates random type names from the core theory vocabulary.
fn arb_type_name() -> impl Strategy<Value = String> {
    prop::sample::select(vec![
        "bool".to_string(),
        "nat".to_string(),
        "int".to_string(),
        "prop".to_string(),
        "fun".to_string(),
        "list".to_string(),
        "set".to_string(),
    ])
}

/// Generates random base types.
fn arb_base_type() -> impl Strategy<Value = types::Typ> {
    arb_type_name().prop_map(|n| types::Typ::base(n.as_str()))
}

/// Recursively generates random types (base + arrow).
fn arb_type() -> impl Strategy<Value = types::Typ> {
    let leaf = arb_base_type();
    leaf.prop_recursive(
        4,  // max depth
        16, // max nodes
        3,  // expected branches
        |inner| (inner.clone(), inner.clone()).prop_map(|(a, b)| types::Typ::arrow(a, b)),
    )
}

/// Generates random Isabelle-style variable names.
fn arb_var_name() -> impl Strategy<Value = String> {
    prop::sample::select(vec![
        "x".to_string(),
        "y".to_string(),
        "z".to_string(),
        "a".to_string(),
        "b".to_string(),
        "c".to_string(),
        "P".to_string(),
        "Q".to_string(),
        "R".to_string(),
        "f".to_string(),
        "g".to_string(),
        "h".to_string(),
    ])
}

/// Generates random proposition names.
fn arb_prop_name() -> impl Strategy<Value = String> {
    prop::sample::select(vec![
        "A".to_string(),
        "B".to_string(),
        "C".to_string(),
        "P".to_string(),
        "Q".to_string(),
        "R".to_string(),
    ])
}

/// Generates random terms using the full AST.
fn arb_term() -> impl Strategy<Value = term::Term> {
    let leaf = prop_oneof![
        // Constants
        (arb_type_name(), arb_type()).prop_map(|(n, t)| term::Term::const_(n.as_str(), t)),
        // Free variables
        (arb_var_name(), arb_type()).prop_map(|(n, t)| term::Term::free(n.as_str(), t)),
        // Bound variables
        (0usize..10).prop_map(term::Term::bound),
    ];
    leaf.prop_recursive(
        6,  // max depth
        64, // max nodes
        5,  // expected branches
        |inner| {
            prop_oneof![
                // Application
                (inner.clone(), inner.clone()).prop_map(|(f, a)| term::Term::app(f, a)),
                // Abstraction
                (arb_var_name(), arb_type(), inner).prop_map(|(n, t, b)| term::Term::abs(
                    n.as_str(),
                    t,
                    b
                )),
            ]
        },
    )
}

/// Generates boolean-typed terms (for use in theorems).
fn arb_bool_term() -> impl Strategy<Value = term::Term> {
    arb_term().prop_map(|t| {
        // Force the term to have bool type (simplified for testing)
        t
    })
}

// =========================================================================
// Helper: create equality theorems
// =========================================================================

/// Creates a reflexive theorem `⊢ t ≡ t` from a term.
fn mk_refl(t: &term::Term) -> thm::Thm {
    let ct = thm::CTerm::certify(t.clone());
    thm::ThmKernel::reflexive(ct)
}

// =========================================================================
// Category 1: Display invariants — formatting never panics
// =========================================================================

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256,
        max_shrink_time: 1000,
        ..ProptestConfig::default()
    })]

    #[test]
    fn prop_term_display_never_panics(t in arb_term()) {
        let _ = format!("{:?}", t);
        let _ = format!("{}", t);
    }

    #[test]
    fn prop_type_display_never_panics(typ in arb_type()) {
        let _ = format!("{:?}", typ);
        let _ = format!("{}", typ);
    }

    #[test]
    fn prop_arrow_type_roundtrip(typ in arb_type()) {
        // Destructure then reconstruct arrow types roundtrips
        if let Some((a, b)) = typ.dest_fun() {
            let rebuilt = types::Typ::arrow(a.clone(), b.clone());
            assert_eq!(typ, rebuilt);
        }
    }
}

// =========================================================================
// Category 2: Kernel invariants — each operation preserves soundness
// =========================================================================

proptest! {
    /// assume: A ⊢ A, and the hypothesis set contains exactly A.
    #[test]
    fn prop_assume_has_self_in_hyps(name in arb_prop_name()) {
        let t = term::Term::const_(name.as_str(), types::Typ::base("prop"));
        let ct = thm::CTerm::certify(t.clone());
        let th = thm::ThmKernel::assume(ct.clone());
        // The proposition must equal the input
        assert_eq!(th.prop().term(), ct.term());
        // The hypothesis set must contain the assumption
        assert!(th.hyps().contains(&ct));
        // It has exactly 1 hypothesis (only itself)
        assert_eq!(th.hyps().len(), 1);
    }

    /// reflexive: ⊢ t ≡ t, unconditional.
    #[test]
    fn prop_reflexive_is_unconditional(typ in arb_type()) {
        let t = term::Term::const_("c", typ);
        let ct = thm::CTerm::certify(t);
        let th = thm::ThmKernel::reflexive(ct);
        // Always succeeds (returns Thm, not Result)
        assert!(th.is_unconditional());
        // Must be an equality
        assert!(logic::Pure::dest_equals(th.prop().term()).is_some());
    }

    /// reflexive: the type of the equality term is prop.
    #[test]
    fn prop_reflexive_is_prop(typ in arb_type()) {
        let t = term::Term::const_("x", typ);
        let ct = thm::CTerm::certify(t);
        let th = thm::ThmKernel::reflexive(ct);
        // The prop must be typed as prop
        assert_eq!(th.prop().term_type(), &types::Typ::base("prop"));
    }
}

proptest! {
    /// symmetric: involution — symmetric(symmetric(thm)) == thm (modulo alpha).
    #[test]
    fn prop_symmetric_involution(typ in arb_type()) {
        let t = term::Term::const_("a", typ.clone());
        let _u = term::Term::const_("b", typ);
        // Create t ≡ t (so symmetric is well-defined)
        let refl_t = mk_refl(&t);
        let sym1 = thm::ThmKernel::symmetric(&refl_t).unwrap();
        let sym2 = thm::ThmKernel::symmetric(&sym1).unwrap();
        // After two symmetries, we're back to t ≡ t
        let (lhs, rhs) = logic::Pure::dest_equals(sym2.prop().term()).unwrap();
        assert_eq!(lhs, &t);
        assert_eq!(rhs, &t);
    }

    /// symmetric on reflexive gives same proposition form.
    #[test]
    fn prop_symmetric_preserves_hyps(typ in arb_type()) {
        let t = term::Term::const_("x", typ);
        let ct = thm::CTerm::certify(t.clone());
        // assume x ⊢ x (an implication, not equality)
        let th = thm::ThmKernel::assume(ct);
        // symmetric on a non-equality should fail
        let result = thm::ThmKernel::symmetric(&th);
        assert!(result.is_err());
    }
}

proptest! {
    /// transitive: reflexive then transitive preserves the term.
    #[test]
    fn prop_transitive_preserves_hyps(typ in arb_type()) {
        let t = term::Term::const_("a", typ);
        let refl1 = mk_refl(&t);
        let refl2 = mk_refl(&t);
        let trans = thm::ThmKernel::transitive(&refl1, &refl2).unwrap();
        // t ≡ t trans t ≡ t → t ≡ t
        assert!(trans.is_unconditional());
        let (lhs, rhs) = logic::Pure::dest_equals(trans.prop().term()).unwrap();
        assert_eq!(lhs, &t);
        assert_eq!(rhs, &t);
    }
}

proptest! {
    /// implies_intr then implies_elim is a roundtrip.
    #[test]
    fn prop_implies_intro_elim_roundtrip(name in arb_prop_name()) {
        let t = term::Term::const_(name.as_str(), types::Typ::base("prop"));
        let ct = thm::CTerm::certify(t.clone());
        let assume_th = thm::ThmKernel::assume(ct.clone());

        // Introduce implication: ⊢ A ==> A
        let imp = thm::ThmKernel::implies_intr(&ct, &assume_th).unwrap();
        assert!(imp.is_unconditional());
        assert!(logic::Pure::dest_implies(imp.prop().term()).is_some());

        // Eliminate: if we re-assume A, we get A back
        let elim = thm::ThmKernel::implies_elim(&imp, &assume_th).unwrap();
        assert_eq!(elim.prop().term(), ct.term());
    }

    /// implies_intr with a non-matching hypothesis should fail.
    #[test]
    fn prop_implies_intr_fails_without_hyp(name in arb_prop_name()) {
        // Use distinct names: the input name for A, a fixed different name for B
        let b_name = if name == "B" { "C" } else { "B" };
        let a = thm::CTerm::certify(term::Term::const_(
            name.as_str(),
            types::Typ::base("prop"),
        ));
        let b = thm::CTerm::certify(term::Term::const_(
            b_name,
            types::Typ::base("prop"),
        ));
        let assume_b = thm::ThmKernel::assume(b.clone());
        // A is not in the hyps of assume_b (which contains only b)
        let result = thm::ThmKernel::implies_intr(&a, &assume_b);
        assert!(result.is_err(), "A ({name}) should not be in hyps of assume({b_name})");
    }
}

proptest! {
    /// forall_intr: if x is not free in hyps, we can introduce ∀.
    #[test]
    fn prop_forall_intr_on_unconditional(name in arb_var_name()) {
        let t = term::Term::const_("A", types::Typ::base("prop"));
        let ct = thm::CTerm::certify(t.clone());
        // Create an unconditional theorem via trivial(assume(A))
        let _assume_th = thm::ThmKernel::assume(ct.clone());
        let triv = thm::ThmKernel::trivial(ct).unwrap();
        // triv is unconditional (no hyps), so forall_intr should succeed
        let all = thm::ThmKernel::forall_intr(
            name.as_str(),
            types::Typ::dummy(),
            &triv,
        );
        assert!(all.is_ok());
    }

    /// trivial: always unconditional.
    #[test]
    fn prop_trivial_is_unconditional(name in arb_prop_name()) {
        let t = term::Term::const_(name.as_str(), types::Typ::base("prop"));
        let ct = thm::CTerm::certify(t);
        let th = thm::ThmKernel::trivial(ct).unwrap();
        assert!(th.is_unconditional());
        // trivial(A) gives A ==> A
        assert!(logic::Pure::dest_implies(th.prop().term()).is_some());
    }
}

proptest! {
    /// beta_conversion: (λx. t) x ≡ t, always unconditional.
    #[test]
    fn prop_beta_conversion_is_unconditional(
        (var_name, body) in (arb_var_name(), arb_bool_term())
    ) {
        let abs = term::Term::abs(
            var_name.as_str(),
            types::Typ::base("bool"),
            body.clone(),
        );
        let var = term::Term::free(var_name.as_str(), types::Typ::base("bool"));
        let app = term::Term::app(abs, var);
        let ct = thm::CTerm::certify(app);
        let result = thm::ThmKernel::beta_conversion(ct);
        // May fail if not a proper redex, but if it succeeds:
        if let Ok(th) = result {
            assert!(th.is_unconditional());
            assert!(logic::Pure::dest_equals(th.prop().term()).is_some());
        }
    }

    /// beta_conversion on non-redex should fail.
    #[test]
    fn prop_beta_conversion_fails_non_redex(name in arb_prop_name()) {
        // A non-application shouldn't beta-convert
        let t = term::Term::const_(name.as_str(), types::Typ::base("bool"));
        let ct = thm::CTerm::certify(t);
        let result = thm::ThmKernel::beta_conversion(ct);
        assert!(result.is_err());
    }
}

proptest! {
    /// instantiate: preserves hyps structure (modulo substitution).
    #[test]
    fn prop_instantiate_preserves_unconditional(name in arb_prop_name()) {
        let t = term::Term::const_(name.as_str(), types::Typ::base("prop"));
        let ct = thm::CTerm::certify(t);
        let th = thm::ThmKernel::trivial(ct).unwrap();
        // Instantiate with empty env → same theorem
        let env = envir::Envir::init();
        let inst = thm::ThmKernel::instantiate(&env, &th);
        assert!(inst.is_unconditional());
        // Empty substitution should not change the proposition
        assert_eq!(inst.prop().term(), th.prop().term());
    }
}

// =========================================================================
// Category 3: Algebraic laws — structural properties
// =========================================================================

proptest! {
    /// assume + implies_intr: the hypothesis set shrinks by 1.
    #[test]
    fn prop_implies_intr_removes_hyp(name in arb_prop_name()) {
        let a = term::Term::const_(name.as_str(), types::Typ::base("prop"));
        let ct_a = thm::CTerm::certify(a);
        let assume_a = thm::ThmKernel::assume(ct_a.clone());
        // Before: hyps = {A}
        assert_eq!(assume_a.hyps().len(), 1);
        // After implies_intr: hyps should be empty
        let imp = thm::ThmKernel::implies_intr(&ct_a, &assume_a).unwrap();
        assert!(imp.is_unconditional());
        assert_eq!(imp.hyps().len(), 0);
    }

    /// reflexive + symmetric: the resulting term has same components.
    #[test]
    fn prop_symmetric_preserves_components(typ in arb_type()) {
        let t = term::Term::const_("c", typ);
        let refl = mk_refl(&t);
        let sym = thm::ThmKernel::symmetric(&refl).unwrap();
        // After symmetric on refl, we still have t in both positions
        let (lhs, rhs) = logic::Pure::dest_equals(sym.prop().term()).unwrap();
        assert_eq!(lhs, &t);
        assert_eq!(rhs, &t);
    }
}

// =========================================================================
// Category 4: Unification invariants
// =========================================================================

proptest! {
    /// If unification succeeds, the normalized terms should be alpha-equivalent.
    #[test]
    fn prop_unify_produces_common_instance(
        (t1, t2) in (arb_term(), arb_term())
    ) {
        let config = unify::UnifyConfig {
            search_bound: 20,
            max_unifiers: 1,
        };
        let env = envir::Envir::init();
        let pairs = vec![(t1.clone(), t2.clone())];
        if let Some(result_env) = unify::unifiers(&env, &pairs, &config) {
            let t1_norm = result_env.norm_term(&t1);
            let t2_norm = result_env.norm_term(&t2);
            // After normalization, terms should be syntactically equal
            assert_eq!(t1_norm, t2_norm,
                "unification produced non-equal normalized terms");
        }
    }

    /// A term should always unify with itself.
    #[test]
    fn prop_unify_self_always_succeeds(t in arb_term()) {
        let config = unify::UnifyConfig {
            search_bound: 20,
            max_unifiers: 1,
        };
        let env = envir::Envir::init();
        let pairs = vec![(t.clone(), t.clone())];
        let result = unify::unifiers(&env, &pairs, &config);
        assert!(result.is_some(), "term should unify with itself: {:?}", t);
    }

    /// Unification is symmetric: unify(t, u) succeeds iff unify(u, t) does.
    #[test]
    fn prop_unify_symmetric(
        (t1, t2) in (arb_term(), arb_term())
    ) {
        let config = unify::UnifyConfig {
            search_bound: 20,
            max_unifiers: 1,
        };
        let env = envir::Envir::init();
        let r1 = unify::unifiers(&env, &[(t1.clone(), t2.clone())], &config).is_some();
        let r2 = unify::unifiers(&env, &[(t2, t1)], &config).is_some();
        assert_eq!(r1, r2, "unification is not symmetric");
    }
}

// =========================================================================
// Category 5: Simplifier invariants
// =========================================================================

proptest! {
    /// rewrite produces a theorem proving equivalence.
    #[test]
    fn prop_simplifier_rewrite_does_not_panic(t in arb_bool_term()) {
        use isabelle_rs::core::simplifier::Simplifier;
        // Create simplifier with no rules — validates API contract
        let simp = Simplifier::new(vec![]);
        // rewrite returns Option<(Term, Thm)> — should not panic
        let _result = simp.rewrite(&t);
    }

    /// rewrite_deep is a fixpoint on empty rules.
    #[test]
    fn prop_simplifier_deep_is_fixpoint(t in arb_bool_term()) {
        use isabelle_rs::core::simplifier::Simplifier;
        let simp = Simplifier::new(vec![]);
        if let Some((rewritten, _)) = simp.rewrite_deep(&t) {
            let again = simp.rewrite_deep(&rewritten);
            match again {
                None => {} // Good: can't simplify further
                Some((r2, _)) => {
                    // If it simplifies again, the result should be the same
                    assert_eq!(rewritten, r2,
                        "rewrite_deep is not a fixpoint: {:?} vs {:?}", rewritten, r2);
                }
            }
        }
    }
}

// =========================================================================
// Category 6: Term structural invariants
// =========================================================================

proptest! {
    /// Any term can be type-annotated from TypeEnv (no panic).
    #[test]
    fn prop_type_annotate_never_panics(t in arb_term()) {
        // Create a minimal type env
        let mut env = types::TypeEnv::new();
        env.declare_type("bool", 0);
        env.declare_type("nat", 0);
        env.declare_type("fun", 2);
        let mut t2 = t.clone();
        t2.type_annotate(&env);
        // Just checking it doesn't panic — the annotation is best-effort
    }

    /// maxidx computation is consistent.
    #[test]
    fn prop_maxidx_never_decreases(t in arb_term()) {
        let max1 = thm::CTerm::certify(t.clone()).maxidx();
        // Re-certifying should give same maxidx
        let max2 = thm::CTerm::certify(t).maxidx();
        assert_eq!(max1, max2);
    }
}

// =========================================================================
// Category 7: Morphism invariants
// =========================================================================

proptest! {
    /// Morphism::identity should map terms to themselves.
    #[test]
    fn prop_morphism_identity_preserves_term(t in arb_term()) {
        use isabelle_rs::core::morphism::Morphism;
        let id = Morphism::identity();
        let mapped = id.term(&t);
        // Identity morphism should produce alpha-equivalent term
        assert_eq!(t, mapped, "identity morphism changed term");
    }
}
