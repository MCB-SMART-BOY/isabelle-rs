//! Property-based tests for Isabelle-rs kernel.
//!
//! Uses `proptest` to verify invariants of the LCF kernel
//! with randomly generated inputs.

use proptest::prelude::*;
use isabelle_rs::core::*;

// =========================================================================
// Strategies
// =========================================================================

fn type_name() -> impl Strategy<Value = String> {
    prop::sample::select(vec![
        "bool".to_string(), "nat".to_string(), "prop".to_string(), "dummy".to_string(),
    ])
}

fn prop_name() -> impl Strategy<Value = String> {
    prop::sample::select(vec![
        "A".to_string(), "B".to_string(), "P".to_string(), "Q".to_string(),
    ])
}

// =========================================================================
// Property tests
// =========================================================================

proptest! {
    #[test]
    fn term_display_never_panics(name in type_name()) {
        let t = Term::const_(name.as_str(), Typ::base("prop"));
        let _ = format!("{:?}", t);
        let _ = format!("{}", t);

        let f = Term::free("x", Typ::base("prop"));
        let app = Term::app(t, f);
        let _ = format!("{:?}", app);
        let _ = format!("{}", app);

        let abs = Term::abs("y", Typ::base("dummy"), Term::bound(0));
        let _ = format!("{:?}", abs);
        let _ = format!("{}", abs);
    }

    #[test]
    fn type_display_never_panics(name in type_name()) {
        let t = Typ::base(name.as_str());
        let _ = format!("{:?}", t);
        let arr = Typ::arrow(t.clone(), Typ::base("bool"));
        let _ = format!("{:?}", arr);
    }

    #[test]
    fn assume_has_prop_in_hyps(name in prop_name()) {
        let a = CTerm::certify(Term::const_(name.as_str(), Typ::base("prop")));
        let thm = ThmKernel::assume(a.clone());
        assert!(thm.hyps().contains(&a));
    }

    #[test]
    fn reflexive_is_unconditional(name in type_name()) {
        let t = CTerm::certify(Term::const_(name.as_str(), Typ::base(name.as_str())));
        let thm = ThmKernel::reflexive(t);
        assert!(thm.is_unconditional());
    }

    #[test]
    fn trivial_is_unconditional(name in prop_name()) {
        let a = CTerm::certify(Term::const_(name.as_str(), Typ::base("prop")));
        let thm = ThmKernel::trivial(a).unwrap();
        assert!(thm.is_unconditional());
    }

    #[test]
    fn symmetric_reflexive_is_equality(name in type_name()) {
        let t = CTerm::certify(Term::const_(name.as_str(), Typ::base(name.as_str())));
        let refl = ThmKernel::reflexive(t);
        let sym = ThmKernel::symmetric(&refl).unwrap();
        assert!(Pure::dest_equals(sym.prop().term()).is_some());
    }

    #[test]
    fn intern_deduplicates(s in "\\PC+") {
        let a = types::intern(&s);
        let b = types::intern(&s);
        assert!(std::sync::Arc::ptr_eq(&a, &b));
    }
}

#[test]
fn beta_conversion_is_equality() {
    let lam = Term::abs("x", Typ::base("dummy"), Term::bound(0));
    let arg = Term::free("a", Typ::base("dummy"));
    let app = Term::app(lam, arg);
    let ct = CTerm::certify(app);
    let thm = ThmKernel::beta_conversion(ct).expect("beta_conversion should succeed");
    assert!(Pure::dest_equals(thm.prop().term()).is_some());
}
