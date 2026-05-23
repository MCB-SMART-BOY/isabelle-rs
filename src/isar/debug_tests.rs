#[cfg(test)]
mod debug_tests {
    use crate::hol::hol_loader::HolTheoremDb;
    use crate::core::thm::{Thm, ThmKernel, CTerm};
    use crate::core::logic::Pure;
    use std::sync::Arc;

    #[test]
    fn test_erule_sym() {
        let db = HolTheoremDb::get();
        use crate::core::term::Term;
        let eqc = Term::const_("HOL.eq", crate::core::types::Typ::dummy());
        fn mk_eq(c: &Term, a: Term, b: Term) -> Term { Term::app(Term::app(c.clone(), a), b) }

        // State: Suc m = 0 ==> R  (after rule Suc_neq_Zero on trivial(R))
        let suc = Term::app(Term::free("Suc", crate::core::types::Typ::dummy()), Term::free("m", crate::core::types::Typ::dummy()));
        let sm0 = mk_eq(&eqc, suc, Term::const_("0", crate::core::types::Typ::dummy()));
        let goal = Pure::mk_implies(sm0, Term::const_("R", crate::core::types::Typ::base("prop")));
        let state = ThmKernel::assume(CTerm::certify(goal));
        eprintln!("State: nprems={}", state.nprems());

        // Get sym from DB
        if let Some(sym) = db.by_name.get("sym") {
            eprintln!("sym: nprems={}, prem0={}", sym.nprems(), sym.prem(0).unwrap());
            eprintln!("sym concl: {}", sym.concl());
            
            // Create premise: assume(0 = Suc m)
            let zs = mk_eq(&eqc, Term::const_("0", crate::core::types::Typ::dummy()),
                Term::app(Term::free("Suc", crate::core::types::Typ::dummy()), Term::free("m", crate::core::types::Typ::dummy())));
            let assume_prem = Arc::new(ThmKernel::assume(CTerm::certify(zs)));
            let premises = vec![assume_prem];

            // Try eresolve
            let results = crate::core::tactic::eresolve_tac(&[Arc::clone(sym)], 0)
                .apply(&state, &premises);
            eprintln!("eresolve_tac results: {} states", results.len());

            // Try bicompose_eresolve directly
            let bc = ThmKernel::bicompose_eresolve(true, sym, &state, 0, &premises);
            eprintln!("bicompose_eresolve: {:?}", bc.is_some());
            if let Some(r) = bc {
                eprintln!("  nprems={}", r.nprems());
            }
        }
    }
}
