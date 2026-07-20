//! HOL definitions and theorems through the new kernel acceptance pipeline.

use crate::kernel::{
    ClosedThm, Derivation, KernelError, KernelRules, Name, ProofContext, RawTerm, Signature,
    TrustedTheorem, TrustedTheory, Ty, accept_closed_theorem, theorem_builder,
};

pub fn define_true(
    theory: &TrustedTheory,
) -> Result<(TrustedTheory, TrustedTheorem), crate::kernel::KernelError> {
    let bool_ty = Ty::base("bool").unwrap();
    let rhs_raw = {
        let bool_arrow = Ty::arrow(bool_ty.clone(), bool_ty.clone());
        let fun_ty = Ty::arrow(bool_arrow.clone(), Ty::arrow(bool_arrow.clone(), bool_ty.clone()));
        let hol_eq = RawTerm::const_(Name::from("HOL.eq"), fun_ty);
        let id_abs = RawTerm::abs(Name::from("x"), bool_ty.clone(), RawTerm::bound(0));
        RawTerm::app(RawTerm::app(hol_eq, id_abs.clone()), id_abs)
    };
    // Atomic extend_definition: freshness, closedness, DefineConst extension
    let (theory, rhs) = theory.extend_definition(Name::from("HOL.True"), rhs_raw.clone())?;

    let ctx = ProofContext::new(theory.snapshot().clone());
    let rhs_child = ctx.certify_term(rhs_raw.clone())?;
    let def_thm =
        theorem_builder::definition_theorem(&ctx, Name::from("HOL.True"), rhs_child, rhs_raw)?;
    let closed = theorem_builder::close_thm(def_thm)?;
    accept_closed_theorem(&theory, "True_def", closed)
}

pub fn prove_true_i(
    theory: &TrustedTheory,
) -> Result<(TrustedTheory, TrustedTheorem), crate::kernel::KernelError> {
    let basis = theory
        .logic_basis()
        .ok_or_else(|| KernelError::Invariant("theory requires an installed logic basis".into()))?;

    let bool_ty = Ty::base("bool").unwrap();
    let id_ty = Ty::arrow(bool_ty.clone(), bool_ty.clone());
    let id_raw = RawTerm::abs(Name::from("x"), bool_ty.clone(), RawTerm::bound(0));

    // -- 1. Define HOL.True and accept True_def as a theorem --
    let (theory, true_def_token) = define_true(theory)?;

    // -- 2. Reference the accepted True_def theorem --
    let true_def_closed = KernelRules::theorem_ref(&theory, &true_def_token)?;

    // -- 3. Create proof context and certify the id term --
    let ctx = ProofContext::new(theory.snapshot().clone());
    let id_cterm = ctx.certify_term(id_raw.clone())?;

    // -- 4. Construct the RHS raw term for refl instantiation --
    let rhs_raw = {
        let fun_ty = Ty::arrow(id_ty.clone(), Ty::arrow(id_ty.clone(), bool_ty.clone()));
        let hol_eq = RawTerm::const_(Name::from("HOL.eq"), fun_ty);
        RawTerm::app(RawTerm::app(hol_eq, id_raw.clone()), id_raw.clone())
    };

    // -- 5. Derive Trueprop(rhs) via HOL.refl --
    let trueprop_const =
        RawTerm::const_(Name::from("HOL.Trueprop"), Ty::arrow(bool_ty.clone(), Ty::prop()));
    let rhs_prop = RawTerm::app(trueprop_const, rhs_raw.clone());
    let refl_thm = theorem_builder::axiom_theorem(
        &ctx,
        basis,
        Name::from("HOL.refl"),
        vec![(Name::from("'a"), id_ty.clone())],
        vec![id_cterm],
        rhs_prop,
    )?;

    // -- 6. Lift True_def to prop level via Combination --
    let tp_cterm = ctx.certify_term(RawTerm::const_(
        Name::from("HOL.Trueprop"),
        Ty::arrow(bool_ty, Ty::prop()),
    ))?;
    let tp_refl = KernelRules::reflexive(tp_cterm);
    let lifted = KernelRules::combination(tp_refl.as_kernel(), true_def_closed.as_kernel())?;

    // Symmetric: Trueprop RHS == Trueprop True
    let lifted_sym = KernelRules::symmetric(&lifted)?;
    let true_i_thm = KernelRules::equal_elim(&lifted_sym, &refl_thm)?;
    let closed = theorem_builder::close_thm(true_i_thm)?;
    accept_closed_theorem(&theory, "TrueI", closed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hol::hol_basis::hol_basis;
    use crate::kernel::Signature;

    #[test]
    fn define_true_produces_accepted_theorem() {
        let sig = Signature::new()
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()))
            .unwrap()
            .extend_const("HOL.eq", {
                let ba = Ty::arrow(Ty::base("bool").unwrap(), Ty::base("bool").unwrap());
                Ty::arrow(ba.clone(), Ty::arrow(ba.clone(), Ty::base("bool").unwrap()))
            })
            .unwrap();
        let basis = hol_basis();
        let theory = TrustedTheory::with_basis("HOL", sig, &basis).unwrap();
        match define_true(&theory) {
            Ok((_child, token)) => assert_eq!(token.name().as_str(), "True_def"),
            Err(e) => panic!("define_true: {e:?}"),
        }
    }
    #[test]
    fn prove_true_i_succeeds() {
        let bool_ty = Ty::base("bool").unwrap();
        let sig = Signature::new()
            .extend_const("HOL.Trueprop", Ty::arrow(bool_ty.clone(), Ty::prop()))
            .unwrap()
            .extend_const("HOL.eq", {
                let ba = Ty::arrow(Ty::base("bool").unwrap(), Ty::base("bool").unwrap());
                Ty::arrow(ba.clone(), Ty::arrow(ba.clone(), Ty::base("bool").unwrap()))
            })
            .unwrap();
        let basis = hol_basis();
        let theory = TrustedTheory::with_basis("HOL", sig, &basis).unwrap();
        match prove_true_i(&theory) {
            Ok((_child, token)) => {
                assert_eq!(token.name().as_str(), "TrueI", "theorem name must be TrueI");
                assert!(token.prop().term().ty().is_prop(), "TrueI proposition must be prop-typed");
                // Exact proposition: must destructure as HOL.Trueprop applied to HOL.True
                if let Some((_head, arg)) = token.prop().term().dest_app() {
                    assert_eq!(
                        arg.ty(),
                        Ty::base("bool").unwrap(),
                        "TrueI argument must be bool-typed HOL.True"
                    );
                } else {
                    panic!("TrueI proposition must be an application");
                }
            },
            Err(e) => panic!("prove_true_i failed: {e:?}"),
        }
    }
}
