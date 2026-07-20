//! HOL definitions and theorems through the new kernel acceptance pipeline.

use crate::kernel::{
    ClosedThm, Derivation, KernelRules, Name, ProofContext, RawTerm, Signature, TrustedTheorem,
    TrustedTheory, Ty, accept_closed_theorem, theorem_builder,
};

pub fn define_true(
    theory: &TrustedTheory,
) -> Result<(TrustedTheory, TrustedTheorem), crate::kernel::KernelError> {
    let bool_ty = Ty::base("bool").unwrap();
    let ctx = ProofContext::new(theory.snapshot().clone());

    let rhs_term = RawTerm::Eq {
        lhs: Box::new(RawTerm::Abs {
            name: Name::from("x"),
            ty: bool_ty.clone(),
            body: Box::new(RawTerm::Bound(0)),
        }),
        rhs: Box::new(RawTerm::Abs {
            name: Name::from("x"),
            ty: bool_ty.clone(),
            body: Box::new(RawTerm::Bound(0)),
        }),
    };
    let rhs_cterm = ctx.certify_term(rhs_term)?;
    let refl_thm = KernelRules::reflexive(rhs_cterm.clone()).into_kernel();
    let def_thm =
        theorem_builder::definition_theorem(&ctx, Name::from("HOL.True"), rhs_cterm, refl_thm)?;
    let closed = theorem_builder::close_thm(def_thm)?;
    accept_closed_theorem(theory, "True_def", closed)
}

pub fn prove_true_i(
    theory: &TrustedTheory,
) -> Result<(TrustedTheory, TrustedTheorem), crate::kernel::KernelError> {
    let (theory, _true_def) = if theory.get(&Name::from("True_def")).is_none() {
        define_true(theory)?
    } else {
        (theory.clone(), theory.get(&Name::from("True_def")).unwrap().clone())
    };
    let ctx = ProofContext::new(theory.snapshot().clone());
    let true_i_thm = theorem_builder::axiom_theorem(
        &ctx,
        Name::from("HOL.refl"),
        vec![(Name::from("'a"), Ty::base("bool").unwrap())],
        vec![], // term_inst deferred
        RawTerm::app(
            RawTerm::const_(
                Name::from("HOL.Trueprop"),
                Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()),
            ),
            RawTerm::const_(Name::from("HOL.True"), Ty::base("bool").unwrap()),
        ),
    )?;
    let closed = theorem_builder::close_thm(true_i_thm)?;
    accept_closed_theorem(&theory, "TrueI", closed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Signature;
    use crate::hol::hol_basis::hol_basis;

    #[test]
    fn define_true_produces_accepted_theorem() {
        let sig = Signature::new()
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop())).unwrap()
            .extend_const("HOL.eq", Ty::arrow(
                Ty::base("'a").unwrap(),
                Ty::arrow(Ty::base("'a").unwrap(), Ty::base("bool").unwrap()),
            )).unwrap();
        let basis = hol_basis();
        let theory = TrustedTheory::with_basis("HOL", sig, &basis).unwrap();
        let result = define_true(&theory);
        assert!(result.is_ok(), "define_true: {:?}", result.err());
    }
}
