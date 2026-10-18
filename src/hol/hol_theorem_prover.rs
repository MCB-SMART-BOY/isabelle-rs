//! HOL definitions and theorems through the new kernel acceptance pipeline.

use crate::{
    isar::{
        elaborator::{ElaborationError, elaborate_proposition},
        source_ast::SourceProposition,
    },
    kernel::{
        KernelError, KernelRules, Name, ProofContext, RawTerm, Sort, TrustedTheorem, TrustedTheory,
        Ty, accept_closed_theorem,
        logic::{TypeInstantiation, TypeVarId},
        theorem_builder,
    },
};

#[derive(Debug, thiserror::Error)]
pub enum TrueIProofError {
    #[error("failed to elaborate source proposition: {0}")]
    Elaboration(#[from] ElaborationError),
    #[error("source proposition does not match the proposition proved for TrueI")]
    PropositionMismatch,
    #[error("kernel rejected the TrueI derivation: {0}")]
    Kernel(#[from] Box<KernelError>),
}

impl From<KernelError> for TrueIProofError {
    fn from(source: KernelError) -> Self {
        Self::Kernel(Box::new(source))
    }
}

pub fn define_true(
    theory: &TrustedTheory,
) -> Result<(TrustedTheory, TrustedTheorem), Box<KernelError>> {
    let bool_ty = Ty::base("bool")?;
    let rhs_raw = {
        let bool_arrow = Ty::arrow(bool_ty.clone(), bool_ty.clone());
        let fun_ty = Ty::arrow(bool_arrow.clone(), Ty::arrow(bool_arrow.clone(), bool_ty.clone()));
        let hol_eq = RawTerm::const_(Name::from("HOL.eq"), fun_ty);
        let id_abs = RawTerm::abs(Name::from("x"), bool_ty.clone(), RawTerm::bound(0));
        RawTerm::app(RawTerm::app(hol_eq, id_abs.clone()), id_abs)
    };
    // Atomic define_const: produces certificate, extends theory, accepts theorem
    theory.define_const(Name::from("HOL.True"), rhs_raw).map_err(Box::new)
}

pub fn prove_true_i(
    theory: &TrustedTheory,
    source_proposition: &SourceProposition,
) -> Result<(TrustedTheory, TrustedTheorem), TrueIProofError> {
    let (theory, true_def_token) = define_true(theory)?;
    prove_true_i_from_definition(&theory, &true_def_token, source_proposition)
}

/// Replay the TrueI derivation against an already accepted definition.
/// The caller owns source elaboration and must supply the definition in `theory`.
pub(crate) fn prove_true_i_from_definition(
    theory: &TrustedTheory,
    true_def_token: &TrustedTheorem,
    source_proposition: &SourceProposition,
) -> Result<(TrustedTheory, TrustedTheorem), TrueIProofError> {
    let context = ProofContext::new(theory.snapshot().clone());
    let source_goal = elaborate_proposition(source_proposition, &context)?;
    let derived = derive_unfolding_refl(theory, true_def_token)?;
    if !source_goal.term().alpha_eq(derived.prop().term()) {
        return Err(TrueIProofError::PropositionMismatch);
    }
    let discharged = KernelRules::strip_shyps(theory, &context, &derived)?;
    let closed = theorem_builder::close_thm(discharged)?;
    Ok(accept_closed_theorem(theory, "TrueI", closed)?)
}

fn derive_unfolding_refl(
    theory: &TrustedTheory,
    true_def_token: &TrustedTheorem,
) -> Result<crate::kernel::KernelThm, Box<KernelError>> {
    let basis = theory
        .logic_basis()
        .ok_or_else(|| KernelError::Invariant("theory requires an installed logic basis".into()))?;
    let true_def = KernelRules::theorem_ref(theory, true_def_token)?;
    let context = ProofContext::new(theory.snapshot().clone());
    let bool_ty = Ty::base("bool")?;
    let identity_ty = Ty::arrow(bool_ty.clone(), bool_ty.clone());
    let identity = RawTerm::abs("x", bool_ty.clone(), RawTerm::bound(0));
    let equality_ty =
        Ty::arrow(identity_ty.clone(), Ty::arrow(identity_ty.clone(), bool_ty.clone()));
    let equality = RawTerm::app(
        RawTerm::app(RawTerm::const_("HOL.eq", equality_ty), identity.clone()),
        identity.clone(),
    );
    let trueprop_ty = Ty::arrow(bool_ty, Ty::prop());
    let proposition = RawTerm::app(RawTerm::const_("HOL.Trueprop", trueprop_ty.clone()), equality);
    let mut bindings = std::collections::BTreeMap::new();
    bindings.insert(TypeVarId::new("'a", 0, Sort::hol_type()), identity_ty);
    let refl = theorem_builder::axiom_theorem(
        &context,
        basis,
        Name::from("HOL.refl"),
        TypeInstantiation::try_new(bindings)?,
        vec![context.certify_term(identity)?],
        proposition,
    )?;
    let trueprop = context.certify_term(RawTerm::const_("HOL.Trueprop", trueprop_ty))?;
    let trueprop_refl = KernelRules::reflexive(trueprop);
    let lifted = KernelRules::combination(trueprop_refl.as_kernel(), true_def.as_kernel())?;
    let symmetric = KernelRules::symmetric(&lifted)?;
    KernelRules::equal_elim(&symmetric, &refl).map_err(Box::new)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        hol::hol_basis::hol_owner,
        isar::{source_ast::SourceId, source_parser::parse_source_proposition},
    };

    #[test]
    fn define_true_produces_accepted_theorem() {
        let theory = hol_owner("HOL").unwrap();
        match define_true(&theory) {
            Ok((_child, token)) => assert_eq!(token.name().as_str(), "HOL.True_def"),
            Err(e) => panic!("define_true: {e:?}"),
        }
    }
    #[test]
    fn prove_true_i_succeeds() {
        let theory = hol_owner("HOL").unwrap();
        let source = parse_source_proposition("True", SourceId::new("HOL.thy")).unwrap();
        match prove_true_i(&theory, &source) {
            Ok((_child, token)) => {
                assert_eq!(token.name().as_str(), "TrueI", "theorem name must be TrueI");
                assert!(token.prop().term().ty().is_prop(), "TrueI proposition must be prop-typed");
                // Exact proposition: TrueI must be |- HOL.Trueprop HOL.True
                let term = token.prop().term();
                if let Some((head, arg)) = term.dest_app() {
                    use crate::kernel::Term;
                    match (head, arg) {
                        (Term::Const { name: hn, ty: ht }, Term::Const { name: an, ty: at }) => {
                            assert_eq!(hn.as_str(), "HOL.Trueprop", "head must be HOL.Trueprop");
                            assert_eq!(
                                ht,
                                &Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()),
                                "head type must be bool -> prop"
                            );
                            assert_eq!(an.as_str(), "HOL.True", "arg must be HOL.True");
                            assert_eq!(at, &Ty::base("bool").unwrap(), "arg type must be bool");
                        },
                        _ => panic!(
                            "TrueI head and arg must be Const nodes, got {:?} / {:?}",
                            head, arg
                        ),
                    }
                } else {
                    panic!("TrueI proposition must be an application, got {:?}", term);
                }
            },
            Err(e) => panic!("prove_true_i failed: {e:?}"),
        }
    }
}
