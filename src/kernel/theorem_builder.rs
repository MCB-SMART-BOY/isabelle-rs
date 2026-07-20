use super::{
    CTerm, ClosedThm, Derivation, KernelError, KernelRules, KernelThm, Name, ProofContext, RawTerm,
    Ty,
};

pub(crate) fn axiom_theorem(
    ctx: &ProofContext,
    axiom_name: Name,
    type_inst: Vec<(Name, Ty)>,
    term_inst: Vec<(Name, CTerm)>,
    prop_term: RawTerm,
) -> Result<KernelThm, KernelError> {
    let prop = ctx.certify_prop(prop_term)?;
    Ok(KernelThm::new(
        Vec::new(),
        prop,
        Derivation::AxiomInstance { axiom_name, type_inst, term_inst },
    ))
}

pub(crate) fn definition_theorem(
    ctx: &ProofContext,
    const_name: Name,
    rhs: CTerm,
    witness: KernelThm,
) -> Result<KernelThm, KernelError> {
    let lhs = RawTerm::const_(const_name.clone(), rhs.term().ty().clone());
    let cprop = ctx.certify_prop(RawTerm::Eq {
        lhs: Box::new(lhs),
        rhs: Box::new(RawTerm::const_(Name::from("_rhs"), rhs.term().ty().clone())),
    })?;
    Ok(KernelThm::new(
        Vec::new(),
        cprop,
        Derivation::ConservativeDefinition { const_name, rhs, witness: Box::new(witness) },
    ))
}

pub(crate) fn close_thm(thm: KernelThm) -> Result<ClosedThm, KernelError> {
    if thm.is_open() {
        return Err(KernelError::TheoremNotClosed { hypotheses: thm.hyps().len() });
    }
    Ok(ClosedThm::new(thm))
}
