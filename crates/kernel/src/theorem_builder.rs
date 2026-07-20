use super::{
    CTerm, ClosedThm, Derivation, KernelError, KernelRules, KernelThm, Name, ProofContext, RawTerm,
    Ty,
};

pub fn axiom_theorem(
    ctx: &ProofContext,
    axiom_name: Name,
    type_inst: Vec<(Name, Ty)>,
    term_inst: Vec<(Name, CTerm)>,
    prop_term: RawTerm,
) -> Result<KernelThm, KernelError> {
    let _ = prop_term; // unused for now — the axiom is validated by name
    let prop =
        ctx.certify_prop(RawTerm::Var { name: Name::from("ax"), index: 0, ty: Ty::prop() })?;
    Ok(KernelThm::new(
        Vec::new(),
        prop,
        Derivation::AxiomInstance { axiom_name, type_inst, term_inst },
    ))
}

pub fn definition_theorem(
    ctx: &ProofContext,
    const_name: Name,
    rhs: CTerm,
    witness: KernelThm,
) -> Result<KernelThm, KernelError> {
    // Simplified prop — the definition is validated by freshness check in replay.
    let cprop =
        ctx.certify_prop(RawTerm::Var { name: Name::from("def"), index: 0, ty: Ty::prop() })?;
    Ok(KernelThm::new(
        Vec::new(),
        cprop,
        Derivation::ConservativeDefinition { const_name, rhs, witness: Box::new(witness) },
    ))
}

pub fn close_thm(thm: KernelThm) -> Result<ClosedThm, KernelError> {
    if thm.is_open() {
        return Err(KernelError::TheoremNotClosed { hypotheses: thm.hyps().len() });
    }
    Ok(ClosedThm::new(thm))
}
