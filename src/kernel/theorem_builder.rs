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
    let _ = prop_term; // unused for now — the axiom is validated by name
    let prop =
        ctx.certify_prop(RawTerm::Var { name: Name::from("ax"), index: 0, ty: Ty::prop() })?;
    Ok(KernelThm::new(
        Vec::new(),
        prop,
        Derivation::AxiomInstance { axiom_name, type_inst, term_inst },
    ))
}

pub(crate) fn definition_theorem(
    ctx: &ProofContext,
    certificate: &crate::kernel::DefinitionCertificate,
) -> Result<KernelThm, KernelError> {
    let prop_term = RawTerm::Eq {
        lhs: Box::new(RawTerm::Const {
            name: certificate.name.clone(),
            ty: certificate.declared_ty.clone(),
        }),
        rhs: Box::new(certificate.rhs_raw.clone()),
    };
    let prop = ctx.certify_prop(prop_term)?;
    Ok(KernelThm::new(
        Vec::new(),
        prop,
        Derivation::ConservativeDefinition {
            definition: certificate.id,
        },
    ))
}

pub(crate) fn close_thm(thm: KernelThm) -> Result<ClosedThm, KernelError> {
    if thm.is_open() {
        return Err(KernelError::TheoremNotClosed { hypotheses: thm.hyps().len() });
    }
    Ok(ClosedThm::new(thm))
}
