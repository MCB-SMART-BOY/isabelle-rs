use super::{
    CTerm, ClosedThm, Derivation, KernelError, KernelThm, Name, ProofContext,
    RawTerm, Ty,
};
use super::theory::DefinitionCertificate;

pub fn axiom_theorem(
    ctx: &ProofContext,
    basis: &super::LogicBasis,
    axiom_name: Name,
    type_inst: crate::logic::TypeInstantiation,
    term_inst: Vec<CTerm>,
    prop_term: RawTerm,
) -> Result<KernelThm, KernelError> {
    let schema = basis.get_axiom(&axiom_name)
        .ok_or_else(|| KernelError::Invariant(
            format!("axiom `{axiom_name}` not found in logic basis").into(),
        ))?;
    // Independently instantiate the schema
    let typed = crate::term::subst_types(&schema.prop, &type_inst)?;
    let expected = crate::term::instantiate_schema_binders(&typed, &term_inst)?;
    // Certify both — must produce the same proposition
    let supplied = ctx.certify_prop(prop_term)?;
    let expected_prop = ctx.certify_prop(expected)?;
    if supplied.term() != expected_prop.term() {
        return Err(KernelError::Invariant(
            "supplied proposition does not match instantiated axiom schema".into(),
        ));
    }
    Ok(KernelThm::new(
        Vec::new(),
        supplied,
        Derivation::AxiomInstance {
            axiom_name, type_inst, term_inst,
        },
    ))
}

pub(crate) fn definition_theorem(
    ctx: &ProofContext,
    certificate: &DefinitionCertificate,
) -> Result<KernelThm, KernelError> {
    // Independently reconstruct const == rhs from the certificate
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
pub fn close_thm(thm: KernelThm) -> Result<ClosedThm, KernelError> {
    if thm.is_open() {
        return Err(KernelError::TheoremNotClosed { hypotheses: thm.hyps().len() });
    }
    Ok(ClosedThm::new(thm))
}
