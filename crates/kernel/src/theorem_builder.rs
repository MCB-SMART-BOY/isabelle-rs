use super::{
    CTerm, ClosedThm, Derivation, KernelError, KernelRules, KernelThm, Name, ProofContext, RawTerm,
    Ty,
};

pub fn axiom_theorem(
    ctx: &ProofContext,
    basis: &super::LogicBasis,
    axiom_name: Name,
    type_inst: Vec<(Name, Ty)>,
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

pub fn definition_theorem(
    ctx: &ProofContext,
    const_name: Name,
    rhs: CTerm,
    rhs_raw: RawTerm,
) -> Result<KernelThm, KernelError> {
    let rhs_ty = rhs.ty();
    let prop_term = RawTerm::Eq {
        lhs: Box::new(RawTerm::Const { name: const_name.clone(), ty: rhs_ty.clone() }),
        rhs: Box::new(rhs_raw.clone()),
    };
    let prop = ctx.certify_prop(prop_term.clone())?;
    Ok(KernelThm::new(
        Vec::new(),
        prop,
        Derivation::ConservativeDefinition {
            const_name, rhs, rhs_raw, prop: prop_term,
        },
    ))
}
pub fn close_thm(thm: KernelThm) -> Result<ClosedThm, KernelError> {
    if thm.is_open() {
        return Err(KernelError::TheoremNotClosed { hypotheses: thm.hyps().len() });
    }
    Ok(ClosedThm::new(thm))
}
