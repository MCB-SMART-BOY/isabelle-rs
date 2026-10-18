//! Non-authoritative consumer shared by the executable and its contract tests.
//! Every theorem comes from public checked kernel operations; assertions describe
//! the observable smoke contract, not additional kernel rules.

use isabelle_kernel::{
    CompositionCandidate, CompositionFlags, CompositionOptions, InstEntry, KernelError,
    KernelRules, KernelThm, ProofContext, RawTerm, Signature, TrustedTheorem, TrustedTheory, Ty,
    TypeInstantiation, accept_closed_theorem,
};

pub fn make_function_type() -> Ty {
    Ty::arrow(Ty::prop(), Ty::prop())
}

pub fn make_premise() -> RawTerm {
    RawTerm::eq(RawTerm::const_("p", Ty::prop()), RawTerm::const_("q", Ty::prop()))
}

fn make_application(function: RawTerm, argument: &str) -> RawTerm {
    RawTerm::app(function, RawTerm::const_(argument, Ty::prop()))
}

pub fn make_image_equality() -> RawTerm {
    let g = RawTerm::const_("g", make_function_type());
    RawTerm::eq(make_application(g.clone(), "p"), make_application(g, "q"))
}

pub fn make_conclusion() -> RawTerm {
    let g = RawTerm::const_("g", make_function_type());
    RawTerm::eq(make_application(g.clone(), "q"), make_application(g, "p"))
}

pub fn create_root() -> Result<TrustedTheory, KernelError> {
    let signature = Signature::new()
        .extend_const("p", Ty::prop())?
        .extend_const("q", Ty::prop())?
        .extend_const("g", make_function_type())?;
    Ok(TrustedTheory::root("NativeThm", signature))
}

pub fn create_child(root: &TrustedTheory) -> Result<TrustedTheory, KernelError> {
    let child = root.begin_child("NativeThm.Child").extend_const("r", Ty::prop())?;
    assert_ne!(root.stamp(), child.stamp());
    Ok(child)
}

pub fn create_empty_candidate() -> CompositionCandidate {
    CompositionCandidate {
        type_inst: TypeInstantiation::empty(),
        rule_subst: Vec::new(),
        state_subst: Vec::new(),
        residual_pairs: Vec::new(),
        elimination_choice: None,
    }
}

pub fn derive_schematic_congruence(context: &ProofContext) -> Result<KernelThm, KernelError> {
    let certified_type = context.certify_type(make_function_type())?;
    assert_eq!(certified_type.ty(), &make_function_type());
    assert_eq!(certified_type.context(), context.stamp());
    let premise = context.certify_prop(make_premise())?;
    let assumed = KernelRules::assume(premise.clone())?;
    assert_eq!(assumed.as_kernel().hyps(), std::slice::from_ref(&premise));
    let f = RawTerm::var("f", 0, certified_type.ty().clone());
    let reflexive = KernelRules::reflexive(context.certify_term(f.clone())?);
    let combined = KernelRules::combination(reflexive.as_kernel(), assumed.as_kernel())?;
    let expected = context
        .certify_prop(RawTerm::eq(make_application(f.clone(), "p"), make_application(f, "q")))?;
    assert_eq!(combined.prop(), &expected);
    assert_eq!(combined.hyps(), std::slice::from_ref(&premise));
    Ok(combined)
}

pub fn derive_instantiated_congruence(context: &ProofContext) -> Result<KernelThm, KernelError> {
    let source = derive_schematic_congruence(context)?;
    let replacement = context.certify_term(RawTerm::const_("g", make_function_type()))?;
    let instance = KernelRules::instantiate(
        context,
        &source,
        &TypeInstantiation::empty(),
        &[InstEntry::new("f", 0, make_function_type(), replacement)],
    )?;
    assert_eq!(instance.prop(), &context.certify_prop(make_image_equality())?);
    assert_eq!(instance.hyps(), source.hyps());
    Ok(instance)
}

pub fn derive_composed_symmetry(owner: &TrustedTheory) -> Result<KernelThm, KernelError> {
    let context = ProofContext::new(owner.snapshot().clone());
    let rule = derive_instantiated_congruence(&context)?;
    let image_equality = context.certify_prop(make_image_equality())?;
    let assumed = KernelRules::assume(image_equality.clone())?;
    let symmetric = KernelRules::symmetric(assumed.as_kernel())?;
    let state = KernelRules::implies_intr(&image_equality, &symmetric)?;
    assert!(state.hyps().is_empty());
    // premise_count counts rule implications, not real hypotheses H.
    let composed = KernelRules::bicompose_candidate(
        owner,
        &context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        &rule,
        &state,
        &create_empty_candidate(),
    )?;
    assert_eq!(composed.prop(), &context.certify_prop(make_conclusion())?);
    assert_eq!(composed.hyps(), rule.hyps());
    Ok(composed)
}

pub fn transfer_to_child(
    root: &TrustedTheory,
    source: &KernelThm,
) -> Result<(TrustedTheory, KernelThm), KernelError> {
    let child = create_child(root)?;
    let transferred = KernelRules::transfer(&child, source)?;
    let context = ProofContext::new(child.snapshot().clone());
    let premise = context.certify_prop(make_premise())?;
    assert_eq!(transferred.context(), child.stamp());
    assert_eq!(transferred.hyps(), std::slice::from_ref(&premise));
    assert_eq!(transferred.prop().term(), source.prop().term());
    Ok((child, transferred))
}

pub fn run_closure() -> Result<(TrustedTheorem, TrustedTheorem), KernelError> {
    let root = create_root()?;
    let composed = derive_composed_symmetry(&root)?;
    let (child, transferred) = transfer_to_child(&root, &composed)?;
    let context = ProofContext::new(child.snapshot().clone());
    let premise = context.certify_prop(make_premise())?;
    let discharged = KernelRules::implies_intr(&premise, &transferred)?;
    assert!(discharged.hyps().is_empty());
    let closed = discharged.try_close()?;
    let (accepted_owner, token) = accept_closed_theorem(&child, "congruence_symmetry", closed)?;
    let expected = context.certify_prop(RawTerm::imp(make_premise(), make_conclusion()))?;
    assert_eq!(token.prop(), &expected);
    assert_eq!(token.proved_context(), child.stamp());
    assert_eq!(token.accepted_in(), accepted_owner.id());
    assert_ne!(token.proved_in(), token.accepted_in());
    assert!(token.dependencies().is_empty());
    for old_owner in [&root, &child] {
        assert!(old_owner.get(token.name()).is_none());
        assert!(matches!(
            KernelRules::theorem_ref(old_owner, &token),
            Err(KernelError::UnknownTheoremDependency)
        ));
    }
    let reference = KernelRules::theorem_ref(&accepted_owner, &token)?;
    assert_eq!(reference.context(), accepted_owner.stamp());
    assert_eq!(reference.as_kernel().prop().term(), expected.term());
    let (reused_owner, reused) = accept_closed_theorem(&accepted_owner, "reused", reference)?;
    assert_eq!(reused.prop().term(), expected.term());
    assert_eq!(reused.proved_context(), accepted_owner.stamp());
    assert_eq!(reused.accepted_in(), reused_owner.id());
    assert_eq!(reused.dependencies().len(), 1);
    assert_eq!(accepted_owner.get(token.name()), Some(&token));
    assert_eq!(reused_owner.get(reused.name()), Some(&reused));
    for owner in [&root, &child, &accepted_owner, &reused_owner] {
        assert!(owner.logic_basis().is_none());
    }
    Ok((token, reused))
}
