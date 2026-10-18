//! Non-authoritative public consumer shared by the executable and integration tests.
use std::collections::{BTreeMap, BTreeSet};

use isabelle_kernel::{
    CompositionCandidate, CompositionFlags, CompositionOptions, InstEntry, KernelError,
    KernelRules, KernelThm, Name, ProofContext, RawTerm, Signature, Sort, TrustedTheorem,
    TrustedTheory, Ty, TypeInstantiation, TypeVarId, accept_closed_theorem,
};

pub struct BranchOutcome {
    pub branch_owner: TrustedTheory,
    pub deep_owner: TrustedTheory,
    pub accepted_owner: TrustedTheory,
    pub reused_owner: TrustedTheory,
    pub instance: TrustedTheorem,
    pub reused: TrustedTheorem,
}

pub struct ConsumerOutcome {
    pub root: TrustedTheory,
    pub schema_owner: TrustedTheory,
    pub schema: TrustedTheorem,
    pub left: BranchOutcome,
    pub right: BranchOutcome,
}

#[derive(Clone, Copy)]
struct BranchSpec {
    ty: &'static str,
    p: &'static str,
    q: &'static str,
    g: &'static str,
    marker: &'static str,
    deep_marker: &'static str,
    name: &'static str,
}

const LEFT: BranchSpec = BranchSpec {
    ty: "left_ty",
    p: "p_left",
    q: "q_left",
    g: "g_left",
    marker: "left_marker",
    deep_marker: "left_deep_marker",
    name: "left_instance",
};
const RIGHT: BranchSpec = BranchSpec {
    ty: "right_ty",
    p: "p_right",
    q: "q_right",
    g: "g_right",
    marker: "right_marker",
    deep_marker: "right_deep_marker",
    name: "right_instance",
};

fn make_names(names: &[&str]) -> BTreeSet<Name> {
    names.iter().map(|name| Name::from(*name)).collect()
}

fn make_premise(spec: BranchSpec) -> Result<RawTerm, KernelError> {
    let ty = Ty::base(spec.ty)?;
    Ok(RawTerm::eq(RawTerm::const_(spec.p, ty.clone()), RawTerm::const_(spec.q, ty)))
}

fn make_conclusion(spec: BranchSpec, is_reversed: bool) -> Result<RawTerm, KernelError> {
    let ty = Ty::base(spec.ty)?;
    let function = RawTerm::const_(spec.g, Ty::arrow(ty.clone(), ty.clone()));
    let (left, right) = if is_reversed { (spec.q, spec.p) } else { (spec.p, spec.q) };
    Ok(RawTerm::eq(
        RawTerm::app(function.clone(), RawTerm::const_(left, ty.clone())),
        RawTerm::app(function, RawTerm::const_(right, ty)),
    ))
}

pub fn create_root() -> Result<TrustedTheory, KernelError> {
    let mut signature = Signature::new()
        .extend_type_constructor(LEFT.ty, 0)?
        .extend_type_constructor(RIGHT.ty, 0)?;
    for spec in [LEFT, RIGHT] {
        let ty = Ty::base(spec.ty)?;
        signature = signature
            .extend_const(spec.p, ty.clone())?
            .extend_const(spec.q, ty.clone())?
            .extend_const(spec.g, Ty::arrow(ty.clone(), ty))?;
    }
    Ok(TrustedTheory::root("NativeThmVariables", signature))
}

pub fn create_local_context(root: &TrustedTheory) -> Result<ProofContext, KernelError> {
    let mut context = ProofContext::new(root.snapshot().clone());
    let fixed = context.declare_type_free("a", Sort::empty())?;
    context.declare_free("x", fixed.clone());
    context.declare_free("y", fixed.clone());
    context.declare_free("f", Ty::arrow(fixed.clone(), fixed));
    Ok(context)
}

pub fn derive_local_schema(context: &ProofContext) -> Result<KernelThm, KernelError> {
    let fixed = Ty::tfree("a", Sort::empty());
    let x = RawTerm::free("x", fixed.clone());
    let y = RawTerm::free("y", fixed.clone());
    let f = RawTerm::free("f", Ty::arrow(fixed.clone(), fixed.clone()));
    let premise = context.certify_prop(RawTerm::eq(x, y))?;
    let assumed = KernelRules::assume(premise.clone())?;
    let reflexive = KernelRules::reflexive(context.certify_term(f)?);
    let combined = KernelRules::combination(reflexive.as_kernel(), assumed.as_kernel())?;
    let schema = KernelRules::implies_intr(&premise, &combined)?;
    assert!(schema.hyps().is_empty());
    Ok(schema)
}

pub fn generalize_local_schema(
    context: &ProofContext,
    source: &KernelThm,
) -> Result<KernelThm, KernelError> {
    let type_names = make_names(&["a"]);
    let term_names = make_names(&["x", "y", "f"]);
    let fixed = Ty::tfree("a", Sort::empty());
    let certified_type = context.certify_type(Ty::arrow(fixed.clone(), fixed.clone()))?;
    let generalized_type = context.generalize_type(&certified_type, &type_names, 0)?;
    let variable_type = Ty::tvar("a", 0, Sort::empty());
    assert_eq!(generalized_type.ty(), &Ty::arrow(variable_type.clone(), variable_type.clone()));
    assert_eq!(generalized_type.context(), context.stamp());
    let certified_term = context.certify_term(RawTerm::free("x", fixed))?;
    let (derived, generalized_term) =
        context.generalize_term(&certified_term, &type_names, &term_names, 0)?;
    assert_eq!(derived.stamp(), context.stamp());
    assert_eq!(generalized_term.context(), context.stamp());
    assert_eq!(derived.free_type(&"y".into()), Some(&variable_type));
    assert_eq!(
        generalized_term.term(),
        derived.certify_term(RawTerm::var("x", 0, variable_type))?.term()
    );
    let generalized = KernelRules::generalize(source, &type_names, &term_names, 0)?;
    assert_eq!(generalized.context(), context.stamp());
    assert!(generalized.hyps().is_empty());
    Ok(generalized)
}

fn make_generic_congruence() -> RawTerm {
    let ty = Ty::tvar("a", 0, Sort::empty());
    let function = RawTerm::var("f", 0, Ty::arrow(ty.clone(), ty.clone()));
    let x = RawTerm::var("x", 0, ty.clone());
    let y = RawTerm::var("y", 0, ty);
    RawTerm::imp(
        RawTerm::eq(x.clone(), y.clone()),
        RawTerm::eq(RawTerm::app(function.clone(), x), RawTerm::app(function, y)),
    )
}

pub fn accept_schema(root: &TrustedTheory) -> Result<(TrustedTheory, TrustedTheorem), KernelError> {
    let context = create_local_context(root)?;
    let source = derive_local_schema(&context)?;
    let generalized = generalize_local_schema(&context, &source)?;
    assert!(matches!(
        generalized.clone().try_close(),
        Err(KernelError::LocalTypeScopeEscape { .. })
    ));
    let exported = KernelRules::export_scope(root, &context, &generalized)?;
    assert_eq!(exported.context(), root.stamp());
    let expected =
        ProofContext::new(root.snapshot().clone()).certify_prop(make_generic_congruence())?;
    assert_eq!(exported.prop(), &expected);
    assert_eq!(context.free_type(&"x".into()), Some(&Ty::tfree("a", Sort::empty())));
    assert_eq!(context.free_type(&"y".into()), Some(&Ty::tfree("a", Sort::empty())));
    let fixed = Ty::tfree("a", Sort::empty());
    assert_eq!(context.free_type(&"f".into()), Some(&Ty::arrow(fixed.clone(), fixed)));
    let (owner, token) = accept_closed_theorem(root, "generic_congruence", exported.try_close()?)?;
    assert_eq!(token.prop().term(), expected.term());
    assert!(token.dependencies().is_empty());
    assert_eq!(token.proved_context(), root.stamp());
    assert_eq!(token.accepted_in(), owner.id());
    assert!(root.get(token.name()).is_none());
    Ok((owner, token))
}

fn instantiate_schema(
    branch: &TrustedTheory,
    schema: &TrustedTheorem,
    spec: BranchSpec,
) -> Result<KernelThm, KernelError> {
    let context = ProofContext::new(branch.snapshot().clone());
    let reference = KernelRules::theorem_ref(branch, schema)?;
    let raised = KernelRules::incr_indexes(branch, &context, reference.as_kernel(), 2)?;
    let ty = Ty::base(spec.ty)?;
    let type_inst = TypeInstantiation::try_new(BTreeMap::from([(
        TypeVarId::new("a", 2, Sort::empty()),
        ty.clone(),
    )]))?;
    let mut terms = Vec::with_capacity(3);
    for (variable, constant, variable_ty) in [
        ("x", spec.p, ty.clone()),
        ("y", spec.q, ty.clone()),
        ("f", spec.g, Ty::arrow(ty.clone(), ty.clone())),
    ] {
        let replacement = context.certify_term(RawTerm::const_(constant, variable_ty.clone()))?;
        terms.push(InstEntry::new(variable, 2, variable_ty, replacement));
    }
    let instance = KernelRules::instantiate(&context, &raised, &type_inst, &terms)?;
    let expected =
        context.certify_prop(RawTerm::imp(make_premise(spec)?, make_conclusion(spec, false)?))?;
    assert_eq!(instance.prop(), &expected);
    assert!(instance.hyps().is_empty());
    Ok(instance)
}

fn compose_open_symmetry(
    branch: &TrustedTheory,
    instance: &KernelThm,
    spec: BranchSpec,
) -> Result<KernelThm, KernelError> {
    let context = ProofContext::new(branch.snapshot().clone());
    let premise = context.certify_prop(make_premise(spec)?)?;
    let assumed_premise = KernelRules::assume(premise.clone())?;
    let open_rule = KernelRules::implies_elim(instance, assumed_premise.as_kernel())?;
    assert_eq!(open_rule.hyps(), std::slice::from_ref(&premise));
    let image = context.certify_prop(make_conclusion(spec, false)?)?;
    let image_assumption = KernelRules::assume(image.clone())?;
    let symmetric = KernelRules::symmetric(image_assumption.as_kernel())?;
    let state = KernelRules::implies_intr(&image, &symmetric)?;
    let candidate = CompositionCandidate {
        type_inst: TypeInstantiation::empty(),
        rule_subst: Vec::new(),
        state_subst: Vec::new(),
        residual_pairs: Vec::new(),
        elimination_choice: None,
    };
    let composed = KernelRules::bicompose_candidate(
        branch,
        &context,
        CompositionOptions {
            flags: CompositionFlags::default(),
            is_elimination: false,
            premise_count: 0,
            subgoal_index: 1,
        },
        &open_rule,
        &state,
        &candidate,
    )?;
    assert_eq!(composed.hyps(), std::slice::from_ref(&premise));
    assert_eq!(composed.prop(), &context.certify_prop(make_conclusion(spec, true)?)?);
    Ok(composed)
}

fn run_branch(
    schema_owner: &TrustedTheory,
    schema: &TrustedTheorem,
    spec: BranchSpec,
) -> Result<BranchOutcome, KernelError> {
    let branch_owner = schema_owner.extend_const(spec.marker, Ty::prop())?;
    let instance = instantiate_schema(&branch_owner, schema, spec)?;
    let composed = compose_open_symmetry(&branch_owner, &instance, spec)?;
    let deep_owner = branch_owner.extend_const(spec.deep_marker, Ty::prop())?;
    let transferred = KernelRules::transfer(&deep_owner, &composed)?;
    let context = ProofContext::new(deep_owner.snapshot().clone());
    let premise = context.certify_prop(make_premise(spec)?)?;
    assert_eq!(transferred.hyps(), std::slice::from_ref(&premise));
    let discharged = KernelRules::implies_intr(&premise, &transferred)?;
    let expected =
        context.certify_prop(RawTerm::imp(make_premise(spec)?, make_conclusion(spec, true)?))?;
    assert_eq!(discharged.prop(), &expected);
    assert!(discharged.hyps().is_empty());
    assert!(matches!(
        discharged.clone().try_close(),
        Err(KernelError::TheoremObligations(isabelle_kernel::PayloadError::ExtraSortHypotheses {
            sorts: 1
        },))
    ));
    let discharged = KernelRules::strip_shyps(&deep_owner, &context, &discharged)?;
    let (accepted_owner, instance) =
        accept_closed_theorem(&deep_owner, spec.name, discharged.try_close()?)?;
    assert_eq!(instance.prop().term(), expected.term());
    assert_eq!(instance.proved_context(), deep_owner.stamp());
    assert_eq!(instance.accepted_in(), accepted_owner.id());
    assert_eq!(instance.dependencies().len(), 1);
    assert!(branch_owner.get(instance.name()).is_none());
    assert!(deep_owner.get(instance.name()).is_none());
    let reference = KernelRules::theorem_ref(&accepted_owner, &instance)?;
    let (reused_owner, reused) =
        accept_closed_theorem(&accepted_owner, format!("{}_reused", spec.name), reference)?;
    assert_eq!(reused.prop().term(), expected.term());
    assert_eq!(reused.dependencies().len(), 1);
    assert_eq!(reused.proved_context(), accepted_owner.stamp());
    assert_eq!(reused.accepted_in(), reused_owner.id());
    Ok(BranchOutcome { branch_owner, deep_owner, accepted_owner, reused_owner, instance, reused })
}

pub fn run_closure() -> Result<ConsumerOutcome, KernelError> {
    let root = create_root()?;
    let (schema_owner, schema) = accept_schema(&root)?;
    let left = run_branch(&schema_owner, &schema, LEFT)?;
    let right = run_branch(&schema_owner, &schema, RIGHT)?;
    assert_ne!(left.branch_owner.id(), right.branch_owner.id());
    assert!(schema_owner.get(left.instance.name()).is_none());
    assert!(schema_owner.get(right.instance.name()).is_none());
    for owner in [
        &root,
        &schema_owner,
        &left.branch_owner,
        &left.deep_owner,
        &left.accepted_owner,
        &left.reused_owner,
        &right.branch_owner,
        &right.deep_owner,
        &right.accepted_owner,
        &right.reused_owner,
    ] {
        assert!(owner.logic_basis().is_none());
    }
    Ok(ConsumerOutcome { root, schema_owner, schema, left, right })
}
