use std::collections::BTreeSet;

use isabelle_kernel::{
    KernelError, KernelRules, KernelThm, Name, ProofContext, RawTerm, Signature, Sort,
    TrustedTheory, Ty, accept_closed_theorem,
};

fn discharge_via_dependency(dependency: &KernelThm, result: &KernelThm) -> KernelThm {
    let proposition = dependency.prop();
    let weakened = KernelRules::weaken(proposition, result).unwrap();
    let conditional = KernelRules::implies_intr(proposition, &weakened).unwrap();
    KernelRules::implies_elim(&conditional, dependency).unwrap()
}

fn create_hidden_index_source(index: usize) -> (TrustedTheory, ProofContext, KernelThm) {
    let owner = TrustedTheory::root(
        "HiddenIndexExport",
        Signature::new().extend_const("P", Ty::prop()).unwrap(),
    );
    let mut context = ProofContext::new(owner.snapshot().clone());
    let fixed = context.declare_type_free("a", Sort::empty()).unwrap();
    context.declare_free("y", fixed.clone());
    let local = KernelRules::reflexive(context.certify_term(RawTerm::free("y", fixed)).unwrap());
    context.declare_free("z", Ty::prop());
    let binder = context.certify_term(RawTerm::free("z", Ty::prop())).unwrap();
    let quantified = KernelRules::forall_intr(&binder, local.as_kernel()).unwrap();
    let hidden = context.certify_term(RawTerm::var("hidden", index, Ty::prop())).unwrap();
    let local = KernelRules::forall_elim(&quantified, &hidden).unwrap();
    let result =
        KernelRules::reflexive(context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap());
    let source = discharge_via_dependency(&local, result.as_kernel());
    let generalized = KernelRules::generalize(
        &source,
        &BTreeSet::new(),
        &BTreeSet::from([Name::from("absent")]),
        index.checked_add(1).unwrap(),
    )
    .unwrap();
    assert_eq!(generalized.max_var_index(), None);
    assert!(generalized.hyps().is_empty());
    assert_eq!(generalized.prop(), result.as_kernel().prop());
    (owner, context, generalized)
}

#[test]
fn export_scope_hidden_high_index_remains_usable_after_visible_bound_reset() {
    const HIDDEN_INDEX: usize = 41;
    let (owner, local, source) = create_hidden_index_source(HIDDEN_INDEX);
    let exported = KernelRules::export_scope(&owner, &local, &source).unwrap();
    let context = ProofContext::new(owner.snapshot().clone());
    let indexed = KernelRules::incr_indexes(&owner, &context, &exported, 2).unwrap();
    let stripped = KernelRules::strip_shyps(&owner, &context, &indexed).unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "hidden_index", stripped.try_close().unwrap()).unwrap();
    assert_eq!(token.prop().term(), source.prop().term());
    assert!(token.dependencies().is_empty());
}

#[cfg(target_pointer_width = "64")]
#[test]
fn export_scope_hidden_index_type_freshening_overflow_rejects() {
    let (owner, local, source) = create_hidden_index_source(u32::MAX as usize);
    let exported = KernelRules::export_scope(&owner, &local, &source).unwrap();
    let context = ProofContext::new(owner.snapshot().clone());
    assert!(matches!(
        KernelRules::incr_indexes(&owner, &context, &exported, 1),
        Err(KernelError::TypeVariableIndexOutOfRange { name, index })
            if name == Name::from("a") && index == u32::MAX as usize + 1,
    ));
}
