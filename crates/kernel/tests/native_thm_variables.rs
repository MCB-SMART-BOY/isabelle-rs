use std::collections::BTreeSet;

use isabelle_kernel::{
    KernelError, KernelRules, Name, ProofContext, RawTerm, Signature, TrustedTheory, Ty,
};

#[path = "../examples/native_thm_variables/support.rs"]
mod support;

fn expected_formula(ty_name: &str, p: &str, q: &str, g: &str) -> RawTerm {
    let ty = Ty::base(ty_name).unwrap();
    let function = RawTerm::const_(g, Ty::arrow(ty.clone(), ty.clone()));
    RawTerm::imp(
        RawTerm::eq(RawTerm::const_(p, ty.clone()), RawTerm::const_(q, ty.clone())),
        RawTerm::eq(
            RawTerm::app(function.clone(), RawTerm::const_(q, ty.clone())),
            RawTerm::app(function, RawTerm::const_(p, ty)),
        ),
    )
}

#[test]
fn native_variables_two_distinct_instances_accept_and_reuse_complete_formulas()
-> Result<(), KernelError> {
    let outcome = support::run_closure()?;
    for (branch, expected) in [
        (&outcome.left, expected_formula("left_ty", "p_left", "q_left", "g_left")),
        (&outcome.right, expected_formula("right_ty", "p_right", "q_right", "g_right")),
    ] {
        let context = ProofContext::new(branch.deep_owner.snapshot().clone());
        assert_eq!(branch.instance.prop(), &context.certify_prop(expected.clone())?);
        assert_eq!(branch.reused.prop().term(), branch.instance.prop().term());
        assert_eq!(branch.instance.dependencies().len(), 1);
        assert_eq!(branch.reused.dependencies().len(), 1);
        assert_eq!(branch.instance.proved_in(), branch.deep_owner.id());
        assert_eq!(branch.instance.accepted_in(), branch.accepted_owner.id());
        assert_eq!(branch.reused.proved_in(), branch.accepted_owner.id());
        assert_eq!(branch.reused.accepted_in(), branch.reused_owner.id());
        assert_eq!(branch.accepted_owner.get(branch.instance.name()), Some(&branch.instance));
        assert_eq!(branch.reused_owner.get(branch.reused.name()), Some(&branch.reused));
        assert!(branch.deep_owner.get(branch.instance.name()).is_none());
    }
    assert!(outcome.schema.dependencies().is_empty());
    assert_eq!(outcome.schema.proved_in(), outcome.root.id());
    assert_eq!(outcome.schema.accepted_in(), outcome.schema_owner.id());
    assert!(outcome.root.get(outcome.schema.name()).is_none());
    assert!(outcome.root.logic_basis().is_none());
    Ok(())
}

#[test]
fn native_variables_schema_available_to_both_branches_but_instances_not_siblings()
-> Result<(), KernelError> {
    let outcome = support::run_closure()?;
    for owner in [&outcome.left.branch_owner, &outcome.right.branch_owner] {
        let reference = KernelRules::theorem_ref(owner, &outcome.schema)?;
        assert_eq!(reference.as_kernel().prop().term(), outcome.schema.prop().term());
    }
    for (owner, foreign) in [
        (&outcome.left.reused_owner, &outcome.right.instance),
        (&outcome.right.reused_owner, &outcome.left.instance),
    ] {
        assert!(matches!(
            KernelRules::theorem_ref(owner, foreign),
            Err(KernelError::UnknownTheoremDependency)
        ));
        assert!(matches!(
            KernelRules::transfer(owner, foreign.as_kernel()),
            Err(KernelError::UnknownTheoremDependency)
        ));
    }
    let unrelated = TrustedTheory::root("UnrelatedVariables", Signature::new());
    assert!(matches!(
        KernelRules::theorem_ref(&unrelated, &outcome.schema),
        Err(KernelError::UnknownTheoremDependency)
    ));
    Ok(())
}

#[test]
fn native_variables_local_schema_requires_complete_export_and_its_source_context()
-> Result<(), KernelError> {
    let root = support::create_root()?;
    let context = support::create_local_context(&root)?;
    let original_stamp = context.stamp();
    let source = support::derive_local_schema(&context)?;
    let types_only =
        KernelRules::generalize(&source, &BTreeSet::from([Name::from("a")]), &BTreeSet::new(), 0)?;
    assert!(matches!(
        types_only.clone().try_close(),
        Err(KernelError::LocalTypeScopeEscape { .. })
    ));
    assert!(matches!(
        KernelRules::export_scope(&root, &context, &types_only),
        Err(KernelError::UndeclaredFree(_))
    ));
    let complete = support::generalize_local_schema(&context, &source)?;
    let foreign_context = ProofContext::new(root.snapshot().clone());
    assert!(matches!(
        KernelRules::export_scope(&root, &foreign_context, &complete),
        Err(KernelError::MixedContext { .. })
    ));
    assert_eq!(context.stamp(), original_stamp);
    assert_eq!(
        context.free_type(&"x".into()),
        Some(&Ty::tfree("a", isabelle_kernel::Sort::empty()))
    );
    assert!(root.is_empty());
    Ok(())
}
