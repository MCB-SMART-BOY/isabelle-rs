use std::collections::BTreeSet;

use crate::{
    Derivation, EmptyClassDeclCert, KernelError, KernelRules, KernelThm, Name, ProofContext,
    RawTerm, Signature, Sort, TrustedTheory, Ty, accept_closed_theorem,
};

fn reject_intermediate_annotation(forged_type: Ty) -> KernelError {
    let signature = Signature::new().install_empty_class(EmptyClassDeclCert::hol_type()).unwrap();
    let owner = TrustedTheory::root("IntermediateAnnotation", signature);
    let mut context = ProofContext::new(owner.snapshot().clone());
    let fixed = context.declare_type_free("a", Sort::empty()).unwrap();
    context.declare_free("x", fixed.clone());
    let source = KernelRules::reflexive(context.certify_term(RawTerm::free("x", fixed)).unwrap());
    let type_names = BTreeSet::from([Name::from("a")]);
    let term_names = BTreeSet::from([Name::from("x")]);
    let typed =
        KernelRules::generalize(source.as_kernel(), &type_names, &BTreeSet::new(), 0).unwrap();
    let generalized = KernelRules::generalize(&typed, &BTreeSet::new(), &term_names, 1).unwrap();
    let exported = KernelRules::export_scope(&owner, &context, &generalized).unwrap();
    let mut alternate = context.clone();
    alternate.declare_free("x", forged_type.clone());
    let wrong = RawTerm::free("x", forged_type);
    let prop = alternate.certify_prop(RawTerm::eq(wrong.clone(), wrong)).unwrap();
    let forged = KernelThm::new_with_payload(
        vec![],
        prop,
        typed.payload().clone(),
        typed.derivation().clone(),
    );
    let source_frees = crate::bound_proof::collect_lexical_frees(&forged);
    let forged = KernelThm::new_with_payload(
        vec![],
        generalized.prop().clone(),
        generalized.payload().clone(),
        Derivation::Generalize {
            type_names: BTreeSet::new(),
            term_names,
            index: 1,
            source_frees,
            premise: Box::new(forged),
        },
    );
    let forged = KernelThm::new_with_payload(
        vec![],
        exported.prop().clone(),
        exported.payload().clone(),
        Derivation::ExportScope { scope: context.snapshot_scope(), premise: Box::new(forged) },
    );
    accept_closed_theorem(&owner, "forged_annotation", forged.try_close().unwrap()).unwrap_err()
}

#[test]
fn generalize_intermediate_free_type_tamper_rejected_by_acceptance() {
    assert_eq!(reject_intermediate_annotation(Ty::prop()), KernelError::AcceptanceReplayMismatch);
}

#[test]
fn generalize_intermediate_free_sort_tamper_rejected_by_acceptance() {
    assert_eq!(
        reject_intermediate_annotation(Ty::tvar("a", 0, Sort::hol_type())),
        KernelError::TypeIdentityMismatch {
            name: Name::from("a"),
            index: Some(0),
            expected: Sort::empty(),
            actual: Sort::hol_type(),
        },
    );
}
