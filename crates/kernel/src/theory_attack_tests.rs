use super::*;
use crate::{Derivation, KernelRules, Sort};

fn prove_reflexivity(owner: &TrustedTheory, constant: &str) -> ClosedThm {
    let context = ProofContext::new(owner.snapshot().clone());
    let term = context.certify_term(RawTerm::const_(constant, Ty::prop())).unwrap();
    KernelRules::reflexive(term)
}

#[test]
fn accept_owner_extra_unencoded_sibling_parent_rejects() {
    let root = TrustedTheory::root("Root", Signature::new().extend_const("P", Ty::prop()).unwrap());
    let left = root.begin_child("Left");
    let (left, token) =
        accept_closed_theorem(&left, "left_fact", prove_reflexivity(&left, "P")).unwrap();
    let right = root.begin_child("Right");
    let mut inner = (*right.inner).clone();
    inner.parents = vec![root, left];
    let corrupted = TrustedTheory { inner: Arc::new(inner) };
    let result = KernelRules::theorem_ref(&corrupted, &token)
        .and_then(|proof| accept_closed_theorem(&corrupted, "imported", proof));
    assert!(matches!(result, Err(KernelError::Invariant(_))));
}

#[test]
fn accept_definition_hidden_rhs_type_variable_rejects() {
    let parent = TrustedTheory::root(
        "Root",
        Signature::new().install_empty_class(crate::EmptyClassDeclCert::hol_type()).unwrap(),
    );
    let rhs = RawTerm::forall(
        "x",
        Ty::tvar("a", 0, Sort::hol_type()),
        RawTerm::eq(RawTerm::bound(0), RawTerm::bound(0)),
    );
    let name = Name::from("P");
    let certificate = DefinitionCertificate {
        id: DefinitionCertificate::compute_id(
            &parent.id(),
            &name,
            &Ty::prop(),
            &ConstScheme::Monomorphic(Ty::prop()),
            &rhs,
        ),
        parent: parent.id(),
        name,
        declared_ty: Ty::prop(),
        scheme: ConstScheme::Monomorphic(Ty::prop()),
        rhs_raw: rhs,
    };
    let snapshot = parent.snapshot().extend_definition(&certificate).unwrap();
    let corrupted = TrustedTheory::child(&parent, snapshot, None);
    let context = ProofContext::new(corrupted.snapshot().clone());
    let prop = context
        .certify_prop(RawTerm::eq(RawTerm::const_("P", Ty::prop()), certificate.rhs_raw.clone()))
        .unwrap();
    let candidate = KernelThm::new(
        vec![],
        prop,
        Derivation::ConservativeDefinition { definition: certificate.id },
    )
    .try_close()
    .unwrap();
    assert!(matches!(
        accept_closed_theorem(&corrupted, "bad", candidate),
        Err(KernelError::DefinitionCertificate(
            DefinitionCertificateError::RhsContainsTypeVariables { .. }
        ))
    ));
    assert!(corrupted.is_empty());
}

#[test]
fn accept_descendant_changed_basis_rejects() {
    let signature = Signature::new().extend_const("P", Ty::prop()).unwrap();
    let basis = crate::LogicBasis::try_new(vec![], vec![]).unwrap();
    let parent = TrustedTheory::with_basis("Root", signature, &basis).unwrap();
    let descendant = parent.begin_child("Child");
    let mut inner = (*descendant.inner).clone();
    inner.logic_basis = None;
    let corrupted = TrustedTheory { inner: Arc::new(inner) };
    let candidate = prove_reflexivity(&corrupted, "P");
    assert!(matches!(
        accept_closed_theorem(&corrupted, "bad", candidate),
        Err(KernelError::Invariant(_))
    ));
    assert!(corrupted.is_empty());
}

#[test]
fn accept_basis_later_declaration_cannot_authorize_installation() {
    let root = TrustedTheory::root("Root", Signature::new());
    let basis = crate::LogicBasis::try_new(
        vec![],
        vec![crate::AxiomSchema { name: "ax".into(), prop: RawTerm::const_("P", Ty::prop()) }],
    )
    .unwrap();
    let snapshot = TheorySnapshot::build(
        vec![root.snapshot().clone()],
        root.signature().clone(),
        TheoryExtension::InstallLogicBasis { logic_basis_id: basis.id() },
    );
    let installed = TrustedTheory::child(&root, snapshot, None);
    let mut inner = (*installed.inner).clone();
    inner.logic_basis = Some(Arc::new(basis));
    let corrupted = TrustedTheory { inner: Arc::new(inner) }.extend_const("P", Ty::prop()).unwrap();
    let candidate = prove_reflexivity(&corrupted, "P");
    assert!(matches!(
        accept_closed_theorem(&corrupted, "bad", candidate),
        Err(KernelError::InvalidAxiomSchema { .. })
    ));
    assert!(corrupted.is_empty());
}

#[test]
fn accept_theorem_reference_forged_payload_or_name_rejects() {
    let signature = Signature::new()
        .extend_const("P", Ty::prop())
        .unwrap()
        .extend_const("Q", Ty::prop())
        .unwrap();
    let root = TrustedTheory::root("Root", signature);
    let (owner, canonical) =
        accept_closed_theorem(&root, "refl", prove_reflexivity(&root, "P")).unwrap();
    for (name, closed) in [
        (Name::from("wrong"), canonical.0.closed.clone()),
        (canonical.name().clone(), prove_reflexivity(&root, "Q")),
    ] {
        let forged = TrustedTheorem::seal(
            canonical.id(),
            name,
            closed,
            canonical.dependencies().clone(),
            canonical.accepted_in(),
        );
        assert!(matches!(
            KernelRules::theorem_ref(&owner, &forged),
            Err(KernelError::UnknownTheoremDependency)
        ));
        let context = ProofContext::new(owner.snapshot().clone());
        let prop = context.recertify_prop(forged.prop()).unwrap();
        let candidate = KernelThm::new(vec![], prop, Derivation::TheoremRef { theorem: forged })
            .try_close()
            .unwrap();
        assert!(matches!(
            accept_closed_theorem(&owner, "bad", candidate),
            Err(KernelError::UnknownTheoremDependency)
        ));
        assert_eq!(owner.len(), 1);
    }
}
