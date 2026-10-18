use std::collections::{BTreeMap, BTreeSet};

use isabelle_kernel::{
    AxiomSchema, EmptyClassDeclCert, KernelRules, LogicBasis, Name, PolyType, PolyTypeParam,
    ProofContext, RawTerm, Signature, Sort, TrustedTheory, Ty, TypeInstantiation, TypeVarId,
    accept_closed_theorem, term::subst_types, theorem_builder,
};

fn make_instantiation(sort: Sort, replacement: Ty) -> TypeInstantiation {
    TypeInstantiation::try_new(BTreeMap::from([(TypeVarId::new("a", 0, sort), replacement)]))
        .unwrap()
}

fn make_identity_signature(sort: Sort) -> Signature {
    let alpha = Ty::tvar("a", 0, sort.clone());
    let scheme = PolyType::new(
        vec![PolyTypeParam { id: TypeVarId::new("a", 0, sort) }],
        Ty::arrow(alpha.clone(), alpha),
    )
    .unwrap();
    Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const_scheme("identity", scheme)
        .unwrap()
}

#[test]
fn certify_constant_schematic_instance_replays_as_schema() {
    let owner = TrustedTheory::root("Schematic", make_identity_signature(Sort::empty()));
    let beta = Ty::tvar("b", 1, Sort::empty());
    let ty = Ty::arrow(beta.clone(), beta);
    let context = ProofContext::new(owner.snapshot().clone());
    let raw = RawTerm::const_("identity", ty);
    let constant = context.certify_term(raw.clone()).unwrap();
    let expected = context.certify_prop(RawTerm::eq(raw.clone(), raw)).unwrap();
    let theorem = KernelRules::reflexive(constant);
    let (_, accepted) = accept_closed_theorem(&owner, "schema_refl", theorem).unwrap();
    assert_eq!(accepted.prop().term(), expected.term());
    assert!(accepted.dependencies().is_empty());
}

#[test]
fn substitute_types_self_occurrence_is_replaced_once() {
    let alpha = Ty::tvar("a", 0, Sort::empty());
    let replacement = Ty::apply("list", vec![alpha.clone()]).unwrap();
    let instantiation = make_instantiation(Sort::empty(), replacement.clone());
    let result = subst_types(&RawTerm::var("x", 0, alpha), &instantiation).unwrap();
    assert_eq!(result, RawTerm::var("x", 0, replacement));
}

#[test]
fn substitute_types_cross_references_are_not_recursive() {
    let alpha = Ty::tvar("a", 0, Sort::empty());
    let beta = Ty::tvar("b", 0, Sort::empty());
    let instantiation = TypeInstantiation::try_new(BTreeMap::from([
        (TypeVarId::new("a", 0, Sort::empty()), beta.clone()),
        (TypeVarId::new("b", 0, Sort::empty()), alpha.clone()),
    ]))
    .unwrap();
    let source = RawTerm::var("f", 0, Ty::arrow(alpha.clone(), beta.clone()));
    assert_eq!(
        subst_types(&source, &instantiation).unwrap(),
        RawTerm::var("f", 0, Ty::arrow(beta, alpha)),
    );
}

#[test]
fn substitute_types_fixed_parameter_is_not_a_schematic_key() {
    let fixed = Ty::tfree("a", Sort::empty());
    let alpha = Ty::tvar("a", 0, Sort::empty());
    let instantiation = make_instantiation(Sort::empty(), Ty::prop());
    let source = RawTerm::var("f", 0, Ty::arrow(fixed.clone(), alpha));
    assert_eq!(
        subst_types(&source, &instantiation).unwrap(),
        RawTerm::var("f", 0, Ty::arrow(fixed, Ty::prop())),
    );
}

#[test]
fn certify_constant_weaker_atomic_sort_is_rejected() {
    let signature = make_identity_signature(Sort::hol_type());
    let alpha = Ty::tvar("a", 0, Sort::empty());
    assert!(
        signature
            .certify_const_instance(&Name::from("identity"), &Ty::arrow(alpha.clone(), alpha))
            .is_err()
    );
}

#[test]
fn install_axiom_weaker_constant_instance_is_rejected() {
    let signature = make_identity_signature(Sort::hol_type());
    let alpha = Ty::tvar("a", 0, Sort::empty());
    let identity = RawTerm::const_("identity", Ty::arrow(alpha.clone(), alpha));
    let basis = LogicBasis::try_new(
        vec![],
        vec![AxiomSchema {
            name: Name::from("bad"),
            prop: RawTerm::eq(identity.clone(), identity),
        }],
    )
    .unwrap();
    assert!(TrustedTheory::with_basis("Rejected", signature, &basis).is_err());
}

#[test]
fn build_axiom_erased_binder_still_checks_replacement_sort() {
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const("P", Ty::prop())
        .unwrap();
    let basis = LogicBasis::try_new(
        vec![],
        vec![AxiomSchema {
            name: Name::from("ax"),
            prop: RawTerm::forall(
                "x",
                Ty::tvar("a", 0, Sort::hol_type()),
                RawTerm::const_("P", Ty::prop()),
            ),
        }],
    )
    .unwrap();
    let owner = TrustedTheory::with_basis("ErasedBinder", signature, &basis).unwrap();
    let context = ProofContext::new(owner.snapshot().clone());
    let beta = Ty::tvar("b", 0, Sort::empty());
    let argument = context.certify_term(RawTerm::var("x", 0, beta.clone())).unwrap();
    let instantiation = make_instantiation(Sort::hol_type(), beta);
    assert!(
        theorem_builder::axiom_theorem(
            &context,
            &basis,
            Name::from("ax"),
            instantiation,
            vec![argument],
            RawTerm::const_("P", Ty::prop()),
        )
        .is_err()
    );
}

fn make_unused_binder_owner(parameters: &[Ty]) -> (TrustedTheory, LogicBasis) {
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const("P", Ty::prop())
        .unwrap();
    let proposition = parameters.iter().rev().fold(RawTerm::const_("P", Ty::prop()), |body, ty| {
        RawTerm::forall("unused", ty.clone(), body)
    });
    let basis = LogicBasis::try_new(
        vec![],
        vec![AxiomSchema { name: Name::from("unused"), prop: proposition }],
    )
    .unwrap();
    (TrustedTheory::with_basis("Unused", signature, &basis).unwrap(), basis)
}

#[test]
fn build_axiom_erased_binders_conflicting_type_identity_rejects() {
    let (owner, basis) = make_unused_binder_owner(&[
        Ty::tvar("a", 0, Sort::empty()),
        Ty::tvar("b", 0, Sort::empty()),
    ]);
    let context = ProofContext::new(owner.snapshot().clone());
    let first = Ty::tvar("c", 0, Sort::empty());
    let second = Ty::tvar("c", 0, Sort::hol_type());
    let arguments = vec![
        context.certify_term(RawTerm::var("x", 0, first.clone())).unwrap(),
        context.certify_term(RawTerm::var("y", 0, second.clone())).unwrap(),
    ];
    let instantiation = TypeInstantiation::try_new(BTreeMap::from([
        (TypeVarId::new("a", 0, Sort::empty()), first),
        (TypeVarId::new("b", 0, Sort::empty()), second),
    ]))
    .unwrap();
    assert!(matches!(
        theorem_builder::axiom_theorem(
            &context,
            &basis,
            Name::from("unused"),
            instantiation,
            arguments,
            RawTerm::const_("P", Ty::prop()),
        ),
        Err(isabelle_kernel::KernelError::TypeIdentityMismatch { .. }),
    ));
}

#[test]
fn build_axiom_erased_binder_foreign_argument_rejects() {
    let (owner, basis) = make_unused_binder_owner(&[Ty::prop()]);
    let context = ProofContext::new(owner.snapshot().clone());
    let foreign_owner = TrustedTheory::root(
        "Foreign",
        Signature::new().extend_const("foreign", Ty::prop()).unwrap(),
    );
    let foreign = ProofContext::new(foreign_owner.snapshot().clone())
        .certify_term(RawTerm::const_("foreign", Ty::prop()))
        .unwrap();
    assert!(matches!(
        theorem_builder::axiom_theorem(
            &context,
            &basis,
            Name::from("unused"),
            TypeInstantiation::empty(),
            vec![foreign],
            RawTerm::const_("P", Ty::prop()),
        ),
        Err(isabelle_kernel::KernelError::MixedContext { .. }),
    ));
}

#[test]
fn generalize_discharged_free_schema_accepts_and_references() {
    let owner = TrustedTheory::root("Generalize", Signature::new());
    let mut context = ProofContext::new(owner.snapshot().clone());
    context.declare_free("P", Ty::prop());
    let premise = context.certify_prop(RawTerm::free("P", Ty::prop())).unwrap();
    let assumed = KernelRules::assume(premise.clone()).unwrap();
    let identity = KernelRules::implies_intr(&premise, assumed.as_kernel()).unwrap();
    let schema =
        KernelRules::generalize(&identity, &BTreeSet::new(), &BTreeSet::from([Name::from("P")]), 0)
            .unwrap();
    let (updated, token) =
        accept_closed_theorem(&owner, "identity", schema.try_close().unwrap()).unwrap();
    let expected = context
        .certify_prop(RawTerm::imp(
            RawTerm::var("P", 0, Ty::prop()),
            RawTerm::var("P", 0, Ty::prop()),
        ))
        .unwrap();
    assert_eq!(token.prop().term(), expected.term());
    assert_eq!(
        KernelRules::theorem_ref(&updated, &token).unwrap().as_kernel().prop().term(),
        expected.term()
    );
}

#[test]
fn instantiate_sort_erased_colliding_atom_identity_rejects() {
    let owner = TrustedTheory::root(
        "ErasedIdentity",
        Signature::new().install_empty_class(EmptyClassDeclCert::hol_type()).unwrap(),
    );
    let context = ProofContext::new(owner.snapshot().clone());
    let source = context
        .certify_term(RawTerm::var(
            "f",
            0,
            Ty::arrow(Ty::tvar("a", 0, Sort::hol_type()), Ty::tvar("b", 0, Sort::hol_type())),
        ))
        .unwrap();
    let exported =
        KernelRules::unconstrain_t(&owner, &context, KernelRules::reflexive(source).as_kernel())
            .unwrap();
    let colliding = TypeInstantiation::try_new(BTreeMap::from([(
        TypeVarId::new("a0", 0, Sort::empty()),
        Ty::tvar("a1", 0, Sort::hol_type()),
    )]))
    .unwrap();
    assert!(matches!(
        KernelRules::instantiate(&context, &exported, &colliding, &[]),
        Err(isabelle_kernel::KernelError::TypeIdentityMismatch { .. }),
    ));
}
