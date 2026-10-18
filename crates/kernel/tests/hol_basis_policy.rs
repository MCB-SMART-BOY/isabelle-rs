use isabelle_kernel::{
    AxiomDependencyId, AxiomSchema, BasisDeclaration, EmptyClassDeclCert, KernelError, KernelRules,
    LogicBasis, LogicPolicyId, Name, ProofContext, RawTerm, Signature, TrustedTheory, Ty,
    TypeInstantiation, accept_closed_theorem, theorem_builder,
};

fn find_axiom(name: &str) -> AxiomSchema {
    LogicBasis::hol_v1_manifest()
        .unwrap()
        .1
        .into_iter()
        .find(|axiom| axiom.name.as_str() == name)
        .unwrap()
}

fn make_bool_owner() -> TrustedTheory {
    let root = TrustedTheory::root(
        "HOL",
        Signature::new().install_empty_class(EmptyClassDeclCert::hol_type()).unwrap(),
    );
    let function = root
        .install_semantic_arity(isabelle_kernel::SemanticArityCert::FunctionTypeArityCert)
        .unwrap();
    let declared = function.declare_fresh_nonempty_tycon("bool", 0).unwrap();
    declared
        .install_semantic_arity(isabelle_kernel::SemanticArityCert::FreshNonemptyTyconCert {
            tycon: "bool".into(),
            arity: 0,
        })
        .unwrap()
}

fn make_base_owner() -> TrustedTheory {
    let boolean = Ty::base("bool").unwrap();
    let owner = make_bool_owner()
        .extend_const("HOL.Trueprop", Ty::arrow(boolean.clone(), Ty::prop()))
        .unwrap();
    let owner = owner
        .extend_const(
            "HOL.implies",
            Ty::arrow(boolean.clone(), Ty::arrow(boolean.clone(), boolean.clone())),
        )
        .unwrap();
    let owner = owner.extend_const("P", boolean.clone()).unwrap();
    let owner = owner.extend_const("Q", boolean).unwrap();
    let (declarations, _) = LogicBasis::hol_v1_manifest().unwrap();
    let declarations = declarations.into_iter().filter(|declaration| matches!(declaration,
        BasisDeclaration::TypeConstructor { name, .. } if name.as_str() == "bool"
    ) || matches!(declaration,
        BasisDeclaration::Judgment { const_name, .. } if const_name.as_str() == "HOL.Trueprop"
    ) || matches!(declaration,
        BasisDeclaration::Constant { name, .. } if name.as_str() == "HOL.implies"
    )).collect();
    owner.install_basis(&LogicBasis::try_hol_basis(declarations, vec![]).unwrap()).unwrap()
}

fn install_slot(owner: &TrustedTheory, name: &str) -> TrustedTheory {
    owner
        .install_basis(&LogicBasis::try_hol_basis(vec![], vec![find_axiom(name)]).unwrap())
        .unwrap()
}

fn accept_imp_i(
    owner: &TrustedTheory,
    name: &str,
) -> (TrustedTheory, isabelle_kernel::TrustedTheorem) {
    let context = ProofContext::new(owner.snapshot().clone());
    let boolean = Ty::base("bool").unwrap();
    let p = RawTerm::const_("P", boolean.clone());
    let q = RawTerm::const_("Q", boolean.clone());
    let judgment = |term| {
        RawTerm::app(RawTerm::const_("HOL.Trueprop", Ty::arrow(boolean.clone(), Ty::prop())), term)
    };
    let implication = RawTerm::app(
        RawTerm::app(
            RawTerm::const_(
                "HOL.implies",
                Ty::arrow(boolean.clone(), Ty::arrow(boolean.clone(), boolean.clone())),
            ),
            p.clone(),
        ),
        q.clone(),
    );
    let statement =
        RawTerm::imp(RawTerm::imp(judgment(p.clone()), judgment(q.clone())), judgment(implication));
    let theorem = theorem_builder::axiom_theorem(
        &context,
        owner.logic_basis().unwrap(),
        "HOL.impI".into(),
        TypeInstantiation::empty(),
        vec![context.certify_term(p).unwrap(), context.certify_term(q).unwrap()],
        statement,
    )
    .unwrap();
    accept_closed_theorem(owner, name, theorem.try_close().unwrap()).unwrap()
}

#[test]
fn hol_policy_all_thirteen_schemas_are_structurally_checked() {
    let (declarations, axioms) = LogicBasis::hol_v1_manifest().unwrap();
    let names: Vec<_> = axioms.iter().map(|axiom| axiom.name.as_str()).collect();
    assert_eq!(
        names,
        [
            "HOL.refl",
            "HOL.subst",
            "HOL.ext",
            "HOL.the_eq_trivial",
            "HOL.impI",
            "HOL.mp",
            "HOL.True_or_False",
            "HOL.eq_reflection",
            "Hilbert_Choice.someI",
            "Nat.Suc_Rep_inject",
            "Nat.Suc_Rep_not_Zero_Rep",
            "Set.mem_Collect_eq",
            "Set.Collect_mem_eq",
        ]
    );
    let declaration_names: Vec<_> = declarations
        .iter()
        .map(|declaration| match declaration {
            BasisDeclaration::TypeConstructor { name, .. }
            | BasisDeclaration::Constant { name, .. } => name.as_str(),
            BasisDeclaration::Judgment { const_name, .. } => const_name.as_str(),
        })
        .collect();
    assert_eq!(
        declaration_names,
        [
            "fun",
            "bool",
            "HOL.Trueprop",
            "HOL.implies",
            "HOL.eq",
            "HOL.The",
            "Hilbert_Choice.Eps",
            "Nat.ind",
            "Nat.Zero_Rep",
            "Nat.Suc_Rep",
            "Set.set",
            "Set.Collect",
            "Set.member",
        ]
    );
    let checked = LogicBasis::try_hol_basis(declarations, axioms).unwrap();
    assert_eq!(checked.policy(), LogicPolicyId::HOLBasisV1);
}

#[test]
fn hol_policy_each_slot_structure_mutation_is_rejected() {
    let (_, originals) = LogicBasis::hol_v1_manifest().unwrap();
    for mut axiom in originals {
        let original_name = axiom.name.clone();
        axiom.prop = RawTerm::imp(axiom.prop.clone(), axiom.prop);
        assert!(matches!(LogicBasis::try_hol_basis(vec![], vec![axiom]),
            Err(KernelError::UnapprovedAxiom { name }) if name == original_name));
    }
}

#[test]
fn hol_policy_type_sort_connective_and_declaration_mutations_are_rejected() {
    let refl = find_axiom("HOL.refl");
    let RawTerm::Forall { name, body, .. } = refl.prop else { panic!("fixed refl shape") };
    let wrong_sort = AxiomSchema {
        name: "HOL.refl".into(),
        prop: RawTerm::forall(name, Ty::tvar("'a", 0, isabelle_kernel::Sort::empty()), *body),
    };
    assert!(matches!(
        LogicBasis::try_hol_basis(vec![], vec![wrong_sort]),
        Err(KernelError::UnapprovedAxiom { .. })
    ));
    let reflection = find_axiom("HOL.eq_reflection");
    let swapped = AxiomSchema {
        name: reflection.name,
        prop: RawTerm::imp(reflection.prop.clone(), reflection.prop),
    };
    assert!(matches!(
        LogicBasis::try_hol_basis(vec![], vec![swapped]),
        Err(KernelError::UnapprovedAxiom { .. })
    ));
    let bad_decl = BasisDeclaration::TypeConstructor { name: "Set.set".into(), arity: 2 };
    assert!(matches!(
        LogicBasis::try_hol_basis(vec![bad_decl], vec![]),
        Err(KernelError::UnapprovedAxiom { .. })
    ));
}

#[test]
fn hol_policy_rejects_fourteenth_name_and_is_distinct_from_research() {
    let imp_i = find_axiom("HOL.impI");
    let unknown = AxiomSchema { name: "HOL.additional".into(), prop: imp_i.prop.clone() };
    assert!(matches!(
        LogicBasis::try_hol_basis(vec![], vec![unknown]),
        Err(KernelError::UnapprovedAxiom { .. })
    ));
    let research = LogicBasis::try_new(vec![], vec![imp_i]).unwrap();
    assert_eq!(research.policy(), LogicPolicyId::GenericResearch);
    assert_ne!(
        research.id(),
        LogicBasis::try_hol_basis(vec![], vec![find_axiom("HOL.impI")]).unwrap().id()
    );
}

#[test]
fn hol_owner_sequential_subsets_keep_original_axiom_dependency() {
    let root = make_base_owner();
    let first = install_slot(&root, "HOL.impI");
    let original_basis_id = first.logic_basis().unwrap().id();
    let (first, fact) = accept_imp_i(&first, "imp_i_original");
    assert_eq!(fact.dependencies().len(), 1);

    let second = install_slot(&first.begin_child("Next"), "HOL.mp");
    let expected = LogicBasis::try_hol_basis(
        root.logic_basis().unwrap().declarations().to_vec(),
        vec![find_axiom("HOL.impI"), find_axiom("HOL.mp")],
    )
    .unwrap();
    assert_eq!(second.logic_basis().unwrap().id(), expected.id());
    assert_eq!(second.stamp().logic_basis(), Some(expected.id()));
    assert_ne!(original_basis_id, expected.id());
    assert_ne!(
        AxiomDependencyId::compute(original_basis_id, find_axiom("HOL.impI").id()),
        AxiomDependencyId::compute(expected.id(), find_axiom("HOL.impI").id()),
    );
    assert!(KernelRules::theorem_ref(&second, &fact).is_ok());
    let (_, replayed) = accept_imp_i(&second, "imp_i_after_subset");
    assert_eq!(replayed.dependencies(), fact.dependencies());
}

#[test]
fn hol_owner_disjoint_subsets_merge_replays_original_axiom_origin() {
    let root = make_base_owner();
    let left = install_slot(&root.begin_child("L"), "HOL.impI");
    let (left, fact) = accept_imp_i(&left, "imp_i_fact");
    let right = install_slot(&root.begin_child("R"), "HOL.mp");
    let merged = TrustedTheory::merge_parents("Joint", &[left.clone(), right.clone()]).unwrap();
    assert_eq!(merged.logic_basis().unwrap().axioms().len(), 2);
    assert_ne!(merged.logic_basis().unwrap().id(), left.logic_basis().unwrap().id());
    assert_eq!(merged.stamp().logic_basis(), Some(merged.logic_basis().unwrap().id()));
    assert!(KernelRules::theorem_ref(&merged, &fact).is_ok());
    let (_, replayed) = accept_imp_i(&merged, "imp_i_replayed");
    assert_eq!(replayed.dependencies(), fact.dependencies());
    let reverse = TrustedTheory::merge_parents("Joint", &[right, left]).unwrap();
    assert_eq!(reverse.logic_basis().unwrap().id(), merged.logic_basis().unwrap().id());
    assert_ne!(reverse.id(), merged.id());
    assert!(KernelRules::theorem_ref(&reverse, &fact).is_ok());
}

#[test]
fn hol_owner_duplicate_introduction_and_policy_conflict_are_rejected() {
    let root = make_base_owner();
    let left = install_slot(&root.begin_child("L"), "HOL.impI");
    let right = install_slot(&root.begin_child("R"), "HOL.impI");
    assert!(matches!(TrustedTheory::merge_parents("Ambiguous", &[left.clone(), right]),
        Err(KernelError::DuplicateDeclaration { name }) if name == Name::from("HOL.impI")));
    assert!(
        left.install_basis(
            &LogicBasis::try_hol_basis(vec![], vec![find_axiom("HOL.impI")]).unwrap()
        )
        .is_err()
    );
    let generic = TrustedTheory::root("Research", root.signature().clone())
        .install_basis(&LogicBasis::try_new(vec![], vec![]).unwrap())
        .unwrap();
    assert!(matches!(
        TrustedTheory::merge_parents("Conflict", &[left, generic]),
        Err(KernelError::Invariant(_))
    ));
}

#[test]
fn hol_basis_predefined_judgment_is_rejected_before_installation() {
    let bool_ty = Ty::base("bool").unwrap();
    let owner = make_bool_owner().extend_const("bad", Ty::prop()).unwrap();
    let (owner, _) = owner
        .define_const(
            "HOL.Trueprop",
            RawTerm::abs("p", bool_ty.clone(), RawTerm::const_("bad", Ty::prop())),
        )
        .unwrap();
    let owner = owner
        .extend_const(
            "HOL.implies",
            Ty::arrow(bool_ty.clone(), Ty::arrow(bool_ty.clone(), bool_ty)),
        )
        .unwrap();
    let basis = LogicBasis::try_hol_basis(vec![], vec![find_axiom("HOL.impI")]).unwrap();
    assert!(owner.install_basis(&basis).is_err());
}

#[test]
fn hol_basis_copied_signature_without_declaration_history_is_rejected() {
    let bool_ty = Ty::base("bool").unwrap();
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_type_constructor("bool", 0)
        .unwrap()
        .extend_const("HOL.Trueprop", Ty::arrow(bool_ty.clone(), Ty::prop()))
        .unwrap()
        .extend_const(
            "HOL.implies",
            Ty::arrow(bool_ty.clone(), Ty::arrow(bool_ty.clone(), bool_ty)),
        )
        .unwrap();
    let owner = TrustedTheory::root("Forged", signature);
    let basis = LogicBasis::try_hol_basis(vec![], vec![find_axiom("HOL.impI")]).unwrap();
    assert!(owner.install_basis(&basis).is_err());
}
