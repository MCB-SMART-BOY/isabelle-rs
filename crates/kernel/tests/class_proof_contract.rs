use std::collections::BTreeMap;

use isabelle_kernel::{
    EmptyClassDeclCert, InstEntry, KernelError, KernelRules, Name, OfClassCandidate, PolyType,
    PolyTypeParam, ProofContext, RawTerm, SemanticArityCert, Signature, Sort, TrustedTheory, Ty,
    TypeInstantiation, TypeVarId, accept_closed_theorem, prove_of_class,
};

fn owner() -> TrustedTheory {
    TrustedTheory::root(
        "HOL",
        Signature::new().install_empty_class(EmptyClassDeclCert::hol_type()).unwrap(),
    )
}

#[test]
fn of_class_annotated_atom_requires_explicit_class() {
    let owner = owner();
    let class = Name::from("HOL.type");
    let sorted = Ty::tvar("a", 0, Sort::hol_type());
    let unsorted = Ty::tvar("a", 0, Sort::empty());
    let checked =
        prove_of_class(&owner, sorted.clone(), class.clone(), OfClassCandidate::AnnotatedAtomLeaf)
            .unwrap();
    assert_eq!(checked.ty(), &sorted);
    assert_eq!(checked.owner(), owner.id());
    assert!(matches!(
        prove_of_class(&owner, unsorted, class, OfClassCandidate::AnnotatedAtomLeaf),
        Err(KernelError::UnknownClassEvidence)
    ));
}

#[test]
fn of_class_checked_theorem_accepts_exact_annotation() {
    let owner = owner();
    let atom = Ty::tvar("a", 0, Sort::hol_type());
    let proof =
        prove_of_class(&owner, atom, "HOL.type".into(), OfClassCandidate::AnnotatedAtomLeaf)
            .unwrap();
    let closed = KernelRules::of_class(&owner, &proof).unwrap();
    let (_, token) = accept_closed_theorem(&owner, "HOL.type_intro", closed).unwrap();
    assert_eq!(token.dependencies().len(), 0);
    assert_eq!(token.as_kernel().shyps().len(), 1);
    assert!(token.as_kernel().shyps().contains(&Sort::hol_type()));
    let foreign = TrustedTheory::root("Foreign", owner.signature().clone());
    assert!(matches!(
        KernelRules::of_class(&foreign, &proof),
        Err(KernelError::UnknownClassEvidence)
    ));
}

#[test]
fn of_class_export_premise_cannot_escape_scope() {
    let owner = owner();
    let atom = Ty::tvar("a", 0, Sort::hol_type());
    assert!(matches!(
        prove_of_class(
            &owner,
            atom,
            "HOL.type".into(),
            OfClassCandidate::ExportPremiseLeaf { slot: 0 }
        ),
        Err(KernelError::UnknownClassEvidence)
    ));
}

#[test]
fn of_class_constructor_requires_arity_in_owner() {
    let owner = owner();
    let arg = Ty::tvar("a", 0, Sort::hol_type());
    let fun = Ty::arrow(arg.clone(), arg);
    let candidate = OfClassCandidate::TypeConstructor {
        arguments: vec![vec![OfClassCandidate::AnnotatedAtomLeaf]; 2],
    };
    assert!(matches!(
        prove_of_class(&owner, fun.clone(), "HOL.type".into(), candidate.clone()),
        Err(KernelError::UnknownClassEvidence)
    ));
    let installed = owner.install_semantic_arity(SemanticArityCert::FunctionTypeArityCert).unwrap();
    let checked = prove_of_class(&installed, fun, "HOL.type".into(), candidate).unwrap();
    assert_eq!(checked.owner(), installed.id());
    assert_ne!(installed.signature().id(), owner.signature().id());
}

#[test]
fn of_class_arity_rejects_unsorted_or_missing_argument_proof() {
    let owner = owner().install_semantic_arity(SemanticArityCert::FunctionTypeArityCert).unwrap();
    let sorted = Ty::tvar("a", 0, Sort::hol_type());
    let unsorted = Ty::tvar("b", 0, Sort::empty());
    let fun = Ty::arrow(sorted, unsorted);
    for arguments in [
        vec![vec![OfClassCandidate::AnnotatedAtomLeaf]],
        vec![vec![OfClassCandidate::AnnotatedAtomLeaf]; 2],
        vec![vec![OfClassCandidate::AnnotatedAtomLeaf], vec![]],
    ] {
        assert!(matches!(
            prove_of_class(
                &owner,
                fun.clone(),
                "HOL.type".into(),
                OfClassCandidate::TypeConstructor { arguments }
            ),
            Err(KernelError::UnknownClassEvidence)
        ));
    }
}

#[test]
fn of_class_fresh_model_requires_recorded_fresh_declaration() {
    let owner = owner();
    let model = SemanticArityCert::FreshNonemptyTyconCert { tycon: "box".into(), arity: 1 };
    let predeclared = TrustedTheory::root(
        "Predeclared",
        owner.signature().extend_type_constructor("box", 1).unwrap(),
    );
    assert!(matches!(
        predeclared.install_semantic_arity(model.clone()),
        Err(KernelError::UnknownClassEvidence)
    ));
    let declared = owner.declare_fresh_nonempty_tycon("box", 1).unwrap();
    let installed = declared.install_semantic_arity(model).unwrap();
    let arg = Ty::tvar("a", 0, Sort::hol_type());
    let box_ty = Ty::apply("box", vec![arg]).unwrap();
    prove_of_class(
        &installed,
        box_ty.clone(),
        "HOL.type".into(),
        OfClassCandidate::TypeConstructor {
            arguments: vec![vec![OfClassCandidate::AnnotatedAtomLeaf]],
        },
    )
    .unwrap();
    assert!(matches!(
        prove_of_class(
            &declared,
            box_ty,
            "HOL.type".into(),
            OfClassCandidate::TypeConstructor {
                arguments: vec![vec![OfClassCandidate::AnnotatedAtomLeaf]],
            }
        ),
        Err(KernelError::UnknownClassEvidence)
    ));
}

#[test]
fn of_class_semantic_root_is_not_public_theorem_evidence() {
    let owner = owner();
    let atom = Ty::tvar("a", 0, Sort::hol_type());
    let fun = Ty::arrow(atom.clone(), atom);
    assert!(matches!(
        prove_of_class(
            &owner,
            fun,
            "HOL.type".into(),
            OfClassCandidate::SemanticArity {
                arguments: vec![vec![OfClassCandidate::AnnotatedAtomLeaf]; 2],
            }
        ),
        Err(KernelError::UnknownClassEvidence)
    ));
}

#[test]
fn solve_constraints_nonempty_sort_replays_real_arity() {
    let owner = owner().install_semantic_arity(SemanticArityCert::FunctionTypeArityCert).unwrap();
    let context = ProofContext::new(owner.snapshot().clone());
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let beta = Ty::tvar("b", 0, Sort::hol_type());
    let function = Ty::arrow(beta.clone(), beta);
    let source = KernelRules::reflexive(context.certify_term(RawTerm::var("x", 0, alpha)).unwrap());
    let instantiation = TypeInstantiation::try_new(BTreeMap::from([(
        TypeVarId::new("a", 0, Sort::hol_type()),
        function,
    )]))
    .unwrap();
    let instantiated =
        KernelRules::instantiate(&context, source.as_kernel(), &instantiation, &[]).unwrap();
    assert!(instantiated.clone().try_close().is_err());
    let solved = KernelRules::solve_constraints(&owner, &instantiated).unwrap();
    let (_, token) =
        accept_closed_theorem(&owner, "function_reflexive", solved.try_close().unwrap()).unwrap();
    assert_eq!(token.prop(), instantiated.prop());
    assert_eq!(token.dependencies().len(), 1);
    let stripped = KernelRules::strip_shyps(&owner, &context, &instantiated).unwrap();
    let (_, stripped_token) =
        accept_closed_theorem(&owner, "function_reflexive_stripped", stripped.try_close().unwrap())
            .unwrap();
    assert_eq!(stripped_token.prop(), instantiated.prop());
    assert_eq!(stripped_token.dependencies().len(), 1);
}

#[test]
fn solve_constraints_foreign_owner_does_not_replay() {
    let owner = owner();
    let context = ProofContext::new(owner.snapshot().clone());
    let source = KernelRules::reflexive(
        context.certify_term(RawTerm::var("x", 0, Ty::tvar("a", 0, Sort::hol_type()))).unwrap(),
    );
    let foreign = TrustedTheory::root("Foreign", owner.signature().clone());
    assert!(matches!(
        KernelRules::solve_constraints(&foreign, source.as_kernel()),
        Err(KernelError::MixedContext { .. })
    ));
}

#[test]
fn of_class_copied_graph_without_certificate_does_not_authorize() {
    let certified =
        owner().install_semantic_arity(SemanticArityCert::FunctionTypeArityCert).unwrap();
    let graph_only = TrustedTheory::root("CopiedGraph", certified.signature().clone());
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let function = Ty::arrow(alpha.clone(), alpha);
    assert!(matches!(
        prove_of_class(
            &graph_only,
            function.clone(),
            "HOL.type".into(),
            OfClassCandidate::TypeConstructor {
                arguments: vec![vec![OfClassCandidate::AnnotatedAtomLeaf]; 2],
            }
        ),
        Err(KernelError::UnknownClassEvidence)
    ));
    let context = ProofContext::new(graph_only.snapshot().clone());
    let reflexive =
        KernelRules::reflexive(context.certify_term(RawTerm::var("x", 0, function)).unwrap());
    assert!(matches!(
        accept_closed_theorem(&graph_only, "copied_graph", reflexive),
        Err(KernelError::Invariant(_))
    ));
}

#[test]
fn fresh_nonempty_sibling_declarations_do_not_merge() {
    let root = owner();
    let first = root.begin_child("A").declare_fresh_nonempty_tycon("Box", 1).unwrap();
    let second = root.begin_child("B").declare_fresh_nonempty_tycon("Box", 1).unwrap();
    assert!(matches!(
        TrustedTheory::merge_parents("ConflictingBox", &[first, second]),
        Err(KernelError::DuplicateDeclaration { .. })
    ));
}

#[test]
fn unconstrain_t_sorted_atom_exports_real_class_premise() {
    let owner = owner();
    let context = ProofContext::new(owner.snapshot().clone());
    let sorted = Ty::tvar("a", 0, Sort::hol_type());
    let term = context.certify_term(RawTerm::var("x", 0, sorted)).unwrap();
    let source = KernelRules::reflexive(term);
    let exported = KernelRules::unconstrain_t(&owner, &context, source.as_kernel()).unwrap();
    assert!(exported.hyps().is_empty());
    assert_eq!(exported.prop().term().nprems(), 1);
    assert_eq!(exported.shyps().iter().cloned().collect::<Vec<_>>(), vec![Sort::empty()]);
    let (_, accepted) =
        accept_closed_theorem(&owner, "sorted_export", exported.try_close().unwrap()).unwrap();
    assert_eq!(accepted.dependencies().len(), 0);
    assert_eq!(accepted.prop().term().nprems(), 1);
}

#[test]
fn unconstrain_t_replays_inner_export_without_consuming_its_premise() {
    let owner = owner();
    let context = ProofContext::new(owner.snapshot().clone());
    let term =
        context.certify_term(RawTerm::var("x", 0, Ty::tvar("a", 0, Sort::hol_type()))).unwrap();
    let first =
        KernelRules::unconstrain_t(&owner, &context, KernelRules::reflexive(term).as_kernel())
            .unwrap();
    let (child, token) =
        accept_closed_theorem(&owner, "inner", first.try_close().unwrap()).unwrap();
    let imported = KernelRules::theorem_ref(&child, &token).unwrap();
    let child_context = ProofContext::new(child.snapshot().clone());
    let outer = KernelRules::unconstrain_t(&child, &child_context, imported.as_kernel()).unwrap();
    assert_eq!(outer.prop().term().nprems(), 1);
    let (_, accepted) = accept_closed_theorem(&child, "outer", outer.try_close().unwrap()).unwrap();
    assert_eq!(accepted.dependencies().len(), 1);
}

#[test]
fn unconstrain_t_nested_transport_replays_without_extra_premises() {
    const NESTED_EXPORT_ROUNDS: usize = 12;
    let owner = TrustedTheory::root("NestedExports", Signature::new());
    let context = ProofContext::new(owner.snapshot().clone());
    let term = context.certify_term(RawTerm::var("p", 0, Ty::prop())).unwrap();
    let mut theorem = KernelRules::reflexive(term).into_kernel();
    for _ in 0..NESTED_EXPORT_ROUNDS {
        theorem = KernelRules::unconstrain_t(&owner, &context, &theorem).unwrap();
        assert_eq!(theorem.prop().term().nprems(), 0);
    }
    let (_, accepted) =
        accept_closed_theorem(&owner, "nested_exports", theorem.try_close().unwrap()).unwrap();
    assert!(accepted.dependencies().is_empty());
}

#[test]
fn unconstrain_t_rejects_foreign_owner_before_source_replay() {
    let owner = owner();
    let context = ProofContext::new(owner.snapshot().clone());
    let term =
        context.certify_term(RawTerm::var("x", 0, Ty::tvar("a", 0, Sort::hol_type()))).unwrap();
    let source = KernelRules::reflexive(term);
    let foreign = TrustedTheory::root("Foreign", owner.signature().clone());
    let foreign_context = ProofContext::new(foreign.snapshot().clone());
    assert!(matches!(
        KernelRules::unconstrain_t(&foreign, &foreign_context, source.as_kernel()),
        Err(KernelError::MixedContext { .. }),
    ));
}

#[test]
fn unconstrain_t_sorted_constant_keeps_occurrence_class_evidence() {
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let ty = Ty::arrow(alpha.clone(), alpha);
    let scheme = PolyType::new(
        vec![PolyTypeParam { id: TypeVarId::new("a", 0, Sort::hol_type()) }],
        ty.clone(),
    )
    .unwrap();
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const_scheme("F", scheme)
        .unwrap();
    let owner = TrustedTheory::root("SortedConstant", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    let term = context.certify_term(RawTerm::const_("F", ty)).unwrap();
    let theorem = KernelRules::reflexive(term);
    let exported = KernelRules::unconstrain_t(&owner, &context, theorem.as_kernel()).unwrap();
    assert_eq!(exported.prop().term().nprems(), 1);
    let (_, token) =
        accept_closed_theorem(&owner, "sorted_const_export", exported.try_close().unwrap())
            .unwrap();
    assert_eq!(token.prop().term().nprems(), 1);
    assert!(token.as_kernel().hyps().is_empty());
}

#[test]
fn unconstrain_t_polymorphic_constant_instantiation_retains_class_premise() {
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let scheme = PolyType::new(
        vec![PolyTypeParam { id: TypeVarId::new("a", 0, Sort::hol_type()) }],
        Ty::arrow(alpha.clone(), alpha.clone()),
    )
    .unwrap();
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const_scheme("F", scheme)
        .unwrap();
    let owner = TrustedTheory::root("PolymorphicExport", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    let function =
        context.certify_term(RawTerm::const_("F", Ty::arrow(alpha.clone(), alpha))).unwrap();
    let exported =
        KernelRules::unconstrain_t(&owner, &context, KernelRules::reflexive(function).as_kernel())
            .unwrap();
    let replacement = TypeInstantiation::try_new(BTreeMap::from([(
        TypeVarId::new("a0", 0, Sort::empty()),
        Ty::prop(),
    )]))
    .unwrap();
    let instantiated = KernelRules::instantiate(&context, &exported, &replacement, &[]).unwrap();
    assert_eq!(instantiated.prop().term().nprems(), 1);
    let (_, token) = accept_closed_theorem(
        &owner,
        "polymorphic_export_instance",
        instantiated.try_close().unwrap(),
    )
    .unwrap();
    assert_eq!(token.prop().term().nprems(), 1);
}

#[test]
fn unconstrain_t_monomorphic_schematic_constant_rejects_type_export() {
    let alpha = Ty::tvar("a", 0, Sort::empty());
    let signature = Signature::new().extend_const("c", alpha.clone()).unwrap();
    let owner = TrustedTheory::root("MonomorphicExport", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    let term = context.certify_term(RawTerm::const_("c", alpha)).unwrap();
    let theorem = KernelRules::reflexive(term);
    assert!(matches!(
        KernelRules::unconstrain_t(&owner, &context, theorem.as_kernel()),
        Err(KernelError::TypeMismatch { .. }),
    ));
    let (_, token) = accept_closed_theorem(&owner, "original_c", theorem).unwrap();
    assert!(token.as_kernel().hyps().is_empty());
}

#[test]
fn instantiate_mixed_erased_theorem_rejects_monomorphic_constant_change() {
    let alpha = Ty::tvar("a", 0, Sort::empty());
    let owner = TrustedTheory::root(
        "ErasedModeBypass",
        Signature::new().extend_const("c", alpha.clone()).unwrap(),
    );
    let context = ProofContext::new(owner.snapshot().clone());
    let source =
        KernelRules::reflexive(context.certify_term(RawTerm::var("p", 0, Ty::prop())).unwrap());
    let exported = KernelRules::unconstrain_t(&owner, &context, source.as_kernel()).unwrap();
    let antecedent = context
        .certify_prop(RawTerm::eq(RawTerm::const_("c", alpha.clone()), RawTerm::const_("c", alpha)))
        .unwrap();
    let mixed = KernelRules::implies_intr(&antecedent, &exported).unwrap();
    let substitution = TypeInstantiation::try_new(BTreeMap::from([(
        TypeVarId::new("a", 0, Sort::empty()),
        Ty::prop(),
    )]))
    .unwrap();
    assert!(matches!(
        KernelRules::instantiate(&context, &mixed, &substitution, &[]),
        Err(KernelError::TypeMismatch { .. }),
    ));
    assert!(owner.signature().certify_const_instance(&Name::from("c"), &Ty::prop()).is_err());
}

#[test]
fn concretized_constant_occurrence_records_semantic_arity_dependency() {
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let scheme = PolyType::new(
        vec![PolyTypeParam { id: TypeVarId::new("a", 0, Sort::hol_type()) }],
        Ty::arrow(alpha.clone(), alpha.clone()),
    )
    .unwrap();
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const_scheme("F", scheme)
        .unwrap();
    let root = TrustedTheory::root("ConcreteInstance", signature);
    let declared = root.declare_fresh_nonempty_tycon("W", 0).unwrap();
    let owner = declared
        .install_semantic_arity(SemanticArityCert::FreshNonemptyTyconCert {
            tycon: "W".into(),
            arity: 0,
        })
        .unwrap();
    let witness = Ty::base("W").unwrap();
    let concrete_ty = Ty::arrow(witness.clone(), witness);
    let context = ProofContext::new(owner.snapshot().clone());
    let source =
        KernelRules::reflexive(context.certify_term(RawTerm::const_("F", concrete_ty)).unwrap());
    let (_, accepted) = accept_closed_theorem(&owner, "direct_concrete", source).unwrap();
    assert_eq!(accepted.dependencies().len(), 1);

    let erased_context = ProofContext::new(owner.snapshot().clone());
    let abstract_ty = Ty::arrow(alpha.clone(), alpha);
    let polymorphic = KernelRules::reflexive(
        erased_context.certify_term(RawTerm::const_("F", abstract_ty)).unwrap(),
    );
    let exported =
        KernelRules::unconstrain_t(&owner, &erased_context, polymorphic.as_kernel()).unwrap();
    let replacement = TypeInstantiation::try_new(BTreeMap::from([(
        TypeVarId::new("a0", 0, Sort::empty()),
        Ty::base("W").unwrap(),
    )]))
    .unwrap();
    let concrete = KernelRules::instantiate(&erased_context, &exported, &replacement, &[]).unwrap();
    let (_, accepted) =
        accept_closed_theorem(&owner, "export_concrete", concrete.try_close().unwrap()).unwrap();
    assert_eq!(accepted.dependencies().len(), 1);

    let graph_only = TrustedTheory::root("UnprovedW", owner.signature().clone());
    let graph_context = ProofContext::new(graph_only.snapshot().clone());
    let unsupported = KernelRules::reflexive(
        graph_context
            .certify_term(RawTerm::const_(
                "F",
                Ty::arrow(Ty::base("W").unwrap(), Ty::base("W").unwrap()),
            ))
            .unwrap(),
    );
    assert!(accept_closed_theorem(&graph_only, "no_arity", unsupported).is_err());
    let abstract_source = KernelRules::reflexive(
        graph_context
            .certify_term(RawTerm::const_(
                "F",
                Ty::arrow(Ty::tvar("a", 0, Sort::hol_type()), Ty::tvar("a", 0, Sort::hol_type())),
            ))
            .unwrap(),
    );
    let graph_export =
        KernelRules::unconstrain_t(&graph_only, &graph_context, abstract_source.as_kernel())
            .unwrap();
    let graph_instance =
        KernelRules::instantiate(&graph_context, &graph_export, &replacement, &[]).unwrap();
    assert!(
        accept_closed_theorem(&graph_only, "no_export_arity", graph_instance.try_close().unwrap())
            .is_err()
    );
}

#[test]
fn concrete_constant_export_permutation_keeps_semantic_arity_dependency() {
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let scheme = PolyType::new(
        vec![PolyTypeParam { id: TypeVarId::new("a", 0, Sort::hol_type()) }],
        Ty::arrow(alpha.clone(), alpha),
    )
    .unwrap();
    let root = TrustedTheory::root(
        "ConcreteExportPermute",
        Signature::new()
            .install_empty_class(EmptyClassDeclCert::hol_type())
            .unwrap()
            .extend_const_scheme("F", scheme)
            .unwrap(),
    );
    let declared = root.declare_fresh_nonempty_tycon("W", 0).unwrap();
    let owner = declared
        .install_semantic_arity(SemanticArityCert::FreshNonemptyTyconCert {
            tycon: "W".into(),
            arity: 0,
        })
        .unwrap();
    let context = ProofContext::new(owner.snapshot().clone());
    let witness = Ty::base("W").unwrap();
    let reflexive = KernelRules::reflexive(
        context.certify_term(RawTerm::const_("F", Ty::arrow(witness.clone(), witness))).unwrap(),
    );
    let exported = KernelRules::unconstrain_t(&owner, &context, reflexive.as_kernel()).unwrap();
    let permuted = KernelRules::permute_prems(&owner, &context, &exported, 0, 0).unwrap();
    let (_, accepted) =
        accept_closed_theorem(&owner, "concrete_export_permuted", permuted.try_close().unwrap())
            .unwrap();
    assert_eq!(accepted.dependencies().len(), 1);
}

fn prepare_hidden_constant_instance() -> (TrustedTheory, Ty) {
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let scheme = PolyType::new(
        vec![PolyTypeParam { id: TypeVarId::new("a", 0, Sort::hol_type()) }],
        Ty::arrow(alpha.clone(), alpha),
    )
    .unwrap();
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const_scheme("F", scheme)
        .unwrap()
        .extend_const("P", Ty::prop())
        .unwrap();
    let declared = TrustedTheory::root("HiddenInstance", signature)
        .declare_fresh_nonempty_tycon("W", 0)
        .unwrap();
    let owner = declared
        .install_semantic_arity(SemanticArityCert::FreshNonemptyTyconCert {
            tycon: "W".into(),
            arity: 0,
        })
        .unwrap();
    let witness = Ty::base("W").unwrap();
    (owner, Ty::arrow(witness.clone(), witness))
}

#[test]
fn forall_elim_discarded_constant_argument_retains_arity_dependency() {
    let (owner, constant_ty) = prepare_hidden_constant_instance();
    let mut context = ProofContext::new(owner.snapshot().clone());
    context.declare_free("x", constant_ty.clone());
    let variable = context.certify_term(RawTerm::free("x", constant_ty.clone())).unwrap();
    let p = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let premise = KernelRules::reflexive(p);
    let quantified = KernelRules::forall_intr(&variable, premise.as_kernel()).unwrap();
    let argument = context.certify_term(RawTerm::const_("F", constant_ty)).unwrap();
    let result = KernelRules::forall_elim(&quantified, &argument).unwrap();
    let (_, accepted) =
        accept_closed_theorem(&owner, "hidden_argument", result.try_close().unwrap()).unwrap();
    assert_eq!(accepted.dependencies().len(), 1);
}

#[test]
fn instantiate_unused_constant_replacement_retains_arity_dependency() {
    let (owner, constant_ty) = prepare_hidden_constant_instance();
    let context = ProofContext::new(owner.snapshot().clone());
    let p = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
    let premise = KernelRules::reflexive(p);
    let replacement = context.certify_term(RawTerm::const_("F", constant_ty.clone())).unwrap();
    let result = KernelRules::instantiate(
        &context,
        premise.as_kernel(),
        &TypeInstantiation::empty(),
        &[InstEntry::new("unused", 0, constant_ty, replacement)],
    )
    .unwrap();
    let (_, accepted) =
        accept_closed_theorem(&owner, "hidden_replacement", result.try_close().unwrap()).unwrap();
    assert_eq!(accepted.dependencies().len(), 1);
}

#[test]
fn unconstrain_t_monomorphic_sorted_constant_rejects_erased_instance() {
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let signature = Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())
        .unwrap()
        .extend_const("c", alpha.clone())
        .unwrap();
    let owner = TrustedTheory::root("SortedMonomorphic", signature);
    let context = ProofContext::new(owner.snapshot().clone());
    let term = context.certify_term(RawTerm::const_("c", alpha)).unwrap();
    let theorem = KernelRules::reflexive(term);
    assert!(matches!(
        KernelRules::unconstrain_t(&owner, &context, theorem.as_kernel()),
        Err(KernelError::TypeMismatch { .. }),
    ));
}

#[test]
fn semantic_arity_repeated_installation_rejects_without_new_owner() {
    let owner = owner().install_semantic_arity(SemanticArityCert::FunctionTypeArityCert).unwrap();
    let unchanged_id = owner.id();
    assert!(matches!(
        owner.install_semantic_arity(SemanticArityCert::FunctionTypeArityCert),
        Err(KernelError::DuplicateDeclaration { .. }),
    ));
    assert!(matches!(
        owner.install_class_arity(
            Name::from("fun"),
            vec![Sort::hol_type(); 2],
            Name::from("HOL.type"),
            OfClassCandidate::TypeConstructor {
                arguments: vec![vec![OfClassCandidate::AnnotatedAtomLeaf]; 2],
            },
        ),
        Err(KernelError::DuplicateDeclaration { .. }),
    ));
    assert_eq!(owner.id(), unchanged_id);
}

#[test]
fn unconstrain_t_same_sort_distinct_atoms_keep_separate_slots() {
    let owner = owner();
    let context = ProofContext::new(owner.snapshot().clone());
    let alpha = Ty::tvar("a", 0, Sort::hol_type());
    let beta = Ty::tvar("b", 1, Sort::hol_type());
    let assumption = context
        .certify_prop(RawTerm::eq(RawTerm::var("x", 0, alpha.clone()), RawTerm::var("x", 0, alpha)))
        .unwrap();
    let body = KernelRules::reflexive(context.certify_term(RawTerm::var("y", 1, beta)).unwrap());
    let theorem = KernelRules::implies_intr(&assumption, body.as_kernel()).unwrap();
    let exported = KernelRules::unconstrain_t(&owner, &context, &theorem).unwrap();
    let (premises, _) = exported.prop().term().dest_imp_chain();
    assert_eq!(premises.len(), 3);
    assert_ne!(premises[0], premises[1]);
    let (_, token) =
        accept_closed_theorem(&owner, "distinct_atoms", exported.try_close().unwrap()).unwrap();
    assert_eq!(token.prop().term().nprems(), 3);
}

#[test]
fn class_predicate_ground_witness_cannot_be_redefined_without_basis() {
    let root = owner().declare_fresh_nonempty_tycon("Witness", 0).unwrap();
    let owner = root
        .install_semantic_arity(SemanticArityCert::FreshNonemptyTyconCert {
            tycon: Name::from("Witness"),
            arity: 0,
        })
        .unwrap();
    let witness = Ty::base("Witness").unwrap();
    let proof = prove_of_class(
        &owner,
        witness,
        Name::from("HOL.type"),
        OfClassCandidate::TypeConstructor { arguments: vec![] },
    )
    .unwrap();
    let (_, token) = accept_closed_theorem(
        &owner,
        "ground_witness",
        KernelRules::of_class(&owner, &proof).unwrap(),
    )
    .unwrap();
    assert!(!token.dependencies().is_empty());
    let a = Ty::tvar("a", 0, Sort::empty());
    let tag = Ty::apply("itself", vec![a]).unwrap();
    let false_predicate =
        RawTerm::abs("tag", tag, RawTerm::forall("p", Ty::prop(), RawTerm::bound(0)));
    assert!(matches!(
        owner.define_const("HOL.type_class", false_predicate),
        Err(KernelError::DuplicateDeclaration { .. }),
    ));
}

#[test]
fn semantic_arity_overflow_is_rejected_before_model_allocation() {
    let owner = owner();
    assert!(matches!(
        owner.signature().extend_type_constructor("Huge", usize::MAX),
        Err(KernelError::TypeConstructorArityOutOfRange { .. }),
    ));
    assert!(matches!(
        owner.declare_fresh_nonempty_tycon("Huge", usize::MAX),
        Err(KernelError::TypeConstructorArityOutOfRange { .. }),
    ));
}
