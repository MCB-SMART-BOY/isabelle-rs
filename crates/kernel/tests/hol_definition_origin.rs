use isabelle_kernel::{
    EmptyClassDeclCert, KernelError, LogicBasis, RawTerm as R, SemanticArityCert, Signature, Sort,
    TrustedTheory, Ty,
};

fn app2(function: R, left: R, right: R) -> R {
    R::app(R::app(function, left), right)
}

fn bool_ty() -> Ty {
    Ty::base("bool").unwrap()
}

fn source_equality(ty: Ty, left: R, right: R) -> R {
    app2(R::const_("HOL.eq", Ty::arrow(ty.clone(), Ty::arrow(ty, bool_ty()))), left, right)
}

fn source_implication(left: R, right: R) -> R {
    let boolean = bool_ty();
    app2(
        R::const_("HOL.implies", Ty::arrow(boolean.clone(), Ty::arrow(boolean.clone(), boolean))),
        left,
        right,
    )
}

fn make_boolean_owner() -> TrustedTheory {
    let root = TrustedTheory::root(
        "HOL",
        Signature::new().install_empty_class(EmptyClassDeclCert::hol_type()).unwrap(),
    );
    let root = root.install_semantic_arity(SemanticArityCert::FunctionTypeArityCert).unwrap();
    let root = root.declare_fresh_nonempty_tycon("bool", 0).unwrap();
    root.install_semantic_arity(SemanticArityCert::FreshNonemptyTyconCert {
        tycon: "bool".into(),
        arity: 0,
    })
    .unwrap()
}

fn make_primitive_owner() -> TrustedTheory {
    let root = make_boolean_owner();
    let boolean = bool_ty();
    let root = root.extend_const("HOL.Trueprop", Ty::arrow(boolean.clone(), Ty::prop())).unwrap();
    let root = root
        .extend_const(
            "HOL.implies",
            Ty::arrow(boolean.clone(), Ty::arrow(boolean.clone(), boolean.clone())),
        )
        .unwrap();
    let variable = Ty::tvar("'a", 0, Sort::hol_type());
    root.extend_const_scheme(
        "HOL.eq",
        isabelle_kernel::PolyType::new(
            vec![isabelle_kernel::PolyTypeParam {
                id: isabelle_kernel::TypeVarId::new("'a", 0, Sort::hol_type()),
            }],
            Ty::arrow(variable.clone(), Ty::arrow(variable, boolean)),
        )
        .unwrap(),
    )
    .unwrap()
}

fn define_source_boolean_connectives(owner: TrustedTheory, true_rhs: R) -> TrustedTheory {
    let boolean = bool_ty();
    let (owner, _) = owner.define_const("HOL.True", true_rhs).unwrap();
    let variable = Ty::tvar("'a", 0, Sort::hol_type());
    let predicate = Ty::arrow(variable.clone(), boolean.clone());
    let all_rhs = R::abs(
        "P",
        predicate.clone(),
        source_equality(
            predicate,
            R::bound(0),
            R::abs("x", variable, R::const_("HOL.True", boolean.clone())),
        ),
    );
    let (owner, _) = owner.define_const("HOL.All", all_rhs).unwrap();
    let all_bool = Ty::arrow(Ty::arrow(boolean.clone(), boolean.clone()), boolean.clone());
    let false_rhs =
        R::app(R::const_("HOL.All", all_bool.clone()), R::abs("P", boolean.clone(), R::bound(0)));
    let (owner, _) = owner.define_const("HOL.False", false_rhs).unwrap();
    let disjunction = source_implication(
        source_implication(R::bound(2), R::bound(0)),
        source_implication(source_implication(R::bound(1), R::bound(0)), R::bound(0)),
    );
    let disj_rhs = R::abs(
        "P",
        boolean.clone(),
        R::abs(
            "Q",
            boolean.clone(),
            R::app(R::const_("HOL.All", all_bool), R::abs("R", boolean, disjunction)),
        ),
    );
    owner.define_const("HOL.disj", disj_rhs).unwrap().0
}

fn make_true_or_false_basis() -> LogicBasis {
    let (_, axioms) = LogicBasis::hol_v1_manifest().unwrap();
    LogicBasis::try_hol_basis(
        vec![],
        axioms.into_iter().filter(|schema| schema.name.as_str() == "HOL.True_or_False").collect(),
    )
    .unwrap()
}

#[test]
fn hol_basis_true_or_false_exact_source_definitions_install() {
    let boolean = bool_ty();
    let identity = R::abs("x", boolean.clone(), R::bound(0));
    let true_rhs = source_equality(Ty::arrow(boolean.clone(), boolean), identity.clone(), identity);
    let owner = define_source_boolean_connectives(make_primitive_owner(), true_rhs);
    assert!(owner.install_basis(&make_true_or_false_basis()).is_ok());
}

#[test]
fn hol_basis_true_or_false_altered_true_definition_rejected() {
    let boolean = bool_ty();
    let identity = R::abs("x", boolean.clone(), R::bound(0));
    let other =
        R::abs("x", boolean.clone(), source_equality(boolean.clone(), R::bound(0), R::bound(0)));
    let altered = source_equality(Ty::arrow(boolean.clone(), boolean), identity, other);
    let owner = define_source_boolean_connectives(make_primitive_owner(), altered);
    assert!(matches!(owner.install_basis(&make_true_or_false_basis()),
        Err(KernelError::InvalidLogicBasisOrigin { name }) if name.as_str() == "HOL.True"));
}

fn make_imp_i_basis() -> LogicBasis {
    let (_, axioms) = LogicBasis::hol_v1_manifest().unwrap();
    LogicBasis::try_hol_basis(
        vec![],
        axioms.into_iter().filter(|schema| schema.name.as_str() == "HOL.impI").collect(),
    )
    .unwrap()
}

#[test]
fn hol_basis_zero_parameter_scheme_declaration_installs() {
    let boolean = bool_ty();
    let owner = make_boolean_owner()
        .extend_const("HOL.Trueprop", Ty::arrow(boolean.clone(), Ty::prop()))
        .unwrap()
        .extend_const_scheme(
            "HOL.implies",
            isabelle_kernel::PolyType::new(
                vec![],
                Ty::arrow(boolean.clone(), Ty::arrow(boolean.clone(), boolean)),
            )
            .unwrap(),
        )
        .unwrap();
    assert!(owner.install_basis(&make_imp_i_basis()).is_ok());
}

#[test]
fn hol_basis_merge_with_sibling_redefining_judgment_is_rejected() {
    let baseline = make_primitive_owner()
        .extend_const("bad", Ty::prop())
        .unwrap()
        .install_basis(&LogicBasis::try_hol_basis(vec![], vec![]).unwrap())
        .unwrap();
    let left = baseline.begin_child("L").install_basis(&make_imp_i_basis()).unwrap();
    let (right, _) = baseline
        .begin_child("R")
        .define_const("HOL.Trueprop", R::abs("p", bool_ty(), R::const_("bad", Ty::prop())))
        .unwrap();
    for parents in [&[left.clone(), right.clone()][..], &[right.clone(), left.clone()][..]] {
        assert!(matches!(TrustedTheory::merge_parents("Joint", parents),
            Err(KernelError::InvalidLogicBasisOrigin { name })
                if name.as_str() == "HOL.Trueprop"));
    }
}
