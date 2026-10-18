//! Exact kernel-side HOLBasisV1 slots, transcribed from fixed Isabelle2025
//! HOL/Hilbert_Choice/Nat/Set declarations. Schema Forall nodes bind the
//! source's schematic term parameters; inner Forall/Imp/Eq are Pure syntax.

use super::{AxiomSchema, BasisDeclaration, LogicPolicyId, PolyType, PolyTypeParam, TypeVarId};
use crate::{KernelError, Name, RawTerm as R, Sort, Ty};

fn bool_ty() -> Result<Ty, KernelError> {
    Ty::base("bool")
}
fn ind_ty() -> Result<Ty, KernelError> {
    Ty::base("Nat.ind")
}
fn alpha() -> Ty {
    Ty::tvar("'a", 0, Sort::hol_type())
}
fn beta() -> Ty {
    Ty::tvar("'b", 0, Sort::hol_type())
}
fn arrow(input: Ty, output: Ty) -> Ty {
    Ty::arrow(input, output)
}
fn scheme(parameters: &[&str], body: Ty) -> Result<PolyType, KernelError> {
    PolyType::new(
        parameters
            .iter()
            .map(|name| PolyTypeParam { id: TypeVarId::new(*name, 0, Sort::hol_type()) })
            .collect(),
        body,
    )
}
fn constant(name: &str, ty: Ty) -> R {
    R::const_(name, ty)
}
fn apply2(func: R, first: R, second: R) -> R {
    R::app(R::app(func, first), second)
}
fn obj_eq(ty: Ty, left: R, right: R) -> Result<R, KernelError> {
    Ok(apply2(constant("HOL.eq", arrow(ty.clone(), arrow(ty, bool_ty()?))), left, right))
}
fn trueprop(prop: R) -> Result<R, KernelError> {
    Ok(R::app(constant("HOL.Trueprop", arrow(bool_ty()?, Ty::prop())), prop))
}
fn obj_imp(left: R, right: R) -> Result<R, KernelError> {
    let bool_ty = bool_ty()?;
    Ok(apply2(
        constant("HOL.implies", arrow(bool_ty.clone(), arrow(bool_ty.clone(), bool_ty))),
        left,
        right,
    ))
}
fn obj_or(left: R, right: R) -> Result<R, KernelError> {
    let bool_ty = bool_ty()?;
    Ok(apply2(
        constant("HOL.disj", arrow(bool_ty.clone(), arrow(bool_ty.clone(), bool_ty))),
        left,
        right,
    ))
}
fn bound_schema(name: &str, params: &[(&str, Ty)], body: R) -> AxiomSchema {
    AxiomSchema {
        name: name.into(),
        prop: params.iter().rev().fold(body, |prop, (name, ty)| R::forall(*name, ty.clone(), prop)),
    }
}
fn hol_axioms() -> Result<Vec<AxiomSchema>, KernelError> {
    let a = alpha();
    let b = beta();
    let bool_ty = bool_ty()?;
    let predicate = arrow(a.clone(), bool_ty.clone());
    let fn_ty = arrow(a.clone(), b.clone());
    let eq_a = |left, right| obj_eq(a.clone(), left, right);
    let object_p = |index| trueprop(R::bound(index));
    let refl =
        bound_schema("HOL.refl", &[("t", a.clone())], trueprop(eq_a(R::bound(0), R::bound(0))?)?);
    let subst = bound_schema(
        "HOL.subst",
        &[("s", a.clone()), ("t", a.clone()), ("P", predicate.clone())],
        R::imp(
            trueprop(eq_a(R::bound(2), R::bound(1))?)?,
            R::imp(
                trueprop(R::app(R::bound(0), R::bound(2)))?,
                trueprop(R::app(R::bound(0), R::bound(1)))?,
            ),
        ),
    );
    let applied = |func: usize| R::app(R::bound(func), R::bound(0));
    let ext = bound_schema(
        "HOL.ext",
        &[("f", fn_ty.clone()), ("g", fn_ty.clone())],
        R::imp(
            R::forall("x", a.clone(), trueprop(obj_eq(b.clone(), applied(2), applied(1))?)?),
            trueprop(obj_eq(
                fn_ty,
                R::abs("x", a.clone(), applied(2)),
                R::abs("x", a.clone(), applied(1)),
            )?)?,
        ),
    );
    let the = R::app(
        constant("HOL.The", arrow(predicate.clone(), a.clone())),
        R::abs("x", a.clone(), eq_a(R::bound(0), R::bound(1))?),
    );
    let the_eq_trivial =
        bound_schema("HOL.the_eq_trivial", &[("a", a.clone())], trueprop(eq_a(the, R::bound(0))?)?);
    let imp_i = bound_schema(
        "HOL.impI",
        &[("P", bool_ty.clone()), ("Q", bool_ty.clone())],
        R::imp(R::imp(object_p(1)?, object_p(0)?), trueprop(obj_imp(R::bound(1), R::bound(0))?)?),
    );
    let mp = bound_schema(
        "HOL.mp",
        &[("P", bool_ty.clone()), ("Q", bool_ty.clone())],
        R::imp(trueprop(obj_imp(R::bound(1), R::bound(0))?)?, R::imp(object_p(1)?, object_p(0)?)),
    );
    let bool_eq = |left, right| obj_eq(bool_ty.clone(), left, right);
    let true_or_false = bound_schema(
        "HOL.True_or_False",
        &[("P", bool_ty.clone())],
        trueprop(obj_or(
            bool_eq(R::bound(0), constant("HOL.True", bool_ty.clone()))?,
            bool_eq(R::bound(0), constant("HOL.False", bool_ty.clone()))?,
        )?)?,
    );
    let eq_reflection = bound_schema(
        "HOL.eq_reflection",
        &[("x", a.clone()), ("y", a.clone())],
        R::imp(trueprop(eq_a(R::bound(1), R::bound(0))?)?, R::eq(R::bound(1), R::bound(0))),
    );
    Ok(vec![refl, subst, ext, the_eq_trivial, imp_i, mp, true_or_false, eq_reflection])
}
fn later_axioms() -> Result<Vec<AxiomSchema>, KernelError> {
    let a = alpha();
    let bool_ty = bool_ty()?;
    let predicate = arrow(a.clone(), bool_ty.clone());
    let some_i = bound_schema(
        "Hilbert_Choice.someI",
        &[("P", predicate.clone()), ("x", a.clone())],
        R::imp(
            trueprop(R::app(R::bound(1), R::bound(0)))?,
            trueprop(R::app(
                R::bound(1),
                R::app(constant("Hilbert_Choice.Eps", arrow(predicate, a.clone())), R::bound(1)),
            ))?,
        ),
    );
    let ind = ind_ty()?;
    let suc = |value| R::app(constant("Nat.Suc_Rep", arrow(ind.clone(), ind.clone())), value);
    let inject = bound_schema(
        "Nat.Suc_Rep_inject",
        &[("x", ind.clone()), ("y", ind.clone())],
        R::imp(
            trueprop(obj_eq(ind.clone(), suc(R::bound(1)), suc(R::bound(0)))?)?,
            trueprop(obj_eq(ind.clone(), R::bound(1), R::bound(0))?)?,
        ),
    );
    let not_zero = bound_schema(
        "Nat.Suc_Rep_not_Zero_Rep",
        &[("x", ind.clone())],
        trueprop(R::app(
            constant("HOL.Not", arrow(bool_ty.clone(), bool_ty.clone())),
            obj_eq(ind.clone(), suc(R::bound(0)), constant("Nat.Zero_Rep", ind))?,
        ))?,
    );
    let set_ty = Ty::apply("Set.set", vec![a.clone()])?;
    let collect = |pred| {
        R::app(
            constant("Set.Collect", arrow(arrow(a.clone(), bool_ty.clone()), set_ty.clone())),
            pred,
        )
    };
    let member = |value, set| {
        apply2(
            constant("Set.member", arrow(a.clone(), arrow(set_ty.clone(), bool_ty.clone()))),
            value,
            set,
        )
    };
    let mem_collect = bound_schema(
        "Set.mem_Collect_eq",
        &[("a", a.clone()), ("P", arrow(a.clone(), bool_ty.clone()))],
        trueprop(obj_eq(
            bool_ty.clone(),
            member(R::bound(1), collect(R::bound(0))),
            R::app(R::bound(0), R::bound(1)),
        )?)?,
    );
    let collected_members = collect(R::abs("x", a.clone(), member(R::bound(0), R::bound(1))));
    let collect_mem = bound_schema(
        "Set.Collect_mem_eq",
        &[("A", set_ty.clone())],
        trueprop(obj_eq(set_ty, collected_members, R::bound(0))?)?,
    );
    Ok(vec![some_i, inject, not_zero, mem_collect, collect_mem])
}

pub(super) fn declarations() -> Result<Vec<BasisDeclaration>, KernelError> {
    let a = alpha();
    let bool_ty = bool_ty()?;
    let ind = ind_ty()?;
    let set = Ty::apply("Set.set", vec![a.clone()])?;
    Ok(vec![
        BasisDeclaration::TypeConstructor { name: "fun".into(), arity: 2 },
        BasisDeclaration::TypeConstructor { name: "bool".into(), arity: 0 },
        BasisDeclaration::Judgment {
            const_name: "HOL.Trueprop".into(),
            ty: arrow(bool_ty.clone(), Ty::prop()),
        },
        BasisDeclaration::Constant {
            name: "HOL.implies".into(),
            scheme: scheme(&[], arrow(bool_ty.clone(), arrow(bool_ty.clone(), bool_ty.clone())))?,
        },
        BasisDeclaration::Constant {
            name: "HOL.eq".into(),
            scheme: scheme(&["'a"], arrow(a.clone(), arrow(a.clone(), bool_ty.clone())))?,
        },
        BasisDeclaration::Constant {
            name: "HOL.The".into(),
            scheme: scheme(&["'a"], arrow(arrow(a.clone(), bool_ty.clone()), a.clone()))?,
        },
        BasisDeclaration::Constant {
            name: "Hilbert_Choice.Eps".into(),
            scheme: scheme(&["'a"], arrow(arrow(a.clone(), bool_ty.clone()), a.clone()))?,
        },
        BasisDeclaration::TypeConstructor { name: "Nat.ind".into(), arity: 0 },
        BasisDeclaration::Constant {
            name: "Nat.Zero_Rep".into(),
            scheme: scheme(&[], ind.clone())?,
        },
        BasisDeclaration::Constant {
            name: "Nat.Suc_Rep".into(),
            scheme: scheme(&[], arrow(ind.clone(), ind))?,
        },
        BasisDeclaration::TypeConstructor { name: "Set.set".into(), arity: 1 },
        BasisDeclaration::Constant {
            name: "Set.Collect".into(),
            scheme: scheme(&["'a"], arrow(arrow(a.clone(), bool_ty.clone()), set.clone()))?,
        },
        BasisDeclaration::Constant {
            name: "Set.member".into(),
            scheme: scheme(&["'a"], arrow(a, arrow(set, bool_ty)))?,
        },
    ])
}

pub(super) fn axioms() -> Result<Vec<AxiomSchema>, KernelError> {
    let mut result = hol_axioms()?;
    result.extend(later_axioms()?);
    Ok(result)
}

fn reject(name: &Name) -> KernelError {
    KernelError::UnapprovedAxiom { name: name.clone() }
}

pub(super) fn check_subset(
    policy: LogicPolicyId,
    declarations: &[BasisDeclaration],
    axioms: &[AxiomSchema],
) -> Result<(), KernelError> {
    if policy == LogicPolicyId::GenericResearch {
        return Ok(());
    }
    let expected_decls = self::declarations()?;
    let mut next = 0;
    for declaration in declarations {
        let Some(index) =
            expected_decls[next..].iter().position(|expected| expected == declaration)
        else {
            return Err(reject(declaration_name(declaration)));
        };
        next += index + 1;
    }
    let expected_axioms = self::axioms()?;
    next = 0;
    for axiom in axioms {
        let Some(index) = expected_axioms[next..].iter().position(|expected| expected == axiom)
        else {
            return Err(reject(&axiom.name));
        };
        next += index + 1;
    }
    Ok(())
}

fn declaration_name(declaration: &BasisDeclaration) -> &Name {
    match declaration {
        BasisDeclaration::TypeConstructor { name, .. }
        | BasisDeclaration::Constant { name, .. } => name,
        BasisDeclaration::Judgment { const_name, .. } => const_name,
    }
}

pub(super) fn order_subset(declarations: &mut [BasisDeclaration], axioms: &mut [AxiomSchema]) {
    if let (Ok(expected_decls), Ok(expected_axioms)) = (self::declarations(), self::axioms()) {
        declarations
            .sort_by_key(|declaration| expected_decls.iter().position(|item| item == declaration));
        axioms.sort_by_key(|axiom| expected_axioms.iter().position(|item| item == axiom));
    }
}
