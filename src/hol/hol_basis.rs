//! Narrow sampled HOL basis, checked against the kernel's exact HOLBasisV1.
//!
//! This adapter installs only the declarations required by the sampled
//! `HOL.refl` proof. The other approved slots require explicit, later owner
//! extensions; publishing reference data here does not authorize them.

use isabelle_kernel::SemanticArityCert;

use crate::kernel::{
    EmptyClassDeclCert, KernelError, LogicBasis, Name, Signature, Sort, TrustedTheory, Ty,
    logic::{PolyType, PolyTypeParam, TypeVarId},
};

/// The sampled owner installs only the exact `HOL.refl` schema.
pub fn hol_basis() -> LogicBasis {
    // The kernel's fixed manifest consists exclusively of statically checked
    // Ty and RawTerm constructors; failure here is an internal invariant.
    let (declarations, axioms) = LogicBasis::hol_v1_manifest().expect("fixed HOLBasisV1 manifest");
    let declarations = declarations
        .into_iter()
        .filter(|declaration| {
            matches!(
                declaration,
                crate::kernel::BasisDeclaration::TypeConstructor { name, .. }
                    if name.as_str() == "fun" || name.as_str() == "bool"
            ) || matches!(
                declaration,
                crate::kernel::BasisDeclaration::Judgment { const_name, .. }
                    if const_name.as_str() == "HOL.Trueprop"
            ) || matches!(
                declaration,
                crate::kernel::BasisDeclaration::Constant { name, .. }
                    if name.as_str() == "HOL.eq"
            )
        })
        .collect();
    let axioms = axioms.into_iter().filter(|axiom| axiom.name.as_str() == "HOL.refl").collect();
    LogicBasis::try_hol_basis(declarations, axioms)
        .expect("fixed sampled HOL subset must satisfy HOLBasisV1")
}

/// Build the signature required by the checked HOL logic basis.
pub fn hol_signature() -> Result<Signature, Box<KernelError>> {
    let bool_ty = Ty::base("bool")?;
    Signature::new()
        .install_empty_class(EmptyClassDeclCert::hol_type())?
        .extend_type_constructor("bool", 0)?
        .extend_const("HOL.Trueprop", Ty::arrow(bool_ty, Ty::prop()))?
        .extend_const_scheme("HOL.eq", hol_equality_scheme()?)
        .map_err(Box::new)
}

/// Reconstruct the audited HOL declarations as committed owner extensions.
/// A signature copied from this owner alone cannot authorize either class arity.
pub fn hol_owner(name: impl Into<Name>) -> Result<TrustedTheory, Box<KernelError>> {
    let root = TrustedTheory::root(
        name,
        Signature::new().install_empty_class(EmptyClassDeclCert::hol_type())?,
    );
    let function_arity = root.install_semantic_arity(SemanticArityCert::FunctionTypeArityCert)?;
    let declared = function_arity.declare_fresh_nonempty_tycon("bool", 0)?;
    let bool_arity =
        declared.install_semantic_arity(SemanticArityCert::FreshNonemptyTyconCert {
            tycon: "bool".into(),
            arity: 0,
        })?;
    let judgment =
        bool_arity.extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool")?, Ty::prop()))?;
    let equality = judgment.extend_const_scheme("HOL.eq", hol_equality_scheme()?)?;
    equality.install_basis(&hol_basis()).map_err(Box::new)
}

fn hol_equality_scheme() -> Result<PolyType, KernelError> {
    let parameter = TypeVarId::new("'a", 0, Sort::hol_type());
    let parameter_ty = Ty::tvar("'a", 0, Sort::hol_type());
    let bool_ty = Ty::base("bool")?;
    PolyType::new(
        vec![PolyTypeParam { id: parameter }],
        Ty::arrow(parameter_ty.clone(), Ty::arrow(parameter_ty, bool_ty)),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Signature;

    #[test]
    fn hol_basis_validates_against_correct_signature() {
        let mut sig = Signature::new()
            .install_empty_class(EmptyClassDeclCert::hol_type())
            .unwrap()
            .extend_type_constructor("bool", 0)
            .unwrap();
        sig = sig
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()))
            .unwrap();
        sig = sig
            .extend_const_scheme(
                "HOL.eq",
                PolyType::new(
                    vec![PolyTypeParam { id: TypeVarId::new("'a", 0, Sort::hol_type()) }],
                    Ty::arrow(
                        Ty::tvar("'a", 0, Sort::hol_type()),
                        Ty::arrow(Ty::tvar("'a", 0, Sort::hol_type()), Ty::base("bool").unwrap()),
                    ),
                )
                .expect("HOL.eq PolyType"),
            )
            .unwrap();
        let basis = hol_basis();
        assert!(basis.validate_against(&sig).is_ok());
    }

    #[test]
    fn hol_basis_id_is_stable() {
        let basis1 = hol_basis();
        let basis2 = hol_basis();
        assert_eq!(basis1.id(), basis2.id());
    }

    #[test]
    fn hol_basis_authorizes_only_refl() {
        let basis = hol_basis();
        let names: Vec<&str> = basis.axioms().iter().map(|axiom| axiom.name.as_str()).collect();
        assert_eq!(names, ["HOL.refl"]);
    }
}
