//! Owner-aware provenance for the fixed HOLBasisV1 assumptions.
//! A well-typed schema alone cannot authorize a symbol with a different meaning.

use std::collections::{BTreeMap, BTreeSet};

use crate::TrustedTheory;
use crate::theory::TheoryExtension;
use crate::{
    BasisDeclaration, ConstScheme, KernelError, LogicBasis, LogicPolicyId, Name, ProofContext,
    RawTerm as R, SemanticArityCert, Ty,
};

fn reject(name: &Name) -> KernelError {
    KernelError::InvalidLogicBasisOrigin { name: name.clone() }
}

fn boolean() -> Result<Ty, KernelError> {
    Ty::base("bool")
}
fn alpha() -> Ty {
    Ty::tvar("'a", 0, crate::Sort::hol_type())
}
fn arrow(left: Ty, right: Ty) -> Ty {
    Ty::arrow(left, right)
}
fn constant(name: &str, ty: Ty) -> R {
    R::const_(name, ty)
}
fn apply2(func: R, left: R, right: R) -> R {
    R::app(R::app(func, left), right)
}
fn equality(ty: Ty, left: R, right: R) -> Result<R, KernelError> {
    Ok(apply2(constant("HOL.eq", arrow(ty.clone(), arrow(ty, boolean()?))), left, right))
}
fn implication(left: R, right: R) -> Result<R, KernelError> {
    let bool_ty = boolean()?;
    Ok(apply2(
        constant("HOL.implies", arrow(bool_ty.clone(), arrow(bool_ty.clone(), bool_ty))),
        left,
        right,
    ))
}
fn quantified(ty: Ty, body: R) -> Result<R, KernelError> {
    Ok(R::app(
        constant("HOL.All", arrow(arrow(ty.clone(), boolean()?), boolean()?)),
        R::abs("x", ty, body),
    ))
}

// Source: fixed Isabelle2025 HOL.thy:100-119. These are conservative
// definitions, not additional basis axioms; compare certified terms modulo
// binder labels, never source text or the const's name alone.
fn expected_definition(name: &Name) -> Result<Option<R>, KernelError> {
    let bool_ty = boolean()?;
    let result = match name.as_str() {
        "HOL.True" => {
            let identity = R::abs("x", bool_ty.clone(), R::bound(0));
            equality(arrow(bool_ty.clone(), bool_ty), identity.clone(), identity)?
        },
        "HOL.All" => {
            let pred = arrow(alpha(), bool_ty.clone());
            let true_term = constant("HOL.True", bool_ty);
            R::abs("P", pred.clone(), equality(pred, R::bound(0), R::abs("x", alpha(), true_term))?)
        },
        "HOL.False" => quantified(bool_ty, R::bound(0))?,
        "HOL.Not" => {
            R::abs("P", bool_ty.clone(), implication(R::bound(0), constant("HOL.False", bool_ty))?)
        },
        "HOL.disj" => {
            let p_to_r = implication(R::bound(2), R::bound(0))?;
            let q_to_r = implication(R::bound(1), R::bound(0))?;
            let disjunction = implication(p_to_r, implication(q_to_r, R::bound(0))?)?;
            R::abs(
                "P",
                bool_ty.clone(),
                R::abs("Q", bool_ty.clone(), quantified(bool_ty, disjunction)?),
            )
        },
        _ => return Ok(None),
    };
    Ok(Some(result))
}

fn declaration_name(declaration: &BasisDeclaration) -> &Name {
    match declaration {
        BasisDeclaration::TypeConstructor { name, .. }
        | BasisDeclaration::Constant { name, .. } => name,
        BasisDeclaration::Judgment { const_name, .. } => const_name,
    }
}

fn require_arity<'a>(
    owner: &'a TrustedTheory,
    name: &Name,
    model: &SemanticArityCert,
) -> Result<&'a TrustedTheory, KernelError> {
    owner
        .ancestors()
        .find(|node| {
            matches!(node.snapshot().extension(),
                TheoryExtension::InstallClassArity { certificate }
                    if certificate.tycon == *name && certificate.result == Name::from("HOL.type")
                        && certificate.semantic.as_ref() == Some(model)
            )
        })
        .ok_or_else(|| reject(name))
}

fn matches_fixed_scheme(actual: &ConstScheme, expected: &ConstScheme) -> bool {
    if actual == expected {
        return true;
    }
    match (actual, expected) {
        (ConstScheme::Monomorphic(ty), ConstScheme::Polymorphic(scheme))
        | (ConstScheme::Polymorphic(scheme), ConstScheme::Monomorphic(ty)) => {
            scheme.params().is_empty() && scheme.body() == ty
        },
        _ => false,
    }
}

fn matches_declaration_event(event: &TheoryExtension, name: &Name, expected: &ConstScheme) -> bool {
    match (event, expected) {
        (TheoryExtension::DeclareConst { name: declared, ty }, ConstScheme::Monomorphic(body)) => {
            declared == name && ty == body
        },
        (
            TheoryExtension::DeclareConst { name: declared, ty },
            ConstScheme::Polymorphic(scheme),
        ) => declared == name && scheme.params().is_empty() && scheme.body() == ty,
        (
            TheoryExtension::DeclareConstScheme { name: declared, scheme },
            ConstScheme::Monomorphic(body),
        ) => declared == name && scheme.params().is_empty() && scheme.body() == body,
        (
            TheoryExtension::DeclareConstScheme { name: declared, scheme },
            ConstScheme::Polymorphic(expected_scheme),
        ) => declared == name && scheme == expected_scheme,
        _ => false,
    }
}

fn require_primitive<'a>(
    owner: &'a TrustedTheory,
    declaration: &BasisDeclaration,
) -> Result<&'a TrustedTheory, KernelError> {
    let name = declaration_name(declaration);
    if name.as_str() == "fun" {
        if owner.signature().type_constructor_arity(name) != Some(2) {
            return Err(reject(name));
        }
        return require_arity(owner, name, &SemanticArityCert::FunctionTypeArityCert);
    }
    if let BasisDeclaration::TypeConstructor { arity, .. } = declaration {
        let intro = owner
            .ancestors()
            .find(|node| {
                matches!(node.snapshot().extension(),
                    TheoryExtension::DeclareFreshNonemptyTycon { name: declared, arity: actual }
                        if declared == name && actual == arity
                )
            })
            .ok_or_else(|| reject(name))?;
        let proof = require_arity(
            owner,
            name,
            &SemanticArityCert::FreshNonemptyTyconCert { tycon: name.clone(), arity: *arity },
        )?;
        require_precedes(intro, proof, name)?;
        return Ok(proof);
    }
    let expected = match declaration {
        BasisDeclaration::Judgment { ty, .. } => ConstScheme::Monomorphic(ty.clone()),
        BasisDeclaration::Constant { scheme, .. } => ConstScheme::Polymorphic(scheme.clone()),
        BasisDeclaration::TypeConstructor { .. } => unreachable!("handled above"),
    };
    if !owner
        .signature()
        .get_const(name)
        .is_some_and(|actual| matches_fixed_scheme(actual, &expected))
        || owner.ancestors().any(|node| {
            matches!(node.snapshot().extension(),
            TheoryExtension::DefineConst { certificate } if &certificate.name == name)
        })
    {
        return Err(reject(name));
    }
    owner
        .ancestors()
        .find(|node| matches_declaration_event(node.snapshot().extension(), name, &expected))
        .ok_or_else(|| reject(name))
}

fn require_precedes(
    earlier: &TrustedTheory,
    later: &TrustedTheory,
    name: &Name,
) -> Result<(), KernelError> {
    if earlier.id() != later.id() && earlier.snapshot().is_ancestor_of(later.snapshot()) {
        Ok(())
    } else {
        Err(reject(name))
    }
}

fn check_definition(
    owner: &TrustedTheory,
    name: &Name,
    expected: &R,
    manifest: &[BasisDeclaration],
) -> Result<(), KernelError> {
    let (node, certificate) = owner
        .ancestors()
        .find_map(|node| match node.snapshot().extension() {
            TheoryExtension::DefineConst { certificate } if &certificate.name == name => {
                Some((node, certificate))
            },
            _ => None,
        })
        .ok_or_else(|| reject(name))?;
    let context = ProofContext::new(owner.snapshot().clone());
    let certified_expected = context.certify_term(expected.clone()).map_err(|_| reject(name))?;
    let certified_actual =
        context.certify_term(certificate.rhs_raw.clone()).map_err(|_| reject(name))?;
    if !certified_actual.term().alpha_eq(certified_expected.term()) {
        return Err(reject(name));
    }
    let source_owner = owner.find_owner(certificate.parent).ok_or_else(|| reject(name))?;
    require_precedes(source_owner, node, name)?;
    let mut dependencies = BTreeSet::new();
    expected.referenced_consts(&mut dependencies);
    for dependency in dependencies {
        let prerequisite = manifest
            .iter()
            .find(|entry| declaration_name(entry) == &dependency)
            .map(|entry| require_primitive(source_owner, entry).map(|_| ()))
            .unwrap_or_else(|| {
                let has_definition = source_owner.ancestors().any(|ancestor| {
                    matches!(
                    ancestor.snapshot().extension(), TheoryExtension::DefineConst { certificate }
                        if certificate.name == dependency)
                });
                if has_definition { Ok(()) } else { Err(reject(&dependency)) }
            });
        prerequisite?;
    }
    Ok(())
}

fn check_declaration_order(
    owner: &TrustedTheory,
    required: &BTreeSet<Name>,
    manifest: &[BasisDeclaration],
) -> Result<(), KernelError> {
    // Each source segment has an exact local order; Nat and Set are separate
    // import branches and need not be linearly ordered against one another.
    const SEGMENTS: &[&[&str]] = &[
        &["fun", "bool", "HOL.Trueprop", "HOL.implies", "HOL.eq", "HOL.The", "Hilbert_Choice.Eps"],
        &["bool", "Nat.ind", "Nat.Zero_Rep", "Nat.Suc_Rep"],
        &["bool", "Set.set", "Set.Collect", "Set.member"],
    ];
    for segment in SEGMENTS {
        let mut preceding: Option<&TrustedTheory> = None;
        for name in *segment {
            if !required.contains(&Name::from(*name)) {
                continue;
            }
            let declaration = manifest
                .iter()
                .find(|entry| declaration_name(entry).as_str() == *name)
                .ok_or_else(|| reject(&Name::from(*name)))?;
            let intro = require_primitive(owner, declaration)?;
            if let Some(before) = preceding {
                require_precedes(before, intro, declaration_name(declaration))?;
            }
            preceding = Some(intro);
        }
    }
    Ok(())
}

pub(super) fn check_hol_basis_origin(
    owner: &TrustedTheory,
    basis: &LogicBasis,
) -> Result<(), KernelError> {
    if basis.policy() != LogicPolicyId::HOLBasisV1 {
        return Ok(());
    }
    let (manifest, _) = LogicBasis::hol_v1_manifest()?;
    let mut pending = BTreeSet::from([Name::from("fun"), Name::from("bool")]);
    for declaration in basis.declarations() {
        pending.insert(declaration_name(declaration).clone());
    }
    for axiom in basis.axioms() {
        axiom.prop.referenced_consts(&mut pending);
        if axiom.name.as_str().starts_with("Nat.") {
            pending.insert("Nat.ind".into());
        }
        if axiom.name.as_str().starts_with("Set.") {
            pending.insert("Set.set".into());
        }
    }
    let mut required = BTreeSet::new();
    let mut definitions = BTreeMap::new();
    while let Some(name) = pending.pop_first() {
        if !required.insert(name.clone()) {
            continue;
        }
        if let Some(expected) = expected_definition(&name)? {
            expected.referenced_consts(&mut pending);
            definitions.insert(name, expected);
        } else if !manifest.iter().any(|entry| declaration_name(entry) == &name) {
            return Err(reject(&name));
        }
    }
    check_declaration_order(owner, &required, &manifest)?;
    for (name, expected) in &definitions {
        check_definition(owner, name, expected, &manifest)?;
    }
    Ok(())
}
