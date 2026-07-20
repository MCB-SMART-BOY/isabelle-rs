//! Data-only HOL logic basis manifest.
//!
//! This module declares the Isabelle/HOL logical basis as an immutable
//! `LogicBasis` value. It contains zero executable code, no theorem
//! constructors, and no Rust functions that return theorems.
//!
//! The manifest transcribes the declarations from `HOL.thy`:
//! - Type constructors: `bool` (arity 0), `fun` (arity 2)
//! - Judgment: `HOL.Trueprop :: bool => prop`
//! - Constants: `HOL.eq :: 'a => 'a => bool`
//! - Axioms: `refl`, `subst`
//!
//! ## Trust status
//!
//! This data is trusted bootstrap input. It is NOT machine-checked against
//! the Isabelle/HOL source file. The kernel validates it structurally against
//! a `Signature`; the correctness of the transcription itself is a
//! trusted-base assumption.

use crate::kernel::{
    BasisDeclaration, LogicBasis, Name, RawTerm, Sort, Ty,
    logic::{AxiomSchema, PolyType, PolyTypeParam, TypeVarId},
};

/// The Isabelle/HOL logic basis.
///
/// Use `HOL_BASIS.validate_against(&signature)` to check compatibility
/// before installing the basis into a `TrustedTheory`.
pub fn hol_basis() -> LogicBasis {
    LogicBasis::try_new(
        vec![
            // ── Type constructors ──────────────────────────────────────
            BasisDeclaration::TypeConstructor { name: Name::from("bool"), arity: 0 },
            BasisDeclaration::TypeConstructor { name: Name::from("fun"), arity: 2 },
            // ── Judgment ──────────────────────────────────────────────
            BasisDeclaration::Judgment {
                const_name: Name::from("HOL.Trueprop"),
                ty: Ty::arrow(Ty::base("bool").expect("bool type"), Ty::prop()),
            },
            // ── Polymorphic constants ──────────────────────────────────
            BasisDeclaration::Constant {
                name: Name::from("HOL.eq"),
                scheme: PolyType::new(
                    vec![PolyTypeParam { id: TypeVarId::new("'a", 0), sort: Sort::typ() }],
                    Ty::arrow(
                        Ty::tvar("'a", 0, crate::kernel::Sort::typ()),
                        Ty::arrow(
                            Ty::tvar("'a", 0, crate::kernel::Sort::typ()),
                            Ty::base("bool").expect("bool type"),
                        ),
                    ),
                )
                .expect("HOL.eq PolyType"),
            },
        ],
        vec![
            // ── Axiom schemas ──────────────────────────────────────────
            AxiomSchema {
                name: Name::from("HOL.refl"),
                // ∀t. Trueprop (t = t)
                prop: RawTerm::Forall {
                    name: Name::from("t"),
                    param_ty: Ty::tvar("'a", 0, crate::kernel::Sort::typ()),
                    body: Box::new(RawTerm::app(
                        RawTerm::const_(
                            Name::from("HOL.Trueprop"),
                            Ty::arrow(Ty::base("bool").expect("bool"), Ty::prop()),
                        ),
                        RawTerm::app(
                            RawTerm::app(
                                RawTerm::const_(
                                    Name::from("HOL.eq"),
                                    Ty::arrow(
                                        Ty::tvar("'a", 0, crate::kernel::Sort::typ()),
                                        Ty::arrow(
                                            Ty::tvar("'a", 0, crate::kernel::Sort::typ()),
                                            Ty::base("bool").expect("bool"),
                                        ),
                                    ),
                                ),
                                RawTerm::Bound(0),
                            ),
                            RawTerm::Bound(0),
                        ),
                    )),
                },
            },
            AxiomSchema {
                name: Name::from("HOL.subst"),
                // ∀s t. (s = t) ⟶ P s ⟶ P t
                prop: RawTerm::Forall {
                    name: Name::from("s"),
                    param_ty: Ty::tvar("'a", 0, crate::kernel::Sort::typ()),
                    body: Box::new(RawTerm::Forall {
                        name: Name::from("t"),
                        param_ty: Ty::tvar("'a", 0, crate::kernel::Sort::typ()),
                        body: Box::new(RawTerm::Imp {
                            premise: Box::new(RawTerm::app(
                                RawTerm::const_(
                                    Name::from("HOL.Trueprop"),
                                    Ty::arrow(Ty::base("bool").expect("bool"), Ty::prop()),
                                ),
                                RawTerm::app(
                                    RawTerm::app(
                                        RawTerm::const_(
                                            Name::from("HOL.eq"),
                                            Ty::arrow(
                                                Ty::tvar("'a", 0, crate::kernel::Sort::typ()),
                                                Ty::arrow(
                                                    Ty::tvar("'a", 0, crate::kernel::Sort::typ()),
                                                    Ty::base("bool").expect("bool"),
                                                ),
                                            ),
                                        ),
                                        RawTerm::var(
                                            Name::from("s"),
                                            0,
                                            Ty::tvar("'a", 0, crate::kernel::Sort::typ()),
                                        ),
                                    ),
                                    RawTerm::var(
                                        Name::from("t"),
                                        1,
                                        Ty::tvar("'a", 0, crate::kernel::Sort::typ()),
                                    ),
                                ),
                            )),
                            conclusion: Box::new(RawTerm::Imp {
                                premise: Box::new(RawTerm::app(
                                    RawTerm::const_(
                                        Name::from("HOL.Trueprop"),
                                        Ty::arrow(Ty::base("bool").expect("bool"), Ty::prop()),
                                    ),
                                    RawTerm::app(
                                        RawTerm::var(
                                            Name::from("P"),
                                            0,
                                            Ty::arrow(
                                                Ty::tvar("'a", 0, crate::kernel::Sort::typ()),
                                                Ty::base("bool").expect("bool"),
                                            ),
                                        ),
                                        RawTerm::var(
                                            Name::from("s"),
                                            2,
                                            Ty::tvar("'a", 0, crate::kernel::Sort::typ()),
                                        ),
                                    ),
                                )),
                                conclusion: Box::new(RawTerm::app(
                                    RawTerm::const_(
                                        Name::from("HOL.Trueprop"),
                                        Ty::arrow(Ty::base("bool").expect("bool"), Ty::prop()),
                                    ),
                                    RawTerm::app(
                                        RawTerm::var(
                                            Name::from("P"),
                                            0,
                                            Ty::arrow(
                                                Ty::tvar("'a", 0, crate::kernel::Sort::typ()),
                                                Ty::base("bool").expect("bool"),
                                            ),
                                        ),
                                        RawTerm::var(
                                            Name::from("t"),
                                            2,
                                            Ty::tvar("'a", 0, crate::kernel::Sort::typ()),
                                        ),
                                    ),
                                )),
                            }),
                        }),
                    }),
                },
            },
        ],
    ).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Signature;

    #[test]
    fn hol_basis_validates_against_correct_signature() {
        let mut sig = Signature::new();
        sig = sig
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()))
            .unwrap();
        sig = sig
            .extend_const(
                "HOL.eq",
                Ty::arrow(
                    Ty::tvar("alpha", 0, crate::kernel::Sort::typ()),
                    Ty::arrow(Ty::tvar("alpha", 0, crate::kernel::Sort::typ()), Ty::base("bool").unwrap()),
                ),
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
    fn hol_basis_contains_refl_and_subst() {
        let basis = hol_basis();
        let names: Vec<&str> = basis.axioms().iter().map(|a| a.name.as_str()).collect();
        assert!(names.contains(&"HOL.refl"));
        assert!(names.contains(&"HOL.subst"));
    }
}
