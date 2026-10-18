//! Private sort export planning. No caller-supplied type map or class slot is trusted.
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use crate::{
    DependencySet, KernelError, KernelThm, Name, ProofContext, Sort, Term, TrustedTheory, Ty,
};

use super::{
    BoundProof, BoundProofError, Node, Proof, Sources, check, inspect::ProofVariables, lower,
    terms, transform,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ExportSlot {
    pub(super) original: Ty,
    pub(super) sort: Sort,
    pub(super) private: Ty,
}

pub(super) struct ExportPlan {
    pub(super) slots: Vec<ExportSlot>,
    pub(super) premises: Vec<(Ty, Name)>,
    pub(super) replacements: BTreeMap<Ty, Ty>,
    pub(super) binder_terms: Vec<Term>,
}

impl ExportPlan {
    pub(super) fn from_source(
        owner: &TrustedTheory,
        source: &KernelThm,
        proof: &Proof,
    ) -> Result<Self, KernelError> {
        if !source.hyps().is_empty()
            || !source.payload().flex_pairs().is_empty()
            || !source.payload().sort_obligations().is_empty()
            || !source.payload().pending().is_empty()
        {
            return Err(BoundProofError::UnsupportedSortExportVariant {
                operation: "open sort export source",
            }
            .into());
        }
        let mut present = BTreeSet::new();
        terms::collect_type_atoms(source.prop().term(), &mut present);
        if present.iter().any(|atom| !atom.is_tvar()) {
            return Err(BoundProofError::UnsupportedSortExportVariant {
                operation: "fixed type in export proposition",
            }
            .into());
        }
        let mut present: Vec<_> = present.into_iter().collect();
        present.sort_by(Ty::cmp_term_ord);
        let present_sorts: BTreeSet<_> =
            present.iter().filter_map(Ty::atomic_sort).cloned().collect();
        let extras = source.payload().shyps().difference(&present_sorts);
        let original =
            present.into_iter().chain(extras.map(|sort| Ty::tvar("__sort_extra", 0, sort.clone())));
        let mut used_names = ProofVariables::collect(proof).atoms;
        let mut slots = Vec::new();
        for (index, atom) in original.enumerate() {
            let sort = atom.atomic_sort().ok_or(KernelError::UnknownClassEvidence)?.clone();
            let name = choose_private_name(index, &used_names)?;
            let private = Ty::tvar(name, 0, Sort::empty());
            used_names.insert(private.clone());
            slots.push(ExportSlot { original: atom, sort, private });
        }
        let mut replacements = BTreeMap::new();
        for slot in &slots {
            replacements.insert(slot.original.clone(), slot.private.clone());
        }
        for atom in ProofVariables::collect(proof).atoms {
            if replacements.contains_key(&atom) {
                continue;
            }
            let sort = atom.atomic_sort().ok_or(KernelError::UnknownClassEvidence)?;
            let target = slots.iter().find(|slot| &slot.sort == sort).ok_or(
                BoundProofError::UnsupportedSortExportVariant {
                    operation: "proof-only atom has no exact source sort",
                },
            )?;
            replacements.insert(atom, target.private.clone());
        }
        let mut premises = Vec::new();
        let mut binder_terms = Vec::new();
        for slot in &slots {
            for class in slot.sort.classes() {
                premises.push((slot.private.clone(), class.clone()));
                binder_terms.push(super::of_class_term(owner, &slot.private, class)?);
            }
        }
        Ok(Self { slots, premises, replacements, binder_terms })
    }
    pub(super) fn recover_sorted_type(&self, erased: &Ty) -> Result<Ty, KernelError> {
        let inverse =
            self.slots.iter().map(|slot| (slot.private.clone(), slot.original.clone())).collect();
        erased.rewrite_atomic_types(&inverse)
    }

    pub(super) fn certify_constant(
        &self,
        owner: &TrustedTheory,
        name: &Name,
        erased: &Ty,
    ) -> Result<crate::class_proof::ScopedOfClassEvidence, KernelError> {
        let sorted = self.recover_sorted_type(erased)?;
        crate::class_proof::certify_sort_erased_const(
            owner,
            name,
            &sorted,
            erased,
            &self.replacements,
            &self.premises,
        )
    }

    pub(super) fn collect_leaf_slots(
        &self,
        owner: &TrustedTheory,
        source: &KernelThm,
        types: &BTreeMap<Ty, Ty>,
    ) -> Result<BTreeSet<usize>, KernelError> {
        let mut slots = BTreeSet::new();
        for (original, erased) in types {
            let sort = original.atomic_sort().ok_or(KernelError::UnknownClassEvidence)?;
            for class in sort.classes() {
                let proof = crate::class_proof::derive_scoped_of_class(
                    owner,
                    erased,
                    class,
                    &self.premises,
                )?;
                slots.extend(proof.slots());
            }
        }
        if matches!(source.payload().mode(), crate::obligations::ProofMode::SortErased) {
            // Its own closed export replay already certifies its constant
            // occurrences under its inner, retained implication premises.
            return Ok(slots);
        }
        source.prop().term().visit_const_occurrences(&mut |name, original| {
            let erased = original.rewrite_atomic_types(types)?;
            let proof = crate::class_proof::certify_sort_erased_const(
                owner,
                name,
                original,
                &erased,
                types,
                &self.premises,
            )?;
            slots.extend(proof.slots());
            Ok(())
        })?;
        Ok(slots)
    }
}
pub(crate) fn replay_export(
    owner: &TrustedTheory,
    context: &ProofContext,
    source: &KernelThm,
    recorded: Option<&BoundProof>,
) -> Result<(KernelThm, DependencySet), KernelError> {
    let sources = Sources::collect(source);
    let root = lower::lower_theorem(source, &sources)?;
    let plan = ExportPlan::from_source(owner, source, &root)?;
    let mut scoped = transform::map_export_proof(&root, owner, &sources, &plan)?;
    for assumption in plan.binder_terms.iter().rev() {
        scoped = Arc::new(Node::ImpliesIntro { assumption: assumption.clone(), body: scoped });
    }
    let proof = BoundProof { root: scoped };
    if recorded.is_some_and(|candidate| candidate != &proof) {
        return Err(BoundProofError::StatementMismatch.into());
    }
    let body = terms::rewrite_term(source.prop().term(), 0, &mut |_, _| Ok(None), &mut |ty| {
        terms::replace_type_atoms(ty, &plan.replacements)
    })?;
    let (checked, dependencies, _) =
        check::check_export(context, owner, &sources, &proof.root, &plan, source, &body)?;
    let expected = Term::mk_imp_chain(&plan.binder_terms, &body)?;
    if !checked.alpha_eq(&expected) {
        return Err(BoundProofError::StatementMismatch.into());
    }
    let public = close_private_types(&checked, &plan)?;
    let proposition = crate::thm::prop_from_term(public, source.context());
    let payload =
        crate::obligations::ProofPayload::from_sort_export(&proposition, source.payload())?;
    Ok((
        KernelThm::new_with_payload(
            Vec::new(),
            proposition,
            payload,
            crate::Derivation::UnconstrainT { premise: Box::new(source.clone()), proof },
        ),
        dependencies,
    ))
}

fn close_private_types(checked: &Term, plan: &ExportPlan) -> Result<Term, KernelError> {
    let replacements = plan
        .slots
        .iter()
        .enumerate()
        .map(|(index, slot)| {
            let public = Ty::tvar(format!("a{index}"), 0, Sort::empty());
            (slot.private.clone(), public)
        })
        .collect();
    terms::rewrite_term(checked, 0, &mut |_, _| Ok(None), &mut |ty| {
        terms::replace_type_atoms(ty, &replacements)
    })
}

fn choose_private_name(index: usize, used: &BTreeSet<Ty>) -> Result<Name, KernelError> {
    let mut suffix = index;
    loop {
        let candidate = Name::from(format!("__sort_scope_{suffix}"));
        let is_used = used.iter().any(|atom| atom.atomic_name() == Some(&candidate));
        if !is_used {
            return Ok(candidate);
        }
        suffix = suffix.checked_add(1).ok_or(BoundProofError::IndexOverflow)?;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        EmptyClassDeclCert, KernelRules, OfClassCandidate, PolyType, PolyTypeParam, RawTerm,
        SemanticArityCert, Signature, TypeVarId, accept_closed_theorem, prove_of_class,
    };

    fn build_export() -> (TrustedTheory, ProofContext, KernelThm) {
        let signature =
            Signature::new().install_empty_class(EmptyClassDeclCert::hol_type()).unwrap();
        let owner = TrustedTheory::root("ExportView", signature);
        let context = ProofContext::new(owner.snapshot().clone());
        let atom = Ty::tvar("a", 0, Sort::hol_type());
        let proof = prove_of_class(
            &owner,
            atom,
            Name::from("HOL.type"),
            OfClassCandidate::AnnotatedAtomLeaf,
        )
        .unwrap();
        let source = KernelRules::of_class(&owner, &proof).unwrap();
        let exported = KernelRules::unconstrain_t(&owner, &context, source.as_kernel()).unwrap();
        (owner, context, exported)
    }

    fn duplicate_first_slot(proof: &Proof) -> Proof {
        match proof.as_ref() {
            Node::ImpliesIntro { assumption, body } => Arc::new(Node::ImpliesIntro {
                assumption: assumption.clone(),
                body: duplicate_first_slot(body),
            }),
            Node::ImpliesElim(left, right) => {
                Arc::new(Node::ImpliesElim(duplicate_first_slot(left), right.clone()))
            },
            Node::ExportHead(view) => {
                let mut changed = view.clone();
                changed.slots.push(0);
                Arc::new(Node::ExportHead(changed))
            },
            _ => panic!("class-proof fixture must contain an exported source leaf"),
        }
    }

    fn misbind_first_premise(proof: &Proof) -> Proof {
        match proof.as_ref() {
            Node::ImpliesIntro { assumption, body } => Arc::new(Node::ImpliesIntro {
                assumption: assumption.clone(),
                body: misbind_first_premise(body),
            }),
            Node::ImpliesElim(left, right) if matches!(right.as_ref(), Node::Hyp(_)) => {
                Arc::new(Node::ImpliesElim(left.clone(), Arc::new(Node::Hyp(1))))
            },
            _ => panic!("class-proof fixture must consume an OFCLASS premise"),
        }
    }

    #[test]
    fn export_head_duplicate_ofclass_slot_rejects_checked_proof() {
        let (owner, context, exported) = build_export();
        let crate::Derivation::UnconstrainT { premise, proof } = exported.derivation() else {
            panic!("expected export derivation");
        };
        let sources = Sources::collect(premise);
        let source_proof = lower::lower_theorem(premise, &sources).unwrap();
        let plan = ExportPlan::from_source(&owner, premise, &source_proof).unwrap();
        let altered = duplicate_first_slot(&proof.root);
        assert!(matches!(
            check::check_export(
                &context,
                &owner,
                &sources,
                &altered,
                &plan,
                premise,
                premise.prop().term()
            ),
            Err(KernelError::BoundProof(BoundProofError::InvalidLeafInstance { .. })),
        ));
    }

    #[test]
    fn export_head_foreign_gamma_slot_rejects_checked_proof() {
        let (owner, context, exported) = build_export();
        let crate::Derivation::UnconstrainT { premise, proof } = exported.derivation() else {
            panic!("expected export derivation");
        };
        let sources = Sources::collect(premise);
        let source_proof = lower::lower_theorem(premise, &sources).unwrap();
        let plan = ExportPlan::from_source(&owner, premise, &source_proof).unwrap();
        assert!(matches!(
            check::check_export(
                &context,
                &owner,
                &sources,
                &misbind_first_premise(&proof.root),
                &plan,
                premise,
                premise.prop().term(),
            ),
            Err(KernelError::BoundProof(BoundProofError::UnboundHypothesis { .. })),
        ));
    }

    #[test]
    fn export_head_tampered_occurrence_rejects_acceptance_replay() {
        let (owner, _, exported) = build_export();
        let crate::Derivation::UnconstrainT { premise, proof } = exported.derivation() else {
            panic!("expected export derivation");
        };
        let altered = KernelThm::new_with_payload(
            exported.hyps().to_vec(),
            exported.prop().clone(),
            exported.payload().clone(),
            crate::Derivation::UnconstrainT {
                premise: premise.clone(),
                proof: BoundProof { root: duplicate_first_slot(&proof.root) },
            },
        );
        assert!(matches!(
            accept_closed_theorem(&owner, "tampered_export", altered.try_close().unwrap()),
            Err(KernelError::BoundProof(BoundProofError::StatementMismatch)),
        ));
    }
    #[test]
    fn export_reflexive_constant_without_class_coverage_rejects() {
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
        let owner = TrustedTheory::root("ConstCoverage", signature);
        let context = ProofContext::new(owner.snapshot().clone());
        let source =
            KernelRules::reflexive(context.certify_term(RawTerm::const_("F", ty)).unwrap());
        let exported = KernelRules::unconstrain_t(&owner, &context, source.as_kernel()).unwrap();
        let crate::Derivation::UnconstrainT { premise, proof } = exported.derivation() else {
            panic!("expected export derivation");
        };
        let sources = Sources::collect(premise);
        let source_proof = lower::lower_theorem(premise, &sources).unwrap();
        let mut plan = ExportPlan::from_source(&owner, premise, &source_proof).unwrap();
        plan.premises.clear();
        assert!(matches!(
            check::check_export(
                &context,
                &owner,
                &sources,
                &proof.root,
                &plan,
                premise,
                premise.prop().term()
            ),
            Err(KernelError::UnknownClassEvidence),
        ));
    }

    #[test]
    fn strip_after_permutation_rejects_forged_inner_export_source() {
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
        let owner = TrustedTheory::root("ForgedStripSource", signature);
        let context = ProofContext::new(owner.snapshot().clone());
        let source =
            KernelRules::reflexive(context.certify_term(RawTerm::const_("F", ty)).unwrap());
        let assumption = source.as_kernel().prop().clone();
        let implication = KernelRules::implies_intr(&assumption, source.as_kernel()).unwrap();
        let exported = KernelRules::unconstrain_t(&owner, &context, &implication).unwrap();
        let permuted = KernelRules::permute_prems(&owner, &context, &exported, 0, 1).unwrap();
        let stripped = KernelRules::strip_shyps(&owner, &context, &permuted).unwrap();
        let crate::Derivation::UnconstrainT { premise, .. } = exported.derivation() else {
            panic!("expected export derivation");
        };
        let forged_export = KernelThm::new_with_payload(
            exported.hyps().to_vec(),
            exported.prop().clone(),
            exported.payload().clone(),
            crate::Derivation::UnconstrainT {
                premise: premise.clone(),
                proof: BoundProof { root: Arc::new(Node::Hyp(0)) },
            },
        );
        let crate::Derivation::PermutePrems { fixed, rotation, proof, .. } = permuted.derivation()
        else {
            panic!("expected permutation derivation");
        };
        let forged_permutation = KernelThm::new_with_payload(
            permuted.hyps().to_vec(),
            permuted.prop().clone(),
            permuted.payload().clone(),
            crate::Derivation::PermutePrems {
                premise: Box::new(forged_export),
                fixed: *fixed,
                rotation: *rotation,
                proof: proof.clone(),
            },
        );
        let crate::Derivation::StripShyps { proof, .. } = stripped.derivation() else {
            panic!("expected strip derivation");
        };
        let forged_strip = KernelThm::new_with_payload(
            stripped.hyps().to_vec(),
            stripped.prop().clone(),
            stripped.payload().clone(),
            crate::Derivation::StripShyps {
                premise: Box::new(forged_permutation),
                proof: proof.clone(),
            },
        );
        assert!(
            accept_closed_theorem(&owner, "forged_source", forged_strip.try_close().unwrap(),)
                .is_err()
        );
    }

    #[test]
    fn recorded_bound_operand_keeps_concrete_arity_dependency() {
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
        let declared = TrustedTheory::root("BoundOperand", signature)
            .declare_fresh_nonempty_tycon("W", 0)
            .unwrap();
        let owner = declared
            .install_semantic_arity(SemanticArityCert::FreshNonemptyTyconCert {
                tycon: "W".into(),
                arity: 0,
            })
            .unwrap();
        let context = ProofContext::new(owner.snapshot().clone());
        let witness = Ty::base("W").unwrap();
        let concrete_ty = Ty::arrow(witness.clone(), witness);
        let p = context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap();
        let source = KernelRules::reflexive(p.clone());
        let stripped = KernelRules::strip_shyps(&owner, &context, source.as_kernel()).unwrap();
        let argument = context.certify_term(RawTerm::const_("F", concrete_ty.clone())).unwrap();
        let root = Arc::new(Node::ForallElim {
            premise: Arc::new(Node::ForallIntro {
                name: "x".into(),
                ty: concrete_ty,
                body: Arc::new(Node::Reflexive(p.term().clone())),
            }),
            argument: argument.term().clone(),
        });
        let altered = KernelThm::new_with_payload(
            stripped.hyps().to_vec(),
            stripped.prop().clone(),
            stripped.payload().clone(),
            crate::Derivation::StripShyps {
                premise: Box::new(source.into_kernel()),
                proof: BoundProof { root },
            },
        );
        let (_, accepted) =
            accept_closed_theorem(&owner, "bound_operand_arity", altered.try_close().unwrap())
                .unwrap();
        assert_eq!(accepted.dependencies().len(), 1);
    }

    #[test]
    fn transported_leaf_does_not_authorize_sibling_reflexive_operand() {
        let alpha = Ty::tvar("a", 0, Sort::hol_type());
        let function_ty = Ty::arrow(alpha.clone(), alpha);
        let scheme = PolyType::new(
            vec![PolyTypeParam { id: TypeVarId::new("a", 0, Sort::hol_type()) }],
            function_ty.clone(),
        )
        .unwrap();
        let signature = Signature::new()
            .install_empty_class(EmptyClassDeclCert::hol_type())
            .unwrap()
            .extend_const_scheme("F", scheme)
            .unwrap();
        let owner = TrustedTheory::root("ScopedTransport", signature);
        let context = ProofContext::new(owner.snapshot().clone());
        let source = KernelRules::reflexive(
            context.certify_term(RawTerm::const_("F", function_ty)).unwrap(),
        );
        let exported = KernelRules::unconstrain_t(&owner, &context, source.as_kernel()).unwrap();
        let stripped = KernelRules::strip_shyps(&owner, &context, &exported).unwrap();
        let (_, erased_equality) = exported.prop().term().dest_imp().unwrap();
        let (_, erased_constant, _) = erased_equality.dest_eq().unwrap();
        let root = Arc::new(Node::ImpliesElim(
            Arc::new(Node::ImpliesIntro {
                assumption: erased_equality.clone(),
                body: Arc::new(Node::ClosedExportTransport(
                    lower::make_leaf_instance(0, &exported).unwrap(),
                )),
            }),
            Arc::new(Node::Reflexive(erased_constant.clone())),
        ));
        let altered = KernelThm::new_with_payload(
            stripped.hyps().to_vec(),
            stripped.prop().clone(),
            stripped.payload().clone(),
            crate::Derivation::StripShyps {
                premise: Box::new(exported),
                proof: BoundProof { root },
            },
        );
        assert!(matches!(
            accept_closed_theorem(&owner, "sibling_leak", altered.try_close().unwrap()),
            Err(KernelError::TypeSortMismatch { .. }),
        ));
    }

    #[test]
    fn recorded_strip_rejects_erased_binder_without_source_adapter() {
        let sorted = Ty::tvar("a", 0, Sort::hol_type());
        let function_ty = Ty::arrow(sorted.clone(), sorted);
        let scheme = PolyType::new(
            vec![PolyTypeParam { id: TypeVarId::new("a", 0, Sort::hol_type()) }],
            function_ty.clone(),
        )
        .unwrap();
        let signature = Signature::new()
            .install_empty_class(EmptyClassDeclCert::hol_type())
            .unwrap()
            .extend_const_scheme("F", scheme)
            .unwrap();
        let owner = TrustedTheory::root("ErasedBinderForgery", signature);
        let context = ProofContext::new(owner.snapshot().clone());
        let reflexive = KernelRules::reflexive(
            context.certify_term(RawTerm::const_("F", function_ty)).unwrap(),
        );
        let assertion = reflexive.as_kernel().prop().clone();
        let source = KernelRules::implies_intr(&assertion, reflexive.as_kernel()).unwrap();
        let exported = KernelRules::unconstrain_t(&owner, &context, &source).unwrap();
        let stripped = KernelRules::strip_shyps(&owner, &context, &exported).unwrap();
        let (class_premise, tail) = exported.prop().term().dest_imp().unwrap();
        let (erased_assertion, _) = tail.dest_imp().unwrap();
        let forged_root = Arc::new(Node::ImpliesIntro {
            assumption: class_premise.clone(),
            body: Arc::new(Node::ImpliesIntro {
                assumption: erased_assertion.clone(),
                body: Arc::new(Node::Hyp(0)),
            }),
        });
        let forged = KernelThm::new_with_payload(
            stripped.hyps().to_vec(),
            stripped.prop().clone(),
            stripped.payload().clone(),
            crate::Derivation::StripShyps {
                premise: Box::new(exported),
                proof: BoundProof { root: forged_root },
            },
        );
        assert!(
            accept_closed_theorem(&owner, "erased_binder_forgery", forged.try_close().unwrap())
                .is_err()
        );
    }
}
