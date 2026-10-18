use std::collections::{BTreeMap, BTreeSet};

use crate::{
    CTerm, DependencySet, KernelError, KernelThm, ProofContext, Sort, Term, TrustedTheory, Ty,
};

use super::{
    BinaryRule, BoundProofError, LeafInstance, Node, Proof, Sources, TermKey, export::ExportPlan,
    terms,
};

/// Transport is considered only for exact subterms of these replayed sources.
pub(super) struct CheckTransport<'a> {
    pub source: &'a Term,
    pub target: &'a Term,
    pub is_canonical_adapter: bool,
    pub flex_pairs: &'a [(CTerm, CTerm)],
}

pub(super) struct ScopedInspection<'a> {
    pub bounds: &'a [Ty],
    pub hypotheses: &'a [(Term, usize)],
    pub source: &'a Term,
    pub target: &'a Term,
    pub flex_pairs: &'a [(CTerm, CTerm)],
}

pub(super) fn check_closed_with_source(
    context: &ProofContext,
    owner: &TrustedTheory,
    sources: &Sources<'_>,
    root: &Proof,
    transport: CheckTransport<'_>,
) -> Result<(Term, BTreeSet<Sort>, DependencySet), KernelError> {
    let pair = transport.is_canonical_adapter.then_some((transport.source, transport.target));
    let (proposition, sorts, dependencies, _) =
        check_with_mode(context, Some(owner), sources, root, None, pair, transport.flex_pairs)?;
    Ok((proposition, sorts, dependencies))
}

pub(super) fn check_export(
    context: &ProofContext,
    owner: &TrustedTheory,
    sources: &Sources<'_>,
    root: &Proof,
    plan: &ExportPlan,
    source: &KernelThm,
    target: &Term,
) -> Result<(Term, DependencySet, BTreeSet<usize>), KernelError> {
    let transport = matches!(source.payload().mode(), crate::obligations::ProofMode::SortErased)
        .then_some((source.prop().term(), target));
    let (proposition, _, dependencies, used_slots) =
        check_with_mode(context, Some(owner), sources, root, Some(plan), transport, &[])?;
    Ok((proposition, dependencies, used_slots))
}

fn check_with_mode<'a, 's>(
    context: &'a ProofContext,
    owner: Option<&'a TrustedTheory>,
    sources: &'a Sources<'s>,
    root: &Proof,
    export: Option<&'a ExportPlan>,
    transport_assumptions: Option<(&'a Term, &'a Term)>,
    flex_pairs: &'a [(CTerm, CTerm)],
) -> Result<(Term, BTreeSet<Sort>, DependencySet, BTreeSet<usize>), KernelError> {
    // All checker entrypoints consume the exact Sources::collect tree from a
    // source already replayed by their owner-checked operation boundary.
    // Replaying each transported leaf here would revisit its entire ancestry.
    let mut checker = Checker {
        context,
        owner,
        sources,
        export,
        transport_assumptions,
        flex_pairs,
        hypotheses: Vec::new(),
        bounds: Vec::new(),
        sorts: BTreeSet::new(),
        dependencies: DependencySet::empty(),
        used_slots: BTreeSet::new(),
    };
    let proposition = checker.check(root)?;
    if !checker.hypotheses.is_empty() || !checker.bounds.is_empty() {
        return Err(BoundProofError::StatementMismatch.into());
    }
    Ok((proposition, checker.sorts, checker.dependencies, checker.used_slots))
}

/// Inspect an intermediate proposition in its exact private proof/term scope.
/// The caller may only use this to build explicit equality conversions; the
/// final closed proof still replays every node and validates its full payload.
pub(super) fn inspect_scoped_proposition(
    context: &ProofContext,
    owner: &TrustedTheory,
    sources: &Sources<'_>,
    proof: &Proof,
    inspection: ScopedInspection<'_>,
) -> Result<Term, KernelError> {
    let mut checker = Checker {
        context,
        owner: Some(owner),
        sources,
        export: None,
        transport_assumptions: Some((inspection.source, inspection.target)),
        flex_pairs: inspection.flex_pairs,
        hypotheses: inspection.hypotheses.to_vec(),
        bounds: inspection.bounds.to_vec(),
        sorts: BTreeSet::new(),
        dependencies: DependencySet::empty(),
        used_slots: BTreeSet::new(),
    };
    checker.check(proof)
}

struct Checker<'a, 's> {
    context: &'a ProofContext,
    owner: Option<&'a TrustedTheory>,
    sources: &'a Sources<'s>,
    // None is Ordinary; Some(plan) is the private SortScoped judgment.
    // Only replay_export turns its closed result into SortErased.
    export: Option<&'a ExportPlan>,
    // Only premise reordering over a fully replayed source may reuse an
    // exact source/target subterm while a transported leaf is checked later.
    transport_assumptions: Option<(&'a Term, &'a Term)>,
    flex_pairs: &'a [(CTerm, CTerm)],
    hypotheses: Vec<(Term, usize)>,
    bounds: Vec<Ty>,
    sorts: BTreeSet<Sort>,
    dependencies: DependencySet,
    used_slots: BTreeSet<usize>,
}

impl Checker<'_, '_> {
    /// Every newly supplied term operand is certified independently; proof
    /// results are checked separately against already validated inputs.
    fn check_term(&mut self, term: &Term) -> Result<(), KernelError> {
        let owner = self.owner.ok_or(KernelError::UnknownClassEvidence)?;
        let dependencies = &mut self.dependencies;
        let used_slots = &mut self.used_slots;
        self.context.validate_sort_erased_term(term, &mut self.bounds, &mut |name, ty| {
            let evidence = if let Some(plan) = self.export {
                if self.context.signature().certify_const_instance(name, ty).is_ok() {
                    crate::class_proof::certify_const_scheme_evidence(
                        owner,
                        name,
                        ty,
                        &plan.premises,
                    )?
                } else {
                    plan.certify_constant(owner, name, ty)?
                }
            } else {
                crate::class_proof::certify_const_scheme_evidence(owner, name, ty, &[])?
            };
            dependencies.extend(evidence.dependencies());
            used_slots.extend(evidence.slots());
            Ok(())
        })?;
        self.record_term_sorts(term);
        Ok(())
    }

    /// The term is reconstructed solely from checked proof nodes, hypotheses,
    /// and certified operands. This pass checks its structure and declarations,
    /// but never grants authority to a new operand.
    fn check_derived_term(&mut self, term: &Term) -> Result<(), KernelError> {
        self.context.validate_sort_erased_term(
            term,
            &mut self.bounds,
            &mut |name, ty| match self.context.signature().get_const(name) {
                Some(crate::ConstScheme::Monomorphic(_)) => {
                    self.context.signature().certify_const_instance(name, ty)?;
                    Ok(())
                },
                Some(crate::ConstScheme::Polymorphic(_)) => Ok(()),
                None => Err(KernelError::UndeclaredConst(name.clone())),
            },
        )?;
        self.record_term_sorts(term);
        Ok(())
    }

    fn record_term_sorts(&mut self, term: &Term) {
        term.for_each_type_annotation(&mut |ty| {
            ty.for_each_type_atom(&mut |_, _, sort| {
                self.sorts.insert(sort.clone());
            });
        });
    }

    fn check_authorized_assumption(&mut self, assumption: &Term) -> Result<(), KernelError> {
        let Some((source, target)) = self.transport_assumptions else {
            return self.check_term(assumption);
        };
        if !contains_subterm(source, assumption) && !contains_subterm(target, assumption) {
            return self.check_term(assumption);
        }
        let owner = self.owner;
        let export = self.export;
        let dependencies = &mut self.dependencies;
        let used_slots = &mut self.used_slots;
        self.context.validate_sort_erased_term(assumption, &mut self.bounds, &mut |name, ty| {
            let certified = self.context.signature().certify_const_instance(name, ty);
            if certified.is_ok() {
                if let (Some(owner), Some(plan)) = (owner, export) {
                    let evidence = crate::class_proof::certify_const_scheme_evidence(
                        owner,
                        name,
                        ty,
                        &plan.premises,
                    )?;
                    dependencies.extend(evidence.dependencies());
                    used_slots.extend(evidence.slots());
                }
                return Ok(());
            }
            let mut is_source_occurrence = false;
            source.visit_const_occurrences(&mut |source_name, source_ty| {
                let transported_ty = match export {
                    Some(plan) => source_ty.rewrite_atomic_types(&plan.replacements)?,
                    None => source_ty.clone(),
                };
                let is_monomorphic_change = source_ty != ty
                    && matches!(
                        self.context.signature().get_const(name),
                        Some(crate::ConstScheme::Monomorphic(_)),
                    );
                is_source_occurrence |=
                    source_name == name && transported_ty == *ty && !is_monomorphic_change;
                Ok(())
            })?;
            if is_source_occurrence && self.context.signature().get_const(name).is_some() {
                return Ok(());
            }
            certified.map(|_| ())
        })?;
        self.record_term_sorts(assumption);
        Ok(())
    }

    // An exhaustive constructor table is the proof checker, not a caller's
    // proposed conclusion. Helpers handle the independently checked rules.
    fn check(&mut self, proof: &Proof) -> Result<Term, KernelError> {
        let result = match proof.as_ref() {
            Node::Hyp(slot) => self.check_hypothesis(*slot)?,
            Node::ImpliesIntro { assumption, body } => {
                self.check_implies_intro(assumption, body)?
            },
            Node::ImpliesElim(major, minor) => {
                let major = self.check(major)?;
                let minor = self.check(minor)?;
                let (assumption, conclusion) =
                    major.dest_imp().ok_or(KernelError::NotImplication)?;
                if !assumption.alpha_eq(&minor) {
                    return Err(KernelError::AntecedentMismatch);
                }
                conclusion.clone()
            },
            Node::ForallIntro { name, ty, body } => {
                let body = self.check_term_binder(ty, body)?;
                Term::Forall { name: name.clone(), param_ty: ty.clone(), body: Box::new(body) }
            },
            Node::EqAbs { name, ty, body } => {
                let equality = self.check_term_binder(ty, body)?;
                abstract_equality(name, ty, equality)?
            },
            Node::ForallElim { premise, argument } => {
                self.check_term(argument)?;
                let proposition = self.check(premise)?;
                let (_, ty, body) = proposition.dest_forall().ok_or(KernelError::NotForall)?;
                require_type(ty, &argument.ty())?;
                Term::instantiate_bound0(body, argument)
            },
            Node::EqSym(premise) => {
                let equality = self.check(premise)?;
                let (_, left, right) = equality.dest_eq().ok_or(KernelError::NotEquality)?;
                Term::mk_eq(right.clone(), left.clone())?
            },
            Node::Binary { rule, left, right } => {
                let left = self.check(left)?;
                let right = self.check(right)?;
                check_binary(*rule, &left, &right)?
            },
            Node::Reflexive(term) => {
                self.check_term(term)?;
                Term::mk_eq(term.clone(), term.clone())?
            },
            Node::Beta(term) => {
                self.check_term(term)?;
                check_beta(term)?
            },
            Node::Eta(term) => {
                self.check_term(term)?;
                Term::mk_eq(term.clone(), crate::rules::contract_eta(term)?)?
            },
            Node::EqFlex(slot) => {
                let (left, right) =
                    self.flex_pairs.get(*slot).ok_or(BoundProofError::UnboundFlexPair {
                        slot: *slot,
                        pairs: self.flex_pairs.len(),
                    })?;
                let left = terms::lift_term(left.term(), self.bounds.len())?;
                let right = terms::lift_term(right.term(), self.bounds.len())?;
                self.check_term(&left)?;
                self.check_term(&right)?;
                Term::mk_eq(left, right)?
            },
            Node::AuthorizedLeaf(instance) => {
                if self.export.is_some() {
                    return Err(
                        BoundProofError::InvalidLeafInstance { leaf: instance.source }.into()
                    );
                }
                self.check_leaf(instance)?
            },
            Node::ClosedExportTransport(instance) => self.check_transport(instance)?,
            Node::ExportHead(view) => self.check_export_head(&view.instance, &view.slots)?,
        };
        self.check_derived_term(&result)?;
        if !result.ty().is_prop() {
            return Err(KernelError::NotProposition(result.ty()));
        }
        Ok(result)
    }

    fn check_hypothesis(&mut self, slot: usize) -> Result<Term, KernelError> {
        let position = self
            .hypotheses
            .len()
            .checked_sub(terms::next_depth(slot)?)
            .ok_or(BoundProofError::UnboundHypothesis { slot, depth: self.hypotheses.len() })?;
        let (proposition, depth) = self
            .hypotheses
            .get(position)
            .ok_or(BoundProofError::UnboundHypothesis { slot, depth: self.hypotheses.len() })?;
        let lift = self.bounds.len().checked_sub(*depth).ok_or(BoundProofError::IndexOverflow)?;
        let proposition = terms::lift_term(proposition, lift)?;
        if self.export.is_some_and(|plan| position < plan.binder_terms.len()) {
            self.used_slots.insert(position);
        }
        Ok(proposition)
    }

    fn check_implies_intro(
        &mut self,
        assumption: &Term,
        body: &Proof,
    ) -> Result<Term, KernelError> {
        self.check_authorized_assumption(assumption)?;
        if !assumption.ty().is_prop() {
            return Err(KernelError::NotProposition(assumption.ty()));
        }
        self.hypotheses.push((assumption.clone(), self.bounds.len()));
        let result = self.check(body);
        self.hypotheses.pop();
        Term::mk_imp(assumption.clone(), result?)
    }

    fn check_term_binder(&mut self, ty: &Ty, body: &Proof) -> Result<Term, KernelError> {
        self.bounds.push(ty.clone());
        let result = self
            .check_term(&Term::Bound { index: 0, ty: ty.clone() })
            .and_then(|()| self.check(body));
        self.bounds.pop();
        result
    }

    fn check_export_head(
        &mut self,
        instance: &LeafInstance,
        slots: &[usize],
    ) -> Result<Term, KernelError> {
        let plan = self.export.ok_or(KernelError::UnknownClassEvidence)?;
        let owner = self.owner.ok_or(KernelError::UnknownClassEvidence)?;
        let source = self
            .sources
            .leaves
            .get(instance.source)
            .ok_or(BoundProofError::UnauthorizedLeaf { leaf: instance.source })?;
        let expected = plan.collect_leaf_slots(owner, source, &instance.types)?;
        if !slots.iter().copied().eq(expected.iter().copied()) {
            return Err(BoundProofError::InvalidLeafInstance { leaf: instance.source }.into());
        }
        let mut proposition = self.check_leaf(instance)?;
        for slot in slots.iter().rev() {
            proposition = Term::mk_imp(
                plan.binder_terms.get(*slot).ok_or(KernelError::UnknownClassEvidence)?.clone(),
                proposition,
            )?;
        }
        Ok(proposition)
    }

    fn check_leaf(&mut self, instance: &LeafInstance) -> Result<Term, KernelError> {
        let source = *self
            .sources
            .leaves
            .get(instance.source)
            .ok_or(BoundProofError::UnauthorizedLeaf { leaf: instance.source })?;
        if matches!(source.payload().mode(), crate::obligations::ProofMode::SortErased) {
            return self.check_transport(instance);
        }
        self.check_instance_keys(instance, source)?;
        self.check_leaf_types(&instance.types)?;
        self.check_leaf_provenance(instance, source)?;
        self.instantiate_leaf(instance, source)
    }

    fn check_transport(&mut self, instance: &LeafInstance) -> Result<Term, KernelError> {
        self.owner.ok_or(KernelError::UnknownClassEvidence)?;
        let source = *self
            .sources
            .leaves
            .get(instance.source)
            .ok_or(BoundProofError::UnauthorizedLeaf { leaf: instance.source })?;
        if !matches!(source.payload().mode(), crate::obligations::ProofMode::SortErased)
            || !source.hyps().is_empty()
        {
            return Err(BoundProofError::UnauthorizedLeaf { leaf: instance.source }.into());
        }
        self.check_instance_keys(instance, source)?;
        self.check_leaf_types(&instance.types)?;
        self.instantiate_leaf(instance, source)
    }

    fn check_instance_keys(
        &self,
        instance: &LeafInstance,
        source: &KernelThm,
    ) -> Result<(), KernelError> {
        let expected = super::lower::make_leaf_instance(instance.source, source)?;
        if !instance.types.keys().eq(expected.types.keys())
            || !instance.terms.keys().eq(expected.terms.keys())
        {
            return Err(BoundProofError::InvalidLeafInstance { leaf: instance.source }.into());
        }
        Ok(())
    }

    fn check_leaf_provenance(
        &mut self,
        instance: &LeafInstance,
        source: &KernelThm,
    ) -> Result<(), KernelError> {
        let Some(owner) = self.owner else {
            return Ok(());
        };
        let premises = self.export.map_or(&[][..], |plan| plan.premises.as_slice());
        source.prop().term().visit_const_occurrences(&mut |name, source_ty| {
            let erased_ty = source_ty.rewrite_atomic_types(&instance.types)?;
            let evidence = crate::class_proof::certify_sort_erased_const(
                owner,
                name,
                source_ty,
                &erased_ty,
                &instance.types,
                premises,
            )?;
            if premises.is_empty() && !evidence.slots().is_empty() {
                return Err(KernelError::UnknownClassEvidence);
            }
            self.dependencies.extend(evidence.dependencies());
            self.used_slots.extend(evidence.slots());
            Ok(())
        })
    }

    fn instantiate_leaf(
        &mut self,
        instance: &LeafInstance,
        source: &KernelThm,
    ) -> Result<Term, KernelError> {
        for (key, value) in &instance.terms {
            self.check_term(value)?;
            require_type(&terms::replace_type_atoms(&key.ty, &instance.types)?, &value.ty())?;
        }
        terms::rewrite_term(
            source.prop().term(),
            0,
            &mut |term, depth| match TermKey::from_term(term)
                .and_then(|key| instance.terms.get(&key))
            {
                Some(value) => Ok(Some(terms::lift_term(value, depth)?)),
                None => Ok(None),
            },
            &mut |ty| terms::replace_type_atoms(ty, &instance.types),
        )
    }

    fn check_leaf_types(&mut self, types: &BTreeMap<Ty, Ty>) -> Result<(), KernelError> {
        for (source, target) in types {
            if source != target
                && let Some(sort) = source.atomic_sort()
            {
                let owner = self.owner.ok_or(BoundProofError::UnsupportedSortExportVariant {
                    operation: "sorted leaf instance",
                })?;
                for class in sort.classes() {
                    if let Some(plan) = self.export {
                        let proof = crate::class_proof::derive_scoped_of_class(
                            owner,
                            target,
                            class,
                            &plan.premises,
                        )?;
                        self.dependencies.extend(proof.dependencies());
                        self.used_slots.extend(proof.slots());
                    } else {
                        let proof = crate::class_proof::derive_of_class(owner, target, class)?;
                        self.dependencies.extend(proof.dependencies());
                    }
                }
            }
            self.context.validate_type(target)?;
            target.for_each_type_atom(&mut |_, _, sort| {
                self.sorts.insert(sort.clone());
            });
        }
        Ok(())
    }
}

use crate::Name;

fn contains_subterm(parent: &Term, candidate: &Term) -> bool {
    if parent == candidate {
        return true;
    }
    match parent {
        Term::Abs { body, .. } | Term::Forall { body, .. } => contains_subterm(body, candidate),
        Term::App { func, arg, .. } => {
            contains_subterm(func, candidate) || contains_subterm(arg, candidate)
        },
        Term::Eq { lhs, rhs, .. } => {
            contains_subterm(lhs, candidate) || contains_subterm(rhs, candidate)
        },
        Term::Imp { premise, conclusion } => {
            contains_subterm(premise, candidate) || contains_subterm(conclusion, candidate)
        },
        Term::Const { .. } | Term::Free { .. } | Term::Var { .. } | Term::Bound { .. } => false,
    }
}

fn require_type(expected: &Ty, actual: &Ty) -> Result<(), KernelError> {
    if expected != actual {
        return Err(KernelError::TypeMismatch {
            expected: expected.clone(),
            actual: actual.clone(),
        });
    }
    Ok(())
}

fn abstract_equality(name: &Name, ty: &Ty, equality: Term) -> Result<Term, KernelError> {
    let (_, left, right) = equality.dest_eq().ok_or(KernelError::NotEquality)?;
    let abstract_term = |body: &Term| Term::Abs {
        name: name.clone(),
        param_ty: ty.clone(),
        body: Box::new(body.clone()),
        ty: Ty::arrow(ty.clone(), body.ty()),
    };
    Term::mk_eq(abstract_term(left), abstract_term(right))
}

fn check_beta(term: &Term) -> Result<Term, KernelError> {
    let (function, argument) =
        term.dest_app().ok_or_else(|| KernelError::BetaRedexExpected(term.ty()))?;
    let (_, ty, body) =
        function.dest_abs().ok_or_else(|| KernelError::BetaRedexExpected(term.ty()))?;
    require_type(ty, &argument.ty())?;
    Term::mk_eq(term.clone(), Term::instantiate_bound0(body, argument))
}

fn check_binary(rule: BinaryRule, left: &Term, right: &Term) -> Result<Term, KernelError> {
    if matches!(rule, BinaryRule::EqualIntr) {
        let (a, b) = left.dest_imp().ok_or(KernelError::NotImplication)?;
        let (reverse_b, reverse_a) = right.dest_imp().ok_or(KernelError::NotImplication)?;
        if !a.alpha_eq(reverse_a) || !b.alpha_eq(reverse_b) {
            return Err(KernelError::AntecedentMismatch);
        }
        return Term::mk_eq(a.clone(), b.clone());
    }
    let (ty, a, b) = left.dest_eq().ok_or(KernelError::NotEquality)?;
    if matches!(rule, BinaryRule::EqualElim) {
        require_type(&Ty::prop(), ty)?;
        if !a.alpha_eq(right) {
            return Err(KernelError::AntecedentMismatch);
        }
        return Ok(b.clone());
    }
    let (other_ty, c, d) = right.dest_eq().ok_or(KernelError::NotEquality)?;
    if matches!(rule, BinaryRule::Transitive) {
        require_type(ty, other_ty)?;
        if !b.alpha_eq(c) {
            return Err(KernelError::MiddleMismatch);
        }
        return Term::mk_eq(a.clone(), d.clone());
    }
    let (domain, range) =
        ty.dest_arrow().ok_or_else(|| KernelError::NotFunctionType(ty.clone()))?;
    require_type(domain, other_ty)?;
    let apply = |function: &Term, argument: &Term| Term::App {
        func: Box::new(function.clone()),
        arg: Box::new(argument.clone()),
        ty: range.clone(),
    };
    Term::mk_eq(apply(a, c), apply(b, d))
}
