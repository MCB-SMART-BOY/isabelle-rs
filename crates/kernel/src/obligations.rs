use std::collections::BTreeSet;

use super::{
    CProp, CTerm, Derivation, InstEntry, KernelError, Name, Sort, Term, Ty,
    identity::CanonicalEncoder,
};
use crate::logic::TypeInstantiation;

/// A staged transaction has not supplied a committed theorem certificate.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct PendingId(u64);
impl PendingId {
    pub(crate) fn write_canonical(&self, encoder: &mut CanonicalEncoder) {
        encoder.write_u64(self.0);
    }
    #[cfg(test)]
    pub(crate) fn value(&self) -> u64 {
        self.0
    }
}

/// Sort-scoped judgments live only in the private bound checker. Only its
/// completely discharged output may enter a theorem payload.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ProofMode {
    Ordinary,
    SortErased,
}

/// Data carried by a derivation, not evidence that any class obligation is solved.
/// There is deliberately no public constructor or obligation-elimination method.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ProofPayload {
    shyps: BTreeSet<Sort>,
    sort_obligations: BTreeSet<(Ty, Sort)>,
    flex_pairs: Vec<(CTerm, CTerm)>,
    pending: BTreeSet<PendingId>,
    mode: ProofMode,
}

/// Closure failures are user-fixable by supplying a valid proof rule/certificate, not by clearing data.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum PayloadError {
    #[error("theorem has {constraints} unresolved type-sort constraints")]
    UnresolvedSortConstraints { constraints: usize },
    #[error("theorem has {pairs} unresolved flex pairs")]
    UnresolvedFlexPairs { pairs: usize },
    #[error("theorem has {pending} unfinished proof transactions")]
    UnfinishedTransactions { pending: usize },
    #[error("theorem retains {sorts} non-present sort hypotheses")]
    ExtraSortHypotheses { sorts: usize },
    #[error("theorem payload omits a sort present in proposition or hypotheses: {sort:?}")]
    MissingPresentSort { sort: Sort },
}

impl ProofPayload {
    pub(crate) fn instantiate(
        premise: &Self,
        type_inst: &TypeInstantiation,
        subst: &[InstEntry],
        hyps: &[CProp],
        prop: &CProp,
    ) -> Result<Self, KernelError> {
        let mut result = premise.clone();
        result.sort_obligations = premise
            .sort_obligations
            .iter()
            .map(|(ty, sort)| Ok((ty.subst_type_vars(type_inst)?, sort.clone())))
            .collect::<Result<_, KernelError>>()?;
        result.flex_pairs = premise
            .flex_pairs
            .iter()
            .map(|(left, right)| {
                Ok((
                    Self::instantiate_flex_term(left, type_inst, subst)?,
                    Self::instantiate_flex_term(right, type_inst, subst)?,
                ))
            })
            .collect::<Result<_, KernelError>>()?;
        result.add_type_instantiation(type_inst);
        result.add_term_instantiation(subst);
        result.add_present_sorts(hyps, prop);
        Ok(result)
    }
    /// Only F is generalized. H, S, C, pending and mode retain their exact
    /// original values; even equal F endpoints remain an unresolved pair.
    pub(crate) fn generalize(
        &self,
        type_names: &BTreeSet<Name>,
        term_names: &BTreeSet<Name>,
        index: usize,
    ) -> Result<Self, KernelError> {
        if type_names.is_empty() && term_names.is_empty() {
            return Ok(self.clone());
        }
        let mut result = self.clone();
        result.flex_pairs = self
            .flex_pairs
            .iter()
            .map(|(left, right)| {
                let generalize_endpoint = |term: &CTerm| -> Result<CTerm, KernelError> {
                    let generalized = term.term().generalize_vars(type_names, term_names, index)?;
                    Ok(CTerm::from_certified_subterm(generalized, term.context()))
                };
                Ok((generalize_endpoint(left)?, generalize_endpoint(right)?))
            })
            .collect::<Result<Vec<_>, KernelError>>()?;
        Ok(result)
    }

    /// Compose an independently checked source-key type→term rewrite. The
    /// caller supplies its exact transformed F; never collapse typed keys
    /// before transforming the source proof and every source flex pair.
    pub(crate) fn instantiate_source_order(
        source: &Self,
        types: &TypeInstantiation,
        source_subst: &[InstEntry],
        hyps: &[CProp],
        prop: &CProp,
        flex_pairs: Vec<(CTerm, CTerm)>,
    ) -> Result<Self, KernelError> {
        let mut result = source.clone();
        result.sort_obligations = source
            .sort_obligations
            .iter()
            .map(|(ty, sort)| Ok((ty.subst_type_vars(types)?, sort.clone())))
            .collect::<Result<_, KernelError>>()?;
        result.flex_pairs = flex_pairs;
        result.add_type_instantiation(types);
        result.add_term_instantiation(source_subst);
        result.add_present_sorts(hyps, prop);
        Ok(result)
    }

    /// A checked pure index renaming preserves C and S; only newly present
    /// sorts in the certified P/H/F may be added, never unifier constraints.
    pub(crate) fn rename_source_indices(
        source: &Self,
        hyps: &[CProp],
        prop: &CProp,
        flex_pairs: Vec<(CTerm, CTerm)>,
    ) -> Self {
        let mut renamed = source.clone();
        renamed.flex_pairs = flex_pairs;
        renamed.add_present_sorts(hyps, prop);
        renamed
    }

    pub(crate) fn resolve_match(
        rule: &Self,
        goal: &Self,
        subst: &[InstEntry],
        hyps: &[CProp],
        prop: &CProp,
    ) -> Result<Self, KernelError> {
        let empty = TypeInstantiation::empty();
        let mut result = rule.clone();
        result.flex_pairs = rule
            .flex_pairs
            .iter()
            .map(|(left, right)| {
                Ok((
                    Self::instantiate_flex_term(left, &empty, subst)?,
                    Self::instantiate_flex_term(right, &empty, subst)?,
                ))
            })
            .collect::<Result<_, KernelError>>()?;
        result.merge(goal);
        result.add_term_instantiation(subst);
        result.add_present_sorts(hyps, prop);
        Ok(result)
    }

    /// Both source-key rewrites have been checked independently. Merge their
    /// retained obligations, then keep precisely the checked residual F.
    pub(crate) fn compose_source_order(
        rule: &Self,
        state: &Self,
        residual: &[(CTerm, CTerm)],
        hyps: &[CProp],
        prop: &CProp,
    ) -> Self {
        let mut result = rule.clone();
        result.merge(state);
        result.flex_pairs = residual.to_vec();
        result.add_present_sorts(hyps, prop);
        result
    }

    /// Single-source assumption proof may discharge only equations established
    /// by its checked equality DAG; all other source obligations survive.
    pub(crate) fn with_residual_flex(
        source: &Self,
        residual: &[(CTerm, CTerm)],
        hyps: &[CProp],
        prop: &CProp,
    ) -> Self {
        let mut result = source.clone();
        result.flex_pairs = residual.to_vec();
        result.add_present_sorts(hyps, prop);
        result
    }

    /// Checked lift preserves C/pending/mode, adds goal sorts, and replaces
    /// F only after canonical source lift/replay verifies every transformed pair.
    pub(crate) fn lift_rule(
        source: &Self,
        goal: &CTerm,
        hyps: &[CProp],
        prop: &CProp,
        flex_pairs: &[(CTerm, CTerm)],
    ) -> Result<Self, KernelError> {
        let mut lifted = source.clone();
        Self::collect_term_sorts(goal.term(), &mut lifted.shyps);
        lifted.flex_pairs = flex_pairs.to_vec();
        lifted.add_present_sorts(hyps, prop);
        Ok(lifted)
    }

    fn instantiate_flex_term(
        term: &CTerm,
        type_inst: &TypeInstantiation,
        subst: &[InstEntry],
    ) -> Result<CTerm, KernelError> {
        let typed = term.term().instantiate_types(type_inst)?;
        Ok(CTerm::from_certified_subterm(typed.instantiate_vars(subst), term.context()))
    }

    pub(crate) fn for_derivation(hyps: &[CProp], prop: &CProp, derivation: &Derivation) -> Self {
        let mut result = Self::ordinary();
        derivation.for_each_premise(&mut |premise| result.merge(premise.payload()));
        if let Derivation::TheoremRef { theorem } = derivation {
            result.merge(theorem.as_kernel().payload());
        }
        match derivation {
            Derivation::ForallElim { arg, .. } => {
                Self::collect_term_sorts(arg.term(), &mut result.shyps);
            },
            Derivation::AxiomInstance { type_inst, term_inst, .. } => {
                result.add_type_instantiation(type_inst);
                for term in term_inst {
                    Self::collect_term_sorts(term.term(), &mut result.shyps);
                }
            },
            _ => {},
        }
        result.add_present_sorts(hyps, prop);
        result
    }

    #[cfg(test)]
    pub(crate) fn from_statement(prop: &CProp, hyps: &[CProp]) -> Self {
        let mut result = Self::ordinary();
        result.add_present_sorts(hyps, prop);
        result
    }

    pub(crate) fn from_bound_proof(
        shyps: BTreeSet<Sort>,
        prop: &CProp,
        hyps: &[CProp],
        source: &Self,
    ) -> Result<Self, PayloadError> {
        let mut result = Self::ordinary();
        result.shyps = shyps;
        result.flex_pairs = source.flex_pairs.clone();
        result.mode = source.mode.clone();
        result.add_present_sorts(hyps, prop);
        result.validate_present_sorts(prop, hyps)?;
        Ok(result)
    }
    pub(crate) fn from_sort_export(prop: &CProp, source: &Self) -> Result<Self, PayloadError> {
        if !source.sort_obligations.is_empty() {
            return Err(PayloadError::UnresolvedSortConstraints {
                constraints: source.sort_obligations.len(),
            });
        }
        if !source.flex_pairs.is_empty() {
            return Err(PayloadError::UnresolvedFlexPairs { pairs: source.flex_pairs.len() });
        }
        let mut result = Self::ordinary();
        result.shyps.insert(Sort::empty());
        result.pending = source.pending.clone();
        result.mode = ProofMode::SortErased;
        result.validate_present_sorts(prop, &[])?;
        Ok(result)
    }

    pub(crate) fn discharge_constraints(
        &self,
        proofs: &[crate::ClosedOfClassProof],
    ) -> Result<Self, KernelError> {
        let mut expected = self
            .sort_obligations
            .iter()
            .flat_map(|(ty, sort)| sort.classes().iter().map(move |class| (ty, class)));
        for proof in proofs {
            let Some((ty, class)) = expected.next() else {
                return Err(KernelError::UnknownClassEvidence);
            };
            if proof.ty() != ty || proof.class() != class {
                return Err(KernelError::UnknownClassEvidence);
            }
        }
        if expected.next().is_some() {
            return Err(KernelError::UnknownClassEvidence);
        }
        let mut discharged = self.clone();
        discharged.sort_obligations.clear();
        Ok(discharged)
    }

    fn ordinary() -> Self {
        Self {
            shyps: BTreeSet::new(),
            sort_obligations: BTreeSet::new(),
            flex_pairs: Vec::new(),
            pending: BTreeSet::new(),
            mode: ProofMode::Ordinary,
        }
    }

    /// Re-certify flex pairs in the target committed owner without changing
    /// their order, constraints, pending transactions or proof mode.
    pub(crate) fn transfer_to(&self, context: &crate::ProofContext) -> Result<Self, KernelError> {
        let mut transferred = self.clone();
        transferred.flex_pairs = self
            .flex_pairs
            .iter()
            .map(|(left, right)| {
                let left = CTerm::from_certified_subterm(left.term().clone(), context.stamp());
                let right = CTerm::from_certified_subterm(right.term().clone(), context.stamp());
                context.validate_cterm(&left)?;
                context.validate_cterm(&right)?;
                Ok((left, right))
            })
            .collect::<Result<Vec<_>, KernelError>>()?;
        for (ty, _) in &self.sort_obligations {
            context.validate_type(ty)?;
        }
        Ok(transferred)
    }

    fn merge(&mut self, other: &Self) {
        self.shyps.extend(other.shyps.iter().cloned());
        self.sort_obligations.extend(other.sort_obligations.iter().cloned());
        self.flex_pairs.extend(other.flex_pairs.iter().cloned());
        self.pending.extend(other.pending.iter().cloned());
        if matches!(other.mode, ProofMode::SortErased) {
            self.mode = ProofMode::SortErased;
        }
    }

    fn add_present_sorts(&mut self, hyps: &[CProp], prop: &CProp) {
        Self::collect_present_sorts(hyps, prop, &self.flex_pairs, &mut self.shyps);
    }

    fn present_sorts(
        hyps: &[CProp],
        prop: &CProp,
        flex_pairs: &[(CTerm, CTerm)],
    ) -> BTreeSet<Sort> {
        let mut sorts = BTreeSet::new();
        Self::collect_present_sorts(hyps, prop, flex_pairs, &mut sorts);
        sorts
    }

    fn collect_present_sorts(
        hyps: &[CProp],
        prop: &CProp,
        flex_pairs: &[(CTerm, CTerm)],
        sorts: &mut BTreeSet<Sort>,
    ) {
        Self::collect_term_sorts(prop.term(), sorts);
        for hyp in hyps {
            Self::collect_term_sorts(hyp.term(), sorts);
        }
        for (left, right) in flex_pairs {
            Self::collect_term_sorts(left.term(), sorts);
            Self::collect_term_sorts(right.term(), sorts);
        }
    }

    fn collect_term_sorts(term: &Term, sorts: &mut BTreeSet<Sort>) {
        term.for_each_type_annotation(&mut |ty| {
            ty.for_each_type_atom(&mut |_, _, sort| {
                sorts.insert(sort.clone());
            });
        });
    }

    fn add_term_instantiation(&mut self, substitutions: &[InstEntry]) {
        for entry in substitutions {
            Self::collect_term_sorts(entry.replacement().term(), &mut self.shyps);
        }
    }

    fn add_type_instantiation(&mut self, instance: &TypeInstantiation) {
        for (id, ty) in instance.iter() {
            if !id.sort.classes().is_empty() {
                self.sort_obligations.insert((ty.clone(), id.sort.clone()));
            }
            // A disappearing type annotation cannot erase its original sort hypothesis.
            self.shyps.insert(id.sort.clone());
            ty.for_each_type_atom(&mut |_, _, sort| {
                self.shyps.insert(sort.clone());
            });
        }
    }
    pub(crate) fn shyps(&self) -> &BTreeSet<Sort> {
        &self.shyps
    }

    pub(crate) fn sort_obligations(&self) -> &BTreeSet<(Ty, Sort)> {
        &self.sort_obligations
    }

    pub(crate) fn pending(&self) -> &BTreeSet<PendingId> {
        &self.pending
    }

    pub(crate) fn mode(&self) -> &ProofMode {
        &self.mode
    }

    pub(crate) fn flex_pairs(&self) -> &[(CTerm, CTerm)] {
        &self.flex_pairs
    }

    pub(crate) fn has_free_in_flex_pairs(&self, name: &Name, ty: &Ty) -> bool {
        self.flex_pairs
            .iter()
            .any(|(left, right)| left.term().free_in(name, ty) || right.term().free_in(name, ty))
    }

    pub(crate) fn max_var_index(&self) -> Option<usize> {
        let mut max = None;
        for (ty, _) in &self.sort_obligations {
            Self::include_type_index(ty, &mut max);
        }
        for (left, right) in &self.flex_pairs {
            Self::include_term_index(left.term(), &mut max);
            Self::include_term_index(right.term(), &mut max);
        }
        max
    }

    pub(crate) fn include_term_index(term: &Term, max: &mut Option<usize>) {
        if let Some(index) = term.max_var_index() {
            *max = Some(max.map_or(index, |previous| previous.max(index)));
        }
        term.for_each_type_annotation(&mut |ty| Self::include_type_index(ty, max));
    }

    fn include_type_index(ty: &Ty, max: &mut Option<usize>) {
        ty.for_each_type_var(&mut |_, index, _| {
            *max = Some(max.map_or(index, |previous| previous.max(index)));
        });
    }
    pub(crate) fn validate_present_sorts(
        &self,
        prop: &CProp,
        hyps: &[CProp],
    ) -> Result<(), PayloadError> {
        let present = Self::present_sorts(hyps, prop, &self.flex_pairs);
        if let Some(sort) = present.difference(&self.shyps).next() {
            return Err(PayloadError::MissingPresentSort { sort: sort.clone() });
        }
        Ok(())
    }

    pub(crate) fn validate_closed(&self, prop: &CProp, hyps: &[CProp]) -> Result<(), PayloadError> {
        self.validate_present_sorts(prop, hyps)?;
        if !self.sort_obligations.is_empty() {
            return Err(PayloadError::UnresolvedSortConstraints {
                constraints: self.sort_obligations.len(),
            });
        }
        if !self.flex_pairs.is_empty() {
            return Err(PayloadError::UnresolvedFlexPairs { pairs: self.flex_pairs.len() });
        }
        if !self.pending.is_empty() {
            return Err(PayloadError::UnfinishedTransactions { pending: self.pending.len() });
        }
        let present = Self::present_sorts(hyps, prop, &self.flex_pairs);
        let extra = self
            .shyps
            .difference(&present)
            .filter(|sort| {
                !matches!(self.mode, ProofMode::SortErased) || !sort.classes().is_empty()
            })
            .count();
        if extra != 0 {
            return Err(PayloadError::ExtraSortHypotheses { sorts: extra });
        }
        Ok(())
    }

    pub(crate) fn write_canonical(&self, encoder: &mut CanonicalEncoder) {
        encoder.write_u64(self.shyps.len() as u64);
        for sort in &self.shyps {
            sort.write_canonical(encoder);
        }
        encoder.write_u64(self.sort_obligations.len() as u64);
        for (ty, sort) in &self.sort_obligations {
            ty.write_canonical(encoder);
            sort.write_canonical(encoder);
        }
        encoder.write_u64(self.flex_pairs.len() as u64);
        for (left, right) in &self.flex_pairs {
            left.context().write_canonical(encoder);
            left.term().write_theorem_canonical(encoder);
            right.context().write_canonical(encoder);
            right.term().write_theorem_canonical(encoder);
        }
        encoder.write_u64(self.pending.len() as u64);
        for pending in &self.pending {
            pending.write_canonical(encoder);
        }
        match self.mode {
            ProofMode::Ordinary => encoder.write_u8(0),
            ProofMode::SortErased => encoder.write_u8(1),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{PayloadError, PendingId, ProofMode, ProofPayload};
    use crate::{ProofContext, RawTerm, Signature, Sort, TrustedTheory, Ty};
    use std::collections::BTreeSet;

    #[test]
    fn generalize_pending_and_equal_flex_preserves_obligations_and_blocks_closure() {
        let signature = Signature::new().extend_const("P", Ty::prop()).unwrap();
        let owner = TrustedTheory::root("PayloadGeneralize", signature);
        let mut context = ProofContext::new(owner.snapshot().clone());
        context.declare_free("x", Ty::prop());
        let prop = context.certify_prop(RawTerm::const_("P", Ty::prop())).unwrap();
        let endpoint = context.certify_term(RawTerm::free("x", Ty::prop())).unwrap();
        let mut source = ProofPayload::from_statement(&prop, &[]);
        source.flex_pairs.push((endpoint.clone(), endpoint));
        source.pending.insert(PendingId(7));
        source.mode = ProofMode::SortErased;
        source.sort_obligations.insert((Ty::prop(), Sort::empty()));

        let generalized =
            source.generalize(&BTreeSet::new(), &BTreeSet::from(["x".into()]), 0).unwrap();
        assert_eq!(generalized.shyps, source.shyps);
        assert_eq!(generalized.sort_obligations, source.sort_obligations);
        assert_eq!(generalized.pending, source.pending);
        assert_eq!(generalized.mode, source.mode);
        assert_eq!(generalized.flex_pairs.len(), 1);
        assert_eq!(generalized.flex_pairs[0].0, generalized.flex_pairs[0].1);
        assert_ne!(generalized.flex_pairs, source.flex_pairs);
        assert_eq!(
            source.flex_pairs[0].0.term(),
            &crate::Term::Free { name: "x".into(), ty: Ty::prop() }
        );

        let mut without_other_obligations = generalized;
        without_other_obligations.sort_obligations.clear();
        without_other_obligations.flex_pairs.clear();
        assert_eq!(
            without_other_obligations.validate_closed(&prop, &[]),
            Err(PayloadError::UnfinishedTransactions { pending: 1 }),
        );
    }

    #[test]
    fn export_and_increment_forged_pending_source_reject_before_transform() {
        use crate::{KernelError, KernelRules, KernelThm};
        let signature = Signature::new().extend_const("P", Ty::prop()).unwrap();
        let owner = TrustedTheory::root("PendingSourceAttack", signature);
        let context = ProofContext::new(owner.snapshot().clone());
        let source =
            KernelRules::reflexive(context.certify_term(RawTerm::const_("P", Ty::prop())).unwrap())
                .into_kernel();
        let mut payload = source.payload().clone();
        payload.pending.insert(PendingId(1));
        let forged = KernelThm::new_with_payload(
            source.hyps().to_vec(),
            source.prop().clone(),
            payload,
            source.derivation().clone(),
        );
        assert_eq!(
            KernelRules::export_scope(&owner, &context, &forged),
            Err(KernelError::AcceptanceReplayMismatch)
        );
        for increment in [0, 1] {
            assert_eq!(
                KernelRules::incr_indexes(&owner, &context, &forged, increment),
                Err(KernelError::AcceptanceReplayMismatch)
            );
        }
    }
}
