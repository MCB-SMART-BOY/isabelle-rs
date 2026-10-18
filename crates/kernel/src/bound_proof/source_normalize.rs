//! Proof-producing normalization at inference results, not an unchecked term
//! rewrite: every beta step is an ordinary Pure equality conversion.
use std::sync::Arc;

use crate::{CTerm, KernelError, ProofContext, Term, TrustedTheory, Ty};

use super::{BinaryRule, BoundProofError, Node, Proof, Sources, check, composition_beta, terms};

struct Normalizer<'a, 's> {
    context: &'a ProofContext,
    owner: &'a TrustedTheory,
    sources: &'a Sources<'s>,
    source: &'a Term,
    target: &'a Term,
    flex_pairs: &'a [(CTerm, CTerm)],
    bounds: Vec<Ty>,
    hypotheses: Vec<(Term, usize)>,
    work: usize,
}

impl Normalizer<'_, '_> {
    fn normalize_result(&self, proof: Proof) -> Result<Proof, KernelError> {
        let actual = check::inspect_scoped_proposition(
            self.context,
            self.owner,
            self.sources,
            &proof,
            check::ScopedInspection {
                bounds: &self.bounds,
                hypotheses: &self.hypotheses,
                source: self.source,
                target: self.target,
                flex_pairs: self.flex_pairs,
            },
        )?;
        let normal = terms::normalize_beta(actual.clone())?;
        if actual.alpha_eq(&normal) {
            return Ok(proof);
        }
        let equality = composition_beta::prove_beta_normalization(&actual, &normal)?;
        Ok(Arc::new(Node::Binary { rule: BinaryRule::EqualElim, left: equality, right: proof }))
    }

    fn normalize_term_binder(
        &mut self,
        name: &crate::Name,
        ty: &Ty,
        body: &Proof,
        is_equality: bool,
    ) -> Result<Proof, KernelError> {
        self.bounds.push(ty.clone());
        let result = self.normalize(body);
        self.bounds.pop();
        let body = result?;
        Ok(Arc::new(if is_equality {
            Node::EqAbs { name: name.clone(), ty: ty.clone(), body }
        } else {
            Node::ForallIntro { name: name.clone(), ty: ty.clone(), body }
        }))
    }

    fn normalize_implication_intro(
        &mut self,
        assumption: &Term,
        body: &Proof,
    ) -> Result<Proof, KernelError> {
        self.hypotheses.push((assumption.clone(), self.bounds.len()));
        let result = self.normalize(body);
        self.hypotheses.pop();
        Ok(Arc::new(Node::ImpliesIntro { assumption: assumption.clone(), body: result? }))
    }

    fn normalize(&mut self, proof: &Proof) -> Result<Proof, KernelError> {
        self.work = self.work.saturating_add(1);
        super::composition_env::check_candidate_budget(
            "source proof",
            "nodes",
            self.work,
            super::composition_env::MAX_CANDIDATE_NODES,
        )?;
        match proof.as_ref() {
            Node::ImpliesIntro { assumption, body } => {
                self.normalize_implication_intro(assumption, body)
            },
            Node::ForallIntro { name, ty, body } => {
                self.normalize_term_binder(name, ty, body, false)
            },
            Node::EqAbs { name, ty, body } => self.normalize_term_binder(name, ty, body, true),
            _ => self.normalize_other(proof),
        }
    }

    fn normalize_other(&mut self, proof: &Proof) -> Result<Proof, KernelError> {
        let node = match proof.as_ref() {
            Node::ImpliesElim(left, right) => {
                Node::ImpliesElim(self.normalize(left)?, self.normalize(right)?)
            },
            Node::ForallElim { premise, argument } => {
                Node::ForallElim { premise: self.normalize(premise)?, argument: argument.clone() }
            },
            Node::EqSym(premise) => Node::EqSym(self.normalize(premise)?),
            Node::Binary { rule, left, right } => Node::Binary {
                rule: *rule,
                left: self.normalize(left)?,
                right: self.normalize(right)?,
            },
            Node::Hyp(_)
            | Node::Reflexive(_)
            | Node::Beta(_)
            | Node::EqFlex(_)
            | Node::Eta(_)
            | Node::AuthorizedLeaf(_)
            | Node::ClosedExportTransport(_)
            | Node::ExportHead(_) => return self.normalize_leaf(proof),
            Node::ImpliesIntro { .. } | Node::ForallIntro { .. } | Node::EqAbs { .. } => {
                return Err(BoundProofError::StatementMismatch.into());
            },
        };
        let needs_conversion = matches!(
            node,
            Node::ForallElim { .. } | Node::Binary { rule: BinaryRule::Combination, .. }
        );
        let rebuilt = Arc::new(node);
        if needs_conversion { self.normalize_result(rebuilt) } else { Ok(rebuilt) }
    }

    fn normalize_leaf(&self, proof: &Proof) -> Result<Proof, KernelError> {
        match proof.as_ref() {
            Node::AuthorizedLeaf(_) | Node::ClosedExportTransport(_) | Node::ExportHead(_) => {
                self.normalize_result(proof.clone())
            },
            _ => Ok(proof.clone()),
        }
    }
}

pub(super) fn normalize_source_proof(
    context: &ProofContext,
    owner: &TrustedTheory,
    sources: &Sources<'_>,
    proof: Proof,
    source: &Term,
    target: &Term,
    flex_pairs: &[(CTerm, CTerm)],
) -> Result<Proof, KernelError> {
    Normalizer {
        context,
        owner,
        sources,
        source,
        target,
        flex_pairs,
        bounds: Vec::new(),
        hypotheses: Vec::new(),
        work: 0,
    }
    .normalize(&proof)
}
