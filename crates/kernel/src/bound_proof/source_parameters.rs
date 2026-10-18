use std::collections::BTreeSet;

use crate::{Derivation, KernelThm, Name, Term, Ty};

use super::terms;

#[derive(Default)]
struct SourceParameters<'a> {
    bound: Vec<(&'a Name, &'a Ty)>,
    frees: BTreeSet<(&'a Name, &'a Ty)>,
}

pub(crate) fn collect_lexical_frees(theorem: &KernelThm) -> Vec<(Name, Ty)> {
    let mut parameters = SourceParameters::default();
    parameters.visit_theorem(theorem);
    parameters.frees.into_iter().map(|(name, ty)| (name.clone(), ty.clone())).collect()
}

pub(super) fn has_statement_free_name(theorem: &KernelThm, name: &Name) -> bool {
    let contains = |term: &Term| {
        let mut found = false;
        terms::visit_free_variables(term, &mut |actual, _| {
            found |= actual == name;
        });
        found
    };
    contains(theorem.prop().term())
        || theorem.hyps().iter().any(|hyp| contains(hyp.term()))
        || theorem
            .payload()
            .flex_pairs()
            .iter()
            .any(|(left, right)| contains(left.term()) || contains(right.term()))
}

pub(super) fn collect_source_parameters(theorem: &KernelThm) -> Vec<(Name, Ty)> {
    collect_lexical_frees(theorem)
        .into_iter()
        .filter(|(name, _)| !has_statement_free_name(theorem, name))
        .collect()
}

impl<'a> SourceParameters<'a> {
    fn visit_term(&mut self, term: &'a Term) {
        terms::visit_free_variables(term, &mut |name, ty| {
            if !self.bound.contains(&(name, ty)) {
                self.frees.insert((name, ty));
            }
        });
    }

    fn visit_bound(
        &mut self,
        premise: &'a KernelThm,
        parameters: impl Iterator<Item = (&'a Name, &'a Ty)>,
    ) {
        let previous_depth = self.bound.len();
        self.bound.extend(parameters);
        self.visit_theorem(premise);
        self.bound.truncate(previous_depth);
    }

    fn visit_theorem(&mut self, theorem: &'a KernelThm) {
        self.visit_term(theorem.prop().term());
        for hypothesis in theorem.hyps() {
            self.visit_term(hypothesis.term());
        }
        for (left, right) in theorem.payload().flex_pairs() {
            self.visit_term(left.term());
            self.visit_term(right.term());
        }
        match theorem.derivation() {
            Derivation::ForallIntr { variable, premise } => {
                // The source has already passed exact replay, including this shape.
                if let Term::Free { name, ty } = variable.term() {
                    self.visit_bound(premise, std::iter::once((name, ty)));
                }
            },
            Derivation::Abstraction { variable_name, variable_type, premise } => {
                self.visit_bound(premise, std::iter::once((variable_name, variable_type)));
            },
            Derivation::Generalize { source_frees, premise, .. } => {
                self.visit_bound(premise, source_frees.iter().map(|(name, ty)| (name, ty)));
            },
            Derivation::ExportScope { .. } | Derivation::Transfer { .. } => {},
            derivation => {
                self.visit_operands(derivation);
                derivation.for_each_premise(&mut |premise| self.visit_theorem(premise));
            },
        }
    }

    fn visit_operands(&mut self, derivation: &'a Derivation) {
        match derivation {
            Derivation::Assume { prop } => self.visit_term(prop.term()),
            Derivation::Weaken { assumption, .. } => self.visit_term(assumption.term()),

            Derivation::Reflexive { term } => self.visit_term(term.term()),
            Derivation::BetaConversion { redex } => self.visit_term(redex.term()),
            Derivation::EtaConversion { redex } => self.visit_term(redex.term()),

            Derivation::ImpliesIntr { assumption, .. } => self.visit_term(assumption.term()),
            Derivation::ForallElim { arg, .. } => self.visit_term(arg.term()),
            Derivation::LiftRule { goal, .. } => self.visit_term(goal.term()),
            Derivation::Instantiate { subst, .. }
            | Derivation::SourceInstantiate { subst, .. }
            | Derivation::Resolve1Match { subst, .. } => {
                for entry in subst {
                    self.visit_term(entry.replacement().term());
                }
            },
            Derivation::Bicompose { residual_pairs, .. }
            | Derivation::Assumption { residual_pairs, .. } => {
                for (left, right) in residual_pairs {
                    self.visit_term(left.term());
                    self.visit_term(right.term());
                }
            },
            Derivation::AxiomInstance { term_inst, .. } => {
                for term in term_inst {
                    self.visit_term(term.term());
                }
            },
            Derivation::TheoremRef { .. }
            | Derivation::Symmetric { .. }
            | Derivation::Transitive { .. }
            | Derivation::ImpliesElim { .. }
            | Derivation::Combination { .. }
            | Derivation::EqualIntr { .. }
            | Derivation::EqualElim { .. }
            | Derivation::SubstPremise { .. }
            | Derivation::ConservativeDefinition { .. }
            | Derivation::OfClass { .. }
            | Derivation::SolveConstraints { .. }
            | Derivation::StripShyps { .. }
            | Derivation::UnconstrainT { .. }
            | Derivation::PermutePrems { .. }
            | Derivation::Transfer { .. }
            | Derivation::ExportScope { .. }
            | Derivation::AdjustMaxIndex { .. }
            | Derivation::SourceRenameIndex { .. }
            | Derivation::EqAssumption { .. }
            | Derivation::RotateRule { .. }
            | Derivation::ForallIntr { .. }
            | Derivation::Abstraction { .. }
            | Derivation::Generalize { .. } => {},
        }
    }
}
