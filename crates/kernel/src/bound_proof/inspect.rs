use std::collections::BTreeSet;

use crate::{Name, Term, Ty, obligations::ProofPayload};

use super::{Node, Proof, terms};

#[derive(Default)]
pub(super) struct ProofVariables {
    pub(super) atoms: BTreeSet<Ty>,
    pub(super) frees: BTreeSet<(Name, Ty)>,
    pub(super) vars: BTreeSet<(Name, usize, Ty)>,
    pub(super) max_index: Option<usize>,
}

impl ProofVariables {
    pub(super) fn collect(proof: &Proof) -> Self {
        let mut variables = Self::default();
        variables.visit_proof(proof);
        variables
    }

    pub(super) fn visit_type(&mut self, ty: &Ty) {
        ty.for_each_type_atom(&mut |name, index, sort| {
            self.atoms.insert(match index {
                Some(index) => Ty::tvar(name.clone(), index, sort.clone()),
                None => Ty::tfree(name.clone(), sort.clone()),
            });
            self.max_index = self.max_index.max(index);
        });
    }

    pub(super) fn visit_term(&mut self, term: &Term) {
        terms::collect_type_atoms(term, &mut self.atoms);
        ProofPayload::include_term_index(term, &mut self.max_index);
        terms::visit_free_variables(term, &mut |name, ty| {
            self.frees.insert((name.clone(), ty.clone()));
        });
        self.visit_schematic_vars(term);
    }

    fn visit_schematic_vars(&mut self, term: &Term) {
        match term {
            Term::Var { name, index, ty } => {
                self.vars.insert((name.clone(), *index, ty.clone()));
            },
            Term::Abs { body, .. } | Term::Forall { body, .. } => self.visit_schematic_vars(body),
            Term::App { func, arg, .. } => {
                self.visit_schematic_vars(func);
                self.visit_schematic_vars(arg);
            },
            Term::Eq { lhs, rhs, .. } => {
                self.visit_schematic_vars(lhs);
                self.visit_schematic_vars(rhs);
            },
            Term::Imp { premise, conclusion } => {
                self.visit_schematic_vars(premise);
                self.visit_schematic_vars(conclusion);
            },
            Term::Const { .. } | Term::Free { .. } | Term::Bound { .. } => {},
        }
    }

    fn visit_instance(&mut self, instance: &super::LeafInstance) {
        for ty in instance.types.values() {
            self.visit_type(ty);
        }
        for term in instance.terms.values() {
            self.visit_term(term);
        }
    }

    fn visit_proof(&mut self, proof: &Proof) {
        match proof.as_ref() {
            Node::Hyp(_) | Node::EqFlex(_) => {},
            Node::ImpliesIntro { assumption, body } => {
                self.visit_term(assumption);
                self.visit_proof(body);
            },
            Node::ImpliesElim(left, right) | Node::Binary { left, right, .. } => {
                self.visit_proof(left);
                self.visit_proof(right);
            },
            Node::ForallIntro { ty, body, .. } | Node::EqAbs { ty, body, .. } => {
                self.visit_type(ty);
                self.visit_proof(body);
            },
            Node::ForallElim { premise, argument } => {
                self.visit_proof(premise);
                self.visit_term(argument);
            },
            Node::EqSym(premise) => self.visit_proof(premise),
            Node::Reflexive(term) | Node::Beta(term) | Node::Eta(term) => self.visit_term(term),
            Node::AuthorizedLeaf(instance) | Node::ClosedExportTransport(instance) => {
                self.visit_instance(instance);
            },
            Node::ExportHead(view) => self.visit_instance(&view.instance),
        }
    }
}
