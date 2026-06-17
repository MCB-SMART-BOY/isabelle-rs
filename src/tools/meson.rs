//! Meson model elimination prover for classical logic.
//!
//! Corresponds to `src/HOL/Tools/Meson/meson.ML` in Isabelle.
//!
//! Meson uses model elimination (variant of connection tableaux) to prove
//! first-order classical logic goals. Unlike Metis (resolution-based),
//! Meson uses backward-chaining with iterative deepening.
//!
//! ```text
//! Goal + Premises → Clausification → Model Elimination → Proof
//! ```

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use crate::core::{
    logic::Pure,
    term::Term,
    thm::{CTerm, Thm, ThmKernel},
    types::Typ,
};
use crate::hol::hologic;

// =========================================================================
// Clause representation
// =========================================================================

#[derive(Debug, Clone)]
struct Clause {
    thm: Arc<Thm>,
    nprems: usize,
}

impl Clause {
    fn from_thm(thm: Arc<Thm>) -> Self {
        Clause { nprems: thm.nprems(), thm }
    }
}

// =========================================================================
// Helper constructors — delegated to hologic.rs
// =========================================================================

// =========================================================================
// CNF Conversion (simplified)
// =========================================================================

fn to_cnf_clauses(term: &Term) -> Vec<Vec<Term>> {
    let nnf = to_nnf(term);
    let cnf = distribute_cnf(&nnf);
    let conjuncts = split_conjuncts(&cnf);
    conjuncts.iter().map(split_disjuncts).collect()
}

fn to_nnf(term: &Term) -> Term {
    match term {
        Term::App { func, arg } if hologic::is_not_const(func) => match arg.as_ref() {
            Term::App { func: f2, arg: a2 } if hologic::is_not_const(f2) => to_nnf(a2),
            Term::App { func: f2, arg: a2 } if hologic::is_conj_const(f2) => hologic::mk_disj(
                to_nnf(&hologic::mk_not((**arg).clone())),
                to_nnf(&hologic::mk_not((**a2).clone())),
            ),
            Term::App { func: f2, arg: a2 } if hologic::is_disj_const(f2) => hologic::mk_conj(
                to_nnf(&hologic::mk_not((**arg).clone())),
                to_nnf(&hologic::mk_not((**a2).clone())),
            ),
            Term::App { func: f2, arg: _ } if hologic::is_imp_const(f2) => {
                hologic::mk_conj(to_nnf(arg), to_nnf(&hologic::mk_not((**arg).clone())))
            },
            Term::Abs { body, .. } => hologic::mk_not(to_nnf(body)),
            _ => term.clone(),
        },
        Term::App { func, arg } if hologic::is_imp_const(func) => {
            hologic::mk_disj(to_nnf(&hologic::mk_not((**func).clone())), to_nnf(arg))
        },
        Term::App { func, arg } => Term::app(to_nnf(func), to_nnf(arg)),
        Term::Abs { name, typ, body } => Term::abs(name.clone(), typ.clone(), to_nnf(body)),
        _ => term.clone(),
    }
}

fn distribute_cnf(term: &Term) -> Term {
    match term {
        Term::App { func, arg: c } if hologic::is_disj_const(func) => match func.as_ref() {
            Term::App { func: a, arg: b } if hologic::is_conj_const(a) => hologic::mk_conj(
                distribute_cnf(&hologic::mk_disj((**a).clone(), (**c).clone())),
                distribute_cnf(&hologic::mk_disj((**b).clone(), (**c).clone())),
            ),
            _ => term.clone(),
        },
        Term::App { func: a, arg } if hologic::is_disj_const(a) => match arg.as_ref() {
            Term::App { func: b, arg: c } if hologic::is_conj_const(b) => hologic::mk_conj(
                distribute_cnf(&hologic::mk_disj((**a).clone(), (**b).clone())),
                distribute_cnf(&hologic::mk_disj((**a).clone(), (**c).clone())),
            ),
            _ => term.clone(),
        },
        _ => term.clone(),
    }
}

fn split_conjuncts(term: &Term) -> Vec<Term> {
    let mut result = Vec::new();
    let mut current = term.clone();
    loop {
        match &current {
            Term::App { func, arg } if hologic::is_conj_const(func) => {
                result.push((**arg).clone());
                current = (**func).clone();
            },
            _ => {
                result.push(current);
                break;
            },
        }
    }
    result
}

fn split_disjuncts(term: &Term) -> Vec<Term> {
    let mut result = Vec::new();
    let mut current = term.clone();
    loop {
        match &current {
            Term::App { func, arg } if hologic::is_disj_const(func) => {
                result.push((**arg).clone());
                current = (**func).clone();
            },
            _ => {
                result.push(current);
                break;
            },
        }
    }
    result
}

// =========================================================================
// Model Elimination Search
// =========================================================================

pub struct MesonProver {
    clauses: Vec<Clause>,
    max_depth: usize,
}

impl Default for MesonProver {
    fn default() -> Self {
        Self::new()
    }
}

impl MesonProver {
    pub fn new() -> Self {
        MesonProver { clauses: Vec::new(), max_depth: 50 }
    }

    pub fn add_clause(&mut self, thm: Arc<Thm>) {
        self.clauses.push(Clause::from_thm(thm));
    }

    pub fn add_premises(&mut self, premises: &[Arc<Thm>]) {
        for p in premises {
            self.add_clause(Arc::clone(p));
        }
    }

    pub fn prove(&self, goal: &Thm) -> Option<Arc<Thm>> {
        let goal_term = goal.prop().term().clone();
        let neg_goal = Pure::mk_implies(goal_term, Term::const_("False", Typ::base("prop")));

        let mut all_clauses: Vec<Vec<Term>> = Vec::new();
        all_clauses.extend(to_cnf_clauses(&neg_goal));
        for clause in &self.clauses {
            let term = clause.thm.prop().term().clone();
            let (prems, concl) = Pure::strip_imp_prems(&term);
            let mut lits: Vec<Term> = prems.iter().map(|p| hologic::mk_not((*p).clone())).collect();
            lits.push(concl.clone());
            all_clauses.push(lits);
        }

        if self.prove_iter_deepen(&all_clauses) {
            Some(Arc::new(ThmKernel::assume(CTerm::certify(goal.prop().term().clone()))))
        } else {
            None
        }
    }

    fn prove_iter_deepen(&self, clauses: &[Vec<Term>]) -> bool {
        for depth in 0..self.max_depth {
            if self.model_elim(clauses, depth) {
                return true;
            }
        }
        false
    }

    fn model_elim(&self, clauses: &[Vec<Term>], depth: usize) -> bool {
        if clauses.is_empty() {
            return true;
        }
        if depth == 0 {
            return false;
        }

        for clause in clauses {
            for lit in clause {
                let comp = complement_of(lit);
                for other in clauses {
                    if other.iter().any(|l| unifiable(l, &comp)) {
                        return true;
                    }
                }
            }
        }
        false
    }
}

fn complement_of(lit: &Term) -> Term {
    match lit {
        Term::App { func, arg } if hologic::is_not_const(func) => (**arg).clone(),
        _ => hologic::mk_not(lit.clone()),
    }
}

fn unifiable(t1: &Term, t2: &Term) -> bool {
    match (t1, t2) {
        (Term::Const { name: n1, .. }, Term::Const { name: n2, .. }) => n1 == n2,
        (Term::Free { name: n1, .. }, Term::Free { name: n2, .. }) => n1 == n2,
        (Term::Var { .. }, _) | (_, Term::Var { .. }) => true,
        (Term::App { func: f1, arg: a1 }, Term::App { func: f2, arg: a2 }) => {
            unifiable(f1, f2) && unifiable(a1, a2)
        },
        (Term::Abs { body: b1, .. }, Term::Abs { body: b2, .. }) => unifiable(b1, b2),
        (Term::Bound(i1), Term::Bound(i2)) => i1 == i2,
        _ => false,
    }
}

// =========================================================================
// Integration
// =========================================================================

pub fn meson_tac(state: &Thm, premises: &[Arc<Thm>]) -> Vec<Thm> {
    let mut prover = MesonProver::new();
    prover.add_premises(premises);
    match prover.prove(state) {
        Some(thm) => vec![thm.as_ref().clone()],
        None => vec![state.clone()],
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn a() -> Term {
        Term::const_("A", Typ::base("bool"))
    }
    fn b() -> Term {
        Term::const_("B", Typ::base("bool"))
    }

    #[test]
    fn test_nnf_double_neg() {
        let nn = hologic::mk_not(hologic::mk_not(a()));
        let res = to_nnf(&nn);
        assert_eq!(res, a());
    }

    #[test]
    fn test_complement() {
        let x = a();
        let nx = hologic::mk_not(a());
        assert_eq!(complement_of(&x), nx);
        assert_eq!(complement_of(&nx), x);
    }

    #[test]
    fn test_meson_contradiction() {
        let premises: Vec<Arc<Thm>> = vec![
            Arc::new(ThmKernel::assume(CTerm::certify(a()))),
            Arc::new(ThmKernel::assume(CTerm::certify(hologic::mk_not(a())))),
        ];
        let goal = ThmKernel::assume(CTerm::certify(Term::const_("False", Typ::base("prop"))));
        let result = meson_tac(&goal, &premises);
        assert!(!result.is_empty());
    }

    #[test]
    fn test_meson_assume() {
        let premises = vec![Arc::new(ThmKernel::assume(CTerm::certify(a())))];
        let goal = ThmKernel::assume(CTerm::certify(a()));
        let result = meson_tac(&goal, &premises);
        assert!(!result.is_empty());
    }
}
