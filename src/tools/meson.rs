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

#![allow(dead_code)]

use std::sync::Arc;

use crate::core::thm::{CTerm, Thm, ThmKernel};
use crate::isar::proof_result::validate_proof_result;

/// Meson facade: only theorem-producing paths can finish a goal. Boolean
/// complementary literals are not themselves a kernel derivation.
pub struct MesonProver {
    clauses: Vec<Arc<Thm>>,
}

impl Default for MesonProver {
    fn default() -> Self {
        Self::new()
    }
}

impl MesonProver {
    pub fn new() -> Self {
        Self { clauses: Vec::new() }
    }

    pub fn add_clause(&mut self, thm: Arc<Thm>) {
        self.clauses.push(thm);
    }

    pub fn add_premises(&mut self, premises: &[Arc<Thm>]) {
        self.clauses.extend(premises.iter().cloned());
    }

    pub fn prove(&self, goal: &Thm) -> Option<Arc<Thm>> {
        self.clauses
            .iter()
            .find(|fact| validate_proof_result(goal.prop().term(), fact, &[]).is_ok())
            .cloned()
    }
}

// =========================================================================
// Integration
// =========================================================================

pub fn meson_tac(state: &Thm, premises: &[Arc<Thm>]) -> Vec<Thm> {
    let Some(premise) = state.prem(0) else {
        return Vec::new();
    };
    let mut prover = MesonProver::new();
    prover.add_premises(premises);
    let request = ThmKernel::assume_compat(CTerm::certify(premise));
    let Some(proved) = prover.prove(&request) else {
        return Vec::new();
    };
    let Some(next) = ThmKernel::bicompose(false, &proved, state, 0) else {
        return Vec::new();
    };
    if next.nprems() >= state.nprems() {
        return Vec::new();
    }
    vec![next]
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{
        logic::Pure,
        term::Term,
        types::{Typ, TypeEnv},
    };

    #[test]
    fn meson_conditional_fact_does_not_prove_conclusion() {
        let a = Term::const_("A", Typ::base("prop"));
        let b = Term::const_("B", Typ::base("prop"));
        let mut env = TypeEnv::new();
        env.declare_const("B", Typ::base("prop"));
        let assumed = CTerm::certify_checked(b.clone(), &env).unwrap();
        let fact =
            ThmKernel::implies_intr(&assumed, &ThmKernel::assume_checked(assumed.clone()).unwrap())
                .unwrap();
        let mut prover = MesonProver::new();
        prover.add_clause(Arc::new(fact));
        let conditional = Pure::mk_implies(a, b.clone());
        assert!(prover.prove(&ThmKernel::assume_compat(CTerm::certify(conditional))).is_none());
        assert!(prover.prove(&ThmKernel::assume_compat(CTerm::certify(b))).is_none());
    }
}
