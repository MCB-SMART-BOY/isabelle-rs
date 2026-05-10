//! Bi-resolution — forward and backward chaining.
//!
//! Corresponds to `src/Pure/bires.ML`.
//!
//! Resolution is the fundamental inference step: matching a rule's
//! conclusion against a goal, producing new subgoals from the rule's
//! premises. Bi-resolution can work forward or backward.


use super::thm::{Thm, ThmKernel};
use super::unify::{self, UnifyConfig};
use super::envir::Envir;

/// Resolve a rule against a goal (backward chaining).
/// The rule's conclusion is matched against the goal, and the
/// rule's premises become new subgoals.
pub fn biresolution(
    _state: &Thm,     // goal state
    _rule: &Thm,      // rule to apply
    _lift: bool,      // lift the rule to the goal's context?
) -> Option<Vec<Thm>> {
    // Simplified: just check if rule's conclusion matches goal's conclusion
    let config = UnifyConfig::default();
    let env = Envir::init();
    unify::unifiers(
        &env,
        &[(_state.prop().term().clone(), _rule.prop().term().clone())],
        &config,
    )?;
    // If they unify, the rule's hypotheses become subgoals
    let subgoals: Vec<Thm> = _rule.hyps().iter().map(|h| {
        ThmKernel::assume(h.clone())
    }).collect();
    Some(subgoals)
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::thm::CTerm;
    use crate::core::term::Term;
    use crate::core::types::Typ;

    fn prop(name: &str) -> CTerm {
        CTerm::certify(Term::const_(name, Typ::dummy()))
    }

    #[test]
    fn test_biresolution_trivial() {
        let a = prop("A");
        let goal = ThmKernel::trivial(a.clone());
        let rule = ThmKernel::trivial(a);
        let result = biresolution(&goal, &rule, false);
        assert!(result.is_some());
    }
}
