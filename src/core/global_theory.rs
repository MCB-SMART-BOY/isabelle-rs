//! Global theory operations — named theorems and facts.
//!
//! Corresponds to `src/Pure/global_theory.ML`.
//!
//! These operations work on the global theory context: naming theorems,
//! adding facts to the global fact table, checking theory membership.

use std::sync::Arc;

use super::{theory::Theory, thm::Thm};

/// Add a named theorem to the global fact table.
pub fn add_fact(theory: &mut Theory, name: &str, thms: Vec<Arc<Thm>>) {
    // Simplified: store in the theory
    for thm in thms {
        if thm.is_closed_proved() {
            theory.add_theorem(name, thm.as_ref().clone());
        }
    }
}

/// Name a theorem: give it a name in the theory.
pub fn name_thm(_name: &str, thm: &Thm) -> Thm {
    // In Isabelle, naming attaches metadata. Here we just clone.
    thm.clone()
}

/// Collect all named theorems from a theory and its ancestors.
pub fn all_named_thms(theory: &Theory) -> Vec<(String, Arc<Thm>)> {
    theory
        .all_theorem_names()
        .iter()
        .filter_map(|name| {
            theory.lookup_theorem(name).map(|thm| ((*name).to_string(), Arc::clone(thm)))
        })
        .collect()
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{
        term::Term,
        thm::{CTerm, ThmKernel},
        types::Typ,
    };

    #[test]
    fn test_all_named_thms() {
        let pure = Theory::pure();
        let mut thy = Theory::begin("Test", vec![pure]);
        let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
        let thm = ThmKernel::trivial(a).unwrap();
        thy.add_theorem("my_thm", thm);

        let named = all_named_thms(&thy);
        assert!(!named.is_empty());
    }
}
