//! Named fact tables — the theorem database.
//!
//! Corresponds to `src/Pure/facts.ML`.
//!
//! Facts are named collections of theorems. Isabelle uses them for:
//! - `[simp]` rules: simplification rules
//! - `[intro]` rules: introduction rules
//! - `[elim]` rules: elimination rules
//! - Named theorems: `name: thm1 thm2 ...`

use std::collections::BTreeMap;
use std::sync::Arc;

use super::thm::Thm;

// =========================================================================
// Fact table
// =========================================================================

/// A set of named facts — the global and local theorem database.
#[derive(Clone, Debug)]
pub struct Facts {
    entries: BTreeMap<String, Vec<Arc<Thm>>>,
}

impl Facts {
    pub fn empty() -> Self { Facts { entries: BTreeMap::new() } }

    /// Add theorems to a named fact.
    pub fn add(&mut self, name: &str, thms: Vec<Arc<Thm>>) {
        self.entries.entry(name.to_string()).or_default().extend(thms);
    }

    /// Get the theorems for a named fact.
    pub fn get(&self, name: &str) -> Option<&[Arc<Thm>]> {
        self.entries.get(name).map(|v| v.as_slice())
    }

    /// Get a single theorem (the first one).
    pub fn get_single(&self, name: &str) -> Option<&Arc<Thm>> {
        self.entries.get(name).and_then(|v| v.first())
    }

    /// Check if a fact exists.
    pub fn contains(&self, name: &str) -> bool {
        self.entries.contains_key(name)
    }

    /// Iterate over all fact names.
    pub fn names(&self) -> impl Iterator<Item = &String> {
        self.entries.keys()
    }

    /// Merge another fact table into this one.
    pub fn merge(&mut self, other: &Facts) {
        for (name, thms) in &other.entries {
            self.add(name, thms.clone());
        }
    }

    /// Remove a fact.
    pub fn remove(&mut self, name: &str) -> Option<Vec<Arc<Thm>>> {
        self.entries.remove(name)
    }
}

// =========================================================================
// Fact selectors
// =========================================================================

/// Selector for fact retrieval.
#[derive(Clone, Debug)]
pub enum FactRef {
    /// A simple named fact: `foo`
    Named(String),
    /// A numbered selection: `foo(1)`, `foo(2-4)`
    Select { name: String, index: usize },
}

impl FactRef {
    pub fn named(name: &str) -> Self { FactRef::Named(name.to_string()) }
}

impl Facts {
    /// Retrieve facts by reference.
    pub fn retrieve(&self, refs: &[FactRef]) -> Option<Vec<Arc<Thm>>> {
        let mut result = Vec::new();
        for r in refs {
            match r {
                FactRef::Named(name) => {
                    let thms = self.get(name)?;
                    result.extend_from_slice(thms);
                }
                FactRef::Select { name, index } => {
                    let thms = self.get(name)?;
                    if *index >= thms.len() { return None; }
                    result.push(Arc::clone(&thms[*index]));
                }
            }
        }
        Some(result)
    }
}

impl Default for Facts {
    fn default() -> Self { Facts::empty() }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::thm::{CTerm, ThmKernel};
    use crate::core::types::Typ;
    use crate::core::term::Term;

    fn dummy_thm() -> Arc<Thm> {
        let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
        Arc::new(ThmKernel::trivial(a))
    }

    #[test]
    fn test_add_and_get() {
        let mut facts = Facts::empty();
        let thm = dummy_thm();
        facts.add("foo", vec![Arc::clone(&thm)]);
        assert!(facts.contains("foo"));
        assert_eq!(facts.get("foo").unwrap().len(), 1);
    }

    #[test]
    fn test_retrieve() {
        let mut facts = Facts::empty();
        let thm = dummy_thm();
        facts.add("bar", vec![Arc::clone(&thm)]);
        let refs = vec![FactRef::named("bar")];
        let result = facts.retrieve(&refs).unwrap();
        assert_eq!(result.len(), 1);
    }
}
