//! Theory registry — stores and retrieves theories by name.
//!
//! This provides the "global theory space" that mirrors Isabelle's
//! theory database (`Thy_Info`). When a theory imports another,
//! the registry provides the parent theory.

use std::{collections::HashMap, sync::Arc};

use crate::core::theory::Theory;

/// A registry of loaded theories, indexed by name.
#[derive(Clone, Default)]
pub struct TheoryRegistry {
    theories: HashMap<String, Arc<Theory>>,
}

impl TheoryRegistry {
    /// Create an empty registry.
    pub fn new() -> Self {
        let mut reg = TheoryRegistry::default();
        // Pure is always available
        reg.theories.insert("Pure".to_string(), Theory::pure());
        reg
    }

    /// Register a theory.
    pub fn register(&mut self, thy: Arc<Theory>) {
        self.theories.insert(thy.name().to_string(), thy);
    }

    /// Look up a theory by name.
    pub fn lookup(&self, name: &str) -> Option<Arc<Theory>> {
        self.theories.get(name).cloned()
    }

    /// Get the number of registered theories.
    pub fn len(&self) -> usize {
        self.theories.len()
    }

    /// Check if the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.theories.is_empty()
    }

    /// Get a list of all registered theory names.
    pub fn names(&self) -> Vec<&String> {
        self.theories.keys().collect()
    }
}
