//! Definition consistency checking — corresponds to Isabelle's src/Pure/defs.ML.
//!
//! Tracks overloaded constant and type definitions across a theory graph.
//! Ensures no cyclic or conflicting definitions — critical for LCF trustworthiness.
//!
//! ## Design
//!
//! ```text
//! Defs
//! ├── items: Map<Item, Vec<Spec>>         (definition specifications)
//! └── dependents: Map<Item, Vec<Item>>     (dependency tracking)
//! ```
//!
//! ## Key Invariants
//!
//! 1. No cyclic definitions (A depends on B depends on A)
//! 2. No conflicting type arguments (disjoint type patterns)
//! 3. Each item defined at most once per specification

#![allow(non_snake_case)]

use std::collections::{BTreeMap, HashMap, HashSet};

// ============================================================================
// Types
// ============================================================================

/// Kind of a definition item.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ItemKind {
    Const,
    Type,
}

/// A definition item: (kind, name).
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Item {
    pub kind: ItemKind,
    pub name: String,
}

impl Item {
    pub fn konst(name: &str) -> Self {
        Item { kind: ItemKind::Const, name: name.to_string() }
    }
    pub fn typ(name: &str) -> Self {
        Item { kind: ItemKind::Type, name: name.to_string() }
    }
}

/// A definition specification: `{def, description, lhs, rhs}`.
#[derive(Debug, Clone)]
pub struct Spec {
    /// The definition source (e.g., theory name)
    pub def: Option<String>,
    /// Human-readable description
    pub description: String,
    /// Left-hand side type arguments
    pub lhs: Vec<String>,
    /// Right-hand side dependencies: other defined items
    pub rhs: Vec<Item>,
}

/// Entry in Defs: (Item, type arguments).
pub type Entry = (Item, Vec<String>);

// ============================================================================
// Defs — definition graph
// ============================================================================

/// The global definition consistency database.
#[derive(Debug, Clone, Default)]
pub struct Defs {
    /// specifications_of: Item → Vec<Spec>
    specs: BTreeMap<Item, Vec<Spec>>,
    /// Dependency graph: Item → set of Items it depends on
    deps: HashMap<Item, HashSet<Item>>,
    /// Reverse dependencies: Item → set of Items that depend on it
    rev_deps: HashMap<Item, HashSet<Item>>,
}

impl Defs {
    /// Create an empty Defs database.
    pub fn empty() -> Self {
        Defs::default()
    }

    /// Return all specifications for all items.
    pub fn all_specifications(&self) -> Vec<(Item, Vec<Spec>)> {
        self.specs.iter().map(|(k, v)| (k.clone(), v.clone())).collect()
    }

    /// Return specifications for a given item.
    pub fn specifications_of(&self, item: &Item) -> Vec<Spec> {
        self.specs.get(item).cloned().unwrap_or_default()
    }

    /// Merge two Defs databases.
    /// Returns Err on conflicts.
    pub fn merge(&self, other: &Defs) -> Result<Defs, String> {
        let mut result = self.clone();
        for (item, specs) in &other.specs {
            for spec in specs {
                result.define(
                    spec.def.as_deref(),
                    &spec.description,
                    item.clone(),
                    spec.lhs.clone(),
                    spec.rhs.clone(),
                )?;
            }
        }
        Ok(result)
    }

    /// Register a new definition. Returns Err if the definition conflicts.
    pub fn define(
        &mut self,
        def: Option<&str>,
        description: &str,
        item: Item,
        lhs: Vec<String>,
        rhs: Vec<Item>,
    ) -> Result<(), String> {
        // 1. Check for duplicate definitions with incompatible type arguments
        if let Some(existing_specs) = self.specs.get(&item) {
            for existing in existing_specs {
                if !Self::disjoint_args(&lhs, &existing.lhs)
                    && let Some(ref def_name) = existing.def {
                        return Err(format!(
                            "Conflicting type arguments for {} '{}': already defined in '{}'",
                            if item.kind == ItemKind::Const { "constant" } else { "type" },
                            item.name,
                            def_name,
                        ));
                    }
            }
        }

        // 2. Check for cycles: new definition must not create a dependency cycle
        // where the item appears in its own transitive dependencies
        if self.would_create_cycle(&item, &rhs) {
            return Err(format!(
                "Cyclic dependency detected for {} '{}'",
                if item.kind == ItemKind::Const { "constant" } else { "type" },
                item.name,
            ));
        }

        // 3. Register the specification
        let spec = Spec {
            def: def.map(|s| s.to_string()),
            description: description.to_string(),
            lhs,
            rhs: rhs.clone(),
        };
        self.specs.entry(item.clone()).or_default().push(spec);

        // 4. Update dependency graphs
        for dep in &rhs {
            self.deps.entry(item.clone()).or_default().insert(dep.clone());
            self.rev_deps.entry(dep.clone()).or_default().insert(item.clone());
        }

        Ok(())
    }

    /// Check whether defining `item` with dependencies `rhs` would create a cycle.
    fn would_create_cycle(&self, item: &Item, rhs: &[Item]) -> bool {
        // For each dependency, check if `item` is already a transitive dependency of it
        let mut visited = HashSet::new();
        for dep in rhs {
            if self.is_transitive_dep(dep, item, &mut visited) {
                return true;
            }
        }
        false
    }

    /// Check if `ancestor` is a transitive dependency of `node`.
    fn is_transitive_dep(&self, node: &Item, ancestor: &Item, visited: &mut HashSet<Item>) -> bool {
        if node == ancestor {
            return true;
        }
        if !visited.insert(node.clone()) {
            return false;
        }
        if let Some(deps) = self.deps.get(node) {
            for dep in deps {
                if self.is_transitive_dep(dep, ancestor, visited) {
                    return true;
                }
            }
        }
        false
    }

    /// Check if two type argument lists are disjoint (compatible).
    fn disjoint_args(a: &[String], b: &[String]) -> bool {
        if a.len() != b.len() {
            return true; // Different arities — always disjoint
        }
        // Different names at same position → disjoint
        a.iter().zip(b.iter()).any(|(x, y)| x != y)
    }

    /// Return all direct dependencies of an item.
    pub fn get_deps(&self, item: &Item) -> Vec<(Vec<String>, Vec<Item>)> {
        self.specs
            .get(item)
            .map(|specs| specs.iter().map(|s| (s.lhs.clone(), s.rhs.clone())).collect())
            .unwrap_or_default()
    }

    /// Compute the list of constant definitions for reporting.
    pub fn dest_constdefs(&self) -> Vec<(String, String)> {
        self.specs
            .iter()
            .filter(|(item, _)| item.kind == ItemKind::Const)
            .flat_map(|(item, specs)| {
                specs.iter().filter_map(move |spec| {
                    spec.def.as_ref().map(|d| (d.clone(), item.name.clone()))
                })
            })
            .collect()
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_define_simple() {
        let mut defs = Defs::empty();
        assert!(defs.define(Some("HOL"), "True", Item::konst("True"), vec![], vec![]).is_ok());
        assert!(defs.define(Some("HOL"), "False", Item::konst("False"), vec![], vec![]).is_ok());
    }

    #[test]
    fn test_define_with_deps() {
        let mut defs = Defs::empty();
        // True: no dependencies
        defs.define(Some("HOL"), "True", Item::konst("True"), vec![], vec![]).unwrap();
        // conj depends on True
        defs.define(
            Some("HOL"),
            "conj",
            Item::konst("HOL.conj"),
            vec![],
            vec![Item::konst("True")],
        )
        .unwrap();
        assert_eq!(defs.get_deps(&Item::konst("HOL.conj")).len(), 1);
    }

    #[test]
    fn test_cycle_detection() {
        let mut defs = Defs::empty();
        // A depends on B
        defs.define(Some("T"), "A", Item::konst("A"), vec![], vec![Item::konst("B")]).unwrap();
        // B depends on A → cycle!
        assert!(
            defs.define(Some("T"), "B", Item::konst("B"), vec![], vec![Item::konst("A")]).is_err()
        );
    }

    #[test]
    fn test_self_cycle() {
        let mut defs = Defs::empty();
        // A depends on A → self-cycle!
        assert!(
            defs.define(Some("T"), "A", Item::konst("A"), vec![], vec![Item::konst("A")]).is_err()
        );
    }

    #[test]
    fn test_merge_no_conflict() {
        let mut d1 = Defs::empty();
        d1.define(Some("A"), "x", Item::konst("x"), vec![], vec![]).unwrap();
        let mut d2 = Defs::empty();
        d2.define(Some("B"), "y", Item::konst("y"), vec![], vec![]).unwrap();
        let merged = d1.merge(&d2).unwrap();
        assert_eq!(merged.all_specifications().len(), 2);
    }

    #[test]
    fn test_type_item() {
        let mut defs = Defs::empty();
        assert!(defs.define(Some("HOL"), "bool", Item::typ("bool"), vec![], vec![]).is_ok());
        assert_eq!(defs.specifications_of(&Item::typ("bool")).len(), 1);
    }
}
