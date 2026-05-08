//! Axiomatic type classes — class definitions with axioms.
//!
//! Corresponds to `src/Pure/axclass.ML`.
//!
//! Type classes in Isabelle can carry axioms: e.g., class `order`
//! has axioms like `x <= x` (reflexivity). The axclass module
//! manages class definitions with their associated axioms.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use super::term::Term;
use super::types::Symbol;
use super::types::{Sort, Typ, ClassAlgebra};

// =========================================================================
// Class definition
// =========================================================================

/// A type class definition with its axioms.
#[derive(Clone, Debug)]
pub struct ClassDef {
    /// Class name
    pub name: Symbol,
    /// Super classes
    pub super_classes: Vec<Symbol>,
    /// The type variable representing an instance: `'a::class`
    pub class_var: Typ,
    /// Axioms for this class (terms over the class variable)
    pub axioms: Vec<Term>,
}

// =========================================================================
// Axiomatic class manager
// =========================================================================

/// Manages type class definitions and their axioms.
pub struct AxClass {
    classes: BTreeMap<Symbol, ClassDef>,
    algebra: ClassAlgebra,
}

impl AxClass {
    pub fn empty() -> Self {
        AxClass { classes: BTreeMap::new(), algebra: ClassAlgebra::empty() }
    }

    /// Define a new class.
    pub fn define_class(&mut self, def: ClassDef) {
        for sup in &def.super_classes {
            self.algebra.add_classrel(Arc::clone(&def.name), Arc::clone(sup));
        }
        self.classes.insert(Arc::clone(&def.name), def);
    }

    /// Get a class definition.
    pub fn get(&self, name: &str) -> Option<&ClassDef> {
        self.classes.get(name)
    }

    /// Get the class algebra.
    pub fn algebra(&self) -> &ClassAlgebra { &self.algebra }

    /// Check if a type satisfies a sort under this class system.
    pub fn of_sort(&self, typ: &Typ, sort: &Sort) -> bool {
        match typ {
            Typ::TFree { sort: s, .. } => {
                sort.iter().all(|c| {
                    s.iter().any(|sc|
                        self.algebra.is_subclass(sc, c))
                })
            }
            Typ::Type { name: _, args: _ } => {
                // Type constructors satisfy sort if declared
                true // simplified
            }
            Typ::TVar { .. } => true,
        }
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_define_class() {
        let mut ax = AxClass::empty();
        let def = ClassDef {
            name: Arc::from("order"),
            super_classes: vec![Arc::from("type")],
            class_var: Typ::free("'a", Sort::singleton(intern("order"))),
            axioms: vec![],
        };
        ax.define_class(def);
        assert!(ax.get("order").is_some());
    }
}
