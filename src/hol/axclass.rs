//! Type class definition — implements Isabelle's `class` mechanism.
//! 
//! In Isabelle, `class C = A + B + fixes f :: ... assumes ...` 
//! is sugar for:
//! 1. A locale with the same structure
//! 2. A sort algebra entry: C is a subclass of A, B
//! 3. An introduction rule: C_def
//!
//! This module bridges `parse_classes`, `locale::LocaleDef`, 
//! and `sorts::Algebra`.

use crate::core::sorts::Algebra;
use crate::core::term::Term;
use crate::core::thm::{CTerm, ThmKernel};
use crate::core::types::{Symbol, Typ};
use std::sync::Arc;

// =========================================================================
// AxClass — a proper type class
// =========================================================================

/// A type class definition with associated locale and algebra data.
#[derive(Debug, Clone)]
pub struct AxClass {
    /// Class name (e.g., "ring", "order")
    pub name: String,
    /// Superclasses (e.g., ["semiring", "ab_group_add"])
    pub superclasses: Vec<String>,
    /// Fixed parameters: (name, type_str)
    pub fixes: Vec<(String, String)>,
    /// Assumptions (axioms): (name, statement)
    pub assumes: Vec<(String, String)>,
}

impl AxClass {
    /// Convert to a LocaleDef (since class = locale).
    pub fn to_locale(&self) -> crate::hol::locale::LocaleDef {
        let fixes: Vec<(String, String, Option<String>)> = self.fixes.iter()
            .map(|(n, t)| (n.clone(), t.clone(), None))
            .collect();
        crate::hol::locale::LocaleDef {
            name: self.name.clone(),
            extends: self.superclasses.clone(),
            fixes,
            assumes: self.assumes.clone(),
            is_typeclass: true,
        }
    }

    /// Update the sort algebra: register the class and its superclass relations.
    pub fn update_algebra(&self, algebra: &mut Algebra) {
        let class_sym = Symbol::from(self.name.as_str());
        let super_syms: Vec<Symbol> = self.superclasses.iter()
            .map(|s| Symbol::from(s.as_str()))
            .collect();
        algebra.add_class(&class_sym, &super_syms);
    }

    /// Generate all class theorems: locale theorems + class definition.
    pub fn generate_theorems(&self) -> Vec<(String, Term, Vec<String>)> {
        let locale = self.to_locale();
        let mut thms = locale.generate_theorems();

        // Add class definition theorem: `OFCLASS('a, ring)`
        let class_def_name = format!("class.{}.def", self.name);
        let class_def_term = Term::const_(class_def_name.as_str(), Typ::base("prop"));
        thms.push((class_def_name, class_def_term, vec!["class_def".to_string()]));

        thms
    }
}

// =========================================================================
// Convert ClassDef (from parser) → AxClass
// =========================================================================

/// Convert a parsed ClassDef into an AxClass.
pub fn classdef_to_axclass(
    name: &str,
    superclasses: &[String],
    fixes: &[(String, String)],
    assumes: &[(String, String)],
) -> AxClass {
    AxClass {
        name: name.to_string(),
        superclasses: superclasses.to_vec(),
        fixes: fixes.to_vec(),
        assumes: assumes.to_vec(),
    }
}

// =========================================================================
// Generate ParsedLemma entries
// =========================================================================

/// Convert an AxClass into ParsedLemma entries for the theorem database.
pub fn axclass_to_lemmas(cls: &AxClass) -> Vec<crate::hol::hol_loader::ParsedLemma> {
    let mut lemmas = Vec::new();

    // Add locale theorems via the locale system
    let locale = cls.to_locale();
    lemmas.extend(crate::hol::locale::locale_to_lemmas(&locale));

    // Add class-specific theorems
    let class_def_name = format!("class.{}.def", cls.name);
    let class_def_term = Term::const_(class_def_name.as_str(), Typ::base("prop"));
    let thm = ThmKernel::assume(CTerm::certify(class_def_term));

    lemmas.push(crate::hol::hol_loader::ParsedLemma {
        name: format!("{}.class_def", cls.name),
        attributes: vec!["class_def".to_string()],
        theorem: Arc::new(thm),
        proof_script: None,
        alias_for: None,
        source_loc: None,
    });

    lemmas
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_axclass_to_locale() {
        let cls = AxClass {
            name: "ring".to_string(),
            superclasses: vec!["semiring".to_string(), "ab_group_add".to_string()],
            fixes: vec![
                ("plus".to_string(), "'a => 'a => 'a".to_string()),
                ("times".to_string(), "'a => 'a => 'a".to_string()),
            ],
            assumes: vec![
                ("distrib".to_string(), "a * (b + c) = a * b + a * c".to_string()),
            ],
        };

        let locale = cls.to_locale();
        assert_eq!(locale.name, "ring");
        assert_eq!(locale.extends.len(), 2);
        assert!(locale.is_typeclass);
    }

    #[test]
    fn test_axclass_algebra() {
        let cls = AxClass {
            name: "order".to_string(),
            superclasses: vec!["ord".to_string()],
            fixes: vec![],
            assumes: vec![],
        };

        let mut algebra = Algebra::pure();
        cls.update_algebra(&mut algebra);

        let order_sym = Symbol::from("order");
        let ord_sym = Symbol::from("ord");
        assert!(algebra.class_le(&order_sym, &ord_sym));
    }

    #[test]
    fn test_axclass_generate_theorems() {
        let cls = AxClass {
            name: "test_class".to_string(),
            superclasses: vec![],
            fixes: vec![("op".to_string(), "'a => 'a".to_string())],
            assumes: vec![("id".to_string(), "op x = x".to_string())],
        };

        let thms = cls.generate_theorems();
        eprintln!("Generated {} theorems:", thms.len());
        for (name, _, _) in &thms {
            eprintln!("  {}", name);
        }
        // Should have: locale theorems + class definition
        assert!(thms.len() >= 3, "Expected >=3, got {}", thms.len());
    }
}
