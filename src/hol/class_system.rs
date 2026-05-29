//! Type class system — class, subclass, instance declarations.
//! Corresponds to src/Pure/axclass.ML.
//!
//! ## What this module does
//!
//! Handles:
//! - `class` declarations (already partially done in parse_classes)
//! - `subclass` proofs — add subclass relations
//! - `instance` proofs — prove type class membership
//!
//! ## Architecture
//!
//! ```text
//! class ring = semiring + ab_group_add + ...
//! subclass ring < semiring         → algebra.add_classrel(ring, semiring)
//! instance nat :: semiring         → algebra.add_arity(nat, semiring, [])
//! ```

use crate::core::sorts::Algebra;
use crate::core::term::Term;
use crate::core::thm::{CTerm, ThmKernel};
use crate::core::types::{Sort, Typ, Symbol};
use std::sync::Arc;

// =========================================================================
// Class Instance
// =========================================================================

/// A parsed `instance` declaration.
#[derive(Debug, Clone)]
pub struct InstanceDecl {
    /// Type name (e.g., "nat", "list")
    pub type_name: String,
    /// Class name (e.g., "semiring", "ord")
    pub class_name: String,
    /// Type arguments (e.g., for "list" → 1 argument)
    pub type_args: Vec<String>,
    /// The proof method (e.g., "by intro_classes")
    pub proof: Option<String>,
}

/// A parsed `subclass` declaration.
#[derive(Debug, Clone)]
pub struct SubclassDecl {
    /// The subclass (class being defined/declared)
    pub sub_class: String,
    /// The superclass
    pub super_class: String,
    /// Optional proof
    pub proof: Option<String>,
}

// =========================================================================
// Parse instance/subclass from .thy source
// =========================================================================

/// Parse `instance` declarations from source.
pub fn parse_instances(source: &str) -> Vec<InstanceDecl> {
    let mut results = Vec::new();
    let lines: Vec<&str> = source.lines().collect();

    for line in &lines {
        let t = line.trim();
        if !t.starts_with("instance ") {
            continue;
        }

        let rest = t.strip_prefix("instance ").unwrap().trim();

        // Form: instance type :: class
        if let Some(colon_pos) = rest.find(" :: ") {
            let type_part = rest[..colon_pos].trim();
            let class_part = rest[colon_pos + 4..].trim();

            // Parse type arguments: (type) type_name
            let (type_args, type_name) = if type_part.starts_with('(') {
                if let Some(paren_end) = type_part.find(')') {
                    let args_str = &type_part[1..paren_end];
                    let args: Vec<String> = args_str.split(',').map(|s| s.trim().to_string()).collect();
                    let name = type_part[paren_end + 1..].trim().to_string();
                    (args, name)
                } else {
                    (vec![], type_part.to_string())
                }
            } else {
                (vec![], type_part.to_string())
            };

            // Extract proof if present
            let (class_name, proof) = if let Some(by_pos) = class_part.find(" by ") {
                (class_part[..by_pos].trim().to_string(), Some(class_part[by_pos + 4..].trim().to_string()))
            } else {
                (class_part.to_string(), None)
            };

            results.push(InstanceDecl {
                type_name,
                class_name,
                type_args,
                proof,
            });
        }
    }

    results
}

/// Parse `subclass` declarations from source.
pub fn parse_subclasses(source: &str) -> Vec<SubclassDecl> {
    let mut results = Vec::new();
    let lines: Vec<&str> = source.lines().collect();

    for line in &lines {
        let t = line.trim();
        if !t.starts_with("subclass ") {
            continue;
        }

        let rest = t.strip_prefix("subclass ").unwrap().trim();

        // Form: subclass super_class [by method]
        let (super_class, proof) = if let Some(by_pos) = rest.find(" by ") {
            (rest[..by_pos].trim().to_string(), Some(rest[by_pos + 4..].trim().to_string()))
        } else if rest.ends_with("..") {
            // `subclass foo ..` — omit proof
            (rest[..rest.len()-2].trim().to_string(), None)
        } else {
            (rest.to_string(), None)
        };

        results.push(SubclassDecl {
            sub_class: String::new(), // filled by context (current class)
            super_class,
            proof,
        });
    }

    results
}

// =========================================================================
// Generate theorems from instance/subclass declarations
// =========================================================================

/// Generate theorems for a class instance.
pub fn instance_to_lemmas(
    decl: &InstanceDecl,
) -> Vec<crate::hol::hol_loader::ParsedLemma> {
    let mut lemmas = Vec::new();

    let instance_name = format!("instance_{}_{}", decl.type_name, decl.class_name);
    let instance_term = Term::const_(instance_name.as_str(), Typ::base("prop"));
    let thm = ThmKernel::assume(CTerm::certify(instance_term));

    lemmas.push(crate::hol::hol_loader::ParsedLemma {
        name: format!("{}.{}.instance", decl.type_name, decl.class_name),
        attributes: vec!["instance".to_string()],
        theorem: Arc::new(thm),
        proof_script: decl.proof.clone(),
        alias_for: None,
        source_loc: None,
    });

    lemmas
}

/// Generate theorems for a subclass relation.
pub fn subclass_to_lemmas(
    decl: &SubclassDecl,
) -> Vec<crate::hol::hol_loader::ParsedLemma> {
    let mut lemmas = Vec::new();

    let subclass_name = format!("subclass_{}_subseteq_{}", decl.sub_class, decl.super_class);
    let subclass_term = Term::const_(subclass_name.as_str(), Typ::base("prop"));
    let thm = ThmKernel::assume(CTerm::certify(subclass_term));

    lemmas.push(crate::hol::hol_loader::ParsedLemma {
        name: format!("{}.subclass_{}", decl.sub_class, decl.super_class),
        attributes: vec!["subclass".to_string(), "classrel".to_string()],
        theorem: Arc::new(thm),
        proof_script: decl.proof.clone(),
        alias_for: None,
        source_loc: None,
    });

    lemmas
}

// =========================================================================
// ClassStore — manages class hierarchy
// =========================================================================

/// Global registry of type classes and their relationships.
#[derive(Debug, Clone, Default)]
pub struct ClassStore {
    /// Direct subclass relations: sub → super
    pub classrels: Vec<(String, String)>,
    /// Type instances: type_name → [(class_name, arg_sorts)]
    pub instances: Vec<InstanceDecl>,
}

impl ClassStore {
    pub fn new() -> Self {
        ClassStore::default()
    }

    /// Record a subclass relation.
    pub fn add_classrel(&mut self, sub: &str, sup: &str) {
        self.classrels.push((sub.to_string(), sup.to_string()));
    }

    /// Record an instance.
    pub fn add_instance(&mut self, decl: InstanceDecl) {
        self.instances.push(decl);
    }

    /// Apply all class relations to the algebra.
    pub fn apply_to_algebra(&self, algebra: &mut Algebra) {
        for (sub, sup) in &self.classrels {
            algebra.add_classrel(
                &Symbol::from(sub.as_str()),
                &Symbol::from(sup.as_str()),
            );
        }
        for inst in &self.instances {
            let arg_sorts: Vec<Sort> = inst.type_args.iter()
                .map(|_| Sort::top())
                .collect();
            algebra.add_arity(
                &Symbol::from(inst.type_name.as_str()),
                &Symbol::from(inst.class_name.as_str()),
                arg_sorts,
            );
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
    fn test_parse_instance() {
        let src = "instance nat :: semiring by intro_classes";
        let instances = parse_instances(src);
        assert_eq!(instances.len(), 1);
        assert_eq!(instances[0].type_name, "nat");
        assert_eq!(instances[0].class_name, "semiring");
        assert_eq!(instances[0].proof, Some("intro_classes".to_string()));
    }

    #[test]
    fn test_parse_subclass() {
        let src = "subclass monoid_add";
        let subclasses = parse_subclasses(src);
        assert_eq!(subclasses.len(), 1);
        assert_eq!(subclasses[0].super_class, "monoid_add");
    }

    #[test]
    fn test_parse_instance_with_args() {
        let src = "instance (type) list :: ord";
        let instances = parse_instances(src);
        assert_eq!(instances.len(), 1);
        assert_eq!(instances[0].type_name, "list");
        assert_eq!(instances[0].type_args, vec!["type"]);
        assert_eq!(instances[0].class_name, "ord");
    }

    #[test]
    fn test_class_store() {
        let mut store = ClassStore::new();
        store.add_classrel("order", "ord");
        store.add_instance(InstanceDecl {
            type_name: "nat".to_string(),
            class_name: "ord".to_string(),
            type_args: vec![],
            proof: None,
        });

        let mut algebra = crate::core::sorts::Algebra::pure();
        store.apply_to_algebra(&mut algebra);

        let order_sym = crate::core::types::Symbol::from("order");
        let ord_sym = crate::core::types::Symbol::from("ord");
        assert!(algebra.class_le(&order_sym, &ord_sym));
    }
}
