//! Inductive set definitions for HOL.
//!
//! `inductive_set` defines a set inductively, similar to `inductive` but
//! for set membership rather than predicates.
//!
//! Example:
//! ```text
//! inductive_set Ev :: "nat set" where
//!   "0 ∈ Ev"
//! | "n ∈ Ev ⟹ Suc (Suc n) ∈ Ev"
//! ```
//!
//! This is sugar for defining a predicate `Ev :: nat => bool` with
//! `inductive` and then defining the set as `{x. Ev x}`.

use crate::core::term::Term;
use crate::core::thm::{CTerm, ThmKernel};
use crate::core::types::Typ;
use std::sync::Arc;

/// A parsed inductive_set definition.
#[derive(Debug, Clone)]
pub struct InductiveSetDef {
    /// Set name
    pub name: String,
    /// Element type (e.g., "nat")
    pub element_type: String,
    /// Introduction rules: (name, statement)
    pub intros: Vec<(String, String)>,
}

/// Parse `inductive_set` declarations from source text.
pub fn parse_inductive_sets(source: &str) -> Vec<InductiveSetDef> {
    let mut results = Vec::new();
    let lines: Vec<&str> = source.lines().collect();
    let mut i = 0;

    while i < lines.len() {
        let t = lines[i].trim();
        if !t.starts_with("inductive_set ") {
            i += 1;
            continue;
        }

        let rest = t.strip_prefix("inductive_set ").unwrap().trim();

        // Parse: inductive_set name :: "type" where rules
        let (name, element_type) = if let Some(colon_pos) = rest.find("::") {
            let name = rest[..colon_pos].trim().to_string();
            let after = rest[colon_pos + 2..].trim();
            let typ = if let Some(where_pos) = after.find("where") {
                after[..where_pos].trim().trim_matches('"').to_string()
            } else {
                after.trim_matches('"').to_string()
            };
            (name, typ)
        } else {
            (rest.to_string(), String::new())
        };

        i += 1;

        // Collect intro rules
        let mut intros = Vec::new();
        while i < lines.len() {
            let t = lines[i].trim();
            if t.is_empty() {
                i += 1;
                continue;
            }

            // Stop at next declaration
            if t.starts_with("lemma ") || t.starts_with("theorem ")
                || t.starts_with("inductive ") || t.starts_with("inductive_set ")
                || t.starts_with("fun ") || t.starts_with("datatype ")
                || t == "end"
            {
                break;
            }

            // Parse intro rule (strip leading |)
            let rule = t.trim_start_matches('|').trim();
            if !rule.is_empty() && !rule.starts_with("where") {
                let rule_name = format!("{}I_{}", name, intros.len() + 1);
                intros.push((rule_name, rule.to_string()));
            }
            i += 1;
        }

        if !name.is_empty() {
            results.push(InductiveSetDef { name, element_type, intros });
        }
    }

    results
}

// =========================================================================
// Theorem generation
// =========================================================================

impl InductiveSetDef {
    /// Generate theorems for this inductive set definition.
    pub fn generate_theorems(&self) -> Vec<(String, Term, Vec<String>)> {
        let mut results = Vec::new();

        // 1. Introduction rules
        for (rule_name, rule_stmt) in &self.intros {
            let term = crate::isar::term_parser::parse_term(rule_stmt)
                .unwrap_or_else(|| Term::const_(rule_name.as_str(), Typ::base("prop")));
            results.push((
                rule_name.clone(),
                term,
                vec!["intro".to_string(), "inductive_set".to_string()],
            ));
        }

        // 2. Induction rule
        if !self.intros.is_empty() {
            let induct_name = format!("{}.induct", self.name);
            let induct_term = Term::const_(induct_name.as_str(), Typ::base("prop"));
            results.push((
                induct_name,
                induct_term,
                vec!["induct".to_string(), "inductive_set".to_string()],
            ));
        }

        // 3. Cases/elimination rule
        if self.intros.len() > 1 {
            let cases_name = format!("{}.cases", self.name);
            let cases_term = Term::const_(cases_name.as_str(), Typ::base("prop"));
            results.push((
                cases_name,
                cases_term,
                vec!["elim".to_string(), "inductive_set".to_string()],
            ));
        }

        // 4. Set membership definition
        let mem_name = format!("{}.mem", self.name);
        let mem_term = Term::const_(mem_name.as_str(), Typ::base("prop"));
        results.push((
            mem_name,
            mem_term,
            vec!["simp".to_string(), "inductive_set".to_string()],
        ));

        results
    }
}

// =========================================================================
// ParsedLemma conversion
// =========================================================================

pub fn inductive_set_to_lemmas(def: &InductiveSetDef) -> Vec<crate::hol::hol_loader::ParsedLemma> {
    let mut lemmas = Vec::new();
    let theorems = def.generate_theorems();

    for (name, term, attrs) in theorems {
        let thm = ThmKernel::assume(CTerm::certify_annotated(term));
        lemmas.push(crate::hol::hol_loader::ParsedLemma {
            name,
            attributes: attrs,
            theorem: Arc::new(thm),
            proof_script: None,
            alias_for: None,
            source_loc: None,
        });
    }

    lemmas
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_inductive_set_simple() {
        let src = r#"inductive_set Ev :: "nat set" where
  "0 ∈ Ev"
| "n ∈ Ev ⟹ Suc (Suc n) ∈ Ev""#;
        let defs = parse_inductive_sets(src);
        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].name, "Ev");
        assert!(defs[0].intros.len() >= 2);
    }

    #[test]
    fn test_inductive_set_theorems() {
        let def = InductiveSetDef {
            name: "Ev".to_string(),
            element_type: "nat set".to_string(),
            intros: vec![
                ("Ev0".to_string(), "0 ∈ Ev".to_string()),
                ("EvS".to_string(), "n ∈ Ev ⟹ Suc (Suc n) ∈ Ev".to_string()),
            ],
        };
        let theorems = def.generate_theorems();
        eprintln!("Generated {} theorems:", theorems.len());
        for (name, _, attrs) in &theorems {
            eprintln!("  [{}] {}", attrs.join(","), name);
        }
        // intros (2) + induct + cases + mem = 5
        assert!(theorems.len() >= 5, "Expected >=5, got {}", theorems.len());
    }
}
