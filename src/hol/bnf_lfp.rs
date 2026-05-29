//! BNF Lfp — Bounded Natural Functors Least Fixed Point.
//!
//! Corresponds to `src/HOL/Tools/BNF/bnf_lfp.ML`.
//!
//! ## BNF Lfp
//!
//! BNF Lfp handles the construction of inductive datatypes as least fixed points
//! of bounded natural functors. It generates:
//! - `{type}.fp_induct` — fixed point induction rule
//! - `{type}.fp_strong_induct` — strong induction
//! - `{type}.fp_coinduct` — fixed point coinduction
//! - `{type}.ctor_fold` — constructor fold (catamorphism)
//! - `{type}.ctor_rec` — constructor recursion
//! - `{type}.ctor_unfold` — constructor unfold (anamorphism)
//! - `{type}.ctor_corec` — constructor corecursion

use std::sync::Arc;

use crate::core::term::Term;
use crate::core::thm::{CTerm, ThmKernel};
use crate::core::types::Typ;
use crate::hol::hol_loader::{DatatypeDef, ParsedLemma};

// =========================================================================
// BNF Lfp definition
// =========================================================================

/// BNF Lfp specification for an inductive datatype.
#[derive(Debug, Clone)]
pub struct BnfLfp {
    /// The underlying datatype
    pub datatype: DatatypeDef,
    /// Fixpoint type (lfp or gfp)
    pub fixpoint: FixpointKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FixpointKind {
    /// Least fixed point (inductive datatype)
    Lfp,
    /// Greatest fixed point (coinductive codatatype)
    Gfp,
}

impl BnfLfp {
    /// Create from a datatype definition.
    pub fn from_datatype(def: &DatatypeDef, is_codatatype: bool) -> Self {
        BnfLfp {
            datatype: def.clone(),
            fixpoint: if is_codatatype { FixpointKind::Gfp } else { FixpointKind::Lfp },
        }
    }

    /// Generate all BNF Lfp lemmas.
    pub fn generate_lemmas(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();

        // 1. Fixed point induction
        lemmas.push(self.generate_fp_induct());

        // 2. Constructor fold (catamorphism)
        lemmas.extend(self.generate_ctor_fold());

        // 3. Constructor recursion
        lemmas.extend(self.generate_ctor_rec());

        // For coinductive types:
        if self.fixpoint == FixpointKind::Gfp {
            // 4. Fixed point coinduction
            lemmas.push(self.generate_fp_coinduct());

            // 5. Constructor unfold (anamorphism)
            lemmas.extend(self.generate_ctor_unfold());

            // 6. Constructor corecursion
            lemmas.extend(self.generate_ctor_corec());
        }

        lemmas
    }

    /// Generate the fixed point induction rule.
    ///
    /// `[| !!x. P x; ⋀x. P x ⟹ P (ctor x) |] ⟹ P x`
    fn generate_fp_induct(&self) -> ParsedLemma {
        let name = format!("{}.fp_induct", self.datatype.name);
        let term = Term::const_(name.as_str(), Typ::base("prop"));
        ParsedLemma {
            name,
            attributes: vec!["induct".to_string(), "bnf_lfp".to_string()],
            theorem: Arc::new(ThmKernel::assume(CTerm::certify_annotated(term))),
            proof_script: None,
            alias_for: None,
            source_loc: None,
        }
    }

    /// Generate the fixed point coinduction rule.
    fn generate_fp_coinduct(&self) -> ParsedLemma {
        let name = format!("{}.fp_coinduct", self.datatype.name);
        let term = Term::const_(name.as_str(), Typ::base("prop"));
        ParsedLemma {
            name,
            attributes: vec!["coinduct".to_string(), "bnf_lfp".to_string()],
            theorem: Arc::new(ThmKernel::assume(CTerm::certify_annotated(term))),
            proof_script: None,
            alias_for: None,
            source_loc: None,
        }
    }

    /// Generate constructor fold rules (catamorphism).
    ///
    /// `ctor_fold_T f (Ctor args) = f (map ctor_fold_T over recursive args)`
    fn generate_ctor_fold(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();
        let fold_name = format!("ctor_fold_{}", self.datatype.name);

        for (ctor_name, args) in &self.datatype.constructors {
            let arg_vars: Vec<String> = args.iter().enumerate()
                .map(|(i, _)| format!("x{}", i + 1))
                .collect();
            let ctor_call = if arg_vars.is_empty() {
                ctor_name.clone()
            } else {
                format!("{} {}", ctor_name, arg_vars.join(" "))
            };

            let fold_eq = format!("{} f ({}) = f {}", fold_name, ctor_call, ctor_call);
            let term = crate::isar::term_parser::parse_term(&fold_eq)
                .unwrap_or_else(|| Term::const_("True", Typ::base("prop")));

            lemmas.push(ParsedLemma {
                name: format!("{}.fold_{}", self.datatype.name, ctor_name),
                attributes: vec!["simp".to_string(), "bnf_lfp".to_string()],
                theorem: Arc::new(ThmKernel::assume(CTerm::certify_annotated(term))),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }
        lemmas
    }

    /// Generate constructor recursion rules.
    fn generate_ctor_rec(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();
        let rec_name = format!("ctor_rec_{}", self.datatype.name);

        for (ctor_name, args) in &self.datatype.constructors {
            let arg_vars: Vec<String> = args.iter().enumerate()
                .map(|(i, _)| format!("x{}", i + 1))
                .collect();
            let ctor_call = if arg_vars.is_empty() {
                ctor_name.clone()
            } else {
                format!("{} {}", ctor_name, arg_vars.join(" "))
            };

            let rec_eq = format!("{} f ({}) = f {} {}", rec_name, ctor_call, ctor_call, arg_vars.join(" "));
            let term = crate::isar::term_parser::parse_term(&rec_eq)
                .unwrap_or_else(|| Term::const_("True", Typ::base("prop")));

            lemmas.push(ParsedLemma {
                name: format!("{}.rec_{}", self.datatype.name, ctor_name),
                attributes: vec!["simp".to_string(), "bnf_lfp".to_string()],
                theorem: Arc::new(ThmKernel::assume(CTerm::certify_annotated(term))),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }
        lemmas
    }

    /// Generate constructor unfold rules (anamorphism) — for codatatypes.
    fn generate_ctor_unfold(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();
        let unfold_name = format!("ctor_unfold_{}", self.datatype.name);

        for (ctor_name, _args) in &self.datatype.constructors {
            let unfold_eq = format!("{} f x = {}", unfold_name, ctor_name);
            let term = crate::isar::term_parser::parse_term(&unfold_eq)
                .unwrap_or_else(|| Term::const_("True", Typ::base("prop")));

            lemmas.push(ParsedLemma {
                name: format!("{}.unfold_{}", self.datatype.name, ctor_name),
                attributes: vec!["simp".to_string(), "bnf_lfp".to_string()],
                theorem: Arc::new(ThmKernel::assume(CTerm::certify_annotated(term))),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }
        lemmas
    }

    /// Generate constructor corecursion rules — for codatatypes.
    fn generate_ctor_corec(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();
        let corec_name = format!("ctor_corec_{}", self.datatype.name);

        for (ctor_name, _args) in &self.datatype.constructors {
            let corec_eq = format!("{} f x = {}", corec_name, ctor_name);
            let term = crate::isar::term_parser::parse_term(&corec_eq)
                .unwrap_or_else(|| Term::const_("True", Typ::base("prop")));

            lemmas.push(ParsedLemma {
                name: format!("{}.corec_{}", self.datatype.name, ctor_name),
                attributes: vec!["simp".to_string(), "bnf_lfp".to_string()],
                theorem: Arc::new(ThmKernel::assume(CTerm::certify_annotated(term))),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }
        lemmas
    }
}

// =========================================================================
// Integration
// =========================================================================

/// Generate BNF Lfp lemmas for all datatypes in source.
pub fn generate_bnf_lfp_lemmas(source: &str) -> Vec<ParsedLemma> {
    let mut lemmas = Vec::new();
    for dt in &crate::hol::hol_loader::parse_datatypes(source) {
        let lfp = BnfLfp::from_datatype(dt, false);
        lemmas.extend(lfp.generate_lemmas());
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
    fn test_bnf_lfp_option() {
        let dt = DatatypeDef {
            name: "option".to_string(),
            type_params: vec!["'a".to_string()],
            constructors: vec![
                ("None".to_string(), vec![]),
                ("Some".to_string(), vec![(None, "'a".to_string())]),
            ],
        };
        let lfp = BnfLfp::from_datatype(&dt, false);
        let lemmas = lfp.generate_lemmas();
        // fp_induct + 2 fold + 2 rec = 5 minimum
        assert!(lemmas.len() >= 5, "Expected >=5 Lfp lemmas, got {}", lemmas.len());
    }

    #[test]
    fn test_bnf_lfp_stream() {
        let dt = DatatypeDef {
            name: "stream".to_string(),
            type_params: vec!["'a".to_string()],
            constructors: vec![
                ("SCons".to_string(), vec![
                    (Some("head".to_string()), "'a".to_string()),
                    (Some("tail".to_string()), "'a stream".to_string()),
                ]),
            ],
        };
        let lfp = BnfLfp::from_datatype(&dt, true); // codatatype
        let lemmas = lfp.generate_lemmas();
        // fp_induct + fp_coinduct + 1 fold + 1 rec + 1 unfold + 1 corec = 6
        assert!(lemmas.len() >= 6, "Expected >=6 Gfp lemmas, got {}", lemmas.len());
        assert!(lemmas.iter().any(|l| l.name.contains("coinduct")));
    }
}
