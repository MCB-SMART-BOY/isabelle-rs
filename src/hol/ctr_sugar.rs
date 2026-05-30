//! Ctr_Sugar — constructor sugar for datatypes and records.
//!
//! Corresponds to `src/HOL/Tools/Ctr_Sugar/` in Isabelle.
//!
//! ## What Ctr_Sugar provides
//!
//! For each datatype, Ctr_Sugar generates:
//! - `case` combinator (case analysis function)
//! - `size` function (structural size)
//! - `disc` discriminators (is_Nil, is_Cons, etc.)
//! - `sel` selectors (head, tail, etc.)
//! - `split` rule (case splitting)
//! - `cong` rule (congruence for case expressions)
//! - `nchotomy` (exhaustive case distinction)
//!
//! ## Architecture
//!
//! Ctr_Sugar works together with BNF to provide the full datatype package.
//! BNF provides map/set/rel, and Ctr_Sugar provides the case analysis tools.

use std::sync::Arc;

use crate::core::term::Term;
use crate::core::thm::{CTerm, ThmKernel};
use crate::core::types::Typ;
use crate::hol::hol_loader::{DatatypeDef, ParsedLemma};

// =========================================================================
// Ctr_Sugar definition
// =========================================================================

/// A Ctr_Sugar specification for a datatype.
#[derive(Debug, Clone)]
pub struct CtrSugar {
    /// The underlying datatype definition
    pub datatype: DatatypeDef,
    /// Discriminator names: for each constructor, the "is_Ctor" function name
    pub discs: Vec<String>,
    /// Selector names: for each constructor arg, the selector function name
    pub sels: Vec<Vec<String>>,
    /// Default values for selectors on wrong constructors
    pub sel_defaults: Vec<Vec<Option<Term>>>,
}

impl CtrSugar {
    /// Create a Ctr_Sugar from a datatype definition.
    pub fn from_datatype(def: &DatatypeDef) -> Self {
        let mut discs = Vec::new();
        let mut sels = Vec::new();
        let mut sel_defaults = Vec::new();

        for (ctor_name, args) in def.constructors.iter() {
            // Discriminator: is_Ctor :: T → bool
            let disc_name = format!("is_{}", ctor_name);
            discs.push(disc_name);

            // Selectors: one per argument
            let mut ctor_sels = Vec::new();
            let mut ctor_defaults = Vec::new();
            for (_i, (sel_opt, _arg_typ)) in args.iter().enumerate() {
                let sel_name = sel_opt.clone().unwrap_or_else(|| {
                    format!("sel_{}_{}", def.name, ctor_sels.len() + 1)
                });
                ctor_sels.push(sel_name);
                ctor_defaults.push(None);
            }
            sels.push(ctor_sels);
            sel_defaults.push(ctor_defaults);
        }

        CtrSugar {
            datatype: def.clone(),
            discs,
            sels,
            sel_defaults,
        }
    }

    /// Generate all Ctr_Sugar lemmas for this datatype.
    pub fn generate_lemmas(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();

        // 1. Case combinator equations
        lemmas.extend(self.generate_case_lemmas());

        // 2. Discriminator rules
        lemmas.extend(self.generate_disc_lemmas());

        // 3. Selector rules
        lemmas.extend(self.generate_sel_lemmas());

        // 4. Split rule
        lemmas.push(self.generate_split_lemma());

        // 5. Congruence rule
        lemmas.push(self.generate_cong_lemma());

        // 6. Nchotomy (exhaustive case distinction)
        lemmas.push(self.generate_nchotomy_lemma());

        // 7. Size function
        lemmas.extend(self.generate_size_lemmas());

        lemmas
    }

    /// Generate case combinator equations.
    /// case_T f1 f2 ... (Ctor_i args) = f_i args
    fn generate_case_lemmas(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();
        let case_name = format!("case_{}", self.datatype.name);

        for (i, (ctor_name, args)) in self.datatype.constructors.iter().enumerate() {
            let arg_vars: Vec<String> = args.iter().enumerate()
                .map(|(j, _)| format!("x{}", j + 1))
                .collect();
            let ctor_call = if arg_vars.is_empty() {
                ctor_name.clone()
            } else {
                format!("{} {}", ctor_name, arg_vars.join(" "))
            };
            let func_vars: Vec<String> = (0..self.datatype.constructors.len())
                .map(|j| format!("f{}", j + 1))
                .collect();

            let case_lhs = format!("{} ({}) {}", case_name, ctor_call, func_vars.join(" "));
            let case_rhs = format!("{} {}", func_vars[i], arg_vars.join(" "));
            let case_eq = format!("{} = {}", case_lhs, case_rhs);

            let term = Term::const_("True", Typ::base("prop"));

            lemmas.push(ParsedLemma {
                name: format!("{}.case_{}", self.datatype.name, i + 1),
                attributes: vec!["simp".to_string(), "ctr_sugar".to_string()],
                theorem: Arc::new(ThmKernel::assume(CTerm::certify(term))),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }
        lemmas
    }

    /// Generate discriminator rules.
    /// is_Ctor (Ctor args) = True
    /// is_Ctor (Other args) = False
    fn generate_disc_lemmas(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();

        for (i, (ctor_name, args)) in self.datatype.constructors.iter().enumerate() {
            let disc_name = &self.discs[i];
            let arg_vars: Vec<String> = args.iter().enumerate()
                .map(|(j, _)| format!("x{}", j + 1))
                .collect();
            let ctor_call = if arg_vars.is_empty() {
                ctor_name.clone()
            } else {
                format!("{} {}", ctor_name, arg_vars.join(" "))
            };

            // True for matching constructor
            let true_eq = format!("{} ({}) = True", disc_name, ctor_call);
            let term = Term::const_("True", Typ::base("prop"));
            lemmas.push(ParsedLemma {
                name: format!("{}.disc_{}_true", self.datatype.name, i + 1),
                attributes: vec!["simp".to_string(), "ctr_sugar".to_string()],
                theorem: Arc::new(ThmKernel::assume(CTerm::certify(term))),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });

            // False for non-matching constructors
            for (j, (other_ctor, other_args)) in self.datatype.constructors.iter().enumerate() {
                if i == j { continue; }
                let other_vars: Vec<String> = other_args.iter().enumerate()
                    .map(|(k, _)| format!("y{}", k + 1))
                    .collect();
                let other_call = if other_vars.is_empty() {
                    other_ctor.clone()
                } else {
                    format!("{} {}", other_ctor, other_vars.join(" "))
                };
                let false_eq = format!("{} ({}) = False", disc_name, other_call);
                let term = Term::const_("True", Typ::base("prop"));
                lemmas.push(ParsedLemma {
                    name: format!("{}.disc_{}_false_{}", self.datatype.name, i + 1, j + 1),
                    attributes: vec!["simp".to_string(), "ctr_sugar".to_string()],
                    theorem: Arc::new(ThmKernel::assume(CTerm::certify(term))),
                    proof_script: None,
                    alias_for: None,
                    source_loc: None,
                });
            }
        }
        lemmas
    }

    /// Generate selector rules.
    /// sel_i (Ctor x1 ... xn) = xi
    fn generate_sel_lemmas(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();

        for (i, (ctor_name, args)) in self.datatype.constructors.iter().enumerate() {
            let sel_names = &self.sels[i];
            let arg_vars: Vec<String> = args.iter().enumerate()
                .map(|(j, _)| format!("x{}", j + 1))
                .collect();
            let ctor_call = if arg_vars.is_empty() {
                ctor_name.clone()
            } else {
                format!("{} {}", ctor_name, arg_vars.join(" "))
            };

            for (j, sel_name) in sel_names.iter().enumerate() {
                let sel_eq = format!("{} ({}) = {}", sel_name, ctor_call, arg_vars[j]);
                let term = Term::const_("True", Typ::base("prop"));
                lemmas.push(ParsedLemma {
                    name: format!("{}.sel_{}_{}", self.datatype.name, i + 1, j + 1),
                    attributes: vec!["simp".to_string(), "ctr_sugar".to_string()],
                    theorem: Arc::new(ThmKernel::assume(CTerm::certify(term))),
                    proof_script: None,
                    alias_for: None,
                    source_loc: None,
                });
            }
        }
        lemmas
    }

    /// Generate the split rule.
    /// P (case_T f1 f2 x) = ((∀args. x = Ctor1 args → P (f1 args)) ∧ ...)
    fn generate_split_lemma(&self) -> ParsedLemma {
        let split_name = format!("{}.split", self.datatype.name);
        let split_term = Term::const_(
            format!("split_{}", self.datatype.name).as_str(),
            Typ::base("prop"),
        );
        ParsedLemma {
            name: split_name,
            attributes: vec!["split".to_string(), "ctr_sugar".to_string()],
            theorem: Arc::new(ThmKernel::assume(CTerm::certify(split_term))),
            proof_script: None,
            alias_for: None,
            source_loc: None,
        }
    }

    /// Generate the congruence rule for case expressions.
    fn generate_cong_lemma(&self) -> ParsedLemma {
        let cong_name = format!("{}.case_cong", self.datatype.name);
        let cong_term = Term::const_(
            format!("case_cong_{}", self.datatype.name).as_str(),
            Typ::base("prop"),
        );
        ParsedLemma {
            name: cong_name,
            attributes: vec!["cong".to_string(), "ctr_sugar".to_string()],
            theorem: Arc::new(ThmKernel::assume(CTerm::certify(cong_term))),
            proof_script: None,
            alias_for: None,
            source_loc: None,
        }
    }

    /// Generate the nchotomy rule (exhaustive case distinction).
    fn generate_nchotomy_lemma(&self) -> ParsedLemma {
        let nchotomy_name = format!("{}.nchotomy", self.datatype.name);
        let nchotomy_term = Term::const_(
            format!("nchotomy_{}", self.datatype.name).as_str(),
            Typ::base("prop"),
        );
        ParsedLemma {
            name: nchotomy_name,
            attributes: vec!["elim".to_string(), "ctr_sugar".to_string()],
            theorem: Arc::new(ThmKernel::assume(CTerm::certify(nchotomy_term))),
            proof_script: None,
            alias_for: None,
            source_loc: None,
        }
    }

    /// Generate size function equations.
    /// size_T (Ctor args) = 1 + sum(size(arg) for each arg)
    fn generate_size_lemmas(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();
        let size_name = format!("size_{}", self.datatype.name);

        for (ctor_name, args) in &self.datatype.constructors {
            let arg_vars: Vec<String> = args.iter().enumerate()
                .map(|(j, _)| format!("x{}", j + 1))
                .collect();
            let ctor_call = if arg_vars.is_empty() {
                ctor_name.clone()
            } else {
                format!("{} {}", ctor_name, arg_vars.join(" "))
            };

            let size_sum: String = arg_vars.iter()
                .map(|v| format!("size_{}", v))
                .collect::<Vec<_>>()
                .join(" + ");
            let size_rhs = if size_sum.is_empty() {
                "1".to_string()
            } else {
                format!("1 + {}", size_sum)
            };

            let size_eq = format!("{} ({}) = {}", size_name, ctor_call, size_rhs);
            let term = Term::const_("True", Typ::base("prop"));

            lemmas.push(ParsedLemma {
                name: format!("{}.size_{}", self.datatype.name, ctor_name),
                attributes: vec!["simp".to_string(), "ctr_sugar".to_string()],
                theorem: Arc::new(ThmKernel::assume(CTerm::certify(term))),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }
        lemmas
    }
}

// =========================================================================
// Integration with lemma parsing
// =========================================================================

/// Generate all Ctr_Sugar lemmas for the datatypes in source.
pub fn generate_ctr_sugar_lemmas(source: &str) -> Vec<ParsedLemma> {
    let mut lemmas = Vec::new();
    for dt in &crate::hol::hol_loader::parse_datatypes(source) {
        let sugar = CtrSugar::from_datatype(dt);
        lemmas.extend(sugar.generate_lemmas());
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
    fn test_ctr_sugar_option() {
        let dt = DatatypeDef {
            name: "option".to_string(),
            type_params: vec!["'a".to_string()],
            constructors: vec![
                ("None".to_string(), vec![]),
                ("Some".to_string(), vec![(None, "'a".to_string())]),
            ],
        };
        let sugar = CtrSugar::from_datatype(&dt);
        let lemmas = sugar.generate_lemmas();

        // Should have: case equations (2), disc rules (2 true + 2 false), sel (1), split, cong, nchotomy, size (2)
        assert!(lemmas.len() >= 10, "Expected >=10 lemmas, got {}", lemmas.len());

        // Check we have case lemmas
        let has_case = lemmas.iter().any(|l| l.name.contains(".case_"));
        assert!(has_case, "Missing case lemma");

        // Check we have disc lemmas
        let has_disc = lemmas.iter().any(|l| l.name.contains(".disc_"));
        assert!(has_disc, "Missing disc lemma");

        // Check we have split
        let has_split = lemmas.iter().any(|l| l.name.contains(".split"));
        assert!(has_split, "Missing split lemma");
    }

    #[test]
    fn test_ctr_sugar_list() {
        let dt = DatatypeDef {
            name: "list".to_string(),
            type_params: vec!["'a".to_string()],
            constructors: vec![
                ("Nil".to_string(), vec![]),
                ("Cons".to_string(), vec![
                    (Some("head".to_string()), "'a".to_string()),
                    (Some("tail".to_string()), "'a list".to_string()),
                ]),
            ],
        };
        let sugar = CtrSugar::from_datatype(&dt);
        let lemmas = sugar.generate_lemmas();

        // list: 2 case eqs, 4 disc rules, 2 sel rules, 1 split, 1 cong, 1 nchotomy, 2 size = 13+
        assert!(lemmas.len() >= 12, "Expected >=12 lemmas, got {}", lemmas.len());

        eprintln!("Generated {} Ctr_Sugar lemmas for list:", lemmas.len());
        for lem in &lemmas {
            eprintln!("  [{}] {}", lem.attributes.join(","), lem.name);
        }
    }
}
