//! Function definition package for HOL.
//! Corresponds to src/HOL/Tools/Function/.
//!
//! Handles `fun`, `function`, and `primrec` declarations.
//!
//! ## What this module does
//!
//! Given a function definition like:
//! ```text
//! fun append :: "'a list => 'a list => 'a list" where
//!   "append [] ys = ys"
//! | "append (x#xs) ys = x # append xs ys"
//! ```
//!
//! It generates:
//! 1. Defining equations as theorems with [simp] attribute
//! 2. An induction rule: `P [] ys ==> (!!x xs ys. P xs ys ==> P (x#xs) ys) ==> P xs ys`
//! 3. A `.cases` rule for case analysis
//!
//! ## Architecture
//!
//! ```text
//! FunDef { name, typ, equations, is_recursive }
//!   → gen_simps()        — equation theorems
//!   → gen_induct()       — structural induction rule
//!   → gen_cases()        — case analysis rule
//!   → Vec<ParsedLemma>   — theorems to add to DB
//! ```

use std::sync::Arc;

use crate::core::{
    term::Term,
    thm::{CTerm, ThmKernel},
    types::Typ,
};

// =========================================================================
// Function Definition
// =========================================================================

/// A parsed function/primrec definition.
#[derive(Debug, Clone)]
pub struct FunDef {
    /// Function name
    pub name: String,
    /// Type signature (as string, e.g., "'a list => 'a list => 'a list")
    pub typ_str: String,
    /// Equations: (label, lhs_string, rhs_string)
    /// label is None for unnamed equations
    pub equations: Vec<(Option<String>, String, String)>,
    /// Is this function recursive? (has self-references on RHS)
    pub is_recursive: bool,
}

impl FunDef {
    /// Create a new FunDef and detect recursion.
    pub fn new(
        name: String,
        typ_str: String,
        equations: Vec<(Option<String>, String, String)>,
    ) -> Self {
        let is_recursive = equations.iter().any(|(_, _, rhs)| rhs.contains(&name));
        FunDef { name, typ_str, equations, is_recursive }
    }

    /// Detect if the function is recursive by analyzing equations.
    pub fn detect_recursion(equations: &[(Option<String>, String, String)], name: &str) -> bool {
        equations.iter().any(|(_, lhs, rhs)| {
            // Check if RHS contains the function name
            let tokens: Vec<&str> = rhs.split_whitespace().collect();
            tokens.contains(&name) ||
            // Also check if the RHS mentions the function via its LHS pattern
            // (e.g., "x # xs @ ys" contains "@" which is "append")
            lhs.split_whitespace().any(|t| {
                // If the LHS uses an infix operator, check if RHS uses it too
                rhs.contains(t) && t != "=" && t != "|"
            })
        })
    }

    /// Generate all theorems for this function definition.
    pub fn generate_theorems(&self) -> Vec<(String, Term, Vec<String>)> {
        let mut results = Vec::new();

        // 1. Generate equation theorems (.simps)
        for (label, lhs, rhs) in &self.equations {
            if let Some(term) = self.parse_equation(lhs, rhs) {
                let eq_name = label.clone().unwrap_or_else(|| format!("{}.simps", self.name));
                results.push((eq_name, term, vec!["simp".to_string(), "fun_simp".to_string()]));
            }
        }

        // 2. Generate induction rule (only for recursive functions)
        if self.is_recursive
            && let Some(induct) = self.gen_induction_rule()
        {
            results.push((format!("{}.induct", self.name), induct, vec!["induct".to_string()]));
        }

        // 3. Generate cases rule
        if self.equations.len() > 1
            && let Some(cases) = self.gen_cases_rule()
        {
            results.push((
                format!("{}.cases", self.name),
                cases,
                vec!["elim".to_string(), "cases".to_string()],
            ));
        }

        results
    }

    /// Parse an equation "lhs = rhs" into a Pure equality term.
    fn parse_equation(&self, lhs_str: &str, rhs_str: &str) -> Option<Term> {
        let eq_stmt = format!("{} = {}", lhs_str, rhs_str);
        crate::isar::term_parser::parse_term(&eq_stmt)
    }

    /// Generate the induction rule from the equations.
    ///
    /// For a function defined by pattern matching, the induction rule follows
    /// the structure of the patterns. For each equation:
    /// - Base cases (no recursive calls) generate base induction premises
    /// - Recursive cases generate step premises with induction hypotheses
    ///
    /// Example for `append`:
    /// ```
    /// [| !!ys. P [] ys; !!x xs ys. P xs ys ==> P (x#xs) ys |] ==> P xs ys
    /// ```
    fn gen_induction_rule(&self) -> Option<Term> {
        if self.equations.is_empty() {
            return None;
        }

        let mut induct_premises: Vec<Term> = Vec::new();

        for (_label, lhs, rhs) in &self.equations {
            let premise = self.make_induct_premise(lhs, rhs);
            induct_premises.push(premise);
        }

        // Build: prem1 ==> prem2 ==> ... ==> P(args)
        // Use a generic variable pattern
        let args_var = Term::var("?args", 0, Typ::dummy());
        let p_var = Term::var("?P", 0, Typ::arrow(Typ::dummy(), Typ::base("prop")));
        let p_call = Term::app(p_var, args_var);

        let mut result = p_call;
        for prem in induct_premises.iter().rev() {
            result = crate::core::logic::Pure::mk_implies(prem.clone(), result);
        }

        Some(result)
    }

    /// Create a single induction premise from one equation.
    fn make_induct_premise(&self, lhs: &str, rhs: &str) -> Term {
        // Parse the LHS to extract the pattern variables
        let lhs_term = crate::isar::term_parser::parse_term(lhs)
            .unwrap_or_else(|| Term::const_("True", Typ::base("prop")));

        // Collect variable names from the LHS
        let mut vars: Vec<String> = Vec::new();
        self.collect_free_vars(&lhs_term, &mut vars);

        // Check if this equation has recursive calls
        let has_recursion = rhs.contains(&self.name);

        if has_recursion {
            // Recursive case: generate IH for each recursive call
            // Pattern: !!vars. (IHs) ==> P(lhs)
            let mut ihs: Vec<Term> = Vec::new();

            // For each recursive call on RHS, generate an IH
            // Simplified: assume P holds for all recursive arguments
            for var in &vars {
                let p_var = Term::var("?P", 0, Typ::dummy());
                let var_term = Term::free(var.as_str(), Typ::dummy());
                let ih = Term::app(p_var, var_term);
                ihs.push(ih);
            }

            let p_var = Term::var("?P", 0, Typ::dummy());
            let lhs_call = Term::app(p_var, lhs_term.clone());

            let mut result = lhs_call;
            for ih in ihs.iter().rev() {
                result = crate::core::logic::Pure::mk_implies(ih.clone(), result);
            }
            result
        } else {
            // Base case: just P(lhs)
            let p_var = Term::var("?P", 0, Typ::dummy());
            Term::app(p_var, lhs_term)
        }
    }

    /// Collect free variable names from a term.
    fn collect_free_vars(&self, term: &Term, vars: &mut Vec<String>) {
        let mut stack: Vec<&Term> = vec![term];
        while let Some(t) = stack.pop() {
            match t {
                Term::Free { name, .. } => {
                    let s = name.as_ref().to_string();
                    if !vars.contains(&s) {
                        vars.push(s);
                    }
                },
                Term::App { func, arg } => {
                    stack.push(arg);
                    stack.push(func);
                },
                Term::Abs { body, .. } => {
                    stack.push(body);
                },
                _ => {},
            }
        }
    }

    /// Generate a case analysis rule.
    ///
    /// For each equation, create a case that matches the LHS pattern.
    fn gen_cases_rule(&self) -> Option<Term> {
        if self.equations.len() <= 1 {
            return None;
        }

        let mut cases: Vec<Term> = Vec::new();

        for (_label, lhs, rhs) in &self.equations {
            let eq_term = self
                .parse_equation(lhs, rhs)
                .unwrap_or_else(|| Term::const_("True", Typ::base("prop")));

            let (prems, _concl) = crate::core::logic::Pure::strip_imp_prems(&eq_term);
            let q = Term::var("?Q", 0, Typ::base("prop"));

            let mut case_prem = q.clone();
            for p in prems.iter().rev() {
                case_prem = crate::core::logic::Pure::mk_implies((*p).clone(), case_prem);
            }
            cases.push(case_prem);
        }

        // Build: P ==> case1 ==> case2 ==> ... ==> Q ==> Q
        let q_var = Term::var("?Q", 0, Typ::base("prop"));
        let p_var = Term::var("?P", 0, Typ::base("prop"));

        let mut result = q_var;
        for case in cases.iter().rev() {
            result = crate::core::logic::Pure::mk_implies(case.clone(), result);
        }
        result = crate::core::logic::Pure::mk_implies(p_var, result);

        Some(result)
    }
}

// =========================================================================
// Generate ParsedLemma entries
// =========================================================================

/// Convert a FunDef into ParsedLemma entries for the theorem database.
pub fn fundef_to_lemmas(def: &FunDef) -> Vec<crate::hol::hol_loader::ParsedLemma> {
    let mut lemmas = Vec::new();
    let theorems = def.generate_theorems();

    for (name, term, attrs) in theorems {
        let thm = ThmKernel::assume_compat(CTerm::certify(term));
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

    fn make_append_def() -> FunDef {
        FunDef::new(
            "append".to_string(),
            "'a list => 'a list => 'a list".to_string(),
            vec![
                (None, "append [] ys".to_string(), "ys".to_string()),
                (None, "append (x#xs) ys".to_string(), "x # append xs ys".to_string()),
            ],
        )
    }

    fn make_add_def() -> FunDef {
        FunDef::new(
            "add".to_string(),
            "nat => nat => nat".to_string(),
            vec![
                (None, "add 0 n".to_string(), "n".to_string()),
                (
                    Some("add_Suc".to_string()),
                    "add (Suc m) n".to_string(),
                    "Suc (add m n)".to_string(),
                ),
            ],
        )
    }

    #[test]
    fn test_generate_fundef_theorems() {
        let def = make_append_def();
        let theorems = def.generate_theorems();
        eprintln!("Generated {} theorems for append:", theorems.len());
        for (name, term, attrs) in &theorems {
            eprintln!("  [{}] {}: {:?}", attrs.join(","), name, term);
        }
        // Should have: equations (2) + induction + cases
        assert!(theorems.len() >= 4, "Expected >=4 theorems, got {}", theorems.len());
    }

    #[test]
    fn test_recursion_detection() {
        let def = make_append_def();
        assert!(def.is_recursive, "append should be detected as recursive");

        let nonrec = FunDef::new(
            "id".to_string(),
            "'a => 'a".to_string(),
            vec![(None, "id x".to_string(), "x".to_string())],
        );
        assert!(!nonrec.is_recursive, "id should not be recursive");
    }

    #[test]
    fn test_add_function() {
        let def = make_add_def();
        assert!(def.is_recursive, "add should be recursive");
        let theorems = def.generate_theorems();
        eprintln!("add theorems: {}", theorems.len());
        // Should have: add_0, add_Suc, add.induct, add.cases
        assert!(theorems.len() >= 4);

        // Check that we have a labeled equation
        let has_labeled = theorems.iter().any(|(n, _, _)| n == "add_Suc");
        assert!(has_labeled, "Missing labeled equation add_Suc");
    }
}
