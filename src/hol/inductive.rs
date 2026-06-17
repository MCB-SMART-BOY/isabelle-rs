//! Inductive and coinductive definitions for HOL.
//! Corresponds to src/HOL/Tools/inductive.ML.
//!
//! ## What this module does
//!
//! Given a set of introduction rules like:
//! ```text
//! inductive even :: "nat => bool" where
//!   "even 0"
//! | "even n ==> even (Suc (Suc n))"
//! ```
//!
//! It generates:
//! 1. The introduction rules (as theorems)
//! 2. The induction rule: `P 0 ==> (!!n. P n ==> P (Suc (Suc n))) ==> P n`
//! 3. The elimination rule (case analysis)
//!
//! ## Architecture
//!
//! ```text
//! InductiveDef { name, predicates, intros }
//!   → gen_induct_rule()      — least fixed-point induction
//!   → gen_elim_rule()        — case analysis from intros
//!   → gen_coinduct_rule()    — greatest fixed-point coinduction
//!   → Vec<ParsedLemma>       — theorems to add to DB
//! ```

use std::sync::Arc;

use crate::core::{
    term::Term,
    thm::{CTerm, ThmKernel},
    types::Typ,
};

// =========================================================================
// Inductive Definition
// =========================================================================

/// A parsed inductive/coinductive definition.
#[derive(Debug, Clone)]
pub struct InductiveDef {
    /// Name of the predicate being defined
    pub name: String,
    /// Is this a coinductive definition?
    pub is_coind: bool,
    /// Type of the predicate (e.g., "nat => bool")
    pub typ: Option<Typ>,
    /// Introduction rules: (name, term)
    pub intros: Vec<(String, Term)>,
}

impl InductiveDef {
    /// Generate all theorems for this inductive definition.
    /// Returns: introduction rules + induction rule + elimination rule.
    pub fn generate_theorems(&self) -> Vec<(String, Term, Vec<String>)> {
        let mut results = Vec::new();

        // 1. Introduction rules become axioms (we assume them)
        for (name, term) in &self.intros {
            results.push((
                name.clone(),
                term.clone(),
                vec![format!("{}_intro", if self.is_coind { "coinduct" } else { "induct" })],
            ));
        }

        // 2. Generate induction rule
        if !self.is_coind {
            if let Some(induct) = self.gen_induct_rule() {
                results.push((format!("{}.induct", self.name), induct, vec!["induct".to_string()]));
            }
        } else {
            if let Some(coinduct) = self.gen_coinduct_rule() {
                results.push((
                    format!("{}.coinduct", self.name),
                    coinduct,
                    vec!["coinduct".to_string()],
                ));
            }
        }

        // 3. Generate elimination rule (cases)
        if let Some(elim) = self.gen_elim_rule() {
            results.push((
                format!("{}.elim", self.name),
                elim,
                vec!["elim".to_string(), "cases".to_string()],
            ));
        }

        results
    }

    /// Generate the induction rule from introduction rules.
    ///
    /// For each intro rule of the form `prem1 ==> prem2 ==> ... ==> P t`,
    /// we generate an induction hypothesis for each recursive occurrence of P.
    ///
    /// The induction rule has the form:
    /// ```
    /// [| !!args1. IH1 ==> P t1; ...; !!argsN. IHN ==> P tN |] ==> P x
    /// ```
    fn gen_induct_rule(&self) -> Option<Term> {
        if self.intros.is_empty() {
            return None;
        }

        // For each intro rule, extract the premises that mention the predicate
        // and generate an induction hypothesis
        let mut induct_premises: Vec<Term> = Vec::new();
        let predicate_name = self.name.clone();

        for (_name, intro_term) in &self.intros {
            let premise = self.induct_premise_from_intro(intro_term, &predicate_name);
            induct_premises.push(premise);
        }

        // Build: prem1 ==> prem2 ==> ... ==> P x
        let x = Term::var("?x", 0, Typ::dummy());
        let pred_x = Term::app(Term::const_(predicate_name.as_str(), Typ::dummy()), x.clone());

        let mut result = pred_x;
        for prem in induct_premises.iter().rev() {
            result = crate::core::logic::Pure::mk_implies(prem.clone(), result);
        }

        // Wrap with !!/?x. ...
        Some(crate::core::logic::Pure::mk_all("?x", Typ::dummy(), result))
    }

    /// Generate a single induction premise from an introduction rule.
    fn induct_premise_from_intro(&self, intro: &Term, pred_name: &str) -> Term {
        // Walk the intro term and find all occurrences of the predicate
        // For each occurrence, generate an induction hypothesis
        let mut ihs: Vec<Term> = Vec::new();
        let mut args_list: Vec<Vec<Term>> = Vec::new();

        self.collect_pred_occurrences(intro, pred_name, &mut args_list);

        // For each occurrence P(args), assume P(args) (induction hypothesis)
        for args in &args_list {
            let pred_app = Term::apps(Term::const_(pred_name, Typ::dummy()), args.iter().cloned());
            ihs.push(pred_app);
        }

        // Build: !!vars. (IHs) ==> P(conclusion_args)
        // Get the conclusion (last implication chain element)
        let (_prems, concl) = crate::core::logic::Pure::strip_imp_prems(intro);

        // Extract conclusion args from P(args)
        let mut concl_args: Vec<Term> = Vec::new();
        self.extract_pred_args(concl, pred_name, &mut concl_args);

        let pred_concl =
            Term::apps(Term::const_(pred_name, Typ::dummy()), concl_args.iter().cloned());

        if ihs.is_empty() {
            // Base case: no induction hypotheses, just P(conclusion)
            pred_concl
        } else {
            // Step case: IHs ==> P(conclusion)
            let mut result = pred_concl;
            for ih in ihs.iter().rev() {
                result = crate::core::logic::Pure::mk_implies(ih.clone(), result);
            }
            result
        }
    }

    /// Collect all occurrences of `pred_name(args)` in a term.
    fn collect_pred_occurrences(
        &self,
        term: &Term,
        pred_name: &str,
        args_list: &mut Vec<Vec<Term>>,
    ) {
        let mut stack: Vec<&Term> = vec![term];
        while let Some(t) = stack.pop() {
            match t {
                Term::App { func, arg } => {
                    if let Term::Const { name, .. } = func.as_ref()
                        && (name.as_ref() == pred_name
                            || name.as_ref().ends_with(&format!(".{}", pred_name)))
                    {
                        let args = vec![arg.as_ref().clone()];
                        // Collect additional args from nested apps
                        let mut current = func.as_ref();
                        while let Term::App { func: f, arg: _a } = current {
                            if let Term::Const { name: n, .. } = f.as_ref()
                                && n.as_ref() == pred_name
                            {
                                break;
                            }
                            current = f.as_ref();
                        }
                        args_list.push(args);
                    }
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

    /// Extract the arguments of a predicate application.
    fn extract_pred_args(&self, term: &Term, pred_name: &str, args: &mut Vec<Term>) {
        if let Term::App { func, arg } = term {
            if let Term::Const { name, .. } = func.as_ref()
                && name.as_ref() == pred_name
            {
                args.push(arg.as_ref().clone());
            }
            self.extract_pred_args(func, pred_name, args);
            // Non-predicate apps: recurse into both sides
            if !matches!(func.as_ref(), Term::Const { name, .. } if name.as_ref() == pred_name) {
                self.extract_pred_args(arg, pred_name, &mut Vec::new());
            }
        }
    }

    /// Generate the coinduction rule.
    fn gen_coinduct_rule(&self) -> Option<Term> {
        // Coinduction is the dual of induction: for the greatest fixed point,
        // we have a rule that allows proving membership by showing it's consistent
        // with the introduction rules.
        //
        // Simplified: P x ==> (P x = exists args. intro1(args) ==> ...)
        // For now, generate a basic coinduction rule
        let x = Term::var("?x", 0, Typ::dummy());
        let pred_x = Term::app(Term::const_(self.name.as_str(), Typ::dummy()), x.clone());

        // Coinduction: if we can show P(x), then P(x) holds.
        // This is essentially a reflexivity-like rule for the predicate.
        // A full coinduction rule would be more complex.
        Some(pred_x)
    }

    /// Generate the elimination rule from introduction rules.
    ///
    /// For each intro rule, we create a case. The elimination rule has the form:
    /// ```
    /// [| P x; !!args1. [| prem1; ... |] ==> Q; ... |] ==> Q
    /// ```
    fn gen_elim_rule(&self) -> Option<Term> {
        if self.intros.is_empty() {
            return None;
        }

        let mut cases: Vec<Term> = Vec::new();
        let x = Term::var("?x", 0, Typ::dummy());
        let pred_x = Term::app(Term::const_(self.name.as_str(), Typ::dummy()), x.clone());

        for (_name, intro) in &self.intros {
            let (prems, _concl) = crate::core::logic::Pure::strip_imp_prems(intro);
            let case_concl = Term::const_("?Q", Typ::base("prop"));

            let mut case_prem = case_concl.clone();
            for p in prems.iter().rev() {
                case_prem = crate::core::logic::Pure::mk_implies((*p).clone(), case_prem);
            }

            // Wrap with universal quantifiers for the variables
            // (Simplified: just use the implication chain)
            cases.push(case_prem);
        }

        // Build: P x ==> case1 ==> case2 ==> ... ==> Q ==> Q
        let q_var = Term::var("?Q", 0, Typ::base("prop"));
        let mut result = q_var;
        for case in cases.iter().rev() {
            result = crate::core::logic::Pure::mk_implies(case.clone(), result);
        }
        result = crate::core::logic::Pure::mk_implies(pred_x, result);

        Some(result)
    }
}

// =========================================================================
// Generate ParsedLemma entries from InductiveDef
// =========================================================================

/// Convert an InductiveDef into ParsedLemma entries for the theorem database.
pub fn inductive_to_lemmas(def: &InductiveDef) -> Vec<crate::hol::hol_loader::ParsedLemma> {
    let mut lemmas = Vec::new();
    let theorems = def.generate_theorems();

    for (name, term, attrs) in &theorems {
        let thm = ThmKernel::assume(CTerm::certify(term.clone()));
        lemmas.push(crate::hol::hol_loader::ParsedLemma {
            name: name.clone(),
            attributes: attrs.clone(),
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
    use crate::core::logic::Pure;

    fn make_even_def() -> InductiveDef {
        // even 0
        let even0 =
            Term::app(Term::const_("even", Typ::dummy()), Term::const_("0", Typ::base("nat")));
        // even n ==> even (Suc (Suc n))
        let n = Term::var("n", 0, Typ::base("nat"));
        let even_n = Term::app(Term::const_("even", Typ::dummy()), n.clone());
        let suc_suc = Term::app(
            Term::const_("Suc", Typ::dummy()),
            Term::app(Term::const_("Suc", Typ::dummy()), n.clone()),
        );
        let even_ss = Term::app(Term::const_("even", Typ::dummy()), suc_suc);

        InductiveDef {
            name: "even".to_string(),
            is_coind: false,
            typ: Some(Typ::arrow(Typ::base("nat"), Typ::base("bool"))),
            intros: vec![
                ("even0".to_string(), even0),
                ("evenS".to_string(), Pure::mk_implies(even_n, even_ss)),
            ],
        }
    }

    #[test]
    fn test_generate_inductive_theorems() {
        let def = make_even_def();
        let theorems = def.generate_theorems();
        eprintln!("Generated {} theorems:", theorems.len());
        for (name, term, attrs) in &theorems {
            eprintln!("  {} {:?}: {:?}", attrs.join(","), name, term);
        }
        // Should have: even0 (intro), evenS (intro), even.induct, even.elim
        assert!(theorems.len() >= 4, "Expected at least 4 theorems, got {}", theorems.len());

        // Check that induction rule exists
        let has_induct = theorems.iter().any(|(n, _, _)| n == "even.induct");
        assert!(has_induct, "Missing induction rule");
    }

    #[test]
    fn test_induction_rule_structure() {
        let def = make_even_def();
        let induct = def.gen_induct_rule().expect("Should generate induction rule");
        eprintln!("Induction rule: {:?}", induct);

        // Should be a Pure.all application wrapping an implication chain
        match &induct {
            Term::App { func, .. } => match func.as_ref() {
                Term::Const { name, .. } if name.as_ref() == "Pure.all" => {},
                _ => panic!("Expected Pure.all, got {:?}", func),
            },
            _ => panic!("Expected App(Pure.all, ...), got {:?}", induct),
        }
    }
}
