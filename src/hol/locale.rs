//! Locale system — Isabelle's module system for mathematical theories.
//! Corresponds to src/Pure/Isar/locale.ML.
//!
//! ## What this module does
//!
//! A locale is a named context with fixed variables and assumptions:
//! ```text
//! locale partial_order =
//!   fixes le :: "'a => 'a => bool" (infixl "\<sqsubseteq>" 50)
//!   assumes refl: "x \<sqsubseteq> x"
//!     and antisym: "x \<sqsubseteq> y ==> y \<sqsubseteq> x ==> x = y"
//!     and trans: "x \<sqsubseteq> y ==> y \<sqsubseteq> z ==> x \<sqsubseteq> z"
//! ```
//!
//! Locales support:
//! - Inheritance: `locale linear_order = partial_order + ...`
//! - Interpretation: `interpretation nat_order: partial_order "(\<le>)"`
//! - Sublocale: `sublocale linear_order < order`
//!
//! ## Architecture
//!
//! ```text
//! LocaleDef { name, extends, fixes, assumptions }
//!   → gen_locale_thms()  — instantiated locale theorems
//!   → Interpretation     — locale activation
//! ```

use std::{collections::HashMap, sync::Arc};

use crate::core::{
    term::Term,
    thm::{CTerm, ThmKernel},
    types::Typ,
};

// =========================================================================
// Locale Definition
// =========================================================================

/// A parsed locale declaration.
#[derive(Debug, Clone)]
pub struct LocaleDef {
    /// Locale name
    pub name: String,
    /// Parent locales (extended by this locale)
    pub extends: Vec<String>,
    /// Fixed variables: (name, type_str, mixfix)
    pub fixes: Vec<(String, String, Option<String>)>,
    /// Assumptions: (name, statement_str)
    pub assumes: Vec<(String, String)>,
    /// Is this a typeclass? (locale + sort constraint)
    pub is_typeclass: bool,
}

impl LocaleDef {
    /// Generate theorems for this locale.
    /// Returns locale assumptions as named theorems.
    pub fn generate_theorems(&self) -> Vec<(String, Term, Vec<String>)> {
        let mut results = Vec::new();

        // Each assumption becomes a named theorem in the locale context
        for (name, stmt) in &self.assumes {
            if let Some(term) = crate::isar::term_parser::parse_term(stmt) {
                let thm_name = if name.is_empty() {
                    format!("{}.axiom", self.name)
                } else {
                    format!("{}.{}", self.name, name)
                };
                results.push((thm_name, term, vec!["locale".to_string()]));
            }
        }

        // Generate locale intro rules
        if !self.assumes.is_empty()
            && let Some(intro) = self.gen_intro_rule()
        {
            results.push((
                format!("{}.intro", self.name),
                intro,
                vec!["intro".to_string(), "locale_intro".to_string()],
            ));
        }

        results
    }

    /// Generate the locale introduction rule.
    ///
    /// Combines all locale assumptions into a single rule:
    /// `[| assm1; assm2; ... |] ==> locale_predicate args`
    fn gen_intro_rule(&self) -> Option<Term> {
        if self.assumes.is_empty() {
            return None;
        }

        let mut prems: Vec<Term> = Vec::new();
        for (_name, stmt) in &self.assumes {
            if let Some(term) = crate::isar::term_parser::parse_term(stmt) {
                prems.push(term);
            }
        }

        // Build the locale predicate
        let pred_name = format!("{}.locale", self.name);
        let pred = Term::const_(pred_name.as_str(), Typ::base("prop"));

        let mut result = pred;
        for p in prems.iter().rev() {
            result = crate::core::logic::Pure::mk_implies(p.clone(), result);
        }

        Some(result)
    }
}

// =========================================================================
// Locale Store
// =========================================================================

/// Global store of locale definitions.
#[derive(Debug, Clone, Default)]
pub struct LocaleStore {
    /// Locale name → definition
    pub locales: HashMap<String, LocaleDef>,
}

impl LocaleStore {
    pub fn new() -> Self {
        LocaleStore::default()
    }

    /// Register a locale definition.
    pub fn register(&mut self, def: LocaleDef) {
        self.locales.insert(def.name.clone(), def);
    }

    /// Get a locale definition by name.
    pub fn get(&self, name: &str) -> Option<&LocaleDef> {
        self.locales.get(name)
    }

    /// Check if a locale is defined.
    pub fn has(&self, name: &str) -> bool {
        self.locales.contains_key(name)
    }

    /// Get all locale names.
    pub fn names(&self) -> Vec<&String> {
        self.locales.keys().collect()
    }
}

// =========================================================================
// Locale Interpretation
// =========================================================================

/// Represents a locale interpretation: applying a locale's structure
/// to concrete types/terms.
#[derive(Debug, Clone)]
pub struct Interpretation {
    /// Optional name for this interpretation
    pub name: Option<String>,
    /// The locale being interpreted
    pub locale: String,
    /// Instantiation: parameter name → concrete term
    pub params: HashMap<String, Term>,
    /// Type instantiation: type variable → concrete type
    pub type_params: HashMap<String, Typ>,
}

impl Interpretation {
    /// Create a new interpretation.
    pub fn new(locale: String) -> Self {
        Interpretation { name: None, locale, params: HashMap::new(), type_params: HashMap::new() }
    }

    /// Set the prefix name for this interpretation.
    pub fn with_name(mut self, name: &str) -> Self {
        self.name = Some(name.to_string());
        self
    }

    /// Add a parameter instantiation.
    pub fn param(mut self, name: &str, term: Term) -> Self {
        self.params.insert(name.to_string(), term);
        self
    }

    /// Instantiate a locale theorem by substituting the parameters.
    pub fn instantiate(&self, theorem: &Term, locale_def: &LocaleDef) -> Option<Term> {
        let mut result = theorem.clone();

        // Substitute fixed parameters with concrete terms
        for (fix_name, _fix_type, _) in &locale_def.fixes {
            if let Some(concrete) = self.params.get(fix_name) {
                result = substitute_param(&result, fix_name, concrete);
            }
        }

        Some(result)
    }
}

/// Substitute a parameter name with a concrete term in a given term.
fn substitute_param(term: &Term, param_name: &str, replacement: &Term) -> Term {
    match term {
        Term::Free { name, typ } if name.as_ref() == param_name => replacement.clone(),
        Term::Free { .. } | Term::Const { .. } | Term::Bound(_) | Term::Var { .. } => term.clone(),
        Term::Abs { name, typ, body } => {
            Term::abs(name.clone(), typ.clone(), substitute_param(body, param_name, replacement))
        },
        Term::App { func, arg } => Term::app(
            substitute_param(func, param_name, replacement),
            substitute_param(arg, param_name, replacement),
        ),
    }
}

// =========================================================================
// Parse locale declarations from .thy source
// =========================================================================

/// Parse `locale` declarations from .thy source.
pub fn parse_locales(source: &str) -> Vec<LocaleDef> {
    let mut results = Vec::new();
    let lines: Vec<&str> = source.lines().collect();
    let mut i = 0;

    while i < lines.len() {
        let t = lines[i].trim();
        if !t.starts_with("locale ") {
            i += 1;
            continue;
        }

        let rest = t.strip_prefix("locale ").unwrap().trim();

        // Parse: name = parent1 + parent2 + ...
        let (name, extends) = if let Some(eq_pos) = rest.find('=') {
            let name = rest[..eq_pos].trim().to_string();
            let after = rest[eq_pos + 1..].trim();
            let extends: Vec<String> =
                after.split('+').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect();
            (name, extends)
        } else {
            (rest.to_string(), Vec::new())
        };

        i += 1;

        // Collect locale body: fixes and assumes
        let mut fixes: Vec<(String, String, Option<String>)> = Vec::new();
        let mut assumes: Vec<(String, String)> = Vec::new();
        let mut current_section = "";

        while i < lines.len() {
            let body_line = lines[i].trim();
            if body_line.is_empty() {
                i += 1;
                continue;
            }

            // Detect section headers
            if body_line.starts_with("fixes ") {
                current_section = "fixes";
                parse_locale_fixes(body_line.strip_prefix("fixes ").unwrap(), &mut fixes);
                i += 1;
                continue;
            }
            if body_line.starts_with("assumes ") {
                current_section = "assumes";
                parse_locale_assumes(body_line.strip_prefix("assumes ").unwrap(), &mut assumes);
                i += 1;
                continue;
            }

            // "and" continuation lines
            if body_line.starts_with("and ") && current_section == "fixes" {
                parse_locale_fixes(body_line.strip_prefix("and ").unwrap(), &mut fixes);
                i += 1;
                continue;
            }
            if body_line.starts_with("and ") && current_section == "assumes" {
                parse_locale_assumes(body_line.strip_prefix("and ").unwrap(), &mut assumes);
                i += 1;
                continue;
            }

            // Stop at next command or keyword
            if body_line.starts_with("lemma ")
                || body_line.starts_with("theorem ")
                || body_line.starts_with("locale ")
                || body_line.starts_with("begin")
                || body_line.starts_with("end")
                || body_line.starts_with("interpretation ")
                || body_line.starts_with("sublocale ")
            {
                break;
            }

            // Otherwise, treat as continuation of current section
            if current_section == "assumes" {
                parse_locale_assumes(body_line, &mut assumes);
            }
            i += 1;
        }

        results.push(LocaleDef { name, extends, fixes, assumes, is_typeclass: false });
    }

    results
}

/// Parse a fixes clause: `x :: 'a => bool` or `le :: "'a => 'a => bool" (infixl ...)`
fn parse_locale_fixes(fixes_str: &str, fixes: &mut Vec<(String, String, Option<String>)>) {
    for fix_part in fixes_str.split(" and ") {
        let fix_part = fix_part.trim();
        if fix_part.is_empty() {
            continue;
        }

        // Extract name and type
        if let Some(colon_pos) = fix_part.find("::") {
            let name = fix_part[..colon_pos].trim().to_string();
            let after = fix_part[colon_pos + 2..].trim();

            // Extract mixfix if present: `(infixl ...)`
            let (typ_str, mixfix) = if let Some(paren_pos) = after.find('(') {
                let typ = after[..paren_pos].trim().to_string();
                let mixfix = Some(after[paren_pos..].trim().to_string());
                (typ, mixfix)
            } else {
                (after.to_string(), None)
            };

            fixes.push((name, typ_str, mixfix));
        }
    }
}

/// Parse an assumes clause: `name: "statement"` or `"statement"`
fn parse_locale_assumes(assm_str: &str, assumes: &mut Vec<(String, String)>) {
    let assm_str = assm_str.trim();
    if assm_str.is_empty() {
        return;
    }

    // Multiple assumptions separated by "and"
    for part in assm_str.split(" and ") {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }

        if let Some(colon_pos) = part.find(':') {
            let name = part[..colon_pos].trim().to_string();
            let stmt = part[colon_pos + 1..].trim().trim_matches('"').to_string();
            assumes.push((name, stmt));
        } else if part.starts_with('"') {
            let stmt = part.trim_matches('"').to_string();
            let name = format!("assm_{}", assumes.len() + 1);
            assumes.push((name, stmt));
        }
    }
}

// =========================================================================
// Generate ParsedLemma entries
// =========================================================================

/// Convert locale definitions into ParsedLemma entries.
pub fn locale_to_lemmas(def: &LocaleDef) -> Vec<crate::hol::hol_loader::ParsedLemma> {
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

    #[test]
    fn test_parse_simple_locale() {
        let src = r#"
locale partial_order =
  fixes le :: "'a => 'a => bool"
  assumes refl: "le x x"
    and antisym: "le x y ==> le y x ==> x = y"
    and trans: "le x y ==> le y z ==> le x z"
"#;
        let locs = parse_locales(src);
        assert_eq!(locs.len(), 1, "Should find one locale");
        let loc = &locs[0];
        assert_eq!(loc.name, "partial_order");
        assert_eq!(loc.fixes.len(), 1);
        assert_eq!(loc.fixes[0].0, "le");
        assert_eq!(loc.assumes.len(), 3);
    }

    #[test]
    fn test_parse_locale_with_extends() {
        let src = r#"
locale linear_order = partial_order +
  assumes linear: "le x y | le y x"
"#;
        let locs = parse_locales(src);
        assert_eq!(locs.len(), 1);
        let loc = &locs[0];
        assert_eq!(loc.name, "linear_order");
        assert_eq!(loc.extends, vec!["partial_order"]);
        assert_eq!(loc.assumes.len(), 1);
    }

    #[test]
    fn test_generate_locale_theorems() {
        let def = LocaleDef {
            name: "test_locale".to_string(),
            extends: vec![],
            fixes: vec![("x".to_string(), "'a".to_string(), None)],
            assumes: vec![
                ("refl".to_string(), "x = x".to_string()),
                ("sym".to_string(), "x = y ==> y = x".to_string()),
            ],
            is_typeclass: false,
        };
        let thms = def.generate_theorems();
        eprintln!("Generated {} theorems:", thms.len());
        for (name, _term, _attrs) in &thms {
            eprintln!("  {}", name);
        }
        // Should have: test_locale.refl, test_locale.sym, test_locale.intro
        assert!(thms.len() >= 3, "Expected >=3 theorems, got {}", thms.len());
    }

    #[test]
    fn test_interpretation() {
        let loc = LocaleDef {
            name: "order".to_string(),
            extends: vec![],
            fixes: vec![("le".to_string(), "'a => 'a => bool".to_string(), None)],
            assumes: vec![("refl".to_string(), "le x x".to_string())],
            is_typeclass: false,
        };

        let interp = Interpretation::new("order".to_string())
            .with_name("nat")
            .param("le", Term::const_("less_eq", Typ::dummy()));

        let refl_term = crate::isar::term_parser::parse_term("le x x").unwrap();
        let instantiated = interp.instantiate(&refl_term, &loc).unwrap();
        eprintln!("Original: {:?}", refl_term);
        eprintln!("Instantiated: {:?}", instantiated);
    }

    #[test]
    fn test_locale_store() {
        let mut store = LocaleStore::new();
        let def = LocaleDef {
            name: "order".to_string(),
            extends: vec![],
            fixes: vec![],
            assumes: vec![("refl".to_string(), "x = x".to_string())],
            is_typeclass: false,
        };
        store.register(def);
        assert!(store.has("order"));
        assert!(!store.has("nonexistent"));
    }
}
