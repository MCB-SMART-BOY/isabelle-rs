//! Rule cases — case annotations for Isar proof rules.
//!
//! Corresponds to `src/Pure/Isar/rule_cases.ML`.
//!
//! ## Core Concepts
//!
//! - **Case names**: named proof cases (e.g., `Nil`, `Cons`) for structured induction
//! - **Consumes**: how many premises a rule uses before producing the conclusion
//! - **Case conclusions**: named sub-conclusions within a case

use std::collections::HashMap;

// =========================================================================
// Rule case
// =========================================================================

/// A named case for structured induction and case analysis.
#[derive(Debug, Clone)]
pub struct RuleCase {
    /// Case name (e.g., "Nil", "Cons", "base", "step")
    pub name: String,
    /// Fixed variables introduced by this case
    pub fixes: Vec<String>,
    /// Assumption names and their formulas
    pub assumes: Vec<(String, Vec<String>)>,
    /// Sub-cases (for nested induction)
    pub cases: Vec<RuleCase>,
}

impl RuleCase {
    pub fn new(name: impl Into<String>) -> Self {
        RuleCase {
            name: name.into(),
            fixes: Vec::new(),
            assumes: Vec::new(),
            cases: Vec::new(),
        }
    }
}

// =========================================================================
// Case info
// =========================================================================

/// Information about the cases in a rule.
#[derive(Debug, Clone, Default)]
pub struct CaseInfo {
    /// Named cases with their assumption names
    pub case_names: Vec<(String, Vec<String>)>,
    /// How many premises the rule consumes
    pub consumes: usize,
    /// Case conclusions
    pub case_conclusions: HashMap<String, Vec<String>>,
    /// Whether cases are "open" (variables not fixed)
    pub cases_open: bool,
}

impl CaseInfo {
    pub fn new() -> Self {
        CaseInfo::default()
    }

    /// Set the number of premises consumed by this rule.
    pub fn with_consumes(mut self, n: usize) -> Self {
        self.consumes = n;
        self
    }

    /// Add case names.
    pub fn with_cases(mut self, names: Vec<(String, Vec<String>)>) -> Self {
        self.case_names = names;
        self
    }

    /// Get the case names as a flat list.
    pub fn case_name_list(&self) -> Vec<&str> {
        self.case_names.iter().map(|(n, _)| n.as_str()).collect()
    }
}

// =========================================================================
// Case name parser
// =========================================================================

/// Parse case names from a theorem name.
///
/// Convention: `lemma "foo[case_names Nil Cons]"`
/// The case names are "Nil" and "Cons".
pub fn parse_case_names(attrs: &[String]) -> Vec<String> {
    for attr in attrs {
        if let Some(names) = attr.strip_prefix("case_names ") {
            return names.split_whitespace().map(|s| s.to_string()).collect();
        }
    }
    vec![]
}

/// Parse the `consumes` attribute.
///
/// `[consumes 1]` means the rule consumes 1 premise.
pub fn parse_consumes(attrs: &[String]) -> usize {
    for attr in attrs {
        if let Some(n) = attr.strip_prefix("consumes ") {
            return n.trim().parse().unwrap_or(1);
        }
    }
    0
}

// =========================================================================
// Case construction from induction rules
// =========================================================================

/// Construct rule cases from an induction rule's premises.
///
/// For `list.induct`:
/// ```
/// [| P Nil; !!x xs. P xs ==> P (Cons x xs) |] ==> P xs
/// ```
/// Creates cases: `[Nil, Cons]`
pub fn make_cases_from_induct(
    rule_premises: &[String],
    case_names: &[String],
) -> Vec<RuleCase> {
    let mut cases = Vec::new();

    for (i, prem) in rule_premises.iter().enumerate() {
        let name = case_names.get(i)
            .cloned()
            .unwrap_or_else(|| format!("case_{}", i + 1));

        let mut case = RuleCase::new(name.clone());

        // Extract fixed variables from the premise:
        // "!!x y. P x y ==> Q x y" → fixes: [x, y], assumes: ["P x y"]
        let fixes_and_assumes = extract_fixes_assumes(prem);
        case.fixes = fixes_and_assumes.0;
        case.assumes = vec![("IH".to_string(), fixes_and_assumes.1)];

        cases.push(case);
    }

    cases
}

/// Extract fixed variables and assumptions from a premise.
///
/// Input: "!!x y. P x y ==> Q x y"
/// Returns: (["x", "y"], ["P x y"])
fn extract_fixes_assumes(prem: &str) -> (Vec<String>, Vec<String>) {
    let mut fixes = Vec::new();
    let mut assumes = Vec::new();

    // Strip "!!x y." prefix
    let rest = prem.trim();
    if rest.starts_with("!!") {
        if let Some(dot_pos) = rest.find('.') {
            let binders = &rest[2..dot_pos];
            for b in binders.split_whitespace() {
                fixes.push(b.to_string());
            }
            // The rest is the assumption
            assumes.push(rest[dot_pos+1..].trim().to_string());
        }
    } else {
        assumes.push(rest.to_string());
    }

    (fixes, assumes)
}

// =========================================================================
// Case application
// =========================================================================

/// Apply case bindings to a proof state.
///
/// When entering case "Cons" of an induction:
/// - Fix variables x, xs
/// - Assume induction hypothesis: P xs
/// - Goal becomes: P (Cons x xs)
pub fn apply_case(
    _case: &RuleCase,
    _proof_context: &mut crate::isar::proof_context::IsarContext,
) {
    // Fix variables
    for fix in &_case.fixes {
        // Use a default type — actual type comes from the goal
        _proof_context.fix(fix, crate::core::types::Typ::base("'a"));
    }
    // Note: full implementation requires typing from the goal
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_case_names() {
        let names = parse_case_names(&["case_names Nil Cons".to_string()]);
        assert_eq!(names, vec!["Nil", "Cons"]);
    }

    #[test]
    fn test_parse_consumes() {
        assert_eq!(parse_consumes(&["consumes 1".to_string()]), 1);
        assert_eq!(parse_consumes(&["consumes 2".to_string()]), 2);
        assert_eq!(parse_consumes(&["simp".to_string()]), 0);
    }

    #[test]
    fn test_extract_fixes_assumes() {
        let (fixes, assumes) = extract_fixes_assumes("!!x y. P x y ==> Q x y");
        assert_eq!(fixes, vec!["x", "y"]);
        assert_eq!(assumes, vec!["P x y ==> Q x y"]);
    }

    #[test]
    fn test_make_cases_from_induct() {
        let prems = vec![
            "P Nil".to_string(),
            "!!x xs. P xs ==> P (Cons x xs)".to_string(),
        ];
        let cases = make_cases_from_induct(&prems, &["Nil".to_string(), "Cons".to_string()]);
        assert_eq!(cases.len(), 2);
        assert_eq!(cases[0].name, "Nil");
        assert_eq!(cases[1].name, "Cons");
        assert_eq!(cases[1].fixes, vec!["x", "xs"]);
    }

    #[test]
    fn test_case_info() {
        let info = CaseInfo::new()
            .with_consumes(1)
            .with_cases(vec![
                ("Nil".to_string(), vec![]),
                ("Cons".to_string(), vec!["IH".to_string()]),
            ]);
        assert_eq!(info.consumes, 1);
        assert_eq!(info.case_name_list(), vec!["Nil", "Cons"]);
    }
}
