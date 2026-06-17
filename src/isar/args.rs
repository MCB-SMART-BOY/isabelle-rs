//! Method argument parsing — corresponds to Isabelle's src/Pure/Isar/args.ML.
//!
//! Provides parser combinators for method arguments:
//! - Keyword parsers: `add`, `del`, `colon`, `bang`, `only`
//! - Goal specification: `[1]`, `[2-4]`, `[!]`
//! - Modifier clause extraction: `add: thm1 thm2`, `del: thm3`, `only: thm4`
//! - Theorem name parsing with `[OF ...]` suffix support
//!
//! Naming follows Isabelle/ML conventions for easy cross-reference.

#![allow(non_snake_case)]

use crate::core::thm::Thm;
use std::sync::Arc;

// ============================================================================
// MethodArgs — parsed method arguments
// ============================================================================

/// Parsed arguments for a method invocation.
/// Examples:
/// - `simp add: foo del: bar` → add_names=["foo"], del_names=["bar"]
/// - `induct rule: baz arbitrary: x y` → rule_name=Some("baz"), arbitrary=["x", "y"]
/// - `auto intro: a dest: b` → intro_names=["a"], dest_names=["b"]
#[derive(Debug, Default, Clone)]
pub struct MethodArgs {
    /// Theorem names to add (from `add: name1 name2 ...`)
    pub add_names: Vec<String>,
    /// Theorem names to delete (from `del: name1 name2 ...`)
    pub del_names: Vec<String>,
    /// Whether `only:` was specified — use ONLY these rules, no DB defaults
    pub only_mode: bool,
    /// `rule: name` — explicit rule name
    pub rule_name: Option<String>,
    /// `arbitrary: x y z` — variables to generalize over
    pub arbitrary: Vec<String>,
    /// `intro: thm1 thm2` — intro rules
    pub intro_names: Vec<String>,
    /// `elim: thm1 thm2` — elimination rules
    pub elim_names: Vec<String>,
    /// `dest: thm1 thm2` — destruction rules
    pub dest_names: Vec<String>,
    /// `simp: thm1 thm2` — simp rules (as modifier in auto/force)
    pub simp_names: Vec<String>,
    /// Target goal specification, e.g. `[1]`, `[2-4]`, `[!]` (all)
    pub goal_spec: Option<GoalSpec>,
}

/// Goal specification for method targeting.
#[derive(Debug, Clone)]
pub enum GoalSpec {
    /// Apply to a single subgoal: `[1]`
    Single(usize),
    /// Apply to a range of subgoals: `[2-4]`
    Range(usize, usize),
    /// Apply to all subgoals from i onward: `[3-]`
    From(usize),
    /// Apply to all subgoals: `[!]`
    All,
}

impl MethodArgs {
    /// Create empty args.
    pub fn new() -> Self {
        MethodArgs::default()
    }

    /// Quick check: are there any arguments at all?
    pub fn is_empty(&self) -> bool {
        self.add_names.is_empty()
            && self.del_names.is_empty()
            && !self.only_mode
            && self.rule_name.is_none()
            && self.arbitrary.is_empty()
            && self.intro_names.is_empty()
            && self.elim_names.is_empty()
            && self.dest_names.is_empty()
            && self.simp_names.is_empty()
            && self.goal_spec.is_none()
    }

    /// Resolve add_names to actual theorems from the DB.
    pub fn resolve_add(&self, db: &crate::hol::hol_loader::HolTheoremDb) -> Vec<Arc<Thm>> {
        resolve_names(&self.add_names, db)
    }

    /// Resolve del_names to actual theorems from the DB.
    pub fn resolve_del(&self, db: &crate::hol::hol_loader::HolTheoremDb) -> Vec<Arc<Thm>> {
        resolve_names(&self.del_names, db)
    }
}

// ============================================================================
// Args — parser combinators
// ============================================================================

pub struct Args;

impl Args {
    // -- Keyword matchers --

    /// Match the keyword `add`.
    pub fn add() -> &'static str {
        "add"
    }
    /// Match the keyword `del`.
    pub fn del() -> &'static str {
        "del"
    }
    /// Match the keyword `only`.
    pub fn only() -> &'static str {
        "only"
    }
    /// Match the keyword `rule`.
    pub fn rule() -> &'static str {
        "rule"
    }
    /// Match the keyword `arbitrary`.
    pub fn arbitrary() -> &'static str {
        "arbitrary"
    }
    /// Match the keyword `intro`.
    pub fn intro() -> &'static str {
        "intro"
    }
    /// Match the keyword `elim`.
    pub fn elim() -> &'static str {
        "elim"
    }
    /// Match the keyword `dest`.
    pub fn dest() -> &'static str {
        "dest"
    }
    /// Match the keyword `simp`.
    pub fn simp() -> &'static str {
        "simp"
    }

    /// List of all known modifier keywords used in method arguments.
    pub fn modifier_keywords() -> &'static [&'static str] {
        &[
            "add:",
            "del:",
            "only:",
            "rule:",
            "arbitrary:",
            "intro:",
            "elim:",
            "dest:",
            "simp:",
            "iff:",
        ]
    }

    // -- Goal specification parsing --

    /// Parse a goal specification from a string like `[1]`, `[2-4]`, `[3-]`, `[!]`.
    /// Returns None if no goal spec found.
    pub fn parse_goal_spec(s: &str) -> Option<GoalSpec> {
        let s = s.trim();
        if s == "[!]" {
            return Some(GoalSpec::All);
        }
        let inner = s.strip_prefix('[')?.strip_suffix(']')?.trim();
        if inner.is_empty() {
            return None;
        }
        if let Some((from, to)) = inner.split_once('-') {
            let from: usize = from.trim().parse().ok()?;
            if to.is_empty() {
                Some(GoalSpec::From(from))
            } else {
                let to: usize = to.trim().parse().ok()?;
                Some(GoalSpec::Range(from, to))
            }
        } else {
            let n: usize = inner.trim().parse().ok()?;
            Some(GoalSpec::Single(n))
        }
    }

    // -- Modifier clause extraction --

    /// Extract a named clause from a method argument string.
    /// E.g., `extract_clause("simp add: foo del: bar", "add:")` → `Some("foo")`.
    /// Returns the string between the keyword and the next keyword.
    pub fn extract_clause<'a>(method_str: &'a str, keyword: &str) -> Option<&'a str> {
        let rest = method_str.split_once(keyword)?.1.trim();
        // Find the end: either another modifier keyword or end of string
        let end = find_next_keyword(rest);
        let value = rest[..end].trim();
        if value.is_empty() { None } else { Some(value) }
    }

    /// Parse all modifiers from a method string into a MethodArgs.
    /// Handles: `add:`, `del:`, `only:`, `rule:`, `arbitrary:`
    pub fn parse_modifiers(method_str: &str) -> MethodArgs {
        let mut args = MethodArgs::new();
        if method_str.is_empty() {
            return args;
        }

        let s = method_str.trim();
        // Parse goal spec first (if present at start)
        let s = if s.starts_with('[') {
            if let Some(end) = s.find(']') {
                let spec = &s[..=end];
                if let Some(gs) = Self::parse_goal_spec(spec) {
                    args.goal_spec = Some(gs);
                }
                s[end + 1..].trim()
            } else {
                s
            }
        } else {
            s
        };

        // Extract each modifier clause
        if let Some(names) = Self::extract_clause(s, "add:") {
            args.add_names = split_thm_names(names);
        }
        if let Some(names) = Self::extract_clause(s, "del:") {
            args.del_names = split_thm_names(names);
        }
        if s.contains("only:") {
            args.only_mode = true;
            if let Some(names) = Self::extract_clause(s, "only:") {
                args.add_names = split_thm_names(names);
            } else {
                args.add_names.clear();
            }
        }
        if let Some(name) = Self::extract_clause(s, "rule:") {
            args.rule_name =
                name.split_whitespace().next().map(|n| n.trim_end_matches(',').to_string());
        }
        if let Some(vars) = Self::extract_clause(s, "arbitrary:") {
            args.arbitrary =
                vars.split_whitespace().map(|v| v.trim_end_matches(',').to_string()).collect();
        }
        if let Some(names) = Self::extract_clause(s, "intro:") {
            args.intro_names = split_thm_names(names);
        }
        if let Some(names) = Self::extract_clause(s, "elim:") {
            args.elim_names = split_thm_names(names);
        }
        if let Some(names) = Self::extract_clause(s, "dest:") {
            args.dest_names = split_thm_names(names);
        }
        if let Some(names) = Self::extract_clause(s, "simp:") {
            args.simp_names = split_thm_names(names);
        }

        args
    }
}

// ============================================================================
// Helper functions
// ============================================================================

/// Find the position of the next modifier keyword in `s`.
fn find_next_keyword(s: &str) -> usize {
    let keywords = [
        "add:",
        "del:",
        "only:",
        "rule:",
        "arbitrary:",
        "intro:",
        "elim:",
        "dest:",
        "simp:",
        "iff:",
    ];
    let mut earliest = s.len();
    for kw in &keywords {
        // Search for keyword preceded by space or at start
        let mut pos = 0;
        while let Some(found) = s[pos..].find(kw) {
            let abs_pos = pos + found;
            if abs_pos == 0 || s.as_bytes().get(abs_pos - 1) == Some(&b' ') {
                earliest = earliest.min(abs_pos);
                break;
            }
            pos = abs_pos + 1;
        }
    }
    earliest
}

/// Split theorem names by whitespace, handling `[OF ...]` brackets.
fn split_thm_names(s: &str) -> Vec<String> {
    let mut names = Vec::new();
    let mut depth = 0usize;
    let mut current = String::new();
    for ch in s.chars() {
        match ch {
            '[' => {
                depth += 1;
                current.push(ch);
            },
            ']' => {
                depth -= 1;
                current.push(ch);
            },
            ' ' | '\t' if depth == 0 => {
                if !current.is_empty() {
                    names.push(current.clone());
                    current.clear();
                }
            },
            _ => current.push(ch),
        }
    }
    if !current.is_empty() {
        names.push(current);
    }
    names
}

/// Resolve theorem names to Thm references using the theorem database.
fn resolve_names(names: &[String], db: &crate::hol::hol_loader::HolTheoremDb) -> Vec<Arc<Thm>> {
    let mut thms = Vec::new();
    for name in names {
        // Strip [OF ...] suffix for lookup
        let lookup = if let Some(pos) = name.find('[') { &name[..pos] } else { name.as_str() };
        let trimmed = lookup.trim();
        if let Some(thm) = db.by_name.get(trimmed) {
            thms.push(Arc::clone(thm));
        }
        // Also try with dot-separated names
        for lookup2 in &[trimmed.replace('_', "."), trimmed.replace('.', "_")] {
            if let Some(thm) = db.by_name.get(lookup2.as_str()) {
                thms.push(Arc::clone(thm));
                break;
            }
        }
    }
    thms
}

// ============================================================================
// TODO: placeholder for theorem name parsing with [OF ...] suffix
// ============================================================================

/// Parse `[OF thm1 thm2]` suffix from a theorem reference.
/// Returns the OF parameters if present.
pub fn parse_of_suffix(s: &str) -> (&str, Vec<String>) {
    if let Some(pos) = s.find('[') {
        let name = s[..pos].trim();
        let rest = &s[pos..];
        let of_args =
            if let Some(inner) = rest.strip_prefix("[OF ").and_then(|r| r.strip_suffix(']')) {
                inner.split_whitespace().map(|s| s.to_string()).collect()
            } else {
                Vec::new()
            };
        (name, of_args)
    } else {
        (s, Vec::new())
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_goal_spec_single() {
        assert!(matches!(Args::parse_goal_spec("[1]"), Some(GoalSpec::Single(1))));
        assert!(matches!(Args::parse_goal_spec("[5]"), Some(GoalSpec::Single(5))));
    }

    #[test]
    fn test_goal_spec_range() {
        assert!(matches!(Args::parse_goal_spec("[2-4]"), Some(GoalSpec::Range(2, 4))));
    }

    #[test]
    fn test_goal_spec_from() {
        assert!(matches!(Args::parse_goal_spec("[3-]"), Some(GoalSpec::From(3))));
    }

    #[test]
    fn test_goal_spec_all() {
        assert!(matches!(Args::parse_goal_spec("[!]"), Some(GoalSpec::All)));
    }

    #[test]
    fn test_goal_spec_none() {
        assert!(Args::parse_goal_spec("no_spec").is_none());
        assert!(Args::parse_goal_spec("").is_none());
    }

    #[test]
    fn test_parse_modifiers_basic() {
        let args = Args::parse_modifiers("add: foo bar");
        assert_eq!(args.add_names, vec!["foo", "bar"]);
        assert!(!args.only_mode);
    }

    #[test]
    fn test_parse_modifiers_only() {
        let args = Args::parse_modifiers("only: foo");
        assert!(args.only_mode);
        assert_eq!(args.add_names, vec!["foo"]);
    }

    #[test]
    fn test_parse_modifiers_add_and_del() {
        let args = Args::parse_modifiers("add: foo del: bar");
        assert_eq!(args.add_names, vec!["foo"]);
        assert_eq!(args.del_names, vec!["bar"]);
    }

    #[test]
    fn test_parse_modifiers_rule() {
        let args = Args::parse_modifiers("rule: induct_thm arbitrary: x y");
        assert_eq!(args.rule_name, Some("induct_thm".to_string()));
        assert_eq!(args.arbitrary, vec!["x", "y"]);
    }

    #[test]
    fn test_parse_modifiers_auto_directives() {
        let args = Args::parse_modifiers("intro: foo elim: bar dest: baz simp: qux");
        assert_eq!(args.intro_names, vec!["foo"]);
        assert_eq!(args.elim_names, vec!["bar"]);
        assert_eq!(args.dest_names, vec!["baz"]);
        assert_eq!(args.simp_names, vec!["qux"]);
    }

    #[test]
    fn test_parse_modifiers_empty() {
        let args = Args::parse_modifiers("");
        assert!(args.is_empty());
    }

    #[test]
    fn test_split_thm_names() {
        let names = split_thm_names("foo bar [OF baz] qux");
        assert_eq!(names.len(), 4);
        assert_eq!(names[0], "foo");
        assert_eq!(names[2], "[OF baz]");
    }

    #[test]
    fn test_parse_of_suffix() {
        let (name, ofs) = parse_of_suffix("my_thm[OF a b]");
        assert_eq!(name, "my_thm");
        assert_eq!(ofs, vec!["a", "b"]);
    }

    #[test]
    fn test_parse_of_suffix_none() {
        let (name, ofs) = parse_of_suffix("my_thm");
        assert_eq!(name, "my_thm");
        assert!(ofs.is_empty());
    }

    #[test]
    fn test_find_next_keyword() {
        assert_eq!(find_next_keyword("foo del: bar"), 4);
        // "only" without colon is NOT a keyword — only "only:" triggers
        assert_eq!(find_next_keyword("only foo"), 8); // len("only foo") = 8, no match
        assert_eq!(find_next_keyword("foo"), 3);
        // "add:" at position 0 works
        assert_eq!(find_next_keyword("add: foo"), 0);
    }

    #[test]
    fn test_extract_clause() {
        assert_eq!(Args::extract_clause("add: foo bar del: baz", "add:"), Some("foo bar"));
        assert_eq!(Args::extract_clause("add: foo bar del: baz", "del:"), Some("baz"));
        assert_eq!(Args::extract_clause("just foo", "add:"), None);
    }
}
