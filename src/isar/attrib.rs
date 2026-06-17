//! Attribute system — parse and apply theorem attributes.
//!
//! Corresponds to `src/Pure/Isar/attrib.ML`.
//!
//! ## Attributes
//!
//! Isabelle attributes are annotations on theorems that control how they
//! are used in proof search:
//!
//! | Attribute | Effect |
//! |-----------|--------|
//! | `[simp]` | Add to simplifier rule set |
//! | `[intro]` | Add to introduction rule set (unsafe) |
//! | `[intro!]` | Add to **safe** introduction rule set |
//! | `[intro?]` | Add to **extra** introduction rule set |
//! | `[elim]` | Add to elimination rule set |
//! | `[elim!]` | Add to **safe** elimination rule set |
//! | `[dest]` | Add to destruction rule set |
//! | `[iff]` | Add to intro + elim + simp sets |
//! | `[induct]` | Mark as induction rule |
//! | `[split]` | Mark as case split rule |
//! | `[cong]` | Mark as congruence rule |
//! | `[trans]` | Mark as transitivity rule |
//! | `[sym]` | Mark as symmetry rule |

use std::collections::HashSet;

// =========================================================================
// Attribute types
// =========================================================================

/// Parsed attribute with optional modifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Attribute {
    /// Simplification rule
    Simp,
    /// Introduction rule
    Intro(IntroModifier),
    /// Elimination rule
    Elim(ElimModifier),
    /// Destruction rule
    Dest,
    /// Both intro and elim (iff)
    Iff,
    /// Induction rule
    Induct,
    /// Case split rule
    Split,
    /// Congruence rule
    Cong,
    /// Transitivity rule
    Trans,
    /// Symmetry rule
    Sym,
    /// Named rule (for specific use)
    Named(String),
}

/// Modifier for introduction rules.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntroModifier {
    /// `[intro]` — unsafe (may need backtracking)
    Unsafe,
    /// `[intro!]` — safe (applied eagerly)
    Safe,
    /// `[intro?]` — extra (applied only if needed)
    Extra,
}

/// Modifier for elimination rules.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ElimModifier {
    /// `[elim]` — regular
    Regular,
    /// `[elim!]` — safe
    Safe,
}

// =========================================================================
// Attribute classification
// =========================================================================

/// Classification of a theorem based on its attributes and structure.
#[derive(Debug, Clone)]
#[derive(Default)]
pub struct AttrClass {
    /// Whether this theorem should be in the safe intro set.
    pub safe_intro: bool,
    /// Whether this theorem should be in the unsafe intro set.
    pub unsafe_intro: bool,
    /// Whether this theorem should be in the safe elim set.
    pub safe_elim: bool,
    /// Whether this theorem should be in the regular elim set.
    pub elim: bool,
    /// Whether this theorem should be in the dest set.
    pub dest: bool,
    /// Whether this theorem should be in the simp set.
    pub simp: bool,
    /// Whether this theorem is an induction rule.
    pub induct: bool,
    /// Whether this theorem is a split rule.
    pub split: bool,
    /// Whether this theorem is a congruence rule.
    pub cong: bool,
}


// =========================================================================
// Attribute parser
// =========================================================================

/// Parse a list of attribute strings into a set of attributes.
///
/// Input: `["simp", "intro!", "elim"]`
/// Output: `[Simp, Intro(Safe), Elim(Regular)]`
pub fn parse_attributes(attrs: &[String]) -> Vec<Attribute> {
    attrs.iter().filter_map(|s| parse_single(s)).collect()
}

/// Parse a single attribute string.
pub fn parse_single(s: &str) -> Option<Attribute> {
    let s = s.trim();
    match s {
        "simp" => Some(Attribute::Simp),
        "intro" => Some(Attribute::Intro(IntroModifier::Unsafe)),
        "intro!" => Some(Attribute::Intro(IntroModifier::Safe)),
        "intro?" => Some(Attribute::Intro(IntroModifier::Extra)),
        "elim" => Some(Attribute::Elim(ElimModifier::Regular)),
        "elim!" => Some(Attribute::Elim(ElimModifier::Safe)),
        "dest" => Some(Attribute::Dest),
        "iff" => Some(Attribute::Iff),
        "induct" => Some(Attribute::Induct),
        "split" => Some(Attribute::Split),
        "cong" => Some(Attribute::Cong),
        "trans" => Some(Attribute::Trans),
        "sym" => Some(Attribute::Sym),
        s if s.starts_with("rule:") => {
            Some(Attribute::Named(s.strip_prefix("rule:").unwrap().to_string()))
        },
        _ => None,
    }
}

/// Classify a theorem based on its explicit attributes.
///
/// This replaces the heuristic classification that guesses safe/unsafe
/// based on the theorem structure.
pub fn classify_from_attrs(attrs: &[Attribute]) -> AttrClass {
    let mut class = AttrClass::default();

    for attr in attrs {
        match attr {
            Attribute::Simp => class.simp = true,
            Attribute::Intro(IntroModifier::Safe) => class.safe_intro = true,
            Attribute::Intro(IntroModifier::Unsafe) => class.unsafe_intro = true,
            Attribute::Intro(IntroModifier::Extra) => {
                // Extra intros are not added to any set by default
            },
            Attribute::Elim(ElimModifier::Safe) => class.safe_elim = true,
            Attribute::Elim(ElimModifier::Regular) => class.elim = true,
            Attribute::Dest => class.dest = true,
            Attribute::Iff => {
                class.safe_intro = true;
                class.safe_elim = true;
                class.simp = true;
            },
            Attribute::Induct => class.induct = true,
            Attribute::Split => class.split = true,
            Attribute::Cong => class.cong = true,
            Attribute::Trans | Attribute::Sym | Attribute::Named(_) => {
                // These don't affect the standard classification
            },
        }
    }

    class
}

/// Classify a theorem using both explicit attributes and structural heuristics.
///
/// When no explicit attributes are given, falls back to structural analysis.
pub fn classify_with_fallback(
    attrs: &[String],
    theorem_name: &str,
    is_equality: bool,
) -> AttrClass {
    let parsed = parse_attributes(attrs);
    let mut class = classify_from_attrs(&parsed);

    // If no explicit classification, use heuristics
    let has_explicit = parsed.iter().any(|a| {
        matches!(a, Attribute::Intro(_) | Attribute::Elim(_) | Attribute::Iff | Attribute::Dest)
    });

    if !has_explicit {
        // Heuristic: theorems named ".induct" or ".cases" are induction rules
        if theorem_name.ends_with(".induct") || theorem_name.ends_with(".cases") {
            class.induct = true;
        }
        // Heuristic: theorems named ".simps" are simplification rules
        if theorem_name.ends_with(".simps") || theorem_name.contains("_simps") {
            class.simp = true;
        }
        // Heuristic: equalities are safe intro rules
        if is_equality {
            class.safe_intro = true;
        }
    }

    class
}

// =========================================================================
// Integration helpers
// =========================================================================

/// Determine which theorem database collections a lemma belongs to,
/// based on its parsed attributes.
pub fn compute_db_categories(attrs: &[String], name: &str, is_equality: bool) -> HashSet<String> {
    let class = classify_with_fallback(attrs, name, is_equality);
    let mut cats = HashSet::new();

    if class.simp {
        cats.insert("simp".to_string());
    }
    if class.safe_intro {
        cats.insert("safe_intro".to_string());
    }
    if class.unsafe_intro {
        cats.insert("unsafe_intro".to_string());
    }
    if class.safe_elim {
        cats.insert("safe_elim".to_string());
    }
    if class.elim {
        cats.insert("elim".to_string());
    }
    if class.dest {
        cats.insert("dest".to_string());
    }
    if class.induct {
        cats.insert("induct".to_string());
    }
    if class.split {
        cats.insert("split".to_string());
    }
    if class.cong {
        cats.insert("cong".to_string());
    }

    // Default: at minimum, add to standard intro set
    if cats.is_empty() {
        cats.insert("intro".to_string());
    }

    cats
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_single() {
        assert_eq!(parse_single("simp"), Some(Attribute::Simp));
        assert_eq!(parse_single("intro!"), Some(Attribute::Intro(IntroModifier::Safe)));
        assert_eq!(parse_single("intro"), Some(Attribute::Intro(IntroModifier::Unsafe)));
        assert_eq!(parse_single("elim!"), Some(Attribute::Elim(ElimModifier::Safe)));
        assert_eq!(parse_single("iff"), Some(Attribute::Iff));
        assert_eq!(parse_single("unknown"), None);
    }

    #[test]
    fn test_classify() {
        let attrs = parse_attributes(&["simp".to_string(), "intro!".to_string()]);
        let class = classify_from_attrs(&attrs);
        assert!(class.simp);
        assert!(class.safe_intro);
        assert!(!class.elim);
    }

    #[test]
    fn test_classify_iff() {
        let attrs = parse_attributes(&["iff".to_string()]);
        let class = classify_from_attrs(&attrs);
        assert!(class.simp);
        assert!(class.safe_intro);
        assert!(class.safe_elim);
    }

    #[test]
    fn test_classify_with_fallback_induct() {
        let class = classify_with_fallback(&[], "list.induct", false);
        assert!(class.induct);
    }

    #[test]
    fn test_compute_categories() {
        let cats =
            compute_db_categories(&["simp".to_string(), "intro!".to_string()], "some_lemma", false);
        assert!(cats.contains("simp"));
        assert!(cats.contains("safe_intro"));
    }
}
