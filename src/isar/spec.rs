//! Isar specification commands — typedecl, specification, local_defs.
//!
//! Corresponds to:
//! - `src/Pure/Isar/typedecl.ML`
//! - `src/Pure/Isar/specification.ML`
//! - `src/Pure/Isar/local_defs.ML`
//! - `src/Pure/Isar/parse_spec.ML`
//!
//! ## Commands
//!
//! | Command | Description |
//! |---------|-------------|
//! | `typedecl` | Declare a new type constructor |
//! | `specification` | Define constants via properties |
//! | `ax_specification` | Axiomatic specification |
//! | `local_def` | Local definition in proof context |

use std::sync::Arc;

use crate::core::term::Term;
use crate::core::thm::{CTerm, ThmKernel};
use crate::core::types::Typ;
use crate::hol::hol_loader::ParsedLemma;

// =========================================================================
// Type declaration
// =========================================================================

/// A type declaration: `typedecl 'a foo`.
#[derive(Debug, Clone)]
pub struct Typedecl {
    /// Type constructor name
    pub name: String,
    /// Number of type arguments
    pub arity: usize,
}

impl Typedecl {
    /// Parse a typedecl command.
    pub fn parse(source: &str) -> Option<Self> {
        let source = source.trim().strip_prefix("typedecl ")?.trim();
        // Skip type parameters like 'a, 'b to get the actual type name
        let words: Vec<&str> = source.split_whitespace().collect();
        // The type name is the last word, type params are the ones starting with '
        let name = words.iter()
            .filter(|w| !w.starts_with('\''))
            .last()?
            .to_string();
        let arity = words.iter().filter(|w| w.starts_with('\'')).count();
        Some(Typedecl { name, arity })
    }

    /// Generate the type declaration theorem.
    pub fn generate_theorem(&self) -> ParsedLemma {
        let term = Term::const_(
            format!("OFCLASS({}, type_class)", self.name).as_str(),
            Typ::base("prop"),
        );
        ParsedLemma {
            name: format!("{}.type", self.name),
            attributes: vec!["typedecl".to_string()],
            theorem: Arc::new(ThmKernel::assume(CTerm::certify_annotated(term))),
            proof_script: None,
            alias_for: None,
            source_loc: None,
        }
    }
}

// =========================================================================
// Specification
// =========================================================================

/// A specification: `specification (x, y) where "P x y"`.
#[derive(Debug, Clone)]
pub struct Specification {
    /// Names being specified
    pub names: Vec<String>,
    /// The properties they satisfy
    pub properties: Vec<Term>,
    /// Whether this is axiomatic (ax_specification)
    pub is_axiom: bool,
}

impl Specification {
    /// Parse a specification command from source text.
    pub fn parse(source: &str) -> Option<Self> {
        let source = source.trim();
        let is_axiom = source.starts_with("ax_specification");
        let rest = if is_axiom {
            source.strip_prefix("ax_specification")?.trim()
        } else {
            source.strip_prefix("specification")?.trim()
        };

        // Extract names: "(x, y, z)"
        let (names_str, rest) = if rest.starts_with('(') {
            let close = rest.find(')')?;
            (&rest[1..close], rest[close+1..].trim())
        } else {
            (rest, "")
        };

        let names: Vec<String> = names_str.split(',')
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .collect();

        // Extract properties after "where"
        let properties = if let Some(where_pos) = rest.find("where") {
            let props_str = &rest[where_pos + 5..];
            props_str.split('"')
                .filter(|s| !s.trim().is_empty())
                .map(|s| Term::const_(s, Typ::base("prop")))
                .collect()
        } else {
            vec![]
        };

        Some(Specification { names, properties, is_axiom })
    }

    /// Generate theorems from this specification.
    pub fn generate_theorems(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();

        for name in &self.names {
            let term = Term::const_(name.as_str(), Typ::base("prop"));
            let attrs = if self.is_axiom {
                vec!["axiom".to_string()]
            } else {
                vec!["specification".to_string()]
            };

            lemmas.push(ParsedLemma {
                name: format!("spec_{}", name),
                attributes: attrs,
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
// Local definitions
// =========================================================================

/// A local definition: `def x ≡ t` in a proof context.
#[derive(Debug, Clone)]
pub struct LocalDef {
    /// Variable name being defined
    pub name: String,
    /// The defining term
    pub term: Term,
    /// Optional type annotation
    pub typ: Option<Typ>,
}

impl LocalDef {
    /// Parse a local definition.
    pub fn parse(source: &str) -> Option<Self> {
        let source = source.trim().strip_prefix("def ")?;
        let parts: Vec<&str> = source.splitn(2, "≡").collect();
        if parts.len() < 2 {
            return None;
        }
        let name = parts[0].trim().to_string();
        let term = crate::isar::term_parser::parse_term(parts[1].trim())
            .unwrap_or_else(|| Term::const_(parts[1].trim(), Typ::base("prop")));

        Some(LocalDef { name, term, typ: None })
    }

    /// Generate the definition theorem.
    pub fn generate_theorem(&self) -> ParsedLemma {
        let def_term = Term::const_(
            format!("def_{}", self.name).as_str(),
            Typ::base("prop"),
        );
        ParsedLemma {
            name: format!("def_{}", self.name),
            attributes: vec!["def".to_string()],
            theorem: Arc::new(ThmKernel::assume(CTerm::certify_annotated(def_term))),
            proof_script: None,
            alias_for: None,
            source_loc: None,
        }
    }
}

// =========================================================================
// Parser integration
// =========================================================================

/// Parse specification-like commands from .thy source.
pub fn parse_spec_commands(source: &str) -> Vec<ParsedLemma> {
    let mut lemmas = Vec::new();
    let lines: Vec<&str> = source.lines().collect();
    let mut i = 0;

    while i < lines.len() {
        let t = lines[i].trim();

        if t.starts_with("typedecl ") {
            if let Some(td) = Typedecl::parse(t) {
                lemmas.push(td.generate_theorem());
            }
        } else if t.starts_with("specification ") || t.starts_with("ax_specification ") {
            // Collect multi-line specification
            let mut block = t.to_string();
            i += 1;
            while i < lines.len() && !lines[i].trim().is_empty()
                && !lines[i].trim().starts_with("lemma ")
                && !lines[i].trim().starts_with("theorem ")
                && lines[i].trim() != "end"
            {
                block.push('\n');
                block.push_str(lines[i]);
                i += 1;
            }
            if let Some(spec) = Specification::parse(&block) {
                lemmas.extend(spec.generate_theorems());
            }
            continue;
        } else if t.starts_with("def ") {
            if let Some(def) = LocalDef::parse(t) {
                lemmas.push(def.generate_theorem());
            }
        }

        i += 1;
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
    fn test_typedecl_parse() {
        let td = Typedecl::parse("typedecl 'a foo").unwrap();
        assert_eq!(td.name, "foo");
        assert_eq!(td.arity, 1);
    }

    #[test]
    fn test_specification_parse() {
        let spec = Specification::parse(
            "specification (f, g) where \"f 0 = 0\""
        ).unwrap();
        assert_eq!(spec.names, vec!["f", "g"]);
        assert!(!spec.is_axiom);
    }

    #[test]
    fn test_ax_specification_parse() {
        let spec = Specification::parse(
            "ax_specification (Eps) where \"P x ==> P (Eps P)\""
        ).unwrap();
        assert!(spec.is_axiom);
        assert_eq!(spec.names, vec!["Eps"]);
    }

    #[test]
    fn test_local_def_parse() {
        let def = LocalDef::parse("def x ≡ 0").unwrap();
        assert_eq!(def.name, "x");
    }

    #[test]
    fn test_parse_spec_commands() {
        let source = r#"
typedecl 'a list
specification (nil, cons) where "nil = []"
def my_def ≡ True
"#;
        let lemmas = parse_spec_commands(source);
        assert!(lemmas.len() >= 1);
    }
}
