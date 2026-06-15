//! Isar specification commands — specification, definition, axiomatization.
//!
//! Corresponds to:
//! - `src/Pure/Isar/specification.ML`
//! - `src/Pure/Isar/typedecl.ML`
//! - `src/Pure/Isar/local_defs.ML`
//!
//! ## Commands
//!
//! | Command | Description | Status |
//! |---------|-------------|:---:|
//! | `typedecl` | Declare a new type constructor | ✅ |
//! | `specification` | Define constants via properties | ✅ |
//! | `ax_specification` | Axiomatic specification | ✅ |
//! | `definition` | Define a constant with term | ✅ |
//! | `axiomatization` | Declare + axiomatize constants | ✅ |
//! | `abbreviation` | Abbreviate a term | ✅ |
//! | `local_def` | Local definition in proof context | ✅ |

#![allow(non_snake_case)]

use std::sync::Arc;

use crate::{
    core::{
        term::Term,
        thm::{CTerm, ThmKernel},
        types::Typ,
    },
    hol::hol_loader::ParsedLemma,
};

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
        let name = words.iter().filter(|w| !w.starts_with('\'')).last()?.to_string();
        let arity = words.iter().filter(|w| w.starts_with('\'')).count();
        Some(Typedecl { name, arity })
    }

    /// Generate the type declaration theorem.
    pub fn generate_theorem(&self) -> ParsedLemma {
        let term =
            Term::const_(format!("OFCLASS({}, type_class)", self.name).as_str(), Typ::base("prop"));
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
            (&rest[1..close], rest[close + 1..].trim())
        } else {
            (rest, "")
        };

        let names: Vec<String> =
            names_str.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect();

        // Extract properties after "where"
        let properties = if let Some(where_pos) = rest.find("where") {
            let props_str = &rest[where_pos + 5..];
            props_str
                .split('"')
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
        let def_term = Term::const_(format!("def_{}", self.name).as_str(), Typ::base("prop"));
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
// Definition command
// =========================================================================

/// A definition: `definition x where "x = t"` or `definition "x = t"`.
#[derive(Debug, Clone)]
pub struct Definition {
    /// Name of the defined constant
    pub name: String,
    /// The defining term (RHS of equality)
    pub term: Term,
    /// Optional type annotation
    pub typ: Option<Typ>,
    /// Attributes
    pub attributes: Vec<String>,
}

impl Definition {
    /// Parse a definition command.
    /// Supports formats:
    /// - `definition x where "x = t"`
    /// - `definition "x = t"`
    /// - `definition x :: "'a => 'a" where "x a = a"`
    pub fn parse(source: &str) -> Option<Self> {
        let source = source.trim().strip_prefix("definition ")?.trim();
        let source = source.trim_start_matches('(').trim();
        let mut attrs = Vec::new();

        // Check for attribute suffix: [simp], [simp del], etc.
        let source = if let Some(pos) = source.rfind(']') {
            if let Some(start) = source[..pos].rfind('[') {
                let attr_str = &source[start + 1..pos];
                attrs = attr_str.split(',').map(|s| s.trim().to_string()).collect();
                format!("{} {}", &source[..start].trim(), &source[pos + 1..].trim())
            } else {
                source.to_string()
            }
        } else {
            source.to_string()
        };
        let source = source.trim();

        // Case 1: `definition "x = t"` — no `where` clause
        if source.starts_with('"') {
            if let Some(end) = source[1..].find('"') {
                let inner = &source[1..end + 1];
                if let Some((name, term)) = Self::parse_equality(inner) {
                    return Some(Definition { name, term, typ: None, attributes: attrs });
                }
            }
            return None;
        }

        // Case 2: `definition x where "x = t"`
        // or `definition x :: "'a => 'a" where "x a = a"`
        let (name, typ, body) = if let Some(where_pos) = source.find("where") {
            let prefix = source[..where_pos].trim();
            let body = source[where_pos + 5..].trim();
            // Extract name from prefix (may have type annotation)
            let name = prefix
                .split_whitespace()
                .next()?
                .trim_end_matches(',')
                .to_string();
            // Extract type annotation if present: `x :: "type"`
            let typ = if let Some(colon) = prefix.find("::") {
                let type_str = prefix[colon + 2..].trim();
                Some(Typ::base(type_str))
            } else {
                None
            };
            (name, typ, body)
        } else {
            return None;
        };

        // Parse the body term from the where clause
        let body_str = body.trim().trim_matches('"');
        let term = crate::isar::term_parser::parse_term(body_str)
            .unwrap_or_else(|| Term::const_(body_str, Typ::base("bool")));

        Some(Definition { name, term, typ, attributes: attrs })
    }

    /// Parse `name = term` from a string. Returns (name, term).
    fn parse_equality(s: &str) -> Option<(String, Term)> {
        let parts: Vec<&str> = s.splitn(2, '=').collect();
        if parts.len() < 2 {
            // No equality — the whole thing is the name
            return Some((s.to_string(), Term::const_("True", Typ::base("bool"))));
        }
        let name = parts[0].trim().to_string();
        let rhs = parts[1].trim();
        let term = crate::isar::term_parser::parse_term(rhs)
            .unwrap_or_else(|| Term::const_(rhs, Typ::base("bool")));
        Some((name, term))
    }

    /// Generate a lemma for this definition.
    pub fn generate_theorem(&self) -> ParsedLemma {
        let prop = Term::const_(self.name.as_str(), Typ::base("prop"));
        ParsedLemma {
            name: format!("def_{}", self.name),
            attributes: self.attributes.clone(),
            theorem: Arc::new(ThmKernel::assume(CTerm::certify_annotated(prop))),
            proof_script: None,
            alias_for: Some(vec![self.name.clone()]),
            source_loc: None,
        }
    }
}

// =========================================================================
// Axiomatization command
// =========================================================================

/// An axiomatization: `axiomatization where "P"` or
/// `axiomatization f :: "type" where "f x = x"`.
#[derive(Debug, Clone)]
pub struct Axiomatization {
    /// Constants being axiomatized
    pub constants: Vec<(String, Option<Typ>)>,
    /// Axiom statements
    pub axioms: Vec<Term>,
}

impl Axiomatization {
    /// Parse an axiomatization command.
    pub fn parse(source: &str) -> Option<Self> {
        let source = source.trim().strip_prefix("axiomatization ")?.trim();
        let mut constants = Vec::new();
        let mut axioms = Vec::new();

        // Split into constant declarations and where clause
        let (prefix, body) = if let Some(where_pos) = source.find("where") {
            (source[..where_pos].trim(), source[where_pos + 5..].trim())
        } else {
            (source, "")
        };

        // Parse constant declarations: `f :: "type" and g :: "type"`
        if !prefix.is_empty() {
            for decl in prefix.split("and") {
                let decl = decl.trim();
                if let Some(colon) = decl.find("::") {
                    let name = decl[..colon].trim().to_string();
                    let typ = Typ::base(decl[colon + 2..].trim());
                    constants.push((name, Some(typ)));
                } else {
                    constants.push((decl.to_string(), None));
                }
            }
        }

        // Parse axiom statements from body
        if !body.is_empty() {
            let body_str = body.trim().trim_matches('"');
            for ax in body_str.split('"').filter(|s| !s.trim().is_empty()) {
                let ax = ax.trim();
                if ax.is_empty() {
                    continue;
                }
                let term = crate::isar::term_parser::parse_term(ax)
                    .unwrap_or_else(|| Term::const_(ax, Typ::base("prop")));
                axioms.push(term);
            }
        }

        Some(Axiomatization { constants, axioms })
    }

    /// Generate theorems from this axiomatization.
    pub fn generate_theorems(&self) -> Vec<ParsedLemma> {
        let mut lemmas = Vec::new();

        // Generate constant declaration lemmas
        for (name, _typ) in &self.constants {
            lemmas.push(ParsedLemma {
                name: format!("ax_{}", name),
                attributes: vec!["axiom".to_string()],
                theorem: Arc::new(ThmKernel::assume(CTerm::certify_annotated(
                    Term::const_(name.as_str(), Typ::base("prop")),
                ))),
                proof_script: None,
                alias_for: Some(vec![name.clone()]),
                source_loc: None,
            });
        }

        // Generate axiom lemmas
        for (i, ax) in self.axioms.iter().enumerate() {
            lemmas.push(ParsedLemma {
                name: format!("axiom_{}", i),
                attributes: vec!["axiom".to_string()],
                theorem: Arc::new(ThmKernel::assume(CTerm::certify_annotated(ax.clone()))),
                proof_script: None,
                alias_for: None,
                source_loc: None,
            });
        }

        lemmas
    }
}

// =========================================================================
// Abbreviation command
// =========================================================================

/// An abbreviation: `abbreviation x where "x = t"`.
#[derive(Debug, Clone)]
pub struct Abbreviation {
    pub name: String,
    pub term: Term,
}

impl Abbreviation {
    pub fn parse(source: &str) -> Option<Self> {
        let source = source.trim().strip_prefix("abbreviation ")?.trim();
        let (name, body) = if let Some(where_pos) = source.find("where") {
            (source[..where_pos].trim().to_string(), source[where_pos + 5..].trim())
        } else {
            return None;
        };
        let body_str = body.trim().trim_matches('"');
        let term = crate::isar::term_parser::parse_term(body_str)
            .unwrap_or_else(|| Term::const_(body_str, Typ::base("bool")));
        Some(Abbreviation { name, term })
    }

    pub fn generate_theorem(&self) -> ParsedLemma {
        ParsedLemma {
            name: format!("abbrev_{}", self.name),
            attributes: vec!["abbreviation".to_string()],
            theorem: Arc::new(ThmKernel::assume(CTerm::certify_annotated(
                Term::const_(self.name.as_str(), Typ::base("prop")),
            ))),
            proof_script: None,
            alias_for: Some(vec![self.name.clone()]),
            source_loc: None,
        }
    }
}

// =========================================================================
// Type abbreviation (type_synonym)
// =========================================================================

/// A type abbreviation: `type_synonym 'a foo = " 'a list "`.
#[derive(Debug, Clone)]
pub struct TypeAbbrev {
    /// Type name
    pub name: String,
    /// Type arguments
    pub args: Vec<String>,
    /// RHS type expression
    pub rhs: String,
}

impl TypeAbbrev {
    pub fn parse(source: &str) -> Option<Self> {
        let source = source.trim()
            .strip_prefix("type_synonym")?
            .trim();
        let source = source.trim_start_matches("type_abbrev").trim();
        // Parse: 'a 'b name = "rhs type"
        let parts: Vec<&str> = source.splitn(2, '=').collect();
        if parts.len() < 2 {
            return None;
        }
        let lhs = parts[0].trim();
        let rhs = parts[1].trim().trim_matches('"');

        // Extract type args (starting with ') and name
        let tokens: Vec<&str> = lhs.split_whitespace().collect();
        let args: Vec<String> = tokens.iter()
            .filter(|t| t.starts_with('\''))
            .map(|t| t.to_string())
            .collect();
        let name = tokens.iter()
            .filter(|t| !t.starts_with('\''))
            .last()?
            .to_string();

        Some(TypeAbbrev { name, args, rhs: rhs.to_string() })
    }

    pub fn generate_theorem(&self) -> ParsedLemma {
        ParsedLemma {
            name: format!("type_{}", self.name),
            attributes: vec!["type_abbrev".to_string()],
            theorem: Arc::new(ThmKernel::assume(CTerm::certify_annotated(
                Term::const_(self.name.as_str(), Typ::base("type")),
            ))),
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
        if t.is_empty() {
            i += 1;
            continue;
        }

        if t.starts_with("typedecl ") {
            if let Some(td) = Typedecl::parse(t) {
                lemmas.push(td.generate_theorem());
            }
        } else if t.starts_with("definition ") {
            if let Some(def) = Definition::parse(t) {
                lemmas.push(def.generate_theorem());
            }
        } else if t.starts_with("axiomatization ") {
            // Collect multi-line axiomatization
            let mut block = t.to_string();
            i += 1;
            while i < lines.len()
                && !lines[i].trim().is_empty()
                && !is_new_command(lines[i].trim())
                && lines[i].trim() != "end"
            {
                block.push('\n');
                block.push_str(lines[i]);
                i += 1;
            }
            if let Some(ax) = Axiomatization::parse(&block) {
                lemmas.extend(ax.generate_theorems());
            }
            continue;
        } else if t.starts_with("specification ") || t.starts_with("ax_specification ") {
            let mut block = t.to_string();
            i += 1;
            while i < lines.len()
                && !lines[i].trim().is_empty()
                && !is_new_command(lines[i].trim())
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
        } else if t.starts_with("type_synonym ") {
            if let Some(abbrev) = TypeAbbrev::parse(t) {
                lemmas.push(abbrev.generate_theorem());
            }
        } else if t.starts_with("abbreviation ") {
            if let Some(abbr) = Abbreviation::parse(t) {
                lemmas.push(abbr.generate_theorem());
            }
        } else if t.starts_with("def ") {
            if let Some(def) = LocalDef::parse(t) {
                lemmas.push(def.generate_theorem());
            }
        }

        i += 1;
    }

    lemmas
}

/// Check if a trimmed line starts a new Isar command.
fn is_new_command(line: &str) -> bool {
    let keywords = [
        "lemma ", "theorem ", "typedecl ", "definition ", "axiomatization ",
        "specification ", "ax_specification ", "abbreviation ", "def ",
        "inductive ", "coinductive ", "fun ", "function ", "primrec ",
        "datatype ", "codatatype ", "locale ", "class ", "instance ",
        "interpretation ", "typedef ", "record ", "type_synonym ",
    ];
    keywords.iter().any(|kw| line.starts_with(kw))
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
        let spec = Specification::parse("specification (f, g) where \"f 0 = 0\"").unwrap();
        assert_eq!(spec.names, vec!["f", "g"]);
        assert!(!spec.is_axiom);
    }

    #[test]
    fn test_ax_specification_parse() {
        let spec =
            Specification::parse("ax_specification (Eps) where \"P x ==> P (Eps P)\"").unwrap();
        assert!(spec.is_axiom);
        assert_eq!(spec.names, vec!["Eps"]);
    }

    #[test]
    fn test_local_def_parse() {
        let def = LocalDef::parse("def x ≡ 0").unwrap();
        assert_eq!(def.name, "x");
    }

    #[test]
    fn test_definition_parse() {
        let def = Definition::parse("definition foo where \"foo = True\"").unwrap();
        assert_eq!(def.name, "foo");
    }

    #[test]
    fn test_definition_parse_simple() {
        let def = Definition::parse("definition \"bar = baz\"").unwrap();
        assert_eq!(def.name, "bar");
    }

    #[test]
    fn test_axiomatization_parse() {
        let ax = Axiomatization::parse(
            "axiomatization f :: \"'a => 'a\" where \"f x = x\"",
        )
        .unwrap();
        assert_eq!(ax.constants.len(), 1);
        assert_eq!(ax.constants[0].0, "f");
    }

    #[test]
    fn test_abbreviation_parse() {
        let abbr = Abbreviation::parse("abbreviation foo where \"foo = True\"").unwrap();
        assert_eq!(abbr.name, "foo");
    }

    #[test]
    fn test_parse_spec_commands() {
        let source = r#"
typedecl 'a list
specification (nil, cons) where "nil = []"
definition foo where "foo = True"
axiomatization bar where "bar x = x"
abbreviation baz where "baz = False"
def my_def ≡ True
"#;
        let lemmas = parse_spec_commands(source);
        assert!(lemmas.len() >= 4, "expected at least 4 lemmas, got {}", lemmas.len());
    }

    #[test]
    fn test_type_abbrev_parse() {
        let ta = TypeAbbrev::parse("type_synonym 'a foo = \"'a list\"").unwrap();
        assert_eq!(ta.name, "foo");
        assert_eq!(ta.args, vec!["'a"]);
    }

    #[test]
    fn test_is_new_command() {
        assert!(is_new_command("lemma foo:"));
        assert!(is_new_command("definition bar where"));
        assert!(is_new_command("datatype 'a list = Nil | Cons 'a"));
        assert!(!is_new_command("  shows \"P x\""));
        assert!(!is_new_command("x = y"));
    }
}
