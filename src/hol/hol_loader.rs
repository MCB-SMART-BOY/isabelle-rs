//! Load Isabelle's HOL.thy declarations into our theory system.
//!
//! Parses the core declarations from Isabelle's actual HOL.thy file:
//! - `typedecl bool` → declares type
//! - `axiomatization implies :: ...` → declares constant + axiom
//! - `definition True :: bool where "..."` → declares + defines constant
//!
//! This avoids manually rewriting HOL — we reuse Isabelle's own source.

use crate::core::theory::Theory;
use crate::core::types::{Sort, Typ};
use std::sync::Arc;
use crate::core::thm::{CTerm, ThmKernel};
use crate::isar::term_parser::parse_term;

/// Load the HOL theory by parsing Isabelle's HOL.thy declarations.
pub fn load_hol_theory(hol_thy: &str) -> Theory {
    let pure = Theory::pure();
    let mut thy = Theory::begin("HOL", vec![pure]);

    // Parse type declarations: `typedecl bool`
    for cap in &find_declarations(hol_thy, "typedecl") {
        let name = cap.trim();
        if !name.is_empty() && !thy.is_declared(name) {
            thy.declare_const(format!("HOL.{name}"), Typ::base(name));
        }
    }

    // Type class: `axiomatization where fun_arity: "OFCLASS('a => 'b, type_class)"`
    // We skip class axioms for now — just declare the basic types

    // Axiomatized constants: `axiomatization implies :: "[bool, bool] => bool"`
    // Multi-constant format: `axiomatization c1 :: ... and c2 :: ...`
    for block in &find_blocks(hol_thy, "axiomatization") {
        for const_decl in block.split(" and ") {
            let decl = const_decl.trim();
            if let Some((name, typ_str)) = parse_const_decl(decl) {
                if let Some(typ) = parse_hol_type(typ_str) {
                    if !thy.is_declared(&format!("HOL.{name}")) {
                        thy.declare_const(format!("HOL.{name}"), typ);
                    }
                }
            }
        }
    }

    // Definitions: `definition True :: bool where "True == ..."` 
    for block in &find_blocks(hol_thy, "definition") {
        let decl = block.trim();
        if let Some((name, typ_str, _defn)) = parse_definition(decl) {
            if let Some(typ) = parse_hol_type(typ_str) {
                if !thy.is_declared(&format!("HOL.{name}")) {
                    thy.declare_const(format!("HOL.{name}"), typ);
                }
            }
        }
    }

    thy
}

/// Extract declarations of the form `keyword name ...` from the source.
fn find_declarations(source: &str, keyword: &str) -> Vec<String> {
    let mut results = Vec::new();
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with(keyword) {
            let rest = trimmed[keyword.len()..].trim();
            if let Some(name) = rest.split_whitespace().next() {
                results.push(name.to_string());
            }
        }
    }
    results
}

/// Extract multi-line blocks starting with `keyword`.
fn find_blocks(source: &str, keyword: &str) -> Vec<String> {
    let mut results = Vec::new();
    let mut in_block = false;
    let mut block_lines = Vec::new();
    
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with(keyword) && !in_block {
            in_block = true;
            block_lines = vec![trimmed];
        } else if in_block {
            if trimmed.is_empty() {
                let block = block_lines.join("\n");
                let content = block.trim().strip_prefix(keyword).unwrap_or(&block).trim().to_string();
                results.push(content);
                in_block = false;
                block_lines = Vec::new();
            } else {
                block_lines.push(line);
            }
        }
    }
    // Flush last block
    if in_block && !block_lines.is_empty() {
        let block = block_lines.join("\n");
        let content = block.trim().strip_prefix(keyword).unwrap_or(&block).trim().to_string();
        results.push(content);
    }
    results
}

/// Parse `name :: "type"` or `name :: type`.
fn parse_const_decl(decl: &str) -> Option<(&str, &str)> {
    let parts: Vec<&str> = decl.splitn(2, "::").collect();
    if parts.len() == 2 {
        let name = parts[0].trim();
        let typ_str = parts[1].trim().trim_matches('"');
        Some((name, typ_str))
    } else {
        None
    }
}

/// Parse `name :: type where "defn"`.
fn parse_definition(decl: &str) -> Option<(&str, &str, &str)> {
    // name :: type where "defn"
    let parts: Vec<&str> = decl.splitn(2, "::").collect();
    if parts.len() < 2 { return None; }
    let name = parts[0].trim();
    let rest = parts[1].trim();
    // Split at "where"
    let where_parts: Vec<&str> = rest.splitn(2, "where").collect();
    let typ_str = where_parts[0].trim();
    let defn = where_parts.get(1).map(|s| s.trim().trim_matches('"')).unwrap_or("");
    Some((name, typ_str, defn))
}

/// Simplified HOL type parser — handles `bool`, `'a => bool`, `[bool, bool] => bool`
fn parse_hol_type(s: &str) -> Option<Typ> {
    let s = s.trim();
    // Try function type: T1 => T2
    if let Some(pos) = s.find("=>") {
        let left = &s[..pos].trim();
        let right = &s[pos+2..].trim();
        let t1 = parse_hol_type_atom(left)?;
        let t2 = parse_hol_type(right)?;
        return Some(Typ::arrow(t1, t2));
    }
    parse_hol_type_atom(s)
}

fn parse_hol_type_atom(s: &str) -> Option<Typ> {
    let s = s.trim();
    // Bracket list: [bool, bool]
    if s.starts_with('[') && s.ends_with(']') {
        let inner = &s[1..s.len()-1];
        // For simplicity, treat [A, B] => C as A => B => C
        return Some(Typ::base(inner.trim()));
    }
    // Parenthesised
    if s.starts_with('(') && s.ends_with(')') {
        return parse_hol_type(&s[1..s.len()-1]);
    }
    // Type variable
    if s.starts_with('\'') {
        return Some(Typ::free(s, Sort::singleton("type")));
    }
    // Simple type name
    Some(Typ::base(s))
}

/// Load HOL from the actual Isabelle source file.
pub fn load_hol_from_file() -> Theory {
    let hol_thy = include_str!("../../isabelle-source/src/HOL/HOL.thy");
    load_hol_theory(hol_thy)
}

// =========================================================================
// Lemma parsing (Route A)
// =========================================================================

pub struct ParsedLemma {
    pub name: String,
    pub attributes: Vec<String>,
    pub theorem: Arc<crate::core::thm::Thm>,
}

/// Parse inline lemmas from .thy source.
pub fn parse_lemmas(source: &str) -> Vec<ParsedLemma> {
    let mut lemmas = Vec::new();
    for line in source.lines() {
        let t = line.trim();
        if !t.starts_with("lemma ") && !t.starts_with("theorem ") { continue; }
        if let Some(l) = parse_one(t) { lemmas.push(l); }
    }
    lemmas
}

fn parse_one(line: &str) -> Option<ParsedLemma> {
    let rest = line.strip_prefix("lemma ")
        .or_else(|| line.strip_prefix("theorem "))?;
    let (name_part, stmt_part) = rest.split_once(": \"")?;
    let stmt = stmt_part.strip_suffix("\"")?;
    let (name, attrs) = if let Some(b) = name_part.find('[') {
        (name_part[..b].trim(), parse_attrs(&name_part[b..]))
    } else {
        (name_part.trim(), Vec::new())
    };
    let conv = convert_syntax(stmt);
    let term = parse_term(&conv)?;
    let thm = Arc::new(ThmKernel::assume(CTerm::certify(term)));
    Some(ParsedLemma { name: name.to_string(), attributes: attrs, theorem: thm })
}

fn parse_attrs(s: &str) -> Vec<String> {
    s.trim_start_matches('[').trim_end_matches(']')
        .split(',').map(|a| a.trim().to_string()).collect()
}

fn convert_syntax(s: &str) -> String {
    s.replace("\\<lbrakk>", "[|")
     .replace("\\<rbrakk>", "|]")
     .replace("\\<Longrightarrow>", "==>")
     .replace("\\<And>", "!!")
     .replace("\\<not>", "~")
     .replace("\\<noteq>", "~=")
     .replace("\\<forall>", "ALL")
     .replace("\\<exists>", "EX")
     .replace("\\<longrightarrow>", "-->")
     .replace("\\<and>", "&")
     .replace("\\<or>", "|")
     .replace("\\<longleftrightarrow>", "=")
     .replace("\\<equiv>", "=")
}

// =========================================================================
// Global theorem store (A3)
// =========================================================================

use std::sync::LazyLock;

/// All loaded HOL theorems, categorized by attribute.
static HOL_THEOREMS: LazyLock<HolTheoremDb> = LazyLock::new(|| {
    let hol_thy = include_str!("../../isabelle-source/src/HOL/HOL.thy");
    let lemmas = parse_lemmas(hol_thy);
    HolTheoremDb::from_lemmas(&lemmas)
});

pub struct HolTheoremDb {
    pub intros: Vec<Arc<crate::core::thm::Thm>>,
    pub elims: Vec<Arc<crate::core::thm::Thm>>,
    pub simps: Vec<Arc<crate::core::thm::Thm>>,
    pub all: Vec<Arc<crate::core::thm::Thm>>,
}

impl HolTheoremDb {
    fn from_lemmas(lemmas: &[ParsedLemma]) -> Self {
        let mut intros = Vec::new();
        let mut elims = Vec::new();
        let mut simps = Vec::new();
        let mut all = Vec::new();
        for lem in lemmas {
            let thm = Arc::clone(&lem.theorem);
            all.push(Arc::clone(&thm));
            let attrs = &lem.attributes;
            if attrs.iter().any(|a| a.contains("intro")) { intros.push(Arc::clone(&thm)); }
            if attrs.iter().any(|a| a.contains("elim")) { elims.push(Arc::clone(&thm)); }
            if attrs.iter().any(|a| a.contains("simp")) { simps.push(Arc::clone(&thm)); }
        }
        // Always include key rules even without explicit attributes
        for lem in lemmas {
            let thm = Arc::clone(&lem.theorem);
            match lem.name.as_str() {
                "sym" | "trans" | "refl" | "arg_cong" | "fun_cong" | "iffD1" | "iffD2" => {
                    if !simps.iter().any(|t| Arc::ptr_eq(t, &thm)) { simps.push(thm); }
                }
                _ => {}
            }
        }
        HolTheoremDb { intros, elims, simps, all }
    }

    pub fn get() -> &'static Self { &HOL_THEOREMS }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_const_decl() {
        let (name, typ) = parse_const_decl("implies :: \"[bool, bool] => bool\"").unwrap();
        assert_eq!(name, "implies");
    }

    #[test]
    fn test_parse_hol_type_simple() {
        assert_eq!(parse_hol_type("bool"), Some(Typ::base("bool")));
    }

    #[test]
    fn test_parse_hol_type_fun() {
        let t = parse_hol_type("bool => bool").unwrap();
        assert_eq!(t, Typ::arrow(Typ::base("bool"), Typ::base("bool")));
    }

    #[test]
    fn test_load_hol_from_file() {
        let thy = load_hol_from_file();
        // Should have declared HOL constants from HOL.thy
        assert!(thy.is_declared("HOL.bool") || thy.is_declared("HOL.True"));
    }

    #[test]
    fn test_find_declarations() {
        let src = "typedecl bool\ntypedecl ind";
        let names: Vec<_> = find_declarations(src, "typedecl");
        assert_eq!(names, vec!["bool", "ind"]);
    }

    #[test]
    fn test_parse_definition() {
        let src = "True :: bool where \"True == ((%x::bool. x) = (%x. x))\"";
        let (name, typ_str, _defn) = parse_definition(src).unwrap();
        assert_eq!(name, "True");
        assert_eq!(typ_str, "bool");
    }
}

#[cfg(test)]
mod lemma_tests {
    use super::*;

    #[test]
    fn test_parse_sym() {
        let src = "lemma sym: \"s = t \\<Longrightarrow> t = s\"";
        let lemmas = parse_lemmas(src);
        assert_eq!(lemmas.len(), 1);
        assert_eq!(lemmas[0].name, "sym");
    }

    #[test]
    fn test_parse_with_attrs() {
        let src = "lemma trans_sym [Pure.elim?]: \"r = s \\<Longrightarrow> t = s \\<Longrightarrow> r = t\"";
        let lemmas = parse_lemmas(src);
        assert_eq!(lemmas.len(), 1);
        assert_eq!(lemmas[0].name, "trans_sym");
        assert!(!lemmas[0].attributes.is_empty());
    }

    #[test]
    fn test_load_real_hol() {
        let hol_thy = include_str!("../../isabelle-source/src/HOL/HOL.thy");
        let lemmas = parse_lemmas(hol_thy);
        let count = lemmas.len();
        eprintln!("Loaded {} lemmas from HOL.thy", count);
        assert!(count > 30, "expected >30 lemmas, got {}", count);
        let names: Vec<&str> = lemmas.iter().map(|l| l.name.as_str()).collect();
        assert!(names.contains(&"sym"));
        assert!(names.contains(&"disjI1"));
        assert!(names.contains(&"conjI"));
    }
}
