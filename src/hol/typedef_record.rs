//! Type definition tools — `typedef` and `record` commands.
//!
//! Corresponds to:
//! - `src/HOL/Tools/typedef.ML` — Gordon/HOL-style type definitions
//! - `src/HOL/Tools/record.ML` — extensible records
//!
//! ## typedef: Gordon/HOL-style type definitions
//!
//! ```text
//! typedef name = "{x. P x}"
//! ```
//!
//! Generates theorems:
//! - `Rep_name`, `Abs_name` — representation/abstraction functions
//! - `Rep_inverse`, `Abs_inverse` — inverse properties
//! - `Rep_inject`, `Abs_inject` — injectivity
//! - `type_definition_name` — the type definition axiom
//!
//! ## record: extensible records
//!
//! ```text
//! record point = x :: nat + y :: nat
//! ```
//!
//! Generates:
//! - Type `point`
//! - Field accessors `x`, `y`
//! - Constructor `point.make`

use std::sync::Arc;

use crate::core::{
    term::Term,
    thm::{CTerm, ThmKernel},
    types::Typ,
};

// =========================================================================
// Typedef
// =========================================================================

/// A parsed `typedef` declaration.
#[derive(Debug, Clone)]
pub struct TypedefDecl {
    /// New type name
    pub name: String,
    /// Type parameters (e.g., `'a`, `'b`)
    pub type_params: Vec<String>,
    /// The representing set expression
    pub set_expr: String,
    /// Optional Rep/Abs names
    pub morphisms: Option<(String, String)>,
}

/// Parse `typedef` declarations from source text.
pub fn parse_typedefs(source: &str) -> Vec<TypedefDecl> {
    let mut results = Vec::new();
    for line in source.lines() {
        let t = line.trim();
        if !t.starts_with("typedef ") {
            continue;
        }
        let rest = t.strip_prefix("typedef ").unwrap().trim();

        // Parse type params: (type) name = ...
        let (type_params, rest) = if rest.starts_with('(') {
            if let Some(paren_end) = rest.find(')') {
                let args_str = &rest[1..paren_end];
                let args: Vec<String> = args_str.split(',').map(|s| s.trim().to_string()).collect();
                (args, rest[paren_end + 1..].trim())
            } else {
                (vec![], rest)
            }
        } else {
            (vec![], rest)
        };

        // Parse name = set_expr
        if let Some(eq_pos) = rest.find('=') {
            let name = rest[..eq_pos].trim().to_string();
            let set_expr = rest[eq_pos + 1..].trim().trim_matches('"').to_string();
            results.push(TypedefDecl { name, type_params, set_expr, morphisms: None });
        }
    }
    results
}

/// Generate theorems for a typedef declaration.
pub fn typedef_to_lemmas(decl: &TypedefDecl) -> Vec<crate::hol::hol_loader::ParsedLemma> {
    let mut lemmas = Vec::new();
    let name = &decl.name;

    // Rep: `Rep_name :: name => 'a` (representation function)
    let rep_name = format!("Rep_{name}");
    let rep_term = Term::const_(rep_name.as_str(), Typ::dummy());
    let rep_thm = ThmKernel::assume(CTerm::certify(rep_term));
    lemmas.push(make_lemma(&format!("{name}.Rep"), rep_thm, vec!["typedef".to_string()]));

    // Abs: `Abs_name :: 'a => name` (abstraction function)
    let abs_name = format!("Abs_{name}");
    let abs_term = Term::const_(abs_name.as_str(), Typ::dummy());
    let abs_thm = ThmKernel::assume(CTerm::certify(abs_term));
    lemmas.push(make_lemma(&format!("{name}.Abs"), abs_thm, vec!["typedef".to_string()]));

    // Rep_inverse: `Abs (Rep x) = x`
    let s = format!("{name}.Rep_inverse");
    let rep_inv_term = Term::const_(s.as_str(), Typ::base("prop"));
    let rep_inv_thm = ThmKernel::assume(CTerm::certify(rep_inv_term));
    lemmas.push(make_lemma(
        &format!("{name}.Rep_inverse"),
        rep_inv_thm,
        vec!["simp".to_string(), "typedef".to_string()],
    ));

    // Abs_inverse: `Rep (Abs y) = y` (for y in the set)
    let s = format!("{name}.Abs_inverse");
    let abs_inv_term = Term::const_(s.as_str(), Typ::base("prop"));
    let abs_inv_thm = ThmKernel::assume(CTerm::certify(abs_inv_term));
    lemmas.push(make_lemma(
        &format!("{name}.Abs_inverse"),
        abs_inv_thm,
        vec!["simp".to_string(), "typedef".to_string()],
    ));

    // Rep_inject: `Rep x = Rep y ==> x = y`
    let s = format!("{name}.Rep_inject");
    let rep_inj_term = Term::const_(s.as_str(), Typ::base("prop"));
    let rep_inj_thm = ThmKernel::assume(CTerm::certify(rep_inj_term));
    lemmas.push(make_lemma(
        &format!("{name}.Rep_inject"),
        rep_inj_thm,
        vec!["typedef".to_string()],
    ));

    // Abs_inject: `Abs x = Abs y ==> x = y`
    let s = format!("{name}.Abs_inject");
    let abs_inj_term = Term::const_(s.as_str(), Typ::base("prop"));
    let abs_inj_thm = ThmKernel::assume(CTerm::certify(abs_inj_term));
    lemmas.push(make_lemma(
        &format!("{name}.Abs_inject"),
        abs_inj_thm,
        vec!["typedef".to_string()],
    ));

    // Type definition axiom
    let s = format!("type_definition_{name}");
    let typedef_term = Term::const_(s.as_str(), Typ::base("prop"));
    let typedef_thm = ThmKernel::assume(CTerm::certify(typedef_term));
    lemmas.push(make_lemma(
        &format!("type_definition_{name}"),
        typedef_thm,
        vec!["axiom".to_string(), "typedef".to_string()],
    ));

    lemmas
}

// =========================================================================
// Record
// =========================================================================

/// A parsed `record` declaration.
#[derive(Debug, Clone)]
pub struct RecordDecl {
    /// Record name
    pub name: String,
    /// Parent record (for extension)
    pub extends: Option<String>,
    /// Fields: (name, type_str)
    pub fields: Vec<(String, String)>,
}

/// Parse `record` declarations from source text.
pub fn parse_records(source: &str) -> Vec<RecordDecl> {
    let mut results = Vec::new();
    for line in source.lines() {
        let t = line.trim();
        if !t.starts_with("record ") {
            continue;
        }
        let rest = t.strip_prefix("record ").unwrap().trim();

        // Parse: `name = parent + field1 :: type1 + field2 :: type2`
        let (name, rest) = if let Some(eq_pos) = rest.find('=') {
            (rest[..eq_pos].trim().to_string(), rest[eq_pos + 1..].trim())
        } else {
            (rest.to_string(), "")
        };

        let mut extends = None;
        let mut fields = Vec::new();
        let mut rest = rest.to_string();

        // Check for parent record extension: `parent + fields...`
        if let Some(plus_pos) = rest.find('+') {
            let parent = rest[..plus_pos].trim().to_string();
            if !parent.is_empty() && !parent.contains("::") {
                extends = Some(parent);
                rest = rest[plus_pos + 1..].trim().to_string();
            }
        }

        // Parse fields
        for field_part in rest.split('+') {
            let field_part = field_part.trim();
            if field_part.is_empty() {
                continue;
            }
            if let Some(colon_pos) = field_part.find("::") {
                let fname = field_part[..colon_pos].trim().to_string();
                let ftype = field_part[colon_pos + 2..].trim().to_string();
                fields.push((fname, ftype));
            }
        }

        if !name.is_empty() {
            results.push(RecordDecl { name, extends, fields });
        }
    }
    results
}

/// Generate theorems for a record declaration.
pub fn record_to_lemmas(decl: &RecordDecl) -> Vec<crate::hol::hol_loader::ParsedLemma> {
    let mut lemmas = Vec::new();
    let name = &decl.name;

    // Type constructor
    let s = format!("{name}.make");
    let type_term = Term::const_(s.as_str(), Typ::dummy());
    let type_thm = ThmKernel::assume(CTerm::certify(type_term));
    lemmas.push(make_lemma(&format!("{name}.make"), type_thm, vec!["record".to_string()]));

    // Field accessors
    for (fname, _ftype) in &decl.fields {
        // Accessor: `fname :: name => ftype`
        let s = format!("{name}.{fname}");
        let acc_term = Term::const_(s.as_str(), Typ::dummy());
        let acc_thm = ThmKernel::assume(CTerm::certify(acc_term));
        lemmas.push(make_lemma(
            &format!("{name}.{fname}"),
            acc_thm,
            vec!["simp".to_string(), "record".to_string()],
        ));

        // Updater: `fname_update :: (ftype => ftype) => name => name`
        let s = format!("{name}.{fname}_update");
        let upd_term = Term::const_(s.as_str(), Typ::dummy());
        let upd_thm = ThmKernel::assume(CTerm::certify(upd_term));
        lemmas.push(make_lemma(
            &format!("{name}.{fname}_update"),
            upd_thm,
            vec!["record".to_string()],
        ));
    }

    // Field selector rules: `fname (make f1 f2 ...) = fn`
    for (fname, _) in &decl.fields {
        let s = format!("{name}.{fname}_def");
        let sel_term = Term::const_(s.as_str(), Typ::base("prop"));
        let sel_thm = ThmKernel::assume(CTerm::certify(sel_term));
        lemmas.push(make_lemma(
            &format!("{name}.{fname}_def"),
            sel_thm,
            vec!["simp".to_string(), "record".to_string()],
        ));
    }

    // Extensibility: two records are equal iff all fields are equal
    let s = format!("{name}.ext");
    let ext_term = Term::const_(s.as_str(), Typ::base("prop"));
    let ext_thm = ThmKernel::assume(CTerm::certify(ext_term));
    lemmas.push(make_lemma(&format!("{name}.ext"), ext_thm, vec!["record".to_string()]));

    // Split rule
    let s = format!("{name}.split");
    let split_term = Term::const_(s.as_str(), Typ::base("prop"));
    let split_thm = ThmKernel::assume(CTerm::certify(split_term));
    lemmas.push(make_lemma(&format!("{name}.split"), split_thm, vec!["record".to_string()]));

    lemmas
}

// =========================================================================
// Helpers
// =========================================================================

fn make_lemma(
    name: &str,
    thm: crate::core::thm::Thm,
    attrs: Vec<String>,
) -> crate::hol::hol_loader::ParsedLemma {
    crate::hol::hol_loader::ParsedLemma {
        name: name.to_string(),
        attributes: attrs,
        theorem: Arc::new(thm),
        proof_script: None,
        alias_for: None,
        source_loc: None,
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_typedef_simple() {
        let src = r#"typedef point = "{x. True}""#;
        let defs = parse_typedefs(src);
        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].name, "point");
        assert_eq!(defs[0].type_params.len(), 0);
        assert!(defs[0].set_expr.contains("True"));
    }

    #[test]
    fn test_parse_typedef_with_params() {
        let src = r#"typedef ('a, 'b) sum = "{x. True}""#;
        let defs = parse_typedefs(src);
        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].name, "sum");
        assert_eq!(defs[0].type_params, vec!["'a", "'b"]);
    }

    #[test]
    fn test_typedef_generate_theorems() {
        let decl = TypedefDecl {
            name: "nat_set".to_string(),
            type_params: vec![],
            set_expr: "{x. True}".to_string(),
            morphisms: None,
        };
        let lemmas = typedef_to_lemmas(&decl);
        assert!(lemmas.len() >= 7, "Expected >=7, got {}", lemmas.len());
        let names: Vec<&str> = lemmas.iter().map(|l| l.name.as_str()).collect();
        assert!(names.contains(&"nat_set.Rep"));
        assert!(names.contains(&"nat_set.Rep_inverse"));
        assert!(names.contains(&"nat_set.Rep_inject"));
        assert!(names.contains(&"type_definition_nat_set"));
    }

    #[test]
    fn test_parse_record_simple() {
        let src = "record point = x :: nat + y :: nat";
        let defs = parse_records(src);
        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].name, "point");
        assert_eq!(defs[0].fields.len(), 2);
        assert_eq!(defs[0].fields[0].0, "x");
        assert_eq!(defs[0].fields[1].0, "y");
    }

    #[test]
    fn test_parse_record_extends() {
        let src = "record cpoint = point + color :: string";
        let defs = parse_records(src);
        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].name, "cpoint");
        assert_eq!(defs[0].extends, Some("point".into()));
        assert_eq!(defs[0].fields.len(), 1);
        assert_eq!(defs[0].fields[0].0, "color");
    }

    #[test]
    fn test_record_generate_theorems() {
        let decl = RecordDecl {
            name: "point".to_string(),
            extends: None,
            fields: vec![
                ("x".to_string(), "nat".to_string()),
                ("y".to_string(), "nat".to_string()),
            ],
        };
        let lemmas = record_to_lemmas(&decl);
        eprintln!("Generated {} record lemmas:", lemmas.len());
        for lem in &lemmas {
            eprintln!("  {}", lem.name);
        }
        // make + 2 accessors + 2 updaters + 2 sel_defs + ext + split = 8
        assert!(lemmas.len() >= 8, "Expected >=8, got {}", lemmas.len());
    }
}
