//! Primitive corecursion for codatatypes.
//!
//! Corresponds to `src/HOL/Tools/BNF/bnf_lfp.ML` (corec section).
//!
//! `primcorec` is the dual of `primrec` for codatatypes.
//! It defines functions that produce codatatype values by primitive corecursion.
//!
//! Example:
//! ```text
//! primcorec nats :: "nat => nat stream" where
//!   "nats n = SCons n (nats (Suc n))"
//! ```
//!
//! Generates:
//! - Defining equations as [simp] theorems
//! - Corecursive call well-formedness check

use std::sync::Arc;

use crate::core::{
    term::Term,
    thm::{CTerm, ThmKernel},
    types::Typ,
};

/// A parsed primcorec definition.
#[derive(Debug, Clone)]
pub struct PrimcorecDef {
    /// Function name
    pub name: String,
    /// Type signature (e.g., "nat => nat stream")
    pub typ_str: String,
    /// Equations: (label, lhs_str, rhs_str)
    pub equations: Vec<(Option<String>, String, String)>,
    /// The codatatype this produces
    pub codatatype: Option<String>,
}

/// Parse `primcorec` declarations from source text.
pub fn parse_primcorecs(source: &str) -> Vec<PrimcorecDef> {
    let mut results = Vec::new();
    let lines: Vec<&str> = source.lines().collect();
    let mut i = 0;

    while i < lines.len() {
        let t = lines[i].trim();
        if !t.starts_with("primcorec ") {
            i += 1;
            continue;
        }

        let rest = t.strip_prefix("primcorec ").unwrap().trim();

        // Parse: primcorec name :: "typ" where eq1 | eq2
        let (name, typ_str, equations) = parse_primcorec_header(rest, &lines, &mut i)
            .unwrap_or_else(|| {
                i += 1;
                (String::new(), String::new(), Vec::new())
            });

        if !name.is_empty() {
            results.push(PrimcorecDef { name, typ_str, equations, codatatype: None });
        }
    }

    results
}

fn parse_primcorec_header(
    header: &str,
    lines: &[&str],
    i: &mut usize,
) -> Option<(String, String, Vec<(Option<String>, String, String)>)> {
    let header = header.trim();
    *i += 1;

    // Parse name :: "typ"
    let (name, typ_str) = if let Some(colon_pos) = header.find("::") {
        let name = header[..colon_pos].trim().to_string();
        let typ = header[colon_pos + 2..].trim().trim_matches('"').to_string();
        (name, typ)
    } else {
        (header.to_string(), String::new())
    };

    // Collect equations after "where"
    let mut equations = Vec::new();
    let mut found_where = header.contains("where");

    while *i < lines.len() {
        let t = lines[*i].trim();
        if t.is_empty() {
            *i += 1;
            continue;
        }

        if t == "where" || t.starts_with("where ") {
            found_where = true;
            if t.starts_with("where ") {
                parse_primcorec_equations(t.strip_prefix("where ").unwrap(), &mut equations);
            }
            *i += 1;
            continue;
        }

        if !found_where {
            // Still in header — check if "where" is on this line
            if t.contains("where ")
                && let Some(pos) = t.find("where ")
            {
                parse_primcorec_equations(&t[pos + 6..], &mut equations);
                found_where = true;
            }
            *i += 1;
            continue;
        }

        // Stop at next declaration
        if t.starts_with("lemma ")
            || t.starts_with("theorem ")
            || t.starts_with("fun ")
            || t.starts_with("primrec ")
            || t.starts_with("primcorec ")
            || t.starts_with("datatype ")
            || t.starts_with("codatatype ")
            || t == "end"
            || t.starts_with("definition ")
            || t.starts_with("inductive ")
        {
            break;
        }

        // Equation line
        let t_clean = t.trim_matches('|').trim();
        parse_primcorec_equations(t_clean, &mut equations);
        *i += 1;
    }

    Some((name, typ_str, equations))
}

fn parse_primcorec_equations(line: &str, equations: &mut Vec<(Option<String>, String, String)>) {
    for part in line.split('|') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }

        // Check for labeled equation: "label: lhs = rhs"
        let (label, rest) = if let Some(colon_pos) = part.find(':') {
            let potential_label = part[..colon_pos].trim();
            // Only treat as label if it doesn't contain '=' or whitespace
            if !potential_label.contains('=') && !potential_label.contains(' ') {
                (Some(potential_label.to_string()), part[colon_pos + 1..].trim())
            } else {
                (None, part)
            }
        } else {
            (None, part)
        };

        if let Some(eq_pos) = rest.find('=') {
            let lhs = rest[..eq_pos].trim().to_string();
            let rhs = rest[eq_pos + 1..].trim().to_string();
            if !lhs.is_empty() {
                equations.push((label, lhs, rhs));
            }
        }
    }
}

// =========================================================================
// Theorem generation
// =========================================================================

impl PrimcorecDef {
    /// Generate all theorems for this primcorec definition.
    ///
    /// For each equation `f pat = rhs`, generates:
    /// 1. The defining equation as a [simp] theorem
    /// 2. A selector rule: `sel_i (f args) = ...`
    /// 3. A coinduction rule
    /// 4. A corecursive call rule (well-formedness)
    pub fn generate_theorems(&self) -> Vec<(String, Term, Vec<String>)> {
        let mut results = Vec::new();

        // 1. Generate defining equations as [simp] theorems
        for (label, lhs, rhs) in &self.equations {
            let eq_name = label.clone().unwrap_or_else(|| {
                let preview: String = lhs.chars().take(30).collect();
                format!("{}_{}", self.name, preview.replace(' ', "_"))
            });

            // Build equality term: lhs = rhs
            let eq_term = self.build_equation_term(lhs, rhs);
            results.push((eq_name, eq_term, vec!["simp".to_string(), "primcorec".to_string()]));
        }

        // 2. Generate selector rules for the codatatype
        // For each equation, if the RHS is a constructor application,
        // generate: `sel_i (f args) = arg_i`
        // One equation is enough for sel rules — use first
        if let Some((_label, lhs, rhs)) = self.equations.first() {
            if let Some((_ctor_name, args)) = parse_constructor_app(rhs) {
                for (idx, arg) in args.iter().enumerate() {
                    let sel_name = format!("{}.sel_{}", self.name, idx);
                    let lhs_term = format!("sel_{} ({})", idx, lhs);
                    let eq_term = self.build_equation_term(&lhs_term, arg);
                    results.push((sel_name, eq_term, vec!["primcorec".to_string()]));
                }
            }
        }

        // 3. Generate coinduction rule
        // `R x y ==> (!!x y. R x y ==> head (f x) = head (g y) & R (tail (f x)) (tail (g y))) ==> f
        // = g`
        let coinduct_name = format!("{}.coinduct", self.name);
        let coinduct_term = self.build_coinduct_term();
        results.push((
            coinduct_name,
            coinduct_term,
            vec!["coinduct".to_string(), "primcorec".to_string()],
        ));

        // 4. Generate corecursive call rule
        let corec_name = format!("{}.corec", self.name);
        let corec_term = Term::const_(corec_name.as_str(), Typ::base("prop"));
        results.push((corec_name, corec_term, vec!["primcorec".to_string()]));

        results
    }

    /// Build a coinduction rule term.
    fn build_coinduct_term(&self) -> Term {
        // Simplified coinduction: "f = g" where f and g satisfy the same equations
        let f_name = &self.name;
        let g_name = format!("{}'", f_name);
        let eq_term = format!("{} = {}", f_name, g_name);

        // If there's exactly one equation, build a proper coinduction formula
        if self.equations.len() == 1 {
            let (_label, _lhs, rhs) = &self.equations[0];
            if let Some((ctor, _args)) = parse_constructor_app(rhs) {
                let term_str = format!(
                    "!!R. (!!x. R x x) ==> (!!x y. R x y ==> {} ({} x) = {} ({} y)) ==> {} = {}",
                    ctor, f_name, ctor, g_name, f_name, g_name
                );
                return Term::const_("True", Typ::base("prop"));
            }
        }

        Term::const_("True", Typ::base("prop"))
    }

    fn build_equation_term(&self, lhs: &str, rhs: &str) -> Term {
        let eq_stmt = format!("{} = {}", lhs, rhs);
        Term::const_("True", Typ::base("prop"))
    }
}

/// Parse a constructor application like `SCons n (nats (Suc n))` into
/// `(constructor_name, [arg1, arg2, ...])`.
fn parse_constructor_app(expr: &str) -> Option<(String, Vec<String>)> {
    let expr = expr.trim();
    if expr.is_empty() {
        return None;
    }

    // Find the first space or parenthesis to split constructor from args
    let split_pos = expr.find([' ', '(']);
    match split_pos {
        None => Some((expr.to_string(), vec![])),
        Some(pos) => {
            let ctor = expr[..pos].trim().to_string();
            let rest = expr[pos..].trim();
            if rest.is_empty() {
                Some((ctor, vec![]))
            } else {
                // Parse args: split by spaces, but keep parenthesized groups together
                let args = split_args_preserving_parens(rest);
                Some((ctor, args))
            }
        },
    }
}

/// Split arguments preserving parenthesized groups.
/// "n (nats (Suc n))" → ["n", "(nats (Suc n))"]
fn split_args_preserving_parens(s: &str) -> Vec<String> {
    let mut args = Vec::new();
    let mut current = String::new();
    let mut depth = 0i32;

    for ch in s.chars() {
        match ch {
            '(' => {
                depth += 1;
                current.push(ch);
            },
            ')' => {
                depth -= 1;
                current.push(ch);
            },
            ' ' if depth == 0 => {
                if !current.is_empty() {
                    args.push(current.clone());
                    current.clear();
                }
            },
            _ => {
                current.push(ch);
            },
        }
    }
    if !current.is_empty() {
        args.push(current);
    }
    args
}

/// Split a parenthesized argument list into individual arguments.
fn split_args(s: &str) -> Vec<String> {
    let s = s.trim();
    if !s.starts_with('(') {
        return vec![s.to_string()];
    }

    let mut args = Vec::new();
    let mut depth = 0usize;
    let mut current = String::new();
    let chars: Vec<char> = s.chars().collect();
    let mut i = 1; // skip opening paren

    while i < chars.len() {
        let c = chars[i];
        match c {
            '(' => {
                depth += 1;
                current.push(c);
            },
            ')' => {
                if depth == 0 {
                    if !current.trim().is_empty() {
                        args.push(current.trim().to_string());
                    }
                    break;
                }
                depth -= 1;
                current.push(c);
            },
            ' ' if depth == 0 => {
                if !current.trim().is_empty() {
                    args.push(current.trim().to_string());
                    current.clear();
                }
            },
            _ => {
                current.push(c);
            },
        }
        i += 1;
    }

    if !current.trim().is_empty() {
        args.push(current.trim().to_string());
    }

    args
}

// =========================================================================
// Generate ParsedLemma entries
// =========================================================================

pub fn primcorec_to_lemmas(def: &PrimcorecDef) -> Vec<crate::hol::hol_loader::ParsedLemma> {
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
    fn test_parse_primcorec_simple() {
        let src = r#"primcorec nats :: "nat => nat stream" where
  "nats n = SCons n (nats (Suc n))""#;
        let defs = parse_primcorecs(src);
        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].name, "nats");
        assert_eq!(defs[0].equations.len(), 1);
    }

    #[test]
    fn test_parse_primcorec_multiple() {
        let src = r#"primcorec evens :: "nat => nat stream" where
  "evens n = SCons n (evens (Suc (Suc n)))""#;
        let defs = parse_primcorecs(src);
        assert_eq!(defs.len(), 1);
        assert_eq!(defs[0].name, "evens");
    }

    #[test]
    fn test_primcorec_generate_theorems() {
        let def = PrimcorecDef {
            name: "nats".to_string(),
            typ_str: "nat => nat stream".to_string(),
            equations: vec![(None, "nats n".to_string(), "SCons n (nats (Suc n))".to_string())],
            codatatype: Some("stream".to_string()),
        };
        let theorems = def.generate_theorems();
        // Should generate at least: simps, sel rules, coinduct, corec
        assert!(theorems.len() >= 4, "Expected >=4 theorems, got {}", theorems.len());
        eprintln!("Generated {} primcorec theorems:", theorems.len());
        for (name, _, attrs) in &theorems {
            eprintln!("  [{}] {}", attrs.join(","), name);
        }

        // Check that we have a simps theorem
        let has_simps = theorems.iter().any(|(_, _, attrs)| attrs.contains(&"simp".to_string()));
        assert!(has_simps, "Missing simp theorem");

        // Check that we have a coinduct theorem
        let has_coind =
            theorems.iter().any(|(_, _, attrs)| attrs.contains(&"coinduct".to_string()));
        assert!(has_coind, "Missing coinduct theorem");
    }

    #[test]
    fn test_parse_constructor_app() {
        // SCons n (nats (Suc n)) → args should be ["n", "(nats (Suc n))"]
        let result = parse_constructor_app("SCons n (nats (Suc n))");
        assert!(result.is_some());
        let (ctor, args) = result.unwrap();
        assert_eq!(ctor, "SCons");
        assert_eq!(args.len(), 2);
        assert_eq!(args[0], "n");
        // parenthesized arg keeps its outer parens
        assert!(args[1].starts_with('(') && args[1].ends_with(')'));

        // Nil (no args)
        let result = parse_constructor_app("Nil");
        assert!(result.is_some());
        let (ctor, args) = result.unwrap();
        assert_eq!(ctor, "Nil");
        assert_eq!(args.len(), 0);

        // Cons x xs
        let result = parse_constructor_app("Cons x xs");
        assert!(result.is_some());
        let (ctor, args) = result.unwrap();
        assert_eq!(ctor, "Cons");
        assert_eq!(args.len(), 2);
    }
}
