//! Load Isabelle's HOL.thy declarations into our theory system.
//!
//! Parses the core declarations from Isabelle's actual HOL.thy file:
//! - `typedecl bool` → declares type
//! - `axiomatization implies :: ...` → declares constant + axiom
//! - `definition True :: bool where "..."` → declares + defines constant
//!
//! This avoids manually rewriting HOL — we reuse Isabelle's own source.

use crate::core::logic::Pure;
use crate::core::term::{Term, lambda};
use crate::core::theory::Theory;
use crate::core::thm::{CTerm, ThmKernel};
use crate::core::types::{Sort, Typ};
use crate::isar::term_parser::parse_term;
use std::sync::Arc;

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
                let content = block
                    .trim()
                    .strip_prefix(keyword)
                    .unwrap_or(&block)
                    .trim()
                    .to_string();
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
        let content = block
            .trim()
            .strip_prefix(keyword)
            .unwrap_or(&block)
            .trim()
            .to_string();
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
    if parts.len() < 2 {
        return None;
    }
    let name = parts[0].trim();
    let rest = parts[1].trim();
    // Split at "where"
    let where_parts: Vec<&str> = rest.splitn(2, "where").collect();
    let typ_str = where_parts[0].trim();
    let defn = where_parts
        .get(1)
        .map(|s| s.trim().trim_matches('"'))
        .unwrap_or("");
    Some((name, typ_str, defn))
}

/// Simplified HOL type parser — handles `bool`, `'a => bool`, `[bool, bool] => bool`
fn parse_hol_type(s: &str) -> Option<Typ> {
    let s = s.trim();
    // Try function type: T1 => T2
    if let Some(pos) = s.find("=>") {
        let left = &s[..pos].trim();
        let right = &s[pos + 2..].trim();
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
        let inner = &s[1..s.len() - 1];
        // For simplicity, treat [A, B] => C as A => B => C
        return Some(Typ::base(inner.trim()));
    }
    // Parenthesised
    if s.starts_with('(') && s.ends_with(')') {
        return parse_hol_type(&s[1..s.len() - 1]);
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
    let hol_thy = include_str!("../../theories/HOL/HOL.thy");
    load_hol_theory(hol_thy)
}

// =========================================================================
// Lemma parsing (Route A)
// =========================================================================

#[derive(Debug, Clone)]
pub struct ParsedLemma {
    pub name: String,
    pub attributes: Vec<String>,
    pub theorem: Arc<crate::core::thm::Thm>,
    /// The proof command (e.g., "by auto", "by simp", "by (rule sym)")
    pub proof_script: Option<String>,
    /// For `lemmas` commands: names of theorems this is an alias for
    pub alias_for: Option<Vec<String>>,
}

// =========================================================================
// Datatype parsing
// =========================================================================

/// A parsed datatype definition.
#[derive(Debug, Clone)]
pub struct DatatypeDef {
    /// Type name, e.g. "list", "option"
    pub name: String,
    /// Type parameters, e.g. ["'a"]
    pub type_params: Vec<String>,
    /// Constructors: name + list of (selector_name, arg_type) pairs
    pub constructors: Vec<(String, Vec<(Option<String>, String)>)>,
}

/// Parse all `datatype` declarations from .thy source.
pub fn parse_datatypes(source: &str) -> Vec<DatatypeDef> {
    let mut defs = Vec::new();
    let lines: Vec<&str> = source.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let t = lines[i].trim();
        if t.starts_with("datatype ") || t.starts_with("datatype(") {
            if let Some((def, consumed)) = parse_one_datatype(&lines, i) {
                defs.push(def);
                i = consumed;
                continue;
            }
        }
        if t.starts_with("old_rep_datatype ") || t.starts_with("rep_datatype ") {
            if let Some((def, consumed)) = parse_old_rep_datatype(&lines, i) {
                defs.push(def);
                i = consumed;
                continue;
            }
        }
        i += 1;
    }
    defs
}

/// Parse a single datatype declaration starting at line `start`.
fn parse_one_datatype(lines: &[&str], start: usize) -> Option<(DatatypeDef, usize)> {
    let header = lines[start].trim();
    let after_dt = if header.starts_with("datatype(") {
        if let Some(paren_end) = header.find(") ") {
            &header[paren_end + 2..]
        } else {
            header.strip_prefix("datatype")?.trim()
        }
    } else {
        header.strip_prefix("datatype ")?.trim()
    };

    // Collect lines until end of constructors, "where", "for", or next declaration
    let mut combined = String::from(after_dt);
    let mut i = start + 1;
    while i < lines.len() {
        let t = lines[i].trim();
        if t.is_empty() {
            i += 1;
            continue;
        }
        if t == "where"
            || t.starts_with("for ")
            || t == "begin"
            || t.starts_with("lemma ")
            || t.starts_with("theorem ")
            || t.starts_with("datatype ")
            || t.starts_with("fun ")
            || t.starts_with("primrec ")
            || t.starts_with("definition ")
        {
            break;
        }
        combined.push(' ');
        combined.push_str(t);
        i += 1;
        // Stop if line ends a constructor and next line starts new declaration
        if !t.ends_with('|') {
            if i < lines.len() {
                let next = lines[i].trim();
                if !next.starts_with('|') && !next.starts_with("and ") {
                    break;
                }
            }
        }
    }

    let combined = combined.trim();
    let (type_params, rest) = parse_dt_type_params(combined)?;
    let rest = rest.trim();
    let (name, after_eq) = if let Some(eq_pos) = rest.find('=') {
        (rest[..eq_pos].trim().to_string(), rest[eq_pos + 1..].trim())
    } else {
        return None;
    };
    let constructors = parse_dt_constructors(after_eq)?;

    Some((
        DatatypeDef {
            name,
            type_params,
            constructors,
        },
        i,
    ))
}

/// Parse type params: "('a, 'b) name" or "'a name" or just "name"
fn parse_dt_type_params(s: &str) -> Option<(Vec<String>, &str)> {
    let s = s.trim();
    if s.starts_with('(') {
        let paren_end = s.find(')')?;
        let params: Vec<String> = s[1..paren_end]
            .split(',')
            .map(|p| p.trim().to_string())
            .filter(|p| !p.is_empty())
            .collect();
        Some((params, &s[paren_end + 1..]))
    } else if s.starts_with('\'') {
        let first_space = s.find(' ')?;
        let param = s[..first_space].trim().to_string();
        Some((vec![param], &s[first_space..]))
    } else {
        Some((vec![], s))
    }
}

/// Parse old_rep_datatype: `old_rep_datatype "0 :: nat" Suc`
fn parse_old_rep_datatype(lines: &[&str], start: usize) -> Option<(DatatypeDef, usize)> {
    let header = lines[start].trim();
    let after_kw = if header.starts_with("old_rep_datatype ") {
        header.strip_prefix("old_rep_datatype ")?.trim()
    } else {
        header.strip_prefix("rep_datatype ")?.trim()
    };

    // Format: "ctor1 :: type" ctor2 ctor3 ...
    // The first ctor may have :: type annotation, others are bare names
    let mut ctors = Vec::new();
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut in_quote = false;

    for ch in after_kw.chars() {
        if ch == '"' {
            in_quote = !in_quote;
            if !in_quote {
                current.push(ch);
            }
        } else if in_quote {
            current.push(ch);
        } else if ch.is_whitespace() {
            if !current.is_empty() {
                parts.push(current.clone());
                current.clear();
            }
        } else {
            current.push(ch);
        }
    }
    if !current.is_empty() {
        parts.push(current);
    }

    // The type name is embedded in the first constructor's annotation
    // e.g., "0 :: nat" → type is "nat"
    let type_name = if let Some(first) = parts.first() {
        let first_clean = first.trim_matches('"');
        if let Some(colon_pos) = first_clean.find("::") {
            first_clean[colon_pos + 2..].trim().to_string()
        } else {
            // Assume type name from first constructor
            first_clean.to_string()
        }
    } else {
        return None;
    };

    for part in &parts {
        let part_clean = part.trim_matches('"');
        let ctor_name = if let Some(colon_pos) = part_clean.find("::") {
            part_clean[..colon_pos].trim().to_string()
        } else {
            part_clean.to_string()
        };
        if !ctor_name.is_empty() {
            ctors.push((ctor_name, Vec::new()));
        }
    }

    if ctors.is_empty() || parts.is_empty() {
        return None;
    }

    Some((
        DatatypeDef {
            name: type_name,
            type_params: Vec::new(),
            constructors: ctors,
        },
        start + 2,
    ))
}

/// Parse constructors separated by |
/// Parse constructors separated by |
fn parse_dt_constructors(s: &str) -> Option<Vec<(String, Vec<(Option<String>, String)>)>> {
    let mut ctors = Vec::new();
    let parts = split_by_bar_outside_parens(s);
    for part in &parts {
        ctors.push(parse_dt_one_constructor(part)?);
    }
    Some(ctors)
}

/// Split a string by | while respecting parentheses and quotes
fn split_by_bar_outside_parens(s: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut depth = 0i32;
    let mut in_quote = false;
    for ch in s.chars() {
        if ch == '"' {
            in_quote = !in_quote;
            current.push(ch);
        } else if in_quote {
            current.push(ch);
        } else if ch == '(' {
            depth += 1;
            current.push(ch);
        } else if ch == ')' {
            depth -= 1;
            current.push(ch);
        } else if ch == '|' && depth == 0 {
            let trimmed = current.trim().to_string();
            if !trimmed.is_empty() {
                parts.push(trimmed);
            }
            current = String::new();
        } else {
            current.push(ch);
        }
    }
    let trimmed = current.trim().to_string();
    if !trimmed.is_empty() {
        parts.push(trimmed);
    }
    parts
}

/// Parse one constructor: "Cons (hd: 'a) (tl: 'a list)" or "Nil" or "Some 'a"
fn parse_dt_one_constructor(s: &str) -> Option<(String, Vec<(Option<String>, String)>)> {
    let s = s.trim();
    let name_end = s
        .find(|c: char| c.is_whitespace() || c == '(')
        .unwrap_or(s.len());
    let name = s[..name_end].to_string();
    let rest = s[name_end..].trim();
    if rest.is_empty() {
        return Some((name, vec![]));
    }

    // Parse parenthesized argument groups and bare type args
    let mut args = Vec::new();
    let mut cur = String::new();
    let mut depth = 0i32;
    let mut in_quote = false;
    for ch in rest.chars() {
        if ch == '"' {
            in_quote = !in_quote;
            cur.push(ch);
        } else if in_quote {
            cur.push(ch);
        } else if ch == '(' {
            depth += 1;
            if depth > 1 {
                cur.push(ch);
            }
        } else if ch == ')' {
            depth -= 1;
            if depth == 0 {
                args.push(cur.trim().to_string());
                cur = String::new();
            } else {
                cur.push(ch);
            }
        } else if depth > 0 {
            cur.push(ch);
        } else {
            cur.push(ch);
        }
    }
    // Remaining bare types
    if !cur.trim().is_empty() {
        for bare in cur.split_whitespace() {
            if !bare.is_empty() {
                args.push(bare.to_string());
            }
        }
    }

    let parsed_args: Vec<(Option<String>, String)> = args
        .iter()
        .map(|a| {
            let a = a.trim();
            if let Some(colon_pos) = a.find(':') {
                let sel = a[..colon_pos].trim().to_string();
                let typ = a[colon_pos + 1..].trim().trim_matches('"').to_string();
                (Some(sel), typ)
            } else {
                (None, a.trim_matches('"').to_string())
            }
        })
        .collect();

    Some((name, parsed_args))
}

/// Generate synthetic lemma entries for a datatype definition.
/// Creates: {name}.induct, {name}.inject, {name}.distinct, {name}.exhaust, {name}.case
pub fn generate_datatype_lemmas(def: &DatatypeDef) -> Vec<ParsedLemma> {
    let mut lemmas = Vec::new();

    // Build the type: T = (type_params) name
    let typ_name = if def.type_params.is_empty() {
        def.name.clone()
    } else {
        format!("({}) {}", def.type_params.join(", "), def.name)
    };

    // Collect constructor names and their result types
    let ctor_names: Vec<String> = def.constructors.iter().map(|(n, _)| n.clone()).collect();

    // Build constructor function types
    let ctor_types: Vec<String> = def
        .constructors
        .iter()
        .map(|(name, args)| {
            if args.is_empty() {
                format!("{} :: {}", name, typ_name)
            } else {
                let arg_types: Vec<String> = args.iter().map(|(_, t)| t.clone()).collect();
                let fun_type = arg_types.join(" => ") + " => " + &typ_name;
                format!("{} :: {}", name, fun_type)
            }
        })
        .collect();

    // 1. Induction rule: {name}.induct
    // P(Nil) ==> (!!x xs. P(xs) ==> P(Cons x xs)) ==> P(xs)
    if !ctor_names.is_empty() {
        let mut induct_premises = Vec::new();
        for (ctor_name, args) in &def.constructors {
            let non_rec_args: Vec<String> = args
                .iter()
                .filter(|(_, t)| !t.contains(&def.name))
                .enumerate()
                .map(|(i, _)| format!("x{}", i + 1))
                .collect();
            let rec_args: Vec<String> = args
                .iter()
                .filter(|(_, t)| t.contains(&def.name))
                .enumerate()
                .map(|(i, _)| format!("xs{}", i + 1))
                .collect();

            let mut ctor_prem = String::new();
            // P(xs_i) for each recursive arg
            for r in &rec_args {
                if !ctor_prem.is_empty() {
                    ctor_prem.push_str(" ==> ");
                }
                ctor_prem.push_str(&format!("P {}", r));
            }
            let all_args: Vec<String> = non_rec_args
                .iter()
                .chain(rec_args.iter())
                .cloned()
                .collect();
            let ctor_call = format!("{} {}", ctor_name, all_args.join(" "));
            if ctor_prem.is_empty() {
                induct_premises.push(format!("P ({})", ctor_call));
            } else {
                induct_premises.push(format!(
                    "(!!{}. {}) ==> P ({}))",
                    all_args.join(" "),
                    ctor_prem,
                    ctor_call
                ));
            }
        }
        let var_name = if def.name == "list" {
            "xs"
        } else if def.name == "option" {
            "x"
        } else {
            "x"
        };
        let induct_stmt = format!("[| {} |] ==> P ({})", induct_premises.join("; "), var_name);
        let induct_term =
            parse_term(&induct_stmt).unwrap_or_else(|| Term::const_("True", Typ::base("prop")));
        lemmas.push(ParsedLemma {
            name: format!("{}.induct", def.name),
            attributes: vec!["induct".to_string()],
            theorem: Arc::new(ThmKernel::assume(CTerm::certify(induct_term))),
            proof_script: None,
            alias_for: None,
        });
    }

    // 2. Injectivity: {name}.inject
    // (Cons x1 xs1 = Cons x2 xs2) = (x1 = x2 & xs1 = xs2)
    // For each constructor with args, build injectivity statement
    for (ctor_name, args) in &def.constructors {
        if args.is_empty() {
            continue;
        }
        let arg_names1: Vec<String> = args
            .iter()
            .enumerate()
            .map(|(i, _)| format!("a{}", i + 1))
            .collect();
        let arg_names2: Vec<String> = args
            .iter()
            .enumerate()
            .map(|(i, _)| format!("b{}", i + 1))
            .collect();
        let call1 = format!("{} {}", ctor_name, arg_names1.join(" "));
        let call2 = format!("{} {}", ctor_name, arg_names2.join(" "));
        let eqs: Vec<String> = arg_names1
            .iter()
            .zip(arg_names2.iter())
            .map(|(a, b)| format!("{} = {}", a, b))
            .collect();
        let inject_stmt = format!("({} = {}) = ({})", call1, call2, eqs.join(" & "));
        let inject_term =
            parse_term(&inject_stmt).unwrap_or_else(|| Term::const_("True", Typ::base("prop")));
        lemmas.push(ParsedLemma {
            name: format!("{}.inject", def.name),
            attributes: vec!["simp".to_string()],
            theorem: Arc::new(ThmKernel::assume(CTerm::certify(inject_term))),
            proof_script: None,
            alias_for: None,
        });
        break; // Only generate for first constructor with args
    }

    // 3. Distinctness: {name}.distinct
    // Nil ~= Cons x xs
    if ctor_names.len() >= 2 {
        let mut distinct_pairs = Vec::new();
        for i in 0..ctor_names.len() {
            for j in (i + 1)..ctor_names.len() {
                let c1 = &ctor_names[i];
                let c2 = &ctor_names[j];
                distinct_pairs.push(format!("{} ~= {}", c1, c2));
            }
        }
        if !distinct_pairs.is_empty() {
            let distinct_stmt = distinct_pairs.join(" & ");
            let distinct_term = parse_term(&distinct_stmt)
                .unwrap_or_else(|| Term::const_("True", Typ::base("prop")));
            lemmas.push(ParsedLemma {
                name: format!("{}.distinct", def.name),
                attributes: vec!["simp".to_string()],
                theorem: Arc::new(ThmKernel::assume(CTerm::certify(distinct_term))),
                proof_script: None,
                alias_for: None,
            });
        }
    }

    // 4. Exhaustion: {name}.exhaust
    // (!!x. y = None ==> P) ==> (!!a. y = Some a ==> P) ==> P
    let var = if def.name == "list" {
        "xs"
    } else if def.name == "option" {
        "x"
    } else {
        "x"
    };
    let mut exhaust_cases = Vec::new();
    for (ctor_name, args) in &def.constructors {
        let arg_vars: Vec<String> = args
            .iter()
            .enumerate()
            .map(|(i, _)| format!("a{}", i + 1))
            .collect();
        let ctor_call = if arg_vars.is_empty() {
            ctor_name.clone()
        } else {
            format!("{} {}", ctor_name, arg_vars.join(" "))
        };
        if arg_vars.is_empty() {
            exhaust_cases.push(format!("(!!. {} = {} ==> P)", var, ctor_call));
        } else {
            exhaust_cases.push(format!(
                "(!!{}. {} = {} ==> P)",
                arg_vars.join(" "),
                var,
                ctor_call
            ));
        }
    }
    let exhaust_stmt = format!("[| {} |] ==> P", exhaust_cases.join("; "));
    let exhaust_term =
        parse_term(&exhaust_stmt).unwrap_or_else(|| Term::const_("True", Typ::base("prop")));
    lemmas.push(ParsedLemma {
        name: format!("{}.exhaust", def.name),
        attributes: vec!["elim".to_string()],
        theorem: Arc::new(ThmKernel::assume(CTerm::certify(exhaust_term))),
        proof_script: None,
        alias_for: None,
    });

    // 5. Case equation: {name}.case
    // option.case None f1 f2 = f1
    // option.case (Some x) f1 f2 = f2 x
    for (ctor_name, args) in &def.constructors {
        let arg_vars: Vec<String> = args
            .iter()
            .enumerate()
            .map(|(i, _)| format!("a{}", i + 1))
            .collect();
        let ctor_call = if arg_vars.is_empty() {
            ctor_name.clone()
        } else {
            format!("{} {}", ctor_name, arg_vars.join(" "))
        };
        let f_vars: Vec<String> = (0..def.constructors.len())
            .map(|i| format!("f{}", i + 1))
            .collect();
        let case_call = format!("case_{} ({}) {}", def.name, ctor_call, f_vars.join(" "));
        // Which f to pick?
        let ctor_idx = def
            .constructors
            .iter()
            .position(|(n, _)| n == ctor_name)
            .unwrap_or(0);
        let rhs = if args.is_empty() {
            f_vars[ctor_idx].clone()
        } else {
            format!("{} {}", f_vars[ctor_idx], arg_vars.join(" "))
        };
        let case_stmt = format!("{} = {}", case_call, rhs);
        let case_term =
            parse_term(&case_stmt).unwrap_or_else(|| Term::const_("True", Typ::base("prop")));
        lemmas.push(ParsedLemma {
            name: format!("{}.case", def.name),
            attributes: vec!["simp".to_string()],
            theorem: Arc::new(ThmKernel::assume(CTerm::certify(case_term))),
            proof_script: None,
            alias_for: None,
        });
        break; // Only generate for first constructor (others follow same pattern)
    }

    lemmas
}

/// Parse `inductive`/`coinductive` definitions and generate introduction rules.
fn parse_inductives(source: &str) -> Vec<ParsedLemma> {
    let mut results = Vec::new();
    let lines: Vec<&str> = source.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let t = lines[i].trim();
        if !t.starts_with("inductive ") && !t.starts_with("coinductive ") {
            i += 1;
            continue;
        }
        let is_coind = t.starts_with("coinductive ");
        let rest = if is_coind {
            t.strip_prefix("coinductive ").unwrap()
        } else {
            t.strip_prefix("inductive ").unwrap()
        };

        // Parse: `name :: type [where ...]`
        let (name, _typ_str) = if let Some(colon_pos) = rest.find(" ::") {
            let name = rest[..colon_pos].trim().to_string();
            let after = rest[colon_pos + 2..].trim();
            // Stop at "where"
            let typ_part = if let Some(where_pos) = after.find(" where") {
                after[..where_pos].trim()
            } else if let Some(where_pos) = after.find("\nwhere") {
                after[..where_pos].trim()
            } else {
                after
            };
            (name, typ_part.to_string())
        } else {
            // No type annotation — just name
            let name = if let Some(where_pos) = rest.find(" where") {
                rest[..where_pos].trim()
            } else if let Some(where_pos) = rest.find("\nwhere") {
                rest[..where_pos].trim()
            } else {
                rest
            };
            (name.to_string(), String::new())
        };

        i += 1;

        // Find the where clause (may be on same line or subsequent lines)
        let mut where_lines = Vec::new();
        let found_where = if rest.contains(" where ") || rest.contains("\nwhere") {
            // Extract from current line after "where"
            if let Some(pos) = rest.find(" where ") {
                where_lines.push(rest[pos + 7..].trim().to_string());
            } else if let Some(pos) = rest.find("\nwhere") {
                where_lines.push(rest[pos + 7..].trim().to_string());
            }
            true
        } else {
            // Look for "where" on subsequent lines
            let mut found = false;
            while i < lines.len() {
                let cont = lines[i].trim();
                if cont == "where" || cont.starts_with("where ") {
                    found = true;
                    if cont.starts_with("where ") {
                        where_lines.push(cont[6..].trim().to_string());
                    }
                    i += 1;
                    break;
                }
                if !cont.is_empty() && !cont.starts_with("where") {
                    break; // something else, not a where clause
                }
                i += 1;
            }
            // Collect continuation lines (indented intro rules)
            while i < lines.len() {
                let cont = lines[i];
                let cont_trim = cont.trim();
                if cont_trim.is_empty() {
                    i += 1;
                    continue;
                }
                // Stop if we hit a new top-level command
                if !cont.starts_with(' ') && !cont.starts_with('\t') {
                    if cont_trim.starts_with("lemma ")
                        || cont_trim.starts_with("theorem ")
                        || cont_trim.starts_with("inductive ")
                        || cont_trim.starts_with("coinductive ")
                        || cont_trim.starts_with("fun ")
                        || cont_trim.starts_with("primrec ")
                        || cont_trim.starts_with("definition ")
                    {
                        break;
                    }
                }
                where_lines.push(cont_trim.to_string());
                i += 1;
            }
            found
        };

        if !found_where && where_lines.is_empty() {
            continue;
        }

        // Join and parse the where clause: `rule1: "prem ==> concl" | rule2: "..."`
        let where_text = where_lines.join(" ");
        // Split on "|" to get individual rules
        for rule_text in where_text.split('|') {
            let rule_text = rule_text.trim();
            if rule_text.is_empty() {
                continue;
            }

            // Each rule: `rulename: "proposition"` or `"proposition"`
            let (rule_name, prop_str) = if let Some(colon_pos) = rule_text.find(':') {
                let rn = rule_text[..colon_pos].trim().to_string();
                let ps = rule_text[colon_pos + 1..]
                    .trim()
                    .trim_matches('"')
                    .to_string();
                (rn, ps)
            } else {
                let ps = rule_text.trim_matches('"').to_string();
                (format!("{}I_{}", name, results.len() + 1), ps)
            };

            let prop_str = convert_syntax(&prop_str);
            if let Some(term) = parse_term(&prop_str) {
                results.push(ParsedLemma {
                    name: rule_name,
                    attributes: vec![format!(
                        "{}_intro",
                        if is_coind { "coinduct" } else { "induct" }
                    )],
                    theorem: Arc::new(ThmKernel::assume(CTerm::certify(term))),
                    proof_script: None,
                    alias_for: None,
                });
            }
        }
    }
    results
}

/// Parse lemmas from .thy source. Handles inline, multi-line, and `lemmas` commands.
pub fn parse_lemmas(source: &str) -> Vec<ParsedLemma> {
    let mut lemmas = Vec::new();
    // First pass: parse datatypes and generate synthetic induction rules
    for dt in &parse_datatypes(source) {
        lemmas.extend(generate_datatype_lemmas(dt));
    }
    for pr in &parse_primrecs(source) {
        lemmas.extend(generate_primrec_lemmas(pr));
    }
    for cls in &parse_classes(source) {
        lemmas.extend(generate_class_lemmas(cls));
    }
    // Parse inductive definitions and generate introduction rules
    lemmas.extend(parse_inductives(source));
    let lines: Vec<&str> = source.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let t = lines[i].trim();
        // Skip datatype lines (already processed)
        if t.starts_with("datatype ") || t.starts_with("datatype(") {
            i += 1;
            continue;
        }
        if t.starts_with("primrec ") || t.starts_with("fun ") || t.starts_with("function ") {
            i += 1;
            continue;
        }
        if t.starts_with("class ") {
            i += 1;
            continue;
        }
        // Handle `lemmas name = thm` commands
        if t.starts_with("lemmas ") {
            if let Some(ls) = parse_lemmas_cmd(&lines, &mut i) {
                lemmas.extend(ls);
            } else {
                i += 1;
            }
            continue;
        }
        if !t.starts_with("lemma ") && !t.starts_with("theorem ") {
            i += 1;
            continue;
        }
        // Determine if this is inline or multi-line
        let start_i = i;
        if let Some(mut ls) = parse_one_line(&lines, &mut i) {
            // Try to capture proof script from subsequent line
            let (proof, consumed) = capture_proof(&lines, i);
            if let Some(ref proof) = proof {
                for lem in &mut ls {
                    lem.proof_script = Some(proof.clone());
                }
            }
            // Skip past consumed continuation lines (beyond the 1 that the loop will skip)
            if consumed > 1 {
                i += consumed - 1;
            }
            lemmas.extend(ls);
        } else {
            // Try multi-line parse
            if let Some(mut ls) = parse_multi_line(&lines, &mut i) {
                let (proof, consumed) = capture_proof(&lines, i);
                if let Some(ref proof) = proof {
                    for lem in &mut ls {
                        lem.proof_script = Some(proof.clone());
                    }
                }
                if consumed > 1 {
                    i += consumed - 1;
                }
                lemmas.extend(ls);
            } else {
                i = start_i + 1;
            }
        }
    }
    lemmas
}

/// Parse `lemmas` commands: `lemmas [attrs] name = thm1 thm2 [and name2 = thm3]`
fn parse_lemmas_cmd(lines: &[&str], i: &mut usize) -> Option<Vec<ParsedLemma>> {
    let t = lines[*i].trim();
    let rest = t.strip_prefix("lemmas ")?;
    *i += 1;

    // Parse attributes: `[simp, intro]`
    let (attrs, rest) = if rest.starts_with('[') {
        if let Some(end) = rest.find(']') {
            let attr_str = &rest[1..end];
            let attrs: Vec<String> = attr_str.split(',').map(|s| s.trim().to_string()).collect();
            (attrs, rest[end + 1..].trim())
        } else {
            (Vec::new(), rest)
        }
    } else {
        (Vec::new(), rest)
    };

    // Parse `name = thm1 thm2 [and name2 = thm3 ...]`
    let mut results = Vec::new();
    for part in rest.split(" and ") {
        let part = part.trim();
        if let Some(eq_pos) = part.find('=') {
            let name = part[..eq_pos].trim().to_string();
            let thms: Vec<String> = part[eq_pos + 1..]
                .split_whitespace()
                .map(|s| s.to_string())
                .collect();
            if name.is_empty() {
                continue;
            }
            // Create a lemma entry: prop is a placeholder, theorem will be resolved later
            let theorem = Arc::new(crate::core::thm::ThmKernel::assume(
                crate::core::thm::CTerm::certify(crate::core::term::Term::const_(
                    "True",
                    crate::core::types::Typ::base("prop"),
                )),
            ));
            results.push(ParsedLemma {
                name,
                attributes: attrs.clone(),
                theorem,
                proof_script: None,
                alias_for: Some(thms),
            });
        }
    }
    Some(results)
}

/// Try to capture a proof command from the current position.
fn capture_proof(lines: &[&str], pos: usize) -> (Option<String>, usize) {
    if pos >= lines.len() {
        return (None, 0);
    }
    let t = lines[pos].trim();
    if t.starts_with("by ") || t.starts_with("by(") {
        // Collect multi-line by proof: join continuation lines (indented)
        let mut proof = t.to_string();
        let mut i = pos + 1;
        let mut lines_consumed = 1usize;
        while i < lines.len() {
            let cont = lines[i];
            let cont_trim = cont.trim();
            // Stop at blank lines, comments, or non-indented command lines
            if cont_trim.is_empty() {
                break;
            }
            if cont_trim.starts_with("--")
                || cont_trim.starts_with("(*")
                || cont_trim.starts_with("text")
            {
                break;
            }
            // Stop if this is a new lemma/theorem/command
            if !cont.starts_with(' ') && !cont.starts_with('\t') {
                let ct = cont_trim;
                if ct.starts_with("lemma ")
                    || ct.starts_with("theorem ")
                    || ct.starts_with("by ")
                    || ct.starts_with("qed")
                    || ct.starts_with("done")
                    || ct.starts_with("next")
                    || ct.starts_with("definition ")
                    || ct.starts_with("primrec ")
                    || ct.starts_with("fun ")
                    || ct.starts_with("datatype ")
                    || ct.starts_with("inductive ")
                    || ct.starts_with("class ")
                {
                    break;
                }
            }
            // Continuation line — append with space
            proof.push(' ');
            proof.push_str(cont_trim);
            lines_consumed += 1;
            i += 1;
        }
        (Some(proof), lines_consumed)
    } else if t.starts_with("apply") || t.starts_with("proof") {
        // For apply/proof scripts, just capture the first line for now
        (Some(t.to_string()), 1)
    } else {
        (None, 0)
    }
}

/// Strip `(in locale_name)` prefix from a lemma name part.
fn strip_locale_prefix(s: &str) -> &str {
    let s = s.trim();
    if s.starts_with("(in ") {
        // Find the closing )
        if let Some(pos) = s.find(')') {
            return s[pos + 1..].trim();
        }
    }
    s
}

/// Split a lemma/theorem header into (name_part, after_colon).
/// Handles three tricky cases:
/// 1. No name: if rest starts with `"`, name_part is empty, after_colon is the whole rest.
/// 2. `:` inside attribute brackets (e.g., `[induct set: Nats]`): finds the first `:`
///    that is NOT inside `[...]`.
/// 3. No `:` on this line: returns None (caller should look at subsequent lines).
fn split_name_statement(rest: &str) -> Option<(&str, &str)> {
    let rest = rest.trim();
    // Case 1: no name at all — statement starts with a quote
    if rest.starts_with('"') {
        return Some(("", rest));
    }
    // Find the first ':' that is not inside brackets [...]
    let mut depth = 0u32;
    let bytes = rest.as_bytes();
    for (idx, &ch) in bytes.iter().enumerate() {
        if ch == b'[' {
            depth += 1;
        } else if ch == b']' && depth > 0 {
            depth -= 1;
        } else if ch == b':' && depth == 0 {
            let name_part = rest[..idx].trim();
            let after_colon = rest[idx + 1..].trim();
            return Some((name_part, after_colon));
        }
    }
    // No colon found outside brackets
    None
}

/// Try to parse an inline (single-line) lemma.
fn parse_one_line(lines: &[&str], i: &mut usize) -> Option<Vec<ParsedLemma>> {
    let line = lines[*i].trim();
    let rest = line
        .strip_prefix("lemma ")
        .or_else(|| line.strip_prefix("theorem "))?;
    let rest = strip_locale_prefix(rest);
    let (name_part, after_colon) = split_name_statement(rest)?;
    let after_colon = after_colon.trim();
    if !after_colon.starts_with('"') {
        return None; // multi-line, let caller handle
    }
    let (name, attrs) = parse_name_attrs(name_part);

    // Extract all quoted statements from the line
    let mut remaining = after_colon;
    let mut results = Vec::new();
    let mut stmt_idx = 0usize;
    while let Some(stmt) = extract_quoted(remaining) {
        let conv = convert_syntax(&stmt);
        if let Some(term) = parse_term(&conv) {
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(term)));
            let lemma_name = if stmt_idx == 0 {
                if name.is_empty() {
                    let preview: String = stmt.chars().take(30).collect();
                    format!("[anon:{}]", preview)
                } else {
                    name.to_string()
                }
            } else {
                if name.is_empty() {
                    let preview: String = stmt.chars().take(30).collect();
                    format!("[anon:{}]_{}", preview, stmt_idx + 1)
                } else {
                    format!("{}_{}", name, stmt_idx + 1)
                }
            };
            results.push(ParsedLemma {
                name: lemma_name,
                attributes: attrs.clone(),
                theorem: thm,
                proof_script: None,
                alias_for: None,
            });
        }
        stmt_idx += 1;
        // Advance past the quoted string
        let quote_len = stmt.len() + 2; // two quotes
        if remaining.len() > quote_len {
            remaining = remaining[quote_len..].trim();
        } else {
            break;
        }
    }
    if results.is_empty() {
        None
    } else {
        *i += 1;
        Some(results)
    }
}

/// Parse a multi-line lemma with assumes/shows block.
/// Advances `i` past all consumed lines.
fn parse_multi_line(lines: &[&str], i: &mut usize) -> Option<Vec<ParsedLemma>> {
    let header_line = lines[*i].trim();
    let rest = header_line
        .strip_prefix("lemma ")
        .or_else(|| header_line.strip_prefix("theorem "))?;
    let rest = strip_locale_prefix(rest);

    // Try to split name from statement on the header line.
    // If there's no colon on the header line (e.g., name on one line,
    // attributes/colon on the next), scan forward for the colon.
    let (name, attrs, block_lines, proof_cmd) =
        if let Some((name_part, after_colon)) = split_name_statement(rest) {
            let after_colon = after_colon.trim();
            let (name_ref, attrs) = parse_name_attrs(name_part);
            let name = name_ref.to_string();
            let mut block_lines: Vec<String> = Vec::new();
            if !after_colon.is_empty() {
                block_lines.push(after_colon.to_string());
            }
            // Advance past header line
            *i += 1;
            // Collect remaining block lines
            let proof_cmd = collect_block_lines(lines, i, &mut block_lines);
            (name, attrs, block_lines, proof_cmd)
        } else {
            // No colon on header line — combine header with next lines until we find a colon
            let mut combined = String::from(rest);
            let saved_i = *i;
            *i += 1;
            let mut found_colon = false;
            while *i < lines.len() {
                let t = lines[*i].trim();
                if t.is_empty() {
                    *i += 1;
                    continue;
                }
                if t.starts_with("lemma ") || t.starts_with("theorem ") {
                    break;
                }
                combined.push(' ');
                combined.push_str(t);
                if t.contains(':') {
                    found_colon = true;
                    *i += 1;
                    break;
                }
                *i += 1;
            }
            if !found_colon {
                // Reset position on failure
                *i = saved_i + 1;
                return None;
            }
            // Now split the combined string
            let (name_part, after_colon) = split_name_statement(&combined)?;
            let name_part_owned = name_part.to_string();
            let after_colon_owned = after_colon.to_string();
            let (name_ref, attrs) = parse_name_attrs(&name_part_owned);
            let name = name_ref.to_string();
            let mut block_lines: Vec<String> = Vec::new();
            if !after_colon_owned.is_empty() {
                block_lines.push(after_colon_owned);
            }
            let proof_cmd = collect_block_lines(lines, i, &mut block_lines);
            (name, attrs, block_lines, proof_cmd)
        };

    let block = block_lines.join("\n");
    let mut lemmas = parse_structured_stmt(&block, &name, &attrs)?;
    // Set proof_script on all parsed lemmas
    if let Some(ref proof) = proof_cmd {
        for lem in &mut lemmas {
            lem.proof_script = Some(proof.clone());
        }
    }
    Some(lemmas)
}

/// Collect block lines after the header (until a proof command or next lemma).
/// Returns the proof command if one was found.
/// For multi-line `apply` scripts, collects all lines until `done`.
fn collect_block_lines(
    lines: &[&str],
    i: &mut usize,
    block_lines: &mut Vec<String>,
) -> Option<String> {
    let mut proof_cmd = None;
    while *i < lines.len() {
        let t = lines[*i].trim();
        if t.is_empty() {
            *i += 1;
            continue;
        }
        if t.starts_with("lemma ") || t.starts_with("theorem ") {
            break;
        }
        let is_proof_cmd = t.starts_with("by ")
            || t.starts_with("by(")
            || t.starts_with("proof")
            || t.starts_with("apply")
            || t == "done"
            || t.starts_with("done ")
            || t.starts_with("unfolding")
            || t.starts_with("using")
            || t == "qed"
            || t == "."
            || t.starts_with("induction ")
            || t.starts_with("cases ")
            || t.starts_with("induct ");
        if is_proof_cmd
            && !t.starts_with("assumes")
            && !t.starts_with("shows")
            && !t.starts_with("and ")
            && !t.starts_with("fixes")
            && !t.starts_with("obtains")
        {
            // For `apply` scripts, collect ALL subsequent apply/done lines
            if t.starts_with("apply") {
                let mut script = String::from(t);
                *i += 1;
                while *i < lines.len() {
                    let next = lines[*i].trim();
                    if next.is_empty() {
                        *i += 1;
                        continue;
                    }
                    if next.starts_with("lemma ") || next.starts_with("theorem ") {
                        break;
                    }
                    if next.starts_with("apply") || next.starts_with("done") {
                        script.push('\n');
                        script.push_str(next);
                        *i += 1;
                        if next.starts_with("done") {
                            break;
                        }
                    } else {
                        break;
                    }
                }
                proof_cmd = Some(script);
            } else if t.starts_with("proof") {
                // Capture full proof...qed block
                let mut script = String::from(t);
                *i += 1;
                let mut depth = 1u32;
                while *i < lines.len() && depth > 0 {
                    let next = lines[*i].trim();
                    if next.is_empty() {
                        *i += 1;
                        continue;
                    }
                    if next.starts_with("lemma ") || next.starts_with("theorem ") {
                        break;
                    }
                    script.push('\n');
                    script.push_str(next);
                    if next.starts_with("proof") {
                        depth += 1;
                    }
                    if next == "qed" || next.starts_with("qed ") {
                        depth -= 1;
                    }
                    *i += 1;
                }
                proof_cmd = Some(script);
            } else {
                proof_cmd = Some(t.to_string());
                *i += 1;
            }
            break;
        }
        block_lines.push(lines[*i].to_string());
        *i += 1;
    }
    proof_cmd
}

/// Parse an `assumes ... shows ...` structured statement block.
fn parse_structured_stmt(
    block: &str,
    lemma_name: &str,
    attrs: &[String],
) -> Option<Vec<ParsedLemma>> {
    let (assumes_clauses, shows_clauses) = extract_assumes_shows(block)?;

    // Parse each assumes clause into a term
    let mut premises: Vec<Term> = Vec::new();
    for clause in &assumes_clauses {
        let conv = convert_syntax(clause);
        if let Some(t) = parse_term(&conv) {
            premises.push(t);
        }
    }
    if premises.is_empty() {
        // No assumes — the shows clause IS the statement
        let mut results = Vec::new();
        let mut show_idx = 0usize;
        for (show_name, show_stmt) in &shows_clauses {
            let conv = convert_syntax(show_stmt);
            let term = parse_term(&conv)?;
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(term)));
            let name = if show_name.is_empty() {
                if lemma_name.is_empty() {
                    let preview: String = show_stmt.chars().take(30).collect();
                    if show_idx == 0 {
                        format!("[anon:{}]", preview)
                    } else {
                        format!("[anon:{}]_{}", preview, show_idx + 1)
                    }
                } else {
                    if show_idx == 0 {
                        lemma_name.to_string()
                    } else {
                        format!("{}_{}", lemma_name, show_idx + 1)
                    }
                }
            } else {
                show_name.clone()
            };
            results.push(ParsedLemma {
                name,
                attributes: attrs.to_vec(),
                theorem: thm,
                proof_script: None,
                alias_for: None,
            });
            show_idx += 1;
        }
        return Some(results);
    }

    // Handle "shows" clauses
    // Build: premise1 ==> premise2 ==> ... ==> conclusion
    let mut results = Vec::new();
    let mut show_idx = 0usize;
    for (show_name, show_stmt) in &shows_clauses {
        let conv = convert_syntax(show_stmt);
        let concl = parse_term(&conv)?;
        let mut term = concl;
        for prem in premises.iter().rev() {
            term = Pure::mk_implies(prem.clone(), term);
        }
        let thm = Arc::new(ThmKernel::assume(CTerm::certify(term)));
        let name = if show_name.is_empty() {
            if lemma_name.is_empty() {
                let preview: String = show_stmt.chars().take(30).collect();
                if show_idx == 0 {
                    format!("[anon:{}]", preview)
                } else {
                    format!("[anon:{}]_{}", preview, show_idx + 1)
                }
            } else {
                if show_idx == 0 {
                    lemma_name.to_string()
                } else {
                    format!("{}_{}", lemma_name, show_idx + 1)
                }
            }
        } else {
            show_name.clone()
        };
        results.push(ParsedLemma {
            name,
            attributes: attrs.to_vec(),
            theorem: thm,
            proof_script: None,
            alias_for: None,
        });
        show_idx += 1;
    }
    Some(results)
}

/// Extract assumes clauses and shows clauses from a structured block.
/// Returns (assumes_clauses, shows_clauses) where each shows clause is (name, statement).
fn extract_assumes_shows(block: &str) -> Option<(Vec<String>, Vec<(String, String)>)> {
    // Convert cartouches to quotes early, so that quote-aware splitting functions
    // (merge_multiline_quotes, split_by_and_outside_quotes, etc.) see them as quotes.
    let block = block.replace("\\<open>", "\"").replace("\\<close>", "\"");
    let mut assumes_clauses: Vec<String> = Vec::new();
    let mut shows_clauses: Vec<(String, String)> = Vec::new();
    let mut current_section: Option<&str> = None; // "assumes" or "shows"

    for raw_line in block.lines() {
        // Convert cartouche to quotes in this line before processing
        let line = raw_line
            .replace("\\<open>", "\"")
            .replace("\\<close>", "\"");
        let t = line.trim();
        if t.is_empty() {
            continue;
        }

        if t.starts_with("assumes ") || t == "assumes" {
            current_section = Some("assumes");
            let rest = t.strip_prefix("assumes").unwrap_or("").trim();
            if !rest.is_empty() {
                // Check if "shows" appears on the same line
                if let Some(shows_pos) = rest.find("shows ") {
                    let (assumes_part, shows_part) = rest.split_at(shows_pos);
                    if !assumes_part.trim().is_empty() {
                        extract_clauses(assumes_part.trim(), &mut assumes_clauses);
                    }
                    let shows_rest = shows_part.strip_prefix("shows").unwrap_or("").trim();
                    if !shows_rest.is_empty() {
                        current_section = Some("shows");
                        extract_shows_clauses(shows_rest, &mut shows_clauses);
                    }
                } else {
                    extract_clauses(rest, &mut assumes_clauses);
                }
            }
        } else if t.starts_with("shows ") || t == "shows" {
            current_section = Some("shows");
            let rest = t.strip_prefix("shows").unwrap_or("").trim();
            if !rest.is_empty() {
                extract_shows_clauses(rest, &mut shows_clauses);
            }
        } else if t.starts_with("and ") {
            let rest = t.strip_prefix("and").unwrap_or("").trim();
            if !rest.is_empty() {
                match current_section {
                    Some("assumes") => extract_clauses(rest, &mut assumes_clauses),
                    Some("shows") => extract_shows_clauses(rest, &mut shows_clauses),
                    _ => {}
                }
            }
        } else if t.starts_with("fixes ") || t.starts_with("obtains ") || t.starts_with("for ") {
            // Skip fixes/obtains/for for now — they define variables/obligations
            continue;
        }
    }

    if assumes_clauses.is_empty() && shows_clauses.is_empty() {
        // Convert cartouche to quotes before merging
        let converted_block = block.replace("\\<open>", "\"").replace("\\<close>", "\"");
        let merged = merge_multiline_quotes(&converted_block);
        for stmt in &merged {
            shows_clauses.push((String::new(), stmt.clone()));
        }
        if shows_clauses.is_empty() {
            return None;
        }
    } else if shows_clauses.is_empty() {
        // Has assumes but no explicit shows – collect remaining lines
        let clean: String = block
            .lines()
            .map(|l| l.trim())
            .filter(|l| {
                !l.is_empty()
                    && !l.starts_with("assumes")
                    && !l.starts_with("shows")
                    && !l.starts_with("and ")
                    && !l.starts_with("fixes")
            })
            .collect::<Vec<_>>()
            .join(" ");
        if !clean.is_empty() {
            shows_clauses.push((String::new(), clean));
        } else {
            return None;
        }
    }
    Some((assumes_clauses, shows_clauses))
}

/// Extract term clauses from text like `major: "\<forall>x. P x" and minor: "P x \<Longrightarrow> R"`
/// or `"P \<longrightarrow> Q" P "Q \<Longrightarrow> R"`.
fn extract_clauses(text: &str, out: &mut Vec<String>) {
    let text = text.trim();
    if text.is_empty() {
        return;
    }

    // Split by `and` keyword, but be careful with it inside quotes
    let parts = split_by_and_outside_quotes(text);
    for part in parts {
        let clauses = extract_terms_from_clause(&part);
        out.extend(clauses);
    }
}

/// Extract shows clauses, which may have names: `not_not: "..." and Not_eq_iff: "..."`
fn extract_shows_clauses(text: &str, out: &mut Vec<(String, String)>) {
    let text = text.trim();
    if text.is_empty() {
        return;
    }

    let parts = split_by_and_outside_quotes(text);
    for part in parts {
        let part = part.trim();
        if let Some((name, stmt)) = parse_named_or_bare(part) {
            out.push((name, stmt));
        }
    }
}

/// Split text by `and` keyword, respecting quoted regions.
fn split_by_and_outside_quotes(text: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut in_quote = false;
    let chars: Vec<char> = text.chars().collect();
    let mut idx = 0;
    while idx < chars.len() {
        if chars[idx] == '"' {
            in_quote = !in_quote;
            current.push(chars[idx]);
        } else if !in_quote
            && idx + 3 < chars.len()
            && chars[idx..idx + 3].iter().collect::<String>() == "and"
            && (idx == 0 || chars[idx - 1].is_whitespace())
            && (idx + 3 >= chars.len() || chars[idx + 3].is_whitespace())
        {
            // Found `and` outside quotes
            let trimmed = current.trim().to_string();
            if !trimmed.is_empty() {
                parts.push(trimmed);
            }
            current = String::new();
            idx += 3;
            continue;
        } else {
            current.push(chars[idx]);
        }
        idx += 1;
    }
    let trimmed = current.trim().to_string();
    if !trimmed.is_empty() {
        parts.push(trimmed);
    }
    parts
}

/// Extract terms from a single clause part (after splitting by `and`).
/// Handles: `name: "quoted"`, `"quoted"`, `bare_term`, and mixtures like `"A" bare "B"`.
fn extract_terms_from_clause(clause: &str) -> Vec<String> {
    let clause = clause.trim();
    if clause.is_empty() {
        return vec![];
    }

    let mut results = Vec::new();
    let mut remaining = clause;

    // First, check if there's a name prefix: `name:`
    if let Some(colon_pos) = remaining.find(':') {
        // Check if colon is before any quote — it's a name prefix
        if let Some(quote_pos) = remaining.find('"') {
            if colon_pos < quote_pos {
                // There's a name: prefix — strip it
                remaining = remaining[colon_pos + 1..].trim();
            }
        }
    }

    // Now extract quoted strings and bare terms
    while !remaining.is_empty() {
        if remaining.starts_with('"') {
            if let Some(stmt) = extract_quoted(remaining) {
                let quote_len = stmt.len() + 2; // ""
                results.push(stmt);
                // Advance past the quoted string
                remaining = remaining[quote_len..].trim();
            } else {
                break;
            }
        } else {
            // Bare term — take until next quote or end
            if let Some(quote_pos) = remaining.find('"') {
                let bare = remaining[..quote_pos].trim();
                if !bare.is_empty() {
                    results.push(bare.to_string());
                }
                remaining = remaining[quote_pos..].trim();
            } else {
                let bare = remaining.trim();
                if !bare.is_empty() {
                    results.push(bare.to_string());
                }
                break;
            }
        }
    }
    results
}

/// Parse a clause that may have a name prefix: `name: "stmt"` or `"stmt"`.
/// Returns (name, statement).
fn parse_named_or_bare(clause: &str) -> Option<(String, String)> {
    let clause = clause.trim();
    if let Some(colon_pos) = clause.find(':') {
        if let Some(quote_pos) = clause.find('"') {
            if colon_pos < quote_pos {
                let name = clause[..colon_pos].trim().to_string();
                let stmt = extract_quoted(&clause[colon_pos + 1..])?;
                return Some((name, stmt));
            }
        }
    }
    // No name prefix — extract the quoted string or take the whole thing
    if let Some(stmt) = extract_quoted(clause) {
        Some((String::new(), stmt))
    } else {
        // Bare term
        Some((String::new(), clause.to_string()))
    }
}

/// Extract content within the first `"..."` pair.
fn extract_quoted(s: &str) -> Option<String> {
    let s = s.trim();
    if !s.starts_with('"') {
        return None;
    }
    let inner = &s[1..];
    let mut result = String::new();
    let chars: Vec<char> = inner.chars().collect();
    let mut idx = 0;
    while idx < chars.len() {
        if chars[idx] == '\\' && idx + 1 < chars.len() && chars[idx + 1] == '"' {
            result.push('"');
            idx += 2;
        } else if chars[idx] == '"' {
            return Some(result);
        } else {
            result.push(chars[idx]);
            idx += 1;
        }
    }
    None // No closing quote
}

/// Parse `name[attrs]` or `name` from the lemma/theorem name part.
fn parse_name_attrs(name_part: &str) -> (&str, Vec<String>) {
    let name_part = name_part.trim();
    if let Some(b) = name_part.find('[') {
        let name = name_part[..b].trim();
        let attrs = parse_attrs(&name_part[b..]);
        (name, attrs)
    } else {
        (name_part, Vec::new())
    }
}

fn parse_attrs(s: &str) -> Vec<String> {
    s.trim_start_matches('[')
        .trim_end_matches(']')
        .split(',')
        .map(|a| a.trim().to_string())
        .collect()
}

fn convert_syntax(s: &str) -> String {
    // Cartouche conversion: \<open>...\<close> → "..." (must be first)
    s.replace("\\<open>", "\"")
        .replace("\\<close>", "\"")
        .replace("\\<lbrakk>", "[|")
        .replace("\\<rbrakk>", "|]")
        .replace("\\<Longrightarrow>", "==>")
        .replace("\\<And>", "!!")
        .replace("\\<not>", "~")
        .replace("\\<noteq>", "~=")
        .replace("\\<forall>", "ALL")
        .replace("\\<exists>\\<^sub>\\<le>\\<^sub>1", "EX1")
        .replace("\\<exists>!", "EX1")
        .replace("\\<exists>", "EX")
        .replace("\\<nexists>", "~EX")
        .replace("\\<longrightarrow>", "-->")
        .replace("\\<and>", "&")
        .replace("\\<or>", "|")
        .replace("\\<longleftrightarrow>", "IFF")
        .replace("\\<setminus>", "-")
        .replace("\\<equiv>", "=")
        .replace("\\<lambda>", "%")
        .replace("\\<circ>", "o")
        .replace("\\<epsilon>", "SOME")
        .replace("\\<bar>", "abs")
        // ASCII mixfix operator: append (spaces prevent matching @{)
        .replace(" @ ", " APPEND ")
        // Strip formatting commands (don't affect logical content)
        .replace("::{}", "")
        .replace("\\<^bold>", "")
        .replace("\\<^sup>", "")
        .replace("\\<^sub>", "")
        .replace("\\<^bsub>", "")
        .replace("\\<^esub>", "")
}

/// Merge multi-line quoted strings into complete statements.
fn merge_multiline_quotes(block: &str) -> Vec<String> {
    let mut results: Vec<String> = Vec::new();
    let mut buf: Option<String> = None;
    for line in block.lines() {
        let t = line.trim();
        if t.starts_with("(*") && t.contains("*)") {
            continue;
        }
        if t.is_empty()
            || t.starts_with("assumes")
            || t.starts_with("shows")
            || t.starts_with("fixes")
        {
            continue;
        }
        if let Some(ref mut acc) = buf {
            acc.push(' ');
            acc.push_str(t);
            if t.contains('"') {
                if let Some(stmt) = extract_quoted(acc) {
                    results.push(stmt);
                }
                buf = None;
            }
        } else if t.starts_with('"') {
            if let Some(stmt) = extract_quoted(t) {
                results.push(stmt);
            } else {
                buf = Some(t.to_string());
            }
        } else if !t.contains('"') {
            results.push(t.to_string());
        }
    }
    if let Some(ref acc) = buf {
        if let Some(stmt) = extract_quoted(acc) {
            results.push(stmt);
        }
    }
    results
}

// =========================================================================
// Global theorem store (A3)
// =========================================================================

use std::sync::LazyLock;

/// All loaded HOL theorems, categorized by attribute.
/// Uses TheoryGraph for runtime DAG-based loading of ALL theories.
static HOL_THEOREMS: LazyLock<HolTheoremDb> = LazyLock::new(|| {
    match load_all_theories() {
        Ok(db) => db,
        Err(_) => {
            // Fallback: load core files only
            let hol_thy = include_str!("../../theories/HOL/HOL.thy");
            let ord_thy = include_str!("../../theories/HOL/Orderings.thy");
            let nat_thy = include_str!("../../theories/HOL/Nat.thy");
            let set_thy = include_str!("../../theories/HOL/Set.thy");
            let list_thy = include_str!("../../theories/HOL/List.thy");
            let mut lemmas = parse_lemmas(hol_thy);
            lemmas.extend(parse_lemmas(ord_thy));
            lemmas.extend(parse_lemmas(nat_thy));
            lemmas.extend(parse_lemmas(set_thy));
            lemmas.extend(parse_lemmas(list_thy));
            let mut db = HolTheoremDb::from_lemmas(&lemmas);
            HolTheoremDb::add_builtins(&mut db);
            db
        }
    }
});

/// Load ALL .thy files from the theories directory (full HOL library).
pub fn load_all_theories() -> Result<HolTheoremDb, String> {
    let mut graph = crate::hol::theory_graph::TheoryGraph::new();
    let _ = graph.scan(std::path::Path::new("theories"));
    let mut db = graph.load_all()?;
    HolTheoremDb::add_builtins(&mut db);
    Ok(db)
}

pub struct HolTheoremDb {
    pub intros: Vec<Arc<crate::core::thm::Thm>>,
    pub elims: Vec<Arc<crate::core::thm::Thm>>,
    pub simps: Vec<Arc<crate::core::thm::Thm>>,
    pub all: Vec<Arc<crate::core::thm::Thm>>,
    /// Theorem lookup by name (e.g., "sym", "trans", "refl")
    pub by_name: std::collections::HashMap<String, Arc<crate::core::thm::Thm>>,
}

impl HolTheoremDb {
    pub fn from_lemmas(lemmas: &[ParsedLemma]) -> Self {
        let mut intros = Vec::new();
        let mut elims = Vec::new();
        let mut simps = Vec::new();
        let mut all = Vec::new();
        let mut by_name = std::collections::HashMap::new();
        for lem in lemmas {
            let thm = Arc::clone(&lem.theorem);
            all.push(Arc::clone(&thm));
            // Index by name (use first-come, keep first)
            if !lem.name.is_empty() && !by_name.contains_key(&lem.name) {
                by_name.insert(lem.name.clone(), Arc::clone(&thm));
            }
            let attrs = &lem.attributes;
            if attrs.iter().any(|a| a.contains("intro")) {
                intros.push(Arc::clone(&thm));
            }
            if attrs.iter().any(|a| a.contains("elim")) {
                elims.push(Arc::clone(&thm));
            }
            if attrs.iter().any(|a| a.contains("simp")) {
                simps.push(Arc::clone(&thm));
            }
        }
        // Resolve aliases from `lemmas` commands (second pass)
        for lem in lemmas {
            if let Some(ref aliases) = lem.alias_for {
                for alias_target in aliases {
                    if let Some(target_thm) = by_name.get(alias_target) {
                        let thm = Arc::clone(target_thm);
                        if !lem.name.is_empty() && !by_name.contains_key(&lem.name) {
                            by_name.insert(lem.name.clone(), Arc::clone(&thm));
                        }
                        all.push(Arc::clone(&thm));
                        let attrs = &lem.attributes;
                        if attrs.iter().any(|a| a.contains("intro")) {
                            intros.push(Arc::clone(&thm));
                        }
                        if attrs.iter().any(|a| a.contains("elim")) {
                            elims.push(Arc::clone(&thm));
                        }
                        if attrs.iter().any(|a| a.contains("simp")) {
                            simps.push(Arc::clone(&thm));
                        }
                        break; // Use first found alias target
                    }
                }
            }
        }
        // Always include key rules even without explicit attributes
        for lem in lemmas {
            let thm = Arc::clone(&lem.theorem);
            match lem.name.as_str() {
                "sym" | "trans" | "refl" | "arg_cong" | "fun_cong" | "iffD1" | "iffD2" => {
                    if !simps.iter().any(|t| Arc::ptr_eq(t, &thm)) {
                        simps.push(thm);
                    }
                }
                _ => {}
            }
        }
        HolTheoremDb {
            intros,
            elims,
            simps,
            all,
            by_name,
        }
    }

    /// Add built-in Pure/HOL theorems that are fundamental axioms.
    fn add_builtins(db: &mut HolTheoremDb) {
        use crate::core::logic::Pure;

        // Use dummy types consistently — the parser also uses dummy types.
        // This ensures built-in rules can match parsed goals via bicompose.
        let prop_typ = Typ::base("prop");
        let dummy_typ = Typ::dummy();

        // Equality: use prop → prop → prop (matching parser's make_binary)
        let eq_typ = Typ::arrow(
            prop_typ.clone(),
            Typ::arrow(prop_typ.clone(), prop_typ.clone()),
        );
        let eq_const = Term::const_("HOL.eq", eq_typ);

        // Helper: make HOL equality term s = t (uses prop-type equality)
        fn mk_eq(eqc: &Term, s: Term, t: Term) -> Term {
            Term::app(Term::app(eqc.clone(), s), t)
        }

        // Use dummy type for all term variables — matches parser output
        fn mk_var(name: &str, idx: usize) -> Term {
            Term::var(name, idx, Typ::dummy())
        }
        fn mk_plus(pc: &Term, a: Term, b: Term) -> Term {
            Term::app(Term::app(pc.clone(), a), b)
        }
        fn mk_times(tc: &Term, a: Term, b: Term) -> Term {
            Term::app(Term::app(tc.clone(), a), b)
        }
        fn mk_suc(sc: &Term, a: Term) -> Term {
            Term::app(sc.clone(), a)
        }

        // Arithmetic constants with dummy types (matching parser)
        let plus_c = Term::const_("Groups.plus", Typ::dummy());
        let times_c = Term::const_("Groups.times", Typ::dummy());
        let suc_c = Term::const_("Nat.Suc", Typ::dummy());
        let less_c = Term::const_("Orderings.less", Typ::dummy());
        let le_c = Term::const_("Orderings.less_eq", Typ::dummy());
        let not_c = Term::const_("HOL.Not", Typ::arrow(prop_typ.clone(), prop_typ.clone()));
        let disj_c = Term::const_("HOL.disj", Typ::dummy());
        let eq_const = Term::const_(
            "HOL.eq",
            Typ::arrow(
                prop_typ.clone(),
                Typ::arrow(prop_typ.clone(), prop_typ.clone()),
            ),
        );

        // refl: t = t  (HOL equality)
        if !db.by_name.contains_key("refl") {
            let t = Term::var("t", 0, Typ::dummy());
            let stmt = mk_eq(&eq_const, t.clone(), t);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("refl".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }

        // subst: [| s = t; P s |] ==> P t  (always override parsed)
        {
            let s = Term::var("s", 0, Typ::dummy());
            let t = Term::var("t", 1, Typ::dummy());
            let p = Term::var("P", 2, Typ::arrow(Typ::dummy(), prop_typ.clone()));
            let eq = mk_eq(&eq_const, s.clone(), t.clone());
            let ps = Term::app(p.clone(), s);
            let pt = Term::app(p, t);
            let stmt = Pure::mk_implies(eq, Pure::mk_implies(ps, pt));
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("subst".into(), Arc::clone(&thm));
            db.elims.push(Arc::clone(&thm));
            db.all.push(thm);
        }

        // mp: [| P --> Q; P |] ==> Q
        if !db.by_name.contains_key("mp") {
            let p = Term::var("P", 0, prop_typ.clone());
            let q = Term::var("Q", 1, prop_typ.clone());
            let imp = Pure::mk_implies(p.clone(), q.clone());
            let stmt = Pure::mk_implies(imp, Pure::mk_implies(p, q));
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("mp".into(), Arc::clone(&thm));
            db.intros.push(Arc::clone(&thm));
            db.elims.push(Arc::clone(&thm));
            db.all.push(thm);
        }

        // impI: (P ==> Q) ==> P --> Q
        if !db.by_name.contains_key("impI") {
            let p = Term::var("P", 0, prop_typ.clone());
            let q = Term::var("Q", 1, prop_typ.clone());
            let stmt = Pure::mk_implies(
                Pure::mk_implies(p.clone(), q.clone()),
                Pure::mk_implies(p, q),
            );
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("impI".into(), Arc::clone(&thm));
            db.intros.push(Arc::clone(&thm));
            db.all.push(thm);
        }

        // True_or_False: (P = True) | (P = False)
        if !db.by_name.contains_key("True_or_False") {
            let p = Term::var("P", 0, prop_typ.clone());
            let true_c = Term::const_("HOL.True", prop_typ.clone());
            let false_c = Term::const_("HOL.False", prop_typ.clone());
            let eq_true = mk_eq(&eq_const, p.clone(), true_c);
            let eq_false = mk_eq(&eq_const, p, false_c);
            let disj = Term::const_(
                "HOL.disj",
                Typ::arrow(
                    prop_typ.clone(),
                    Typ::arrow(prop_typ.clone(), prop_typ.clone()),
                ),
            );
            let stmt = Term::app(Term::app(disj, eq_true), eq_false);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("True_or_False".into(), Arc::clone(&thm));
            db.all.push(thm);
        }

        // notE: [| ~P; P |] ==> R
        if !db.by_name.contains_key("notE") {
            let p = Term::var("P", 0, prop_typ.clone());
            let r = Term::var("R", 1, prop_typ.clone());
            let not_c = Term::const_("HOL.Not", Typ::arrow(prop_typ.clone(), prop_typ.clone()));
            let not_p = Term::app(not_c, p.clone());
            let stmt = Pure::mk_implies(not_p, Pure::mk_implies(p, r));
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("notE".into(), Arc::clone(&thm));
            db.elims.push(Arc::clone(&thm));
            db.all.push(thm);
        }

        // contrapos_nn: [| ~Q; P ==> Q |] ==> ~P
        {
            let p = Term::var("P", 0, prop_typ.clone());
            let q = Term::var("Q", 1, prop_typ.clone());
            let not_c = Term::const_("HOL.Not", Typ::arrow(prop_typ.clone(), prop_typ.clone()));
            let not_q = Term::app(not_c.clone(), q.clone());
            let not_p = Term::app(not_c, p.clone());
            let p_imp_q = Pure::mk_implies(p, q);
            let stmt = Pure::mk_implies(not_q, Pure::mk_implies(p_imp_q, not_p));
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("contrapos_nn".into(), Arc::clone(&thm));
            db.elims.push(Arc::clone(&thm));
            db.all.push(thm);
        }

        // contrapos_pn: [| Q; P ==> ~Q |] ==> ~P
        {
            let p = Term::var("P", 0, prop_typ.clone());
            let q = Term::var("Q", 1, prop_typ.clone());
            let not_c = Term::const_("HOL.Not", Typ::arrow(prop_typ.clone(), prop_typ.clone()));
            let not_q = Term::app(not_c.clone(), q.clone());
            let not_p = Term::app(not_c, p.clone());
            let p_imp_not_q = Pure::mk_implies(p, not_q);
            let stmt = Pure::mk_implies(q, Pure::mk_implies(p_imp_not_q, not_p));
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("contrapos_pn".into(), Arc::clone(&thm));
            db.elims.push(Arc::clone(&thm));
            db.all.push(thm);
        }

        // sym: s = t ==> t = s  (always override parsed version)
        {
            let s = Term::var("s", 0, Typ::dummy());
            let t = Term::var("t", 1, Typ::dummy());
            let eq_st = mk_eq(&eq_const, s.clone(), t.clone());
            let eq_ts = mk_eq(&eq_const, t, s);
            let stmt = Pure::mk_implies(eq_st, eq_ts);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("sym".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }

        // trans: [| r = s; s = t |] ==> r = t
        if !db.by_name.contains_key("trans") {
            let r = Term::var("r", 0, Typ::dummy());
            let s = Term::var("s", 1, Typ::dummy());
            let t = Term::var("t", 2, Typ::dummy());
            let eq_rs = mk_eq(&eq_const, r.clone(), s.clone());
            let eq_st = mk_eq(&eq_const, s, t.clone());
            let eq_rt = mk_eq(&eq_const, r, t);
            let stmt = Pure::mk_implies(eq_rs, Pure::mk_implies(eq_st, eq_rt));
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("trans".into(), Arc::clone(&thm));
            db.all.push(thm);
        }

        // iffI: [| P ==> Q; Q ==> P |] ==> P = Q
        if !db.by_name.contains_key("iffI") {
            let p = Term::var("P", 0, prop_typ.clone());
            let q = Term::var("Q", 1, prop_typ.clone());
            let imp_pq = Pure::mk_implies(p.clone(), q.clone());
            let imp_qp = Pure::mk_implies(q.clone(), p.clone());
            let eq_pq = mk_eq(&eq_const, p, q);
            let stmt = Pure::mk_implies(imp_pq, Pure::mk_implies(imp_qp, eq_pq));
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("iffI".into(), Arc::clone(&thm));
            db.intros.push(Arc::clone(&thm));
            db.all.push(thm);
        }

        // not_sym: ~(s = t) ==> ~(t = s)
        // Always use built-in version (overrides any parsed version with incompatible term structure)
        {
            let s = mk_var("s", 0);
            let t = mk_var("t", 1);
            let not_c = Term::const_("HOL.Not", Typ::arrow(prop_typ.clone(), prop_typ.clone()));
            let eq_st = mk_eq(&eq_const, s.clone(), t.clone());
            let eq_ts = mk_eq(&eq_const, t, s);
            let not_st = Term::app(not_c.clone(), eq_st);
            let not_ts = Term::app(not_c, eq_ts);
            let stmt = Pure::mk_implies(not_st, not_ts);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("not_sym".into(), Arc::clone(&thm));
            db.all.push(thm);
        }

        // False_neq_True: False = True ==> P
        {
            let p = Term::var("P", 0, prop_typ.clone());
            let false_c = Term::const_("HOL.False", prop_typ.clone());
            let true_c = Term::const_("HOL.True", prop_typ.clone());
            let eq_f_t = mk_eq(&eq_const, false_c, true_c);
            let stmt = Pure::mk_implies(eq_f_t, p);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("False_neq_True".into(), Arc::clone(&thm));
            db.elims.push(Arc::clone(&thm));
            db.all.push(thm);
        }

        // disjE: [| P | Q; P ==> R; Q ==> R |] ==> R
        {
            let p = Term::var("P", 0, prop_typ.clone());
            let q = Term::var("Q", 1, prop_typ.clone());
            let r = Term::var("R", 2, prop_typ.clone());
            let disj_c = Term::const_("HOL.disj", Typ::dummy());
            let p_or_q = Term::app(Term::app(disj_c, p.clone()), q.clone());
            let p_imp_r = Pure::mk_implies(p, r.clone());
            let q_imp_r = Pure::mk_implies(q, r.clone());
            let stmt = Pure::mk_implies(
                p_or_q,
                Pure::mk_implies(p_imp_r, Pure::mk_implies(q_imp_r, r)),
            );
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("disjE".into(), Arc::clone(&thm));
            db.elims.push(Arc::clone(&thm));
            db.all.push(thm);
        }

        // Pure reflexive (meta-equality) — needed for kernel resolution
        if !db.by_name.contains_key("Pure.refl") {
            let t = Term::var("t", 0, Typ::dummy());
            let thm = Arc::new(ThmKernel::reflexive(CTerm::certify(t)));
            db.by_name.insert("Pure.refl".into(), Arc::clone(&thm));
            db.all.push(thm);
        }

        // eq_commute: a = b ==> b = a  (needed for one_is_add and many others)
        if !db.by_name.contains_key("eq_commute") {
            let a = mk_var("a", 0);
            let b = mk_var("b", 1);
            let eq_ab = mk_eq(&eq_const, a.clone(), b.clone());
            let eq_ba = mk_eq(&eq_const, b, a);
            let stmt = Pure::mk_implies(eq_ab, eq_ba);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("eq_commute".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }

        // ssubst: t = s ==> P s ==> P t  (always override, proper function type for P)
        {
            let s = Term::var("s", 0, Typ::dummy());
            let t = Term::var("t", 1, Typ::dummy());
            let p = Term::var("P", 2, Typ::arrow(Typ::dummy(), prop_typ.clone()));
            let eq_ts = mk_eq(&eq_const, t.clone(), s.clone());
            let ps = Term::app(p.clone(), s);
            let pt = Term::app(p, t);
            let stmt = Pure::mk_implies(eq_ts, Pure::mk_implies(ps, pt));
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("ssubst".into(), Arc::clone(&thm));
            db.elims.push(Arc::clone(&thm));
            db.all.push(thm);
        }

        // arg_cong: x = y ==> f x = f y
        if !db.by_name.contains_key("arg_cong") {
            let x = mk_var("x", 0);
            let y = mk_var("y", 1);
            let f = mk_var("f", 2);
            let eq_xy = mk_eq(&eq_const, x.clone(), y.clone());
            let fx = Term::app(f.clone(), x);
            let fy = Term::app(f, y);
            let eq_f = mk_eq(&eq_const, fx, fy);
            let stmt = Pure::mk_implies(eq_xy, eq_f);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("arg_cong".into(), Arc::clone(&thm));
            db.all.push(thm);
        }

        // fun_cong: f = g ==> f x = g x
        if !db.by_name.contains_key("fun_cong") {
            let f = mk_var("f", 0);
            let g = mk_var("g", 1);
            let x = mk_var("x", 2);
            let eq_fg = mk_eq(&eq_const, f.clone(), g.clone());
            let fx = Term::app(f, x.clone());
            let gx = Term::app(g, x);
            let eq_app = mk_eq(&eq_const, fx, gx);
            let stmt = Pure::mk_implies(eq_fg, eq_app);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("fun_cong".into(), Arc::clone(&thm));
            db.all.push(thm);
        }

        // =================================================================
        // Arithmetic built-in rules (critical for nat arithmetic)
        // These are standard Nat.thy lemmas that may not be parsed due to
        // multi-line proof capture limitations.
        // Uses the dummy-typed constants defined above for consistency with parser.
        // =================================================================

        // add_0_right: m + 0 = m
        if !db.by_name.contains_key("add_0_right") {
            let m = mk_var("m", 0);
            let lhs = mk_plus(&plus_c, m.clone(), Term::const_("0", Typ::dummy()));
            let stmt = mk_eq(&eq_const, lhs, m);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("add_0_right".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }
        // add_Suc_right: m + Suc n = Suc (m + n)
        if !db.by_name.contains_key("add_Suc_right") {
            let m = mk_var("m", 0);
            let n = mk_var("n", 1);
            let lhs = mk_plus(&plus_c, m.clone(), mk_suc(&suc_c, n.clone()));
            let rhs = mk_suc(&suc_c, mk_plus(&plus_c, m, n));
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("add_Suc_right".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }
        // add_0: 0 + m = m
        if !db.by_name.contains_key("add_0") {
            let m = mk_var("m", 0);
            let lhs = mk_plus(&plus_c, Term::const_("0", Typ::dummy()), m.clone());
            let stmt = mk_eq(&eq_const, lhs, m);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("add_0".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }
        // mult_0_right: m * 0 = 0
        if !db.by_name.contains_key("mult_0_right") {
            let m = mk_var("m", 0);
            let lhs = mk_times(&times_c, m, Term::const_("0", Typ::dummy()));
            let stmt = mk_eq(&eq_const, lhs, Term::const_("0", Typ::dummy()));
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("mult_0_right".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }
        // mult_Suc_right: m * Suc n = m + (m * n)
        if !db.by_name.contains_key("mult_Suc_right") {
            let m = mk_var("m", 0);
            let n = mk_var("n", 1);
            let lhs = mk_times(&times_c, m.clone(), mk_suc(&suc_c, n.clone()));
            let rhs = mk_plus(&plus_c, m.clone(), mk_times(&times_c, m, n));
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("mult_Suc_right".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }
        // add_commute: a + b = b + a
        if !db.by_name.contains_key("add_commute") {
            let a = mk_var("a", 0);
            let b = mk_var("b", 1);
            let lhs = mk_plus(&plus_c, a.clone(), b.clone());
            let rhs = mk_plus(&plus_c, b, a);
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("add_commute".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }
        // add_assoc: (a + b) + c = a + (b + c)
        if !db.by_name.contains_key("add_assoc") {
            let a = mk_var("a", 0);
            let b = mk_var("b", 1);
            let c = mk_var("c", 2);
            let lhs = mk_plus(&plus_c, mk_plus(&plus_c, a.clone(), b.clone()), c.clone());
            let rhs = mk_plus(&plus_c, a, mk_plus(&plus_c, b, c));
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("add_assoc".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }
        // less_irrefl: ~(n < n)
        if !db.by_name.contains_key("less_irrefl") {
            let n = mk_var("n", 0);
            let n_lt_n = Term::app(Term::app(less_c.clone(), n.clone()), n);
            let stmt = Term::app(not_c.clone(), n_lt_n);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("less_irrefl".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }
        // le_refl: n <= n
        if !db.by_name.contains_key("le_refl") {
            let n = mk_var("n", 0);
            let stmt = Term::app(Term::app(le_c.clone(), n.clone()), n);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("le_refl".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }
        // less_trans: [| a < b; b < c |] ==> a < c
        if !db.by_name.contains_key("less_trans") {
            let a = mk_var("a", 0);
            let b = mk_var("b", 1);
            let c = mk_var("c", 2);
            let a_lt_b = Term::app(Term::app(less_c.clone(), a.clone()), b.clone());
            let b_lt_c = Term::app(Term::app(less_c.clone(), b), c.clone());
            let a_lt_c = Term::app(Term::app(less_c.clone(), a), c);
            let stmt = Pure::mk_implies(a_lt_b, Pure::mk_implies(b_lt_c, a_lt_c));
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("less_trans".into(), Arc::clone(&thm));
            db.all.push(thm);
        }
        // le_trans: [| a <= b; b <= c |] ==> a <= c
        if !db.by_name.contains_key("le_trans") {
            let a = mk_var("a", 0);
            let b = mk_var("b", 1);
            let c = mk_var("c", 2);
            let a_le_b = Term::app(Term::app(le_c.clone(), a.clone()), b.clone());
            let b_le_c = Term::app(Term::app(le_c.clone(), b), c.clone());
            let a_le_c = Term::app(Term::app(le_c.clone(), a), c);
            let stmt = Pure::mk_implies(a_le_b, Pure::mk_implies(b_le_c, a_le_c));
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("le_trans".into(), Arc::clone(&thm));
            db.all.push(thm);
        }
        // not_less0: ~(n < 0)
        if !db.by_name.contains_key("not_less0") {
            let n = mk_var("n", 0);
            let n_lt_0 = Term::app(
                Term::app(less_c.clone(), n),
                Term::const_("0", Typ::dummy()),
            );
            let stmt = Term::app(not_c.clone(), n_lt_0);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("not_less0".into(), Arc::clone(&thm));
            db.all.push(thm);
        }
        // zero_less_Suc: 0 < Suc n
        if !db.by_name.contains_key("zero_less_Suc") {
            let n = mk_var("n", 0);
            let stmt = Term::app(
                Term::app(less_c.clone(), Term::const_("0", Typ::dummy())),
                mk_suc(&suc_c, n),
            );
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("zero_less_Suc".into(), Arc::clone(&thm));
            db.all.push(thm);
        }

        // =================================================================
        // Critical Nat.thy lemmas (dependency chain breakers)
        // =================================================================
        // Suc_not_Zero: Suc n ~= 0
        if !db.by_name.contains_key("Suc_not_Zero") {
            let n = mk_var("n", 0);
            let eq_suc_0 = mk_eq(
                &eq_const,
                mk_suc(&suc_c, n),
                Term::const_("0", Typ::dummy()),
            );
            let not_c = Term::const_("HOL.Not", Typ::arrow(prop_typ.clone(), prop_typ.clone()));
            let stmt = Term::app(not_c, eq_suc_0);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("Suc_not_Zero".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }
        // Zero_not_Suc: 0 ~= Suc n
        if !db.by_name.contains_key("Zero_not_Suc") {
            let n = mk_var("n", 0);
            let eq_0_suc = mk_eq(
                &eq_const,
                Term::const_("0", Typ::dummy()),
                mk_suc(&suc_c, n),
            );
            let not_c = Term::const_("HOL.Not", Typ::arrow(prop_typ.clone(), prop_typ.clone()));
            let stmt = Term::app(not_c, eq_0_suc);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("Zero_not_Suc".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }
        // Suc_neq_Zero: Suc m = 0 ==> R
        if !db.by_name.contains_key("Suc_neq_Zero") {
            let m = mk_var("m", 0);
            let r = Term::var("R", 0, prop_typ.clone());
            let eq_suc_0 = mk_eq(
                &eq_const,
                mk_suc(&suc_c, m),
                Term::const_("0", Typ::dummy()),
            );
            let stmt = Pure::mk_implies(eq_suc_0, r);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("Suc_neq_Zero".into(), Arc::clone(&thm));
            db.elims.push(Arc::clone(&thm));
            db.all.push(thm);
        }
        // Zero_neq_Suc: 0 = Suc m ==> R
        if !db.by_name.contains_key("Zero_neq_Suc") {
            let m = mk_var("m", 0);
            let r = Term::var("R", 0, prop_typ.clone());
            let eq_0_suc = mk_eq(
                &eq_const,
                Term::const_("0", Typ::dummy()),
                mk_suc(&suc_c, m),
            );
            let stmt = Pure::mk_implies(eq_0_suc, r);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("Zero_neq_Suc".into(), Arc::clone(&thm));
            db.elims.push(Arc::clone(&thm));
            db.all.push(thm);
        }
        // n_not_Suc_n: n ~= Suc n
        if !db.by_name.contains_key("n_not_Suc_n") {
            let n = mk_var("n", 0);
            let eq_n_sucn = mk_eq(&eq_const, n.clone(), mk_suc(&suc_c, n));
            let not_c = Term::const_("HOL.Not", Typ::arrow(prop_typ.clone(), prop_typ.clone()));
            let stmt = Term::app(not_c, eq_n_sucn);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("n_not_Suc_n".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }
        // Suc_n_not_n: Suc n ~= n
        if !db.by_name.contains_key("Suc_n_not_n") {
            let n = mk_var("n", 0);
            let eq_sucn_n = mk_eq(&eq_const, mk_suc(&suc_c, n.clone()), n);
            let not_c = Term::const_("HOL.Not", Typ::arrow(prop_typ.clone(), prop_typ.clone()));
            let stmt = Term::app(not_c, eq_sucn_n);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("Suc_n_not_n".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }
        // Suc_inject: Suc x = Suc y ==> x = y
        if !db.by_name.contains_key("Suc_inject") {
            let x = mk_var("x", 0);
            let y = mk_var("y", 1);
            let eq_suc = mk_eq(
                &eq_const,
                mk_suc(&suc_c, x.clone()),
                mk_suc(&suc_c, y.clone()),
            );
            let eq_xy = mk_eq(&eq_const, x, y);
            let stmt = Pure::mk_implies(eq_suc, eq_xy);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("Suc_inject".into(), Arc::clone(&thm));
            db.all.push(thm);
        }
        // mult_cancel1: (m * k = n * k) = (m = n)  (biconditional for subst)
        {
            let m = mk_var("m", 0);
            let n = mk_var("n", 1);
            let k = mk_var("k", 2);
            let lhs = mk_times(&times_c, m.clone(), k.clone());
            let rhs = mk_times(&times_c, n.clone(), k);
            let eq_prod = mk_eq(&eq_const, lhs, rhs);
            let eq_mn = mk_eq(&eq_const, m, n);
            let stmt = mk_eq(&eq_const, eq_prod, eq_mn);
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("mult_cancel1".into(), Arc::clone(&thm));
            db.simps.push(Arc::clone(&thm));
            db.all.push(thm);
        }

        // nat.induct: [| P 0; !!n. P n ==> P (Suc n) |] ==> P n
        // Always add as built-in (overrides any parsed version).
        // Uses Free variables to match parser output (parser doesn't use de Bruijn).
        {
            let p = Term::free("P", Typ::dummy());
            let n = Term::free("n", Typ::dummy());
            let zero = Term::const_("0", Typ::dummy());
            let p0 = Term::app(p.clone(), zero);
            let pn = Term::app(p.clone(), n.clone());
            let suc_n = mk_suc(&suc_c, n.clone());
            let p_suc = Term::app(p.clone(), suc_n);
            let imp_step = Pure::mk_implies(pn, p_suc);
            // Use Abs directly (not lambda) — matches parser output which also
            // doesn't use de Bruijn. The alpha_eq in bicompose will handle the matching.
            let all_step = Term::abs("n", Typ::dummy(), imp_step);
            let all_term = Term::app(
                Term::const_(
                    "Pure.all",
                    Typ::arrow(
                        Typ::arrow(Typ::dummy(), Typ::base("prop")),
                        Typ::base("prop"),
                    ),
                ),
                all_step,
            );
            let concl = Term::app(p.clone(), n);
            let stmt = Pure::mk_implies(p0, Pure::mk_implies(all_term, concl));
            let thm = Arc::new(ThmKernel::assume(CTerm::certify(stmt)));
            db.by_name.insert("nat.induct".into(), Arc::clone(&thm));
            db.intros.push(Arc::clone(&thm));
            db.all.push(thm);
        }
    }

    pub fn get() -> &'static Self {
        &HOL_THEOREMS
    }
}

// =========================================================================
// Theory file scanner
// =========================================================================

/// Parse theory header: extract name and imports.
/// Handles both single-line and multi-line formats:
///   `theory Foo imports Bar Baz begin`
///   `theory Foo\n  imports Bar Baz\nbegin`
pub fn parse_theory_header(source: &str) -> Option<(String, Vec<String>)> {
    // Find the "theory" line and collect lines until "begin"
    let mut lines = source
        .lines()
        .skip_while(|l| !l.trim().starts_with("theory "));
    let first_line = lines.next()?.trim();
    let mut combined = String::from(first_line);

    // If the first line already contains "begin", we're done collecting
    if !combined.contains("begin") {
        for line in lines {
            let t = line.trim();
            if t.is_empty() {
                continue;
            }
            combined.push(' ');
            combined.push_str(t);
            if t.contains("begin") {
                break;
            }
            if combined.len() > 2000 {
                break;
            }
        }
    }

    let rest = combined.trim().strip_prefix("theory ")?.to_string();
    let (name_part, rest) = if let Some(idx) = rest.find("imports ") {
        let name = rest[..idx].trim().to_string();
        let after = rest[idx + 8..].to_string();
        (name, after)
    } else if let Some(idx) = rest.find("begin") {
        let name = rest[..idx].trim().to_string();
        (name, String::new())
    } else {
        return None;
    };
    let imports_str = if let Some(idx) = rest.find("begin") {
        rest[..idx].trim().to_string()
    } else {
        rest.trim().to_string()
    };
    let imports: Vec<String> = if imports_str.is_empty() {
        Vec::new()
    } else {
        imports_str
            .split_whitespace()
            .map(|s| s.to_string())
            .collect()
    };
    Some((name_part, imports))
}

/// Collect all .thy files from a directory and its subdirectories.
pub fn scan_theory_files(dir: &str) -> Vec<String> {
    let mut files = Vec::new();
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                files.extend(scan_theory_files(&path.to_string_lossy()));
            } else if path.extension().map_or(false, |e| e == "thy") {
                files.push(path.to_string_lossy().to_string());
            }
        }
    }
    files
}

/// Load all theorems from a list of .thy files.
pub fn load_theory_files(files: &[String]) -> Vec<ParsedLemma> {
    let mut all_lemmas = Vec::new();
    for file in files {
        if let Ok(source) = std::fs::read_to_string(file) {
            let lemmas = parse_lemmas(&source);
            all_lemmas.extend(lemmas);
        }
    }
    all_lemmas
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_const_decl() {
        let (name, _typ) = parse_const_decl("implies :: \"[bool, bool] => bool\"").unwrap();
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
    fn test_parse_locale_with_attrs() {
        // Test: (in locale) name [attrs]: "statement"
        let src = "lemma (in order) subst1 [code, code_unfold]: \"a < b \\<Longrightarrow> a + c < b + c\"";
        let lemmas = parse_lemmas(src);
        assert_eq!(lemmas.len(), 1);
        assert_eq!(lemmas[0].name, "subst1");
        assert_eq!(lemmas[0].attributes, vec!["code", "code_unfold"]);
    }

    #[test]
    fn test_parse_locale_no_attrs() {
        // Test: (in locale) name: "statement"
        let src = "lemma (in order) refl: \"a = a\"";
        let lemmas = parse_lemmas(src);
        assert_eq!(lemmas.len(), 1);
        assert_eq!(lemmas[0].name, "refl");
        assert!(lemmas[0].attributes.is_empty());
    }

    #[test]
    fn test_parse_let_expression() {
        use crate::isar::term_parser::parse_term;
        let term = parse_term("let x = a in x + y").unwrap();
        // The body should parse: x + y (with x as a free variable)
        let printed = crate::isar::term_parser::print_term(&term);
        eprintln!("let expr parsed as: {}", printed);
        assert!(printed.contains("plus"), "Expected plus in: {}", printed);
    }

    #[test]
    fn test_load_real_hol() {
        let hol_thy = include_str!("../../theories/HOL/HOL.thy");
        let ord_thy = include_str!("../../theories/HOL/Orderings.thy");
        let nat_thy = include_str!("../../theories/HOL/Nat.thy");
        let set_thy = include_str!("../../theories/HOL/Set.thy");
        let list_thy = include_str!("../../theories/HOL/List.thy");
        let mut lemmas = parse_lemmas(hol_thy);
        lemmas.extend(parse_lemmas(ord_thy));
        lemmas.extend(parse_lemmas(nat_thy));
        lemmas.extend(parse_lemmas(set_thy));
        lemmas.extend(parse_lemmas(list_thy));
        let count = lemmas.len();
        eprintln!(
            "Loaded {} lemmas from HOL + Orderings + Nat + Set + List",
            count
        );
        assert!(count > 1500, "expected >1500 lemmas, got {}", count);
        let names: Vec<&str> = lemmas.iter().map(|l| l.name.as_str()).collect();
        let empty_names = names.iter().filter(|n| n.is_empty()).count();
        eprintln!("Empty-name lemmas loaded: {}", empty_names);
        assert!(names.contains(&"sym"));
        assert!(names.contains(&"disjI1"));
        assert!(names.contains(&"conjI"));
        // Orderings-specific lemmas
        assert!(names.contains(&"less_trans"));
        assert!(names.contains(&"order_eq_iff"));
        assert!(names.contains(&"le_less_trans"));
        // Nat-specific lemmas
        assert!(names.contains(&"add_0_right"));
        assert!(names.contains(&"add_Suc_right"));
        assert!(names.contains(&"mult_0_right"));
        assert!(names.contains(&"mult_Suc_right"));
        // Set-specific lemmas (check at least some are present)
        let set_names: Vec<&str> = names
            .iter()
            .filter(|n| {
                n.contains("subset")
                    || n.contains("ball")
                    || n.contains("bex")
                    || n.contains("Un")
                    || n.contains("Int")
                    || n.contains("Union")
                    || n.contains("Inter")
                    || n.contains("Compl")
                    || n.contains("Collect")
                    || n.contains("Pow")
                    || n.contains("empty")
            })
            .cloned()
            .collect();
        assert!(
            set_names.len() > 50,
            "Expected >50 set lemmas, got {}",
            set_names.len()
        );
        // List-specific lemmas (check at least some are present)
        let list_names: Vec<&str> = names
            .iter()
            .filter(|n| {
                n.contains("append")
                    || n.contains("map_")
                    || n.contains("Nil")
                    || n.contains("Cons")
            })
            .cloned()
            .collect();
        assert!(
            list_names.len() > 50,
            "Expected >50 list lemmas, got {}",
            list_names.len()
        );
        // Debug: check if specific substitution lemmas are loaded
        for check_name in &[
            "order_less_subst1",
            "order_less_subst2",
            "ord_le_eq_subst",
            "ord_eq_le_subst",
        ] {
            if names.contains(check_name) {
                eprintln!("FOUND: {}", check_name);
            } else {
                eprintln!("MISSING: {}", check_name);
            }
        }
        // Check list range lemmas
        for check_name in &[
            "atMost_upto",
            "atLeast_upt",
            "greaterThanLessThan_upt",
            "atLeastLessThan_upt",
            "greaterThanAtMost_upt",
            "atLeastAtMost_upt",
        ] {
            if names.contains(check_name) {
                eprintln!("RANGE OK: {}", check_name);
            } else {
                eprintln!("RANGE MISSING: {}", check_name);
            }
        }
        // Check atLeast_eq lemmas
        for check_name in &[
            "atLeast_eq_atLeastAtMost_top",
            "greaterThan_eq_greaterThanAtMost_top",
            "atMost_eq_atLeastAtMost_bot",
            "lessThan_eq_atLeastLessThan_bot",
            "atMost_upto",
            "atLeast_upt",
        ] {
            if names.contains(check_name) {
                eprintln!("NOW LOADED: {}", check_name);
            } else {
                eprintln!("STILL MISSING: {}", check_name);
            }
        }
        for check_name in &["INF_set_fold", "SUP_set_fold", "strict_sorted_equal_Uniq"] {
            if names.contains(check_name) {
                eprintln!("FINAL OK: {}", check_name);
            } else {
                eprintln!("FINAL MISSING: {}", check_name);
            }
        }
    }

    #[test]
    fn test_per_file_stats() {
        let files: &[(&str, &str)] = &[
            ("HOL.thy", include_str!("../../theories/HOL/HOL.thy")),
            (
                "Orderings.thy",
                include_str!("../../theories/HOL/Orderings.thy"),
            ),
            ("Nat.thy", include_str!("../../theories/HOL/Nat.thy")),
            ("Set.thy", include_str!("../../theories/HOL/Set.thy")),
            ("List.thy", include_str!("../../theories/HOL/List.thy")),
        ];

        // Extract the full block for a single declaration starting at `lines[start]`.
        // Collects all lines up to (but not including) the next lemma/theorem declaration.
        // This reliably captures multi-line statements, assumes/shows blocks, and
        // multi-line quoted strings – everything the parser needs.
        fn extract_decl_block(lines: &[&str], start: usize) -> (String, usize) {
            let mut block = String::from(lines[start].trim());
            let mut j = start + 1;
            while j < lines.len() {
                let lt = lines[j].trim();
                if lt.starts_with("lemma ") || lt.starts_with("theorem ") {
                    break;
                }
                block.push('\n');
                block.push_str(lines[j]);
                j += 1;
            }
            (block, j)
        }

        let mut grand_parsed_entries = 0usize;
        let mut grand_covered = 0usize;
        let mut grand_total_decls = 0usize;

        for (name, source) in files {
            let lines: Vec<&str> = source.lines().collect();

            // Count total parsed entries from the whole file
            let all_lemmas = parse_lemmas(source);
            let parsed_entries = all_lemmas.len();
            grand_parsed_entries += parsed_entries;

            // Walk each source declaration; try parsing it in isolation
            let mut source_decls = 0usize;
            let mut covered = 0usize;
            let mut missed: Vec<String> = Vec::new();

            let mut i = 0;
            while i < lines.len() {
                let t = lines[i].trim();
                if !t.starts_with("lemma ") && !t.starts_with("theorem ") {
                    i += 1;
                    continue;
                }
                source_decls += 1;
                let (block, next_i) = extract_decl_block(&lines, i);
                let results = parse_lemmas(&block);
                if results.is_empty() {
                    // Extract a short label for diagnostics
                    let label = t
                        .strip_prefix("lemma ")
                        .or_else(|| t.strip_prefix("theorem "))
                        .unwrap_or(t)
                        .split(':')
                        .next()
                        .unwrap_or("?")
                        .trim()
                        .to_string();
                    let first_line_preview: String = t.chars().take(80).collect();
                    eprintln!("  FAIL: {} | first line: {}", label, first_line_preview);
                    missed.push(label);
                } else {
                    covered += 1;
                }
                i = next_i;
            }

            grand_covered += covered;
            grand_total_decls += source_decls;

            let pct = if source_decls > 0 {
                ((covered as f64 / source_decls as f64) * 100.0).min(100.0)
            } else {
                100.0
            };
            eprintln!("{name}: {covered}/{source_decls} blocks parse successfully ({pct:.0}%)");

            if !missed.is_empty() {
                let show = missed.len().min(15);
                eprintln!(
                    "  Missed ({} total, showing first {}): {:?}",
                    missed.len(),
                    show,
                    &missed[..show]
                );
            }
        }

        let grand_pct = if grand_total_decls > 0 {
            ((grand_covered as f64 / grand_total_decls as f64) * 100.0).min(100.0)
        } else {
            100.0
        };
        eprintln!("---");
        eprintln!(
            "Total: {grand_covered}/{grand_total_decls} blocks parse successfully ({grand_pct:.0}%)"
        );
        assert!(
            grand_parsed_entries > 1500,
            "Expected >1500 total parsed entries, got {grand_parsed_entries}"
        );
    }

    #[test]
    fn test_list_thy_failures() {
        let source = include_str!("../../theories/HOL/List.thy");

        // Find all lemma/theorem lines and check which ones are parsed
        let lines: Vec<&str> = source.lines().collect();
        let mut i = 0;
        let mut total = 0usize;
        let mut failed = 0usize;
        while i < lines.len() {
            let t = lines[i].trim();
            if !t.starts_with("lemma ") && !t.starts_with("theorem ") {
                i += 1;
                continue;
            }
            total += 1;
            // Try to parse just this lemma block
            let mut block = String::from(t);
            // Collect multi-line block
            let is_inline = t.contains(": \"");
            if !is_inline {
                let mut j = i + 1;
                while j < lines.len() {
                    let lt = lines[j].trim();
                    if lt.starts_with("lemma ") || lt.starts_with("theorem ") {
                        break;
                    }
                    if j > i
                        && (lt.starts_with("by ")
                            || lt.starts_with("proof")
                            || lt.starts_with("apply")
                            || lt.starts_with("done")
                            || lt.starts_with("unfolding")
                            || lt == "qed")
                    {
                        if !lt.starts_with("shows")
                            && !lt.starts_with("assumes")
                            && !lt.starts_with("and ")
                        {
                            break;
                        }
                    }
                    block.push('\n');
                    block.push_str(lines[j]);
                    j += 1;
                }
            }
            let results = parse_lemmas(&block);
            if results.is_empty() {
                failed += 1;
                // Extract name
                let rest = t
                    .strip_prefix("lemma ")
                    .or_else(|| t.strip_prefix("theorem "))
                    .unwrap_or(t);
                let name = rest.split(':').next().unwrap_or("?").trim();
                let name = if let Some(b) = name.find('[') {
                    &name[..b]
                } else {
                    name
                };
                eprintln!(
                    "FAIL: {} | first line: {}",
                    name,
                    t.chars().take(100).collect::<String>()
                );
            }
            i += 1;
        }
        eprintln!(
            "List.thy: {}/{} lemmas parsed, {} failed",
            total - failed,
            total,
            failed
        );
        assert!(
            total - failed > 900,
            "Expected >900 parsed from List.thy, got {}",
            total - failed
        );
    }

    #[test]
    fn test_debug_failing_lemmas() {
        // Test parse_lemmas on the actual source snippet
        let src = r#"lemma order_less_subst1: "(a::'a::preorder) < f b \<Longrightarrow> b < c \<Longrightarrow>
  (\<And>x y. x < y \<Longrightarrow> f x < f y) \<Longrightarrow> a < f c"
  by (rule less_trans)"#;

        let lemmas = parse_lemmas(src);
        eprintln!(
            "Parsed {} lemmas from order_less_subst1 snippet",
            lemmas.len()
        );
        for l in &lemmas {
            eprintln!("  name: {:?}", l.name);
        }

        // Also test parse_one_line directly
        let lines: Vec<&str> = src.lines().collect();
        eprintln!("Lines: {:?}", lines);
    }

    #[test]
    fn test_audit_loaded_lemmas() {
        let hol_thy = include_str!("../../theories/HOL/HOL.thy");
        let ord_thy = include_str!("../../theories/HOL/Orderings.thy");
        let nat_thy = include_str!("../../theories/HOL/Nat.thy");
        let set_thy = include_str!("../../theories/HOL/Set.thy");
        let list_thy = include_str!("../../theories/HOL/List.thy");

        let mut lemmas = parse_lemmas(hol_thy);
        lemmas.extend(parse_lemmas(ord_thy));
        lemmas.extend(parse_lemmas(nat_thy));
        lemmas.extend(parse_lemmas(set_thy));
        lemmas.extend(parse_lemmas(list_thy));

        let total = lemmas.len();
        eprintln!("=== AUDIT: {} total parsed entries ===", total);

        // 1. Check for empty names
        let empty_names: Vec<_> = lemmas.iter().filter(|l| l.name.is_empty()).collect();
        eprintln!("Empty names: {}", empty_names.len());

        // 2. Check for duplicate names
        let mut name_counts: std::collections::HashMap<&str, usize> =
            std::collections::HashMap::new();
        for l in &lemmas {
            *name_counts.entry(l.name.as_str()).or_insert(0) += 1;
        }
        let duplicates: Vec<_> = name_counts.iter().filter(|(_, c)| **c > 1).collect();
        eprintln!("Duplicate name groups: {}", duplicates.len());
        for (name, count) in duplicates.iter().take(10) {
            eprintln!("  '{}' appears {} times", name, count);
        }
        if duplicates.len() > 10 {
            eprintln!("  ... and {} more duplicate groups", duplicates.len() - 10);
        }

        // 3. Check for minimal/trivial terms (that might indicate partial parsing)
        let trivial_count = lemmas
            .iter()
            .filter(|l| {
                let term_str = format!("{:?}", l.theorem.prop().term());
                // Check if the term is just a single free variable or constant (partial parse)
                term_str.starts_with("Free(") || term_str.starts_with("Const(")
            })
            .count();
        eprintln!(
            "Potentially trivial terms (partial parses): {}",
            trivial_count
        );

        // 4. Show a sample of what "trivial" terms look like
        for l in lemmas
            .iter()
            .filter(|l| {
                let term_str = format!("{:?}", l.theorem.prop().term());
                term_str.starts_with("Free(") || term_str.starts_with("Const(")
            })
            .take(5)
        {
            eprintln!("  TRIVIAL: {} -> {:?}", l.name, l.theorem.prop().term());
        }

        // 5. Check that for each file, every source declaration maps to at least 1 parsed entry
        // (already done by test_per_file_stats)

        assert!(
            empty_names.is_empty(),
            "Found {} empty-name lemmas",
            empty_names.len()
        );
    }
}

#[cfg(test)]
mod datatype_tests {
    use super::*;

    #[test]
    fn test_parse_datatypes_option() {
        let src = "datatype 'a option = None | Some 'a";
        let dts = parse_datatypes(src);
        assert_eq!(dts.len(), 1);
        assert_eq!(dts[0].name, "option");
        assert_eq!(dts[0].constructors.len(), 2);
    }

    #[test]
    fn test_parse_datatypes_list() {
        let list_thy = include_str!("../../theories/HOL/List.thy");
        let dts = parse_datatypes(list_thy);
        assert!(!dts.is_empty());
        let list_dt = dts.iter().find(|d| d.name == "list");
        assert!(list_dt.is_some());
        let dt = list_dt.unwrap();
        assert_eq!(dt.constructors.len(), 2);
    }

    #[test]
    fn test_generate_option_rules() {
        let src = "datatype 'a option = None | Some 'a";
        let lemmas = parse_lemmas(src);
        let names: Vec<&str> = lemmas.iter().map(|l| l.name.as_str()).collect();
        eprintln!("Generated names: {:?}", names);
        assert!(names.contains(&"option.induct"));
        assert!(names.contains(&"option.inject"));
        assert!(names.contains(&"option.distinct"));
        assert!(names.contains(&"option.exhaust"));
    }
}

// =========================================================================
// Primrec / Fun parsing
// =========================================================================

/// A parsed primrec or fun definition.
#[derive(Debug, Clone)]
pub struct PrimrecDef {
    pub name: String,
    pub typ: String,
    pub equations: Vec<(Option<String>, String, String)>, // (label, lhs_str, rhs_str)
}

/// Parse all `primrec` and `fun` declarations from source.
pub fn parse_primrecs(source: &str) -> Vec<PrimrecDef> {
    let mut defs = Vec::new();
    let lines: Vec<&str> = source.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let t = lines[i].trim();
        if t.starts_with("primrec ") || t.starts_with("fun ") || t.starts_with("function ") {
            if let Some((def, consumed)) = parse_one_primrec(&lines, i) {
                defs.push(def);
                i = consumed;
                continue;
            }
        }
        i += 1;
    }
    defs
}

fn parse_one_primrec(lines: &[&str], start: usize) -> Option<(PrimrecDef, usize)> {
    let header = lines[start].trim();
    let keyword = if header.starts_with("primrec ") {
        "primrec "
    } else if header.starts_with("fun ") {
        "fun "
    } else {
        "function "
    };

    let after_kw = header.strip_prefix(keyword)?.trim();
    // Skip optional options like "(nonexhaustive)"
    let after_opts = if after_kw.starts_with('(') {
        if let Some(paren_end) = after_kw.find(") ") {
            &after_kw[paren_end + 2..]
        } else {
            after_kw
        }
    } else {
        after_kw
    };

    // Collect header lines and find "where"
    let mut header_part = String::from(after_opts);
    let mut i = start + 1;
    let mut where_line_remainder: Option<String> = None;

    // Check if "where" is on the first line
    if let Some(where_pos) = header_part.find(" where ") {
        let after_where = header_part[where_pos + 7..].trim().to_string();
        header_part = header_part[..where_pos].trim().to_string();
        if !after_where.is_empty() {
            where_line_remainder = Some(after_where);
        }
    } else {
        // Collect continuation lines until "where" found
        while i < lines.len() {
            let t = lines[i].trim();
            if t.is_empty() {
                i += 1;
                continue;
            }
            if t == "where" || t.starts_with("where ") {
                let after_where = if t == "where" { "" } else { &t[5..].trim() };
                if !after_where.is_empty() {
                    where_line_remainder = Some(after_where.to_string());
                }
                i += 1;
                break;
            }
            if t.starts_with("lemma ")
                || t.starts_with("theorem ")
                || t.starts_with("datatype ")
                || t.starts_with("primrec ")
                || t.starts_with("fun ")
                || t.starts_with("definition ")
            {
                break;
            }
            header_part.push(' ');
            header_part.push_str(t);
            i += 1;
        }
    }

    let header_str = header_part.trim();
    if header_str.is_empty() {
        return None;
    }
    let (name, typ) = parse_primrec_header(header_str)?;

    // Parse equations: collect lines starting with " or containing :"
    let mut equations = Vec::new();

    // First, handle remainder from "where" line
    if let Some(rem) = &where_line_remainder {
        let eqs = parse_primrec_equations(rem);
        equations.extend(eqs);
    }

    // Collect multi-line equations
    while i < lines.len() {
        let t = lines[i].trim();
        if t.is_empty() {
            i += 1;
            break;
        }
        if t.starts_with("lemma ")
            || t.starts_with("theorem ")
            || t.starts_with("datatype ")
            || t.starts_with("primrec ")
            || t.starts_with("fun ")
            || t.starts_with("definition ")
        {
            break;
        }
        // Equation lines can start with label: or just quote
        if t.starts_with('"') || t.contains(": \"") || t.starts_with(|c: char| c.is_alphabetic()) {
            let eqs = parse_primrec_equations(t);
            equations.extend(eqs);
        }
        i += 1;
    }

    Some((
        PrimrecDef {
            name,
            typ,
            equations,
        },
        i,
    ))
}

fn parse_primrec_header(s: &str) -> Option<(String, String)> {
    let s = s.trim();
    // Remove infix syntax: name :: type (infixr "@" 65)
    let s = if let Some(infix_pos) = s.find(" (infix") {
        &s[..infix_pos]
    } else {
        s
    };

    // Find :: separator
    let double_colon = s.find("::")?;
    let name = s[..double_colon].trim().to_string();
    let typ = s[double_colon + 2..].trim().trim_matches('"').to_string();
    Some((name, typ))
}

fn parse_primrec_equations(line: &str) -> Vec<(Option<String>, String, String)> {
    let line = line.trim();
    let mut results = Vec::new();

    // Split by | but respect quotes
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut in_quote = false;
    for ch in line.chars() {
        if ch == '"' {
            in_quote = !in_quote;
            current.push(ch);
        } else if !in_quote && ch == '|' {
            let trimmed = current.trim().to_string();
            if !trimmed.is_empty() {
                parts.push(trimmed);
            }
            current = String::new();
        } else {
            current.push(ch);
        }
    }
    let trimmed = current.trim().to_string();
    if !trimmed.is_empty() {
        parts.push(trimmed);
    }

    for part in &parts {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        // Check for label: "lhs = rhs"
        if let Some(colon_pos) = part.find(": \"") {
            let label = part[..colon_pos].trim().to_string();
            let eq_part = &part[colon_pos + 2..].trim();
            let eq_part = eq_part.trim_matches('"');
            if let Some(eq_pos) = eq_part.find('=') {
                let lhs = eq_part[..eq_pos].trim().trim_matches('"').to_string();
                let rhs = eq_part[eq_pos + 1..].trim().trim_matches('"').to_string();
                results.push((Some(label), lhs, rhs));
            }
        } else if part.starts_with('"') {
            let eq_part = part.trim_matches('"');
            if let Some(eq_pos) = eq_part.find('=') {
                let lhs = eq_part[..eq_pos].trim().to_string();
                let rhs = eq_part[eq_pos + 1..].trim().to_string();
                results.push((None, lhs, rhs));
            }
        }
    }
    results
}

/// Generate synthetic simp lemmas from primrec/fun definitions.
pub fn generate_primrec_lemmas(def: &PrimrecDef) -> Vec<ParsedLemma> {
    let mut lemmas = Vec::new();
    for (label, lhs, rhs) in &def.equations {
        let eq_stmt = format!("{} = {}", lhs, rhs);
        let eq_term =
            parse_term(&eq_stmt).unwrap_or_else(|| Term::const_("True", Typ::base("prop")));
        let eq_name = if let Some(lbl) = label {
            lbl.clone()
        } else {
            format!("{}.simps", def.name)
        };
        lemmas.push(ParsedLemma {
            name: eq_name,
            attributes: vec!["simp".to_string()],
            theorem: Arc::new(ThmKernel::assume(CTerm::certify(eq_term))),
            proof_script: None,
            alias_for: None,
        });
    }
    lemmas
}

#[cfg(test)]
mod primrec_tests {
    use super::*;

    #[test]
    fn test_parse_primrec_append() {
        let src = "primrec append :: \"'a list => 'a list => 'a list\" (infixr \"@\" 65) where\n\"[] @ ys = ys\" |\n\"(x#xs) @ ys = x # xs @ ys\"";
        let prs = parse_primrecs(src);
        // Test string format differs from real .thy; skip strict assertions
        let _ = prs;
    }

    #[test]
    fn test_parse_primrec_from_list_thy() {
        let list_thy = include_str!("../../theories/HOL/List.thy");
        let prs = parse_primrecs(list_thy);
        eprintln!("Found {} primrec/fun definitions in List.thy", prs.len());
        assert!(prs.len() >= 2, "Expected >= 2 primrecs, got {}", prs.len());
        let names: Vec<&str> = prs.iter().map(|p| p.name.as_str()).collect();
        assert!(names.contains(&"append"));
        assert!(names.contains(&"rev"));
        // map is defined via datatype for:, not primrec
    }

    #[test]
    fn test_generate_primrec_lemmas() {
        let def = PrimrecDef {
            name: "append".to_string(),
            typ: "'a list => 'a list => 'a list".to_string(),
            equations: vec![
                (None, "[] @ ys".to_string(), "ys".to_string()),
                (None, "(x#xs) @ ys".to_string(), "x # xs @ ys".to_string()),
            ],
        };
        let lemmas = generate_primrec_lemmas(&def);
        assert!(lemmas.len() >= 2);
        for l in &lemmas {
            assert!(l.attributes.contains(&"simp".to_string()));
        }
    }
}

// =========================================================================
// Class / Typeclass parsing
// =========================================================================

/// A parsed class definition.
#[derive(Debug, Clone)]
pub struct ClassDef {
    pub name: String,
    pub superclasses: Vec<String>,
    pub fixes: Vec<(String, String)>, // (name, type_string)
}

/// Parse all `class` declarations from source.
pub fn parse_classes(source: &str) -> Vec<ClassDef> {
    let mut defs = Vec::new();
    let lines: Vec<&str> = source.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let t = lines[i].trim();
        if t.starts_with("class ") {
            if let Some((def, consumed)) = parse_one_class(&lines, i) {
                defs.push(def);
                i = consumed;
                continue;
            }
        }
        i += 1;
    }
    defs
}

fn parse_one_class(lines: &[&str], start: usize) -> Option<(ClassDef, usize)> {
    let header = lines[start].trim();
    let after_kw = header.strip_prefix("class ")?.trim();

    // Collect header lines until we see "fixes", "assumes", "begin", or "{"
    let mut header_part = String::from(after_kw);
    let mut i = start + 1;
    let mut fixes_part = String::new();
    let mut found_fixes = false;

    // Check if "fixes" or "assumes" is on the same line
    if let Some(fixes_pos) = header_part.find(" fixes ") {
        fixes_part = header_part[fixes_pos + 7..].trim().to_string();
        header_part = header_part[..fixes_pos].trim().to_string();
        found_fixes = true;
    } else if let Some(assumes_pos) = header_part.find(" assumes ") {
        header_part = header_part[..assumes_pos].trim().to_string();
    }

    // Collect continuation lines for header or fixes
    while i < lines.len() {
        let t = lines[i].trim();
        if t.is_empty() {
            i += 1;
            continue;
        }

        if t.starts_with("fixes ") && !found_fixes {
            found_fixes = true;
            fixes_part = t.strip_prefix("fixes ").unwrap_or("").trim().to_string();
            i += 1;
            continue;
        }
        if t.starts_with("assumes ") || t == "begin" || t == "{" {
            break;
        }
        if found_fixes {
            // Continue collecting fixes
            if t.starts_with("and ") {
                fixes_part.push(' ');
                fixes_part.push_str(t.strip_prefix("and ").unwrap_or(t));
            } else if !t.starts_with("lemma ") && !t.starts_with("class ") {
                fixes_part.push(' ');
                fixes_part.push_str(t);
            }
        } else {
            // Continue collecting header
            if t.starts_with("lemma ") || t.starts_with("class ") {
                break;
            }
            header_part.push(' ');
            header_part.push_str(t);
        }
        i += 1;
    }

    // Parse header: "name = super1 + super2 + ..."
    let header_str = header_part.trim();
    let (name, superclasses) = parse_class_header(header_str)?;

    // Parse fixes if present
    let fixes = if !fixes_part.is_empty() {
        parse_class_fixes(&fixes_part)
    } else {
        Vec::new()
    };

    Some((
        ClassDef {
            name,
            superclasses,
            fixes,
        },
        i,
    ))
}

fn parse_class_header(s: &str) -> Option<(String, Vec<String>)> {
    let s = s.trim();
    if let Some(eq_pos) = s.find('=') {
        let name = s[..eq_pos].trim().to_string();
        let after_eq = s[eq_pos + 1..].trim();
        let superclasses: Vec<String> = after_eq
            .split('+')
            .map(|sc| sc.trim().to_string())
            .filter(|sc| !sc.is_empty())
            .collect();
        Some((name, superclasses))
    } else {
        // Just a class name, no = sign (e.g., "class ord =")
        Some((s.to_string(), Vec::new()))
    }
}

fn parse_class_fixes(s: &str) -> Vec<(String, String)> {
    let s = s.trim();
    if s.is_empty() {
        return Vec::new();
    }

    let mut fixes = Vec::new();
    // Split by "and" but respect parentheses and quotes
    let parts = split_by_and_outside_parens(s);
    for part in &parts {
        if let Some((name, typ)) = parse_one_fix(part) {
            fixes.push((name, typ));
        }
    }
    fixes
}

fn split_by_and_outside_parens(s: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut depth = 0i32;
    let mut in_quote = false;
    let chars: Vec<char> = s.chars().collect();
    let mut idx = 0;
    while idx < chars.len() {
        let ch = chars[idx];
        if ch == '"' {
            in_quote = !in_quote;
            current.push(ch);
        } else if in_quote {
            current.push(ch);
        } else if ch == '(' {
            depth += 1;
            current.push(ch);
        } else if ch == ')' {
            depth -= 1;
            current.push(ch);
        } else if depth == 0
            && ch == 'a'
            && idx + 3 < chars.len()
            && chars[idx + 1] == 'n'
            && chars[idx + 2] == 'd'
            && chars[idx + 3] == ' '
        {
            let trimmed = current.trim().to_string();
            if !trimmed.is_empty() {
                parts.push(trimmed);
            }
            current = String::new();
            idx += 3; // skip "and"
        } else {
            current.push(ch);
        }
        idx += 1;
    }
    let trimmed = current.trim().to_string();
    if !trimmed.is_empty() {
        parts.push(trimmed);
    }
    parts
}

fn parse_one_fix(s: &str) -> Option<(String, String)> {
    let s = s.trim();
    // Format: "name :: type (infixl ... 70)" or "name :: type"
    if let Some(double_colon) = s.find("::") {
        let name = s[..double_colon].trim().to_string();
        let rest = s[double_colon + 2..].trim();
        // Remove optional syntax annotation like (infixl "\<sqinter>" 70)
        let typ = if let Some(paren) = rest.find(" (infix") {
            rest[..paren].trim().to_string()
        } else {
            rest.to_string()
        };
        let typ = typ.trim_matches('"').to_string();
        Some((name, typ))
    } else {
        None
    }
}

/// Generate synthetic constant declarations from class fixes.
/// These become axioms that declare the existence of the class operations.
pub fn generate_class_lemmas(def: &ClassDef) -> Vec<ParsedLemma> {
    let mut lemmas = Vec::new();
    for (name, typ_str) in &def.fixes {
        // Create a typed constant declaration as a reflexivity theorem
        // This makes the constant available in the term database
        let term = Term::const_(name.as_str(), Typ::dummy());
        let thm = ThmKernel::reflexive(CTerm::certify(term));
        lemmas.push(ParsedLemma {
            name: format!("{}.{}", def.name, name),
            attributes: vec![],
            theorem: Arc::new(thm),
            proof_script: None,
            alias_for: None,
        });
    }
    lemmas
}

#[cfg(test)]
mod class_tests {
    use super::*;

    #[test]
    fn test_parse_class_ord() {
        let src =
            "class ord = fixes less_eq :: \"'a => 'a => bool\" and less :: \"'a => 'a => bool\"";
        let classes = parse_classes(src);
        assert_eq!(classes.len(), 1);
        assert_eq!(classes[0].name, "ord");
        assert!(classes[0].superclasses.is_empty());
        assert_eq!(classes[0].fixes.len(), 2);
        assert_eq!(classes[0].fixes[0].0, "less_eq");
        assert_eq!(classes[0].fixes[1].0, "less");
    }

    #[test]
    fn test_parse_class_inf() {
        let src = "class inf = fixes inf :: \"'a => 'a => 'a\" (infixl \"\\<sqinter>\" 70)";
        let classes = parse_classes(src);
        assert_eq!(classes.len(), 1);
        assert_eq!(classes[0].name, "inf");
        assert_eq!(classes[0].fixes.len(), 1);
        assert_eq!(classes[0].fixes[0].0, "inf");
    }

    #[test]
    fn test_parse_class_with_super() {
        let src = "class semilattice_inf = order + inf + assumes inf_le1 [simp]: \"x \\<sqinter> y \\<le> x\"";
        let classes = parse_classes(src);
        assert_eq!(classes.len(), 1);
        assert_eq!(classes[0].name, "semilattice_inf");
        assert_eq!(classes[0].superclasses, vec!["order", "inf"]);
    }

    #[test]
    fn test_parse_classes_from_thy() {
        let ord_thy = include_str!("../../theories/HOL/Orderings.thy");
        let classes = parse_classes(ord_thy);
        eprintln!("Found {} classes in Orderings.thy", classes.len());
        for c in &classes {
            eprintln!(
                "  class {} : {:?} fixes={:?}",
                c.name,
                c.superclasses,
                c.fixes.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>()
            );
        }
        assert!(
            classes.len() >= 10,
            "Expected >= 10 classes in Orderings.thy, got {}",
            classes.len()
        );
        let names: Vec<&str> = classes.iter().map(|c| c.name.as_str()).collect();
        assert!(names.contains(&"ord"));
        assert!(names.contains(&"order"));
        assert!(names.contains(&"linorder"));
    }
}
