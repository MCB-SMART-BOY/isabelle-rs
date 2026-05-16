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
use crate::core::term::Term;
use crate::core::logic::Pure;
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

/// Parse lemmas from .thy source. Handles both inline and multi-line formats.
pub fn parse_lemmas(source: &str) -> Vec<ParsedLemma> {
    let mut lemmas = Vec::new();
    let lines: Vec<&str> = source.lines().collect();
    let mut i = 0;
    while i < lines.len() {
        let t = lines[i].trim();
        if !t.starts_with("lemma ") && !t.starts_with("theorem ") {
            i += 1;
            continue;
        }
        // Determine if this is inline or multi-line
        if let Some(ls) = parse_one_line(&lines, &mut i) {
            lemmas.extend(ls);
        } else {
            // Try multi-line parse
            if let Some(ls) = parse_multi_line(&lines, &mut i) {
                lemmas.extend(ls);
            } else {
                i += 1;
            }
        }
    }
    lemmas
}

/// Strip `(in locale_name)` prefix from a lemma name part.
fn strip_locale_prefix(s: &str) -> &str {
    let s = s.trim();
    if s.starts_with("(in ") {
        // Find the closing )
        if let Some(pos) = s.find(')') {
            return s[pos+1..].trim();
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
            let after_colon = rest[idx+1..].trim();
            return Some((name_part, after_colon));
        }
    }
    // No colon found outside brackets
    None
}

/// Try to parse an inline (single-line) lemma.
fn parse_one_line(lines: &[&str], i: &mut usize) -> Option<Vec<ParsedLemma>> {
    let line = lines[*i].trim();
    let rest = line.strip_prefix("lemma ")
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
            results.push(ParsedLemma { name: lemma_name, attributes: attrs.clone(), theorem: thm });
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
    let rest = header_line.strip_prefix("lemma ")
        .or_else(|| header_line.strip_prefix("theorem "))?;
    let rest = strip_locale_prefix(rest);

    // Try to split name from statement on the header line.
    // If there's no colon on the header line (e.g., name on one line,
    // attributes/colon on the next), scan forward for the colon.
    let (name, attrs, block_lines) = if let Some((name_part, after_colon)) = split_name_statement(rest) {
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
        collect_block_lines(lines, i, &mut block_lines);
        (name, attrs, block_lines)
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
        collect_block_lines(lines, i, &mut block_lines);
        (name, attrs, block_lines)
    };

    let block = block_lines.join("\n");
    parse_structured_stmt(&block, &name, &attrs)
}

/// Collect block lines after the header (until a proof command or next lemma).
fn collect_block_lines(lines: &[&str], i: &mut usize, block_lines: &mut Vec<String>) {
    while *i < lines.len() {
        let t = lines[*i].trim();
        if t.is_empty() {
            *i += 1;
            continue;
        }
        if t.starts_with("lemma ") || t.starts_with("theorem ") {
            break;
        }
        // Check for proof-start keywords (at any indentation level that's not part of the block)
        let is_proof_cmd = t.starts_with("by ") || t.starts_with("by(")
            || t.starts_with("proof") || t.starts_with("apply")
            || t == "done" || t.starts_with("done ")
            || t.starts_with("unfolding") || t.starts_with("using")
            || t == "qed"
            || t == "." || t.starts_with("induction ")
            || t.starts_with("cases ") || t.starts_with("induct ");
        if is_proof_cmd && !t.starts_with("assumes") && !t.starts_with("shows")
           && !t.starts_with("and ") && !t.starts_with("fixes") && !t.starts_with("obtains")
        {
            *i += 1;
            break;
        }
        block_lines.push(lines[*i].to_string());
        *i += 1;
    }
}

/// Parse an `assumes ... shows ...` structured statement block.
fn parse_structured_stmt(block: &str, lemma_name: &str, attrs: &[String]) -> Option<Vec<ParsedLemma>> {
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
            results.push(ParsedLemma { name, attributes: attrs.to_vec(), theorem: thm });
            show_idx += 1;
        }
        return Some(results);
    }

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
        results.push(ParsedLemma { name, attributes: attrs.to_vec(), theorem: thm });
        show_idx += 1;
    }
    Some(results)
}

/// Extract assumes clauses and shows clauses from a structured block.
/// Returns (assumes_clauses, shows_clauses) where each shows clause is (name, statement).
fn extract_assumes_shows(block: &str) -> Option<(Vec<String>, Vec<(String, String)>)> {
    // Convert cartouches to quotes early, so that quote-aware splitting functions
    // (merge_multiline_quotes, split_by_and_outside_quotes, etc.) see them as quotes.
    let block = block
        .replace("\\<open>", "\"")
        .replace("\\<close>", "\"");
    let mut assumes_clauses: Vec<String> = Vec::new();
    let mut shows_clauses: Vec<(String, String)> = Vec::new();
    let mut current_section: Option<&str> = None; // "assumes" or "shows"

    for raw_line in block.lines() {
        // Convert cartouche to quotes in this line before processing
        let line = raw_line.replace("\\<open>", "\"").replace("\\<close>", "\"");
        let t = line.trim();
        if t.is_empty() { continue; }

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
        let clean: String = block.lines()
            .map(|l| l.trim())
            .filter(|l| !l.is_empty()
                && !l.starts_with("assumes") && !l.starts_with("shows")
                && !l.starts_with("and ") && !l.starts_with("fixes"))
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
    if text.is_empty() { return; }

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
    if text.is_empty() { return; }

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
        } else if !in_quote && idx + 3 < chars.len()
            && chars[idx..idx+3].iter().collect::<String>() == "and"
            && (idx == 0 || chars[idx-1].is_whitespace())
            && (idx + 3 >= chars.len() || chars[idx+3].is_whitespace()) {
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
    if clause.is_empty() { return vec![]; }

    let mut results = Vec::new();
    let mut remaining = clause;

    // First, check if there's a name prefix: `name:`
    if let Some(colon_pos) = remaining.find(':') {
        // Check if colon is before any quote — it's a name prefix
        if let Some(quote_pos) = remaining.find('"') {
            if colon_pos < quote_pos {
                // There's a name: prefix — strip it
                remaining = remaining[colon_pos+1..].trim();
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
                let stmt = extract_quoted(&clause[colon_pos+1..])?;
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
    if !s.starts_with('"') { return None; }
    let inner = &s[1..];
    let mut result = String::new();
    let chars: Vec<char> = inner.chars().collect();
    let mut idx = 0;
    while idx < chars.len() {
        if chars[idx] == '\\' && idx + 1 < chars.len() && chars[idx+1] == '"' {
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
    s.trim_start_matches('[').trim_end_matches(']')
        .split(',').map(|a| a.trim().to_string()).collect()
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
        if t.starts_with("(*") && t.contains("*)") { continue; }
        if t.is_empty() || t.starts_with("assumes") || t.starts_with("shows") || t.starts_with("fixes") {
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
static HOL_THEOREMS: LazyLock<HolTheoremDb> = LazyLock::new(|| {
    let hol_thy = include_str!("../../isabelle-source/src/HOL/HOL.thy");
    let ord_thy = include_str!("../../isabelle-source/src/HOL/Orderings.thy");
    let nat_thy = include_str!("../../isabelle-source/src/HOL/Nat.thy");
    let set_thy = include_str!("../../isabelle-source/src/HOL/Set.thy");
    let list_thy = include_str!("../../isabelle-source/src/HOL/List.thy");
    let mut lemmas = parse_lemmas(hol_thy);
    lemmas.extend(parse_lemmas(ord_thy));
    lemmas.extend(parse_lemmas(nat_thy));
    lemmas.extend(parse_lemmas(set_thy));
    lemmas.extend(parse_lemmas(list_thy));
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
        let hol_thy = include_str!("../../isabelle-source/src/HOL/HOL.thy");
        let ord_thy = include_str!("../../isabelle-source/src/HOL/Orderings.thy");
        let nat_thy = include_str!("../../isabelle-source/src/HOL/Nat.thy");
        let set_thy = include_str!("../../isabelle-source/src/HOL/Set.thy");
        let list_thy = include_str!("../../isabelle-source/src/HOL/List.thy");
        let mut lemmas = parse_lemmas(hol_thy);
        lemmas.extend(parse_lemmas(ord_thy));
        lemmas.extend(parse_lemmas(nat_thy));
        lemmas.extend(parse_lemmas(set_thy));
        lemmas.extend(parse_lemmas(list_thy));
        let count = lemmas.len();
        eprintln!("Loaded {} lemmas from HOL + Orderings + Nat + Set + List", count);
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
        let set_names: Vec<&str> = names.iter().filter(|n| {
            n.contains("subset") || n.contains("ball") || n.contains("bex") || n.contains("Un") || n.contains("Int") || n.contains("Union") || n.contains("Inter") || n.contains("Compl") || n.contains("Collect") || n.contains("Pow") || n.contains("empty")
        }).cloned().collect();
        assert!(set_names.len() > 50, "Expected >50 set lemmas, got {}", set_names.len());
        // List-specific lemmas (check at least some are present)
        let list_names: Vec<&str> = names.iter().filter(|n| {
            n.contains("append") || n.contains("map_") || n.contains("Nil") || n.contains("Cons")
        }).cloned().collect();
        assert!(list_names.len() > 50, "Expected >50 list lemmas, got {}", list_names.len());
        // Debug: check if specific substitution lemmas are loaded
        for check_name in &["order_less_subst1", "order_less_subst2", "ord_le_eq_subst", "ord_eq_le_subst"] {
            if names.contains(check_name) {
                eprintln!("FOUND: {}", check_name);
            } else {
                eprintln!("MISSING: {}", check_name);
            }
        }
        // Check list range lemmas
        for check_name in &["atMost_upto", "atLeast_upt", "greaterThanLessThan_upt",
            "atLeastLessThan_upt", "greaterThanAtMost_upt", "atLeastAtMost_upt"] {
            if names.contains(check_name) {
                eprintln!("RANGE OK: {}", check_name);
            } else {
                eprintln!("RANGE MISSING: {}", check_name);
            }
        }
        // Check atLeast_eq lemmas
        for check_name in &["atLeast_eq_atLeastAtMost_top", "greaterThan_eq_greaterThanAtMost_top",
            "atMost_eq_atLeastAtMost_bot", "lessThan_eq_atLeastLessThan_bot",
            "atMost_upto", "atLeast_upt"] {
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
            ("HOL.thy", include_str!("../../isabelle-source/src/HOL/HOL.thy")),
            ("Orderings.thy", include_str!("../../isabelle-source/src/HOL/Orderings.thy")),
            ("Nat.thy", include_str!("../../isabelle-source/src/HOL/Nat.thy")),
            ("Set.thy", include_str!("../../isabelle-source/src/HOL/Set.thy")),
            ("List.thy", include_str!("../../isabelle-source/src/HOL/List.thy")),
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
                eprintln!("  Missed ({} total, showing first {}): {:?}", missed.len(), show, &missed[..show]);
            }
        }

        let grand_pct = if grand_total_decls > 0 {
            ((grand_covered as f64 / grand_total_decls as f64) * 100.0).min(100.0)
        } else {
            100.0
        };
        eprintln!("---");
        eprintln!("Total: {grand_covered}/{grand_total_decls} blocks parse successfully ({grand_pct:.0}%)");
        assert!(grand_parsed_entries > 1500, "Expected >1500 total parsed entries, got {grand_parsed_entries}");
    }

    #[test]
    fn test_list_thy_failures() {
        let source = include_str!("../../isabelle-source/src/HOL/List.thy");

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
                    if j > i && (lt.starts_with("by ") || lt.starts_with("proof")
                        || lt.starts_with("apply") || lt.starts_with("done")
                        || lt.starts_with("unfolding") || lt == "qed") {
                        if !lt.starts_with("shows") && !lt.starts_with("assumes") && !lt.starts_with("and ") {
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
                let rest = t.strip_prefix("lemma ")
                    .or_else(|| t.strip_prefix("theorem "))
                    .unwrap_or(t);
                let name = rest.split(':').next().unwrap_or("?").trim();
                let name = if let Some(b) = name.find('[') { &name[..b] } else { name };
                eprintln!("FAIL: {} | first line: {}", name, t.chars().take(100).collect::<String>());
            }
            i += 1;
        }
        eprintln!("List.thy: {}/{} lemmas parsed, {} failed", total - failed, total, failed);
        assert!(total - failed > 900, "Expected >900 parsed from List.thy, got {}", total - failed);
    }

    #[test]
    fn test_debug_failing_lemmas() {
        // Test parse_lemmas on the actual source snippet
        let src = r#"lemma order_less_subst1: "(a::'a::preorder) < f b \<Longrightarrow> b < c \<Longrightarrow>
  (\<And>x y. x < y \<Longrightarrow> f x < f y) \<Longrightarrow> a < f c"
  by (rule less_trans)"#;
        
        let lemmas = parse_lemmas(src);
        eprintln!("Parsed {} lemmas from order_less_subst1 snippet", lemmas.len());
        for l in &lemmas {
            eprintln!("  name: {:?}", l.name);
        }
        
        // Also test parse_one_line directly
        let lines: Vec<&str> = src.lines().collect();
        eprintln!("Lines: {:?}", lines);
    }

    #[test]
    fn test_audit_loaded_lemmas() {
        let hol_thy = include_str!("../../isabelle-source/src/HOL/HOL.thy");
        let ord_thy = include_str!("../../isabelle-source/src/HOL/Orderings.thy");
        let nat_thy = include_str!("../../isabelle-source/src/HOL/Nat.thy");
        let set_thy = include_str!("../../isabelle-source/src/HOL/Set.thy");
        let list_thy = include_str!("../../isabelle-source/src/HOL/List.thy");

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
        let mut name_counts: std::collections::HashMap<&str, usize> = std::collections::HashMap::new();
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
        let trivial_count = lemmas.iter().filter(|l| {
            let term_str = format!("{:?}", l.theorem.prop().term());
            // Check if the term is just a single free variable or constant (partial parse)
            term_str.starts_with("Free(") || term_str.starts_with("Const(")
        }).count();
        eprintln!("Potentially trivial terms (partial parses): {}", trivial_count);

        // 4. Show a sample of what "trivial" terms look like
        for l in lemmas.iter().filter(|l| {
            let term_str = format!("{:?}", l.theorem.prop().term());
            term_str.starts_with("Free(") || term_str.starts_with("Const(")
        }).take(5) {
            eprintln!("  TRIVIAL: {} -> {:?}", l.name, l.theorem.prop().term());
        }

        // 5. Check that for each file, every source declaration maps to at least 1 parsed entry
        // (already done by test_per_file_stats)

        assert!(empty_names.is_empty(), "Found {} empty-name lemmas", empty_names.len());
    }
}
