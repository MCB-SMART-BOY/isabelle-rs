//! Handler for textDocument/documentSymbol — document outline.
//!
//! Returns the hierarchical structure of theory files: theories, lemmas,
//! theorems, definitions, proofs, etc.

use super::HandlerContext;
use crate::server::lsp_types::*;

/// Parse a theory document and extract its symbol hierarchy.
pub fn handle_document_symbol(ctx: &HandlerContext, req: JsonRpcRequest) {
    let params: DocumentSymbolParams = match serde_json::from_value(req.params) {
        Ok(p) => p,
        Err(e) => {
            ctx.send_error(req.id, JsonRpcError::new(-32602, format!("{e}")));
            return;
        }
    };

    let uri = &params.text_document.uri;

    // Get document text
    let text = match ctx.get_document_text(uri) {
        Some(t) => t,
        None => {
            ctx.send_result(req.id, serde_json::Value::Null);
            return;
        }
    };

    // Parse the document into symbols
    let symbols = parse_document_symbols(&text);

    let result = match serde_json::to_value(&symbols) {
        Ok(v) => v,
        Err(e) => {
            ctx.send_error(
                req.id,
                JsonRpcError::internal_error(format!("serialization: {e}")),
            );
            return;
        }
    };

    ctx.send_result(req.id, result);
}

/// Extract symbol hierarchy from theory source text.
fn parse_document_symbols(source: &str) -> Vec<DocumentSymbol> {
    parse_document_symbols_inner(source)
}

/// Public alias for use by the server handler.
pub fn parse_document_symbols_for_server(source: &str) -> Vec<DocumentSymbol> {
    parse_document_symbols_inner(source)
}

/// Core implementation.
fn parse_document_symbols_inner(source: &str) -> Vec<DocumentSymbol> {
    let mut symbols = Vec::new();
    let lines: Vec<&str> = source.lines().collect();

    let mut current_theory: Option<DocumentSymbol> = None;
    let mut i = 0;

    while i < lines.len() {
        let t = lines[i].trim();
        let line = i as u32;

        // Detect theory header
        if t.starts_with("theory ") && !t.contains("begin") {
            // Multi-line theory header — collect lines until "begin"
            let mut header = String::from(t);
            let start_line = line;
            i += 1;
            while i < lines.len() {
                let next = lines[i].trim();
                header.push(' ');
                header.push_str(next);
                if next.contains("begin") {
                    break;
                }
                i += 1;
            }
            let name = extract_theory_name(&header);
            current_theory = Some(DocumentSymbol {
                name: name.clone(),
                detail: Some(format!("theory {}", name)),
                kind: SymbolKind::Module,
                range: Range {
                    start: Position { line: start_line, character: 0 },
                    end: Position { line: i as u32, character: 0 },
                },
                selection_range: Range {
                    start: Position { line: start_line, character: 0 },
                    end: Position { line: start_line, character: t.len() as u32 },
                },
                children: Some(Vec::new()),
            });
            i += 1;
            continue;
        }

        // Detect lemma/theorem
        if t.starts_with("lemma ") || t.starts_with("theorem ") || t.starts_with("corollary ")
            || t.starts_with("proposition ")
        {
            let (name, end_line) = extract_lemma_name(t, &lines, i);
            let sym = DocumentSymbol {
                name: name.clone(),
                detail: Some(t.split_whitespace().next().unwrap_or("lemma").to_string()),
                kind: SymbolKind::Function,
                range: Range {
                    start: Position { line, character: 0 },
                    end: Position { line: end_line, character: 0 },
                },
                selection_range: Range {
                    start: Position { line, character: 0 },
                    end: Position { line, character: t.len() as u32 },
                },
                children: None,
            };

            if let Some(ref mut thy) = current_theory {
                thy.children.as_mut().unwrap().push(sym);
            } else {
                symbols.push(sym);
            }
            i += 1;
            continue;
        }

        // Detect definition/fun/primrec
        if t.starts_with("definition ") || t.starts_with("fun ") || t.starts_with("primrec ")
            || t.starts_with("inductive ") || t.starts_with("coinductive ")
            || t.starts_with("datatype ") || t.starts_with("record ")
        {
            let kind_word = t.split_whitespace().next().unwrap_or("def");
            let name = t.split_whitespace().nth(1).unwrap_or("?").trim_matches('"');
            let sym = DocumentSymbol {
                name: name.to_string(),
                detail: Some(kind_word.to_string()),
                kind: if kind_word == "datatype" || kind_word == "record" {
                    SymbolKind::Struct
                } else {
                    SymbolKind::Constant
                },
                range: Range {
                    start: Position { line, character: 0 },
                    end: Position { line, character: 0 },
                },
                selection_range: Range {
                    start: Position { line, character: 0 },
                    end: Position { line, character: t.len() as u32 },
                },
                children: None,
            };

            if let Some(ref mut thy) = current_theory {
                thy.children.as_mut().unwrap().push(sym);
            } else {
                symbols.push(sym);
            }
            i += 1;
            continue;
        }

        // Detect class/locale
        if t.starts_with("class ") || t.starts_with("locale ") {
            let kind_word = t.split_whitespace().next().unwrap_or("class");
            let name = t.split_whitespace().nth(1).unwrap_or("?");
            let sym = DocumentSymbol {
                name: name.to_string(),
                detail: Some(kind_word.to_string()),
                kind: SymbolKind::Class,
                range: Range {
                    start: Position { line, character: 0 },
                    end: Position { line, character: 0 },
                },
                selection_range: Range {
                    start: Position { line, character: 0 },
                    end: Position { line, character: t.len() as u32 },
                },
                children: None,
            };

            if let Some(ref mut thy) = current_theory {
                thy.children.as_mut().unwrap().push(sym);
            } else {
                symbols.push(sym);
            }
            i += 1;
            continue;
        }

        // Close theory
        if t == "end" {
            if let Some(thy) = current_theory.take() {
                symbols.push(thy);
            }
            i += 1;
            continue;
        }

        i += 1;
    }

    // Push final theory if not closed
    if let Some(thy) = current_theory {
        symbols.push(thy);
    }

    symbols
}

/// Extract the theory name from a header like "theory Foo imports Bar begin".
fn extract_theory_name(header: &str) -> String {
    let parts: Vec<&str> = header.split_whitespace().collect();
    if parts.len() >= 2 && parts[0] == "theory" {
        parts[1].to_string()
    } else {
        "Unknown".to_string()
    }
}

/// Extract the lemma/theorem name from a statement.
/// Returns (name, end_line).
fn extract_lemma_name(first_line: &str, lines: &[&str], start: usize) -> (String, u32) {
    // Try to extract name after the colon: "lemma foo:"
    let clean = first_line.trim_start_matches(|c: char| c.is_whitespace());
    let parts: Vec<&str> = clean.splitn(2, ':').collect();
    if parts.len() >= 2 {
        let name_part = parts[0];
        // Extract the name after the keyword
        let words: Vec<&str> = name_part.split_whitespace().collect();
        if words.len() >= 2 {
            let name = words[1].to_string();
            // Find the end of the statement (where proof or qed is)
            let mut end_line = start as u32;
            for j in start..lines.len().min(start + 20) {
                let l = lines[j].trim();
                if l == "qed" || l == "done" || l.starts_with("by ") {
                    end_line = j as u32;
                    break;
                }
            }
            return (name, end_line);
        }
    }
    // Fallback: use the first word after keyword
    let words: Vec<&str> = clean.split_whitespace().collect();
    if words.len() >= 2 {
        (words[1].to_string(), start as u32)
    } else {
        ("?".to_string(), start as u32)
    }
}
