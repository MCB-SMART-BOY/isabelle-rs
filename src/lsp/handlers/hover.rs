//! Handler for textDocument/hover.
//! Shows theorem statement and type information.

use super::HandlerContext;
use crate::hol::hol_loader::HolTheoremDb;
use crate::server::lsp_types::*;

pub fn handle_hover(ctx: &HandlerContext, req: JsonRpcRequest) {
    let params: TextDocumentPositionParams = match serde_json::from_value(req.params) {
        Ok(p) => p,
        Err(e) => {
            ctx.send_error(req.id, JsonRpcError::new(-32602, format!("{e}")));
            return;
        }
    };

    // Try fleche first (document-aware hover)
    let hover_text = ctx.fleche.get_hover(
        &params.text_document.uri,
        params.position.line,
        params.position.character,
    );

    // Fall back to theorem DB lookup
    let hover_text = hover_text.or_else(|| {
        let db = HolTheoremDb::get();
        // Get the current word at position from the document
        let doc = ctx.get_document_text(&params.text_document.uri)?;
        let line = doc.lines().nth(params.position.line as usize)?;
        let word = extract_word_at(line, params.position.character as usize);

        // Try to find the theorem by name
        if let Some(word) = word {
            if let Some(thm) = db.by_name.get(&word) {
                let prop = format!("{:?}", thm.prop().term());
                let nprems = thm.nprems();
                let info = if nprems == 0 {
                    format!("**{}** (unconditional)\n\n```\n{}\n```", word, prop)
                } else {
                    format!("**{}** ({} premises)\n\n```\n{}\n```", word, nprems, prop)
                };
                return Some(info);
            }
        }
        None
    });

    match hover_text {
        Some(text) => {
            let hover = Hover {
                contents: HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: text,
                }),
                range: None,
            };
            ctx.send_result(
                req.id,
                serde_json::to_value(hover).expect("Serialization failed"),
            );
        }
        None => {
            ctx.send_result(req.id, serde_json::Value::Null);
        }
    }
}

/// Extract the word at a character position in a line.
fn extract_word_at(line: &str, char_pos: usize) -> Option<String> {
    if char_pos >= line.len() { return None; }
    let chars: Vec<char> = line.chars().collect();
    if char_pos >= chars.len() { return None; }

    // Find word boundaries
    let mut start = char_pos;
    while start > 0 && chars[start - 1].is_alphanumeric() {
        start -= 1;
    }
    let mut end = char_pos;
    while end < chars.len() && (chars[end].is_alphanumeric() || chars[end] == '_' || chars[end] == '.') {
        end += 1;
    }

    if start < end {
        Some(chars[start..end].iter().collect())
    } else {
        None
    }
}
