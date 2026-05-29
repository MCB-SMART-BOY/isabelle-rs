//! Handler for textDocument/definition — go-to-definition.
//!
//! Resolves identifiers at cursor position to their source definitions
//! using the HolTheoremDb definition index.

use super::HandlerContext;
use crate::server::lsp_types::*;

/// Find the word at a given position in text.
/// Returns (word, start_offset, end_offset).
fn word_at_position(text: &str, line: u32, character: u32) -> Option<(String, usize, usize)> {
    let target_line = text.lines().nth(line as usize)?;
    let char_idx = character as usize;

    // Find word boundaries
    let bytes = target_line.as_bytes();
    let end = char_idx.min(bytes.len());

    // Scan backward to find word start
    let mut start = end;
    while start > 0 && is_ident_char(bytes[start - 1]) {
        start -= 1;
    }
    // Scan forward to find word end
    let mut end = end;
    while end < bytes.len() && is_ident_char(bytes[end]) {
        end += 1;
    }

    let word = &target_line[start..end];
    if word.is_empty() {
        return None;
    }
    Some((word.to_string(), start, end))
}

/// Check if a byte is a valid identifier character.
fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'.' || b == b'\''
}

/// Convert a file path to a file:// URI.
fn path_to_uri(path: &str) -> String {
    if path.starts_with("file://") {
        return path.to_string();
    }
    // For relative paths, make them absolute
    let abs = if path.starts_with('/') {
        path.to_string()
    } else {
        format!("/{}", path)
    };
    format!("file://{}", abs)
}

pub fn handle_definition(ctx: &HandlerContext, req: JsonRpcRequest) {
    let params: TextDocumentPositionParams = match serde_json::from_value(req.params) {
        Ok(p) => p,
        Err(e) => {
            ctx.send_error(req.id, JsonRpcError::new(-32602, format!("{e}")));
            return;
        }
    };

    let uri = &params.text_document.uri;

    // Get the document text
    let text = match ctx.get_document_text(uri) {
        Some(t) => t,
        None => {
            // Try to load from file system
            let file_path = uri
                .strip_prefix("file://")
                .unwrap_or(uri);
            match std::fs::read_to_string(file_path) {
                Ok(t) => t,
                Err(e) => {
                    ctx.send_error(
                        req.id,
                        JsonRpcError::new(
                            -32800,
                            format!("Cannot read document: {e}"),
                        ),
                    );
                    return;
                }
            }
        }
    };

    // Find the word at cursor position
    let (word, _col_start, _col_end) = match word_at_position(
        &text,
        params.position.line,
        params.position.character,
    ) {
        Some(w) => w,
        None => {
            ctx.send_result(req.id, serde_json::Value::Null);
            return;
        }
    };

    // Look up in the definition index
    match crate::hol::hol_loader::HolTheoremDb::get_definition_location(&word) {
        Some(loc) => {
            let def_uri = if loc.file == "<unknown>" {
                // For unknown files, try to resolve from the current URI's directory
                uri.clone()
            } else {
                path_to_uri(&loc.file)
            };

            let location = Location {
                uri: def_uri,
                range: Range {
                    start: Position {
                        line: (loc.line as u32).saturating_sub(1), // 0-based
                        character: 0,
                    },
                    end: Position {
                        line: (loc.line as u32).saturating_sub(1),
                        character: 0,
                    },
                },
            };

            let result = match serde_json::to_value(&location) {
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
        None => {
            // Not found — return null
            ctx.send_result(req.id, serde_json::Value::Null);
        }
    }
}
