//! Handler for textDocument/hover.
//! Shows theorem statement and type information.

use super::HandlerContext;
use crate::{core::thm::Thm, hol::hol_loader::HolTheoremDb, server::lsp_types::*};

pub fn handle_hover(ctx: &HandlerContext, req: JsonRpcRequest) {
    let params: TextDocumentPositionParams = match serde_json::from_value(req.params) {
        Ok(p) => p,
        Err(e) => {
            ctx.send_error(req.id, JsonRpcError::new(-32602, format!("{e}")));
            return;
        },
    };

    // Try fleche first (document-aware hover)
    let hover_text = ctx.fleche.get_hover(
        &params.text_document.uri,
        params.position.line,
        params.position.character,
    );

    // Fall back to theorem DB lookup
    let hover_text = hover_text.or_else(|| {
        let db = HolTheoremDb::global();
        // Get the current word at position from the document
        let doc = ctx.get_document_text(&params.text_document.uri)?;
        let line = doc.lines().nth(params.position.line as usize)?;
        let word = extract_word_at(line, params.position.character as usize);

        // Try to find the theorem by name
        if let Some(word) = word
            && let Some(thm) = db.by_name.get(&word)
        {
            return Some(render_db_hover(&word, thm));
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
            ctx.send_result(req.id, serde_json::to_value(hover).expect("Serialization failed"));
        },
        None => {
            ctx.send_result(req.id, serde_json::Value::Null);
        },
    }
}

/// The HOL database stores legacy search facts, not new-kernel trusted tokens.
/// A strict-shaped legacy theorem is still only transitional, even if closed.
pub(super) fn legacy_fact_status(thm: &Thm) -> &'static str {
    if thm.is_admitted_theorem() {
        "legacy admitted/oracle"
    } else if !thm.is_closed() {
        "legacy open (hypotheses or unresolved constraints)"
    } else if thm.is_strict_closed_proved() {
        "legacy transitional strict-closed (not kernel-trusted)"
    } else {
        "legacy compat/unchecked (not kernel-trusted)"
    }
}

fn render_db_hover(name: &str, thm: &Thm) -> String {
    format!(
        "**{}** — search fact: {}\n\n```\n{:?}\n```",
        name,
        legacy_fact_status(thm),
        thm.prop().term()
    )
}

/// Extract the word at a character position in a line.
fn extract_word_at(line: &str, char_pos: usize) -> Option<String> {
    if char_pos >= line.len() {
        return None;
    }
    let chars: Vec<char> = line.chars().collect();
    if char_pos >= chars.len() {
        return None;
    }

    // Find word boundaries
    let mut start = char_pos;
    while start > 0 && chars[start - 1].is_alphanumeric() {
        start -= 1;
    }
    let mut end = char_pos;
    while end < chars.len()
        && (chars[end].is_alphanumeric() || chars[end] == '_' || chars[end] == '.')
    {
        end += 1;
    }

    if start < end { Some(chars[start..end].iter().collect()) } else { None }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{
        term::Term,
        thm::{CTerm, ThmKernel},
        types::{Typ, TypeEnv},
    };

    #[test]
    fn render_db_hover_admitted_and_open_facts_discloses_burdens() {
        let statement = CTerm::certify(Term::const_("P", Typ::base("prop")));
        let admitted = ThmKernel::admit(statement.clone(), "unproved");
        let open = ThmKernel::assume_compat(statement);
        let admitted_text = render_db_hover("admitted_P", &admitted);
        let open_text = render_db_hover("open_P", &open);

        assert!(admitted_text.contains("**admitted_P** — search fact: legacy admitted/oracle"));
        assert!(open_text.contains("**open_P** — search fact: legacy open"));
        assert!(open_text.contains("P"));
        assert!(!admitted_text.contains("KernelTrustedClosed"));
    }

    #[test]
    fn render_db_hover_closed_legacy_facts_never_claim_kernel_trust() {
        let typ = Typ::base("prop");
        let term = Term::const_("P", typ.clone());
        let compat = ThmKernel::reflexive_compat(CTerm::certify(term.clone()));
        let mut env = TypeEnv::new();
        env.declare_const("P", typ);
        let checked = CTerm::certify_checked(term, &env).unwrap();
        let transitional = ThmKernel::reflexive(checked).unwrap();

        assert!(render_db_hover("compat_P", &compat).contains("legacy compat/unchecked"));
        assert!(
            render_db_hover("transitional_P", &transitional)
                .contains("legacy transitional strict-closed (not kernel-trusted)")
        );
    }
}
