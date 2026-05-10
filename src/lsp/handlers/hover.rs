//! Handler for textDocument/hover.

use super::HandlerContext;
use crate::server::lsp_types::*;

pub fn handle_hover(ctx: &HandlerContext, req: JsonRpcRequest) {
    let params: TextDocumentPositionParams = match serde_json::from_value(req.params) {
        Ok(p) => p,
        Err(e) => {
            ctx.send_error(req.id, JsonRpcError::new(-32602, format!("{e}")));
            return;
        }
    };

    let hover_text = ctx.fleche.get_hover(
        &params.text_document.uri,
        params.position.line,
        params.position.character,
    );

    match hover_text {
        Some(text) => {
            let hover = Hover {
                contents: HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::PlainText,
                    value: text,
                }),
                range: None,
            };
            ctx.send_result(req.id, serde_json::to_value(hover).expect("Serialization failed"));
        }
        None => {
            ctx.send_result(req.id, serde_json::Value::Null);
        }
    }
}
