//! Handler for textDocument/definition.

use super::HandlerContext;
use crate::server::lsp_types::*;

pub fn handle_definition(ctx: &HandlerContext, req: JsonRpcRequest) {
    let _params: TextDocumentPositionParams = match serde_json::from_value(req.params) {
        Ok(p) => p,
        Err(e) => {
            ctx.send_error(req.id, JsonRpcError::new(-32602, format!("{e}")));
            return;
        }
    };

    // TODO: implement go-to-definition
    ctx.send_result(req.id, serde_json::Value::Null);
}
