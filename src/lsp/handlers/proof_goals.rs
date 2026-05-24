//! Handler for isabelle/proofGoals.

use super::HandlerContext;
use crate::server::lsp_types::*;

pub fn handle_proof_goals(ctx: &HandlerContext, req: JsonRpcRequest) {
    let params: TextDocumentPositionParams = match serde_json::from_value(req.params) {
        Ok(p) => p,
        Err(e) => {
            ctx.send_error(req.id, JsonRpcError::new(-32602, format!("{e}")));
            return;
        }
    };

    let proof_state = ctx
        .fleche
        .get_proof_state(&params.text_document.uri, params.position.line);

    match proof_state {
        Some(ps) => {
            ctx.send_result(
                req.id,
                serde_json::to_value(ps).expect("Serialization failed"),
            );
        }
        None => {
            ctx.send_result(req.id, serde_json::Value::Null);
        }
    }
}
