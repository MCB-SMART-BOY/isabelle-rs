//! Lifecycle handlers: initialize and shutdown.

use super::HandlerContext;
use crate::server::lsp_types::*;

/// Handle the `initialize` request.
pub fn handle_initialize(ctx: &HandlerContext, req: JsonRpcRequest) {
    let _params: InitializeParams = match serde_json::from_value(req.params.clone()) {
        Ok(p) => p,
        Err(e) => {
            ctx.send_error(req.id, JsonRpcError::new(-32602, format!("Invalid params: {e}")));
            return;
        }
    };

    let result = InitializeResult {
        capabilities: ServerCapabilities {
            text_document_sync: TextDocumentSyncKind::Full,
            hover_provider: true,
            completion_provider: Some(CompletionOptions {
                trigger_characters: vec![".".into(), " ".into()],
            }),
            definition_provider: true,
            references_provider: false,
            document_symbol_provider: true,
            proof_goals_provider: true,
        },
        server_info: ServerInfo {
            name: "isabelle-rs".into(),
            version: env!("CARGO_PKG_VERSION").to_string(),
        },
    };

    ctx.send_result(req.id, serde_json::to_value(result).expect("Serialization failed"));
}

/// Handle the `shutdown` request.
pub fn handle_shutdown(ctx: &HandlerContext, req: JsonRpcRequest) {
    ctx.send_result(req.id, serde_json::Value::Null);
}

/// Handle the `initialized` notification.
pub fn handle_initialized(_ctx: &mut HandlerContext, _notif: JsonRpcNotification) {
    tracing::info!("Client initialized.");
}

/// Handle the `exit` notification.
pub fn handle_exit(ctx: &mut HandlerContext, _notif: JsonRpcNotification) {
    tracing::info!("Client requested exit.");
    ctx.lifecycle = ServerLifecycle::ShuttingDown;
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use crate::fleche::engine::{Fleche, RealExecutor};
    use crate::server::transport::OutgoingMessage;
    use std::sync::mpsc;

    fn make_ctx() -> HandlerContext {
        let fleche = Arc::new(Fleche::new(Arc::new(RealExecutor::new())));
        let (tx, _rx) = mpsc::channel::<OutgoingMessage>();
        HandlerContext::new(tx, fleche)
    }

    #[test]
    fn test_initialize_response() {
        let ctx = make_ctx();
        let req = JsonRpcRequest {
            jsonrpc: "2.0".into(),
            id: RequestId::Number(1),
            method: "initialize".into(),
            params: serde_json::json!({
                "processId": null,
                "capabilities": {}
            }),
        };
        // Should not panic
        handle_initialize(&ctx, req);
    }
}
