//! Document synchronization handlers.

use super::HandlerContext;
use crate::server::lsp_types::*;

/// Handle `textDocument/didOpen` notification.
pub fn handle_did_open(ctx: &mut HandlerContext, notif: JsonRpcNotification) {
    let params: DidOpenTextDocumentParams = match serde_json::from_value(notif.params) {
        Ok(p) => p,
        Err(e) => {
            tracing::info!("Bad didOpen params: {e}");
            return;
        },
    };

    let uri = &params.text_document.uri;
    tracing::info!("Opened document");

    let diags = ctx.fleche.open_file(uri, &params.text_document.text);
    ctx.publish_diagnostics(uri, &diags);
}

/// Handle `textDocument/didChange` notification.
pub fn handle_did_change(ctx: &mut HandlerContext, notif: JsonRpcNotification) {
    let params: DidChangeTextDocumentParams = match serde_json::from_value(notif.params) {
        Ok(p) => p,
        Err(e) => {
            tracing::info!("Bad didChange params: {e}");
            return;
        },
    };

    let uri = &params.text_document.uri;

    let Some(new_text) = extract_latest_full_content(&params.content_changes) else {
        tracing::warn!("didChange requires a complete full-sync snapshot");
        return;
    };
    let diags = ctx.fleche.update_file(uri, new_text);
    ctx.publish_diagnostics(uri, &diags);
}

/// Handle `textDocument/didClose` notification.
pub fn handle_did_close(ctx: &mut HandlerContext, notif: JsonRpcNotification) {
    let params: DidCloseTextDocumentParams = match serde_json::from_value(notif.params) {
        Ok(p) => p,
        Err(e) => {
            tracing::info!("Bad didClose params: {e}");
            return;
        },
    };

    tracing::info!("Closed document");
    ctx.fleche.close_file(&params.text_document.uri);
}

/// Handle `textDocument/didSave` notification.
pub fn handle_did_save(_ctx: &mut HandlerContext, _notif: JsonRpcNotification) {
    // Re-check on save. Future: trigger compilation to .thy artifact.
}
