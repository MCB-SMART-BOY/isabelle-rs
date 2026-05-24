//! LSP request/notification handlers.
//!
//! Each handler is a standalone function that takes a `HandlerContext`
//! and the relevant LSP message type. Handlers are registered with
//! the `Router` and dispatched by method name.
//!
//! ## Architecture
//!
//! ```text
//! Router
//!   ├── "initialize"              → lifecycle::handle_initialize
//!   ├── "shutdown"               → lifecycle::handle_shutdown
//!   ├── "textDocument/hover"     → hover::handle_hover
//!   ├── "textDocument/completion"→ completion::handle_completion
//!   ├── "textDocument/definition"→ definition::handle_definition
//!   ├── "isabelle/proofGoals"    → proof_goals::handle_proof_goals
//!   ├── "textDocument/didOpen"   → document::handle_did_open
//!   ├── "textDocument/didChange" → document::handle_did_change
//!   ├── "textDocument/didClose"  → document::handle_did_close
//!   └── "textDocument/didSave"   → document::handle_did_save
//! ```

use std::sync::Arc;
use std::sync::mpsc;

use crate::fleche::engine::Fleche;
use crate::server::lsp_types::*;
use crate::server::transport::OutgoingMessage;

// =========================================================================
// Handler context
// =========================================================================

/// Shared state passed to all handlers.
pub struct HandlerContext {
    /// Channel to send outgoing messages back to client.
    tx: mpsc::Sender<OutgoingMessage>,
    /// Document checking engine (delegates to Session + FileWorkers).
    pub fleche: Arc<Fleche>,
    /// Server lifecycle state.
    pub lifecycle: ServerLifecycle,
}

impl HandlerContext {
    pub fn new(tx: mpsc::Sender<OutgoingMessage>, fleche: Arc<Fleche>) -> Self {
        HandlerContext {
            tx,
            fleche,
            lifecycle: ServerLifecycle::Created,
        }
    }

    /// Send a successful JSON-RPC response.
    pub fn send_result(&self, id: RequestId, result: serde_json::Value) {
        let _ = self.tx.send(OutgoingMessage::Response(JsonRpcResponse {
            jsonrpc: "2.0".into(),
            id,
            result: Some(result),
            error: None,
        }));
    }

    /// Send an error JSON-RPC response.
    pub fn send_error(&self, id: RequestId, error: JsonRpcError) {
        let _ = self.tx.send(OutgoingMessage::Response(JsonRpcResponse {
            jsonrpc: "2.0".into(),
            id,
            result: None,
            error: Some(error),
        }));
    }

    /// Publish diagnostics for a file URI.
    pub fn publish_diagnostics(&self, uri: &str, diags: &[Diagnostic]) {
        let params = serde_json::json!({
            "uri": uri,
            "diagnostics": diags,
        });
        let _ = self
            .tx
            .send(OutgoingMessage::Notification(JsonRpcNotification {
                jsonrpc: "2.0".into(),
                method: notifications::PUBLISH_DIAGNOSTICS.into(),
                params,
            }));
    }
}

// =========================================================================
// Handler type aliases
// =========================================================================

/// A request handler function.
///
/// Takes context + the JSON-RPC request. The handler is responsible
/// for sending its own response/error via `ctx.send_result` / `ctx.send_error`.
pub type RequestHandler = fn(ctx: &HandlerContext, req: JsonRpcRequest);

/// A notification handler function.
///
/// Takes mutable context (may update lifecycle) + the notification.
pub type NotificationHandler = fn(ctx: &mut HandlerContext, notif: JsonRpcNotification);

// =========================================================================
// Sub-modules
// =========================================================================

pub mod completion;
pub mod definition;
pub mod document;
pub mod hover;
pub mod lifecycle;
pub mod proof_goals;
