//! LSP Router — dispatch table for request/notification handlers.
//!
//! ## Design
//!
//! Instead of a monolithic match-branch, the Router uses `HashMap`s
//! mapping LSP method names to handler functions. Each handler is
//! independently defined in `lsp/handlers/`.
//!
//! ```text
//! IncomingMessage
//!   → Router.route_request(method, req)  → handler(ctx, req)
//!   → Router.route_notification(method, notif) → handler(ctx, notif)
//! ```

use std::collections::HashMap;

use super::handlers::{self, HandlerContext, NotificationHandler, RequestHandler};
use crate::server::lsp_types::*;

// =========================================================================
// Router
// =========================================================================

pub struct Router {
    /// Request handlers keyed by LSP method name.
    requests: HashMap<&'static str, RequestHandler>,
    /// Notification handlers keyed by LSP method name.
    notifications: HashMap<&'static str, NotificationHandler>,
}

impl Router {
    /// Create a new Router with all handlers registered.
    pub fn new() -> Self {
        let mut requests: HashMap<&'static str, RequestHandler> = HashMap::new();
        let mut notifications: HashMap<&'static str, NotificationHandler> = HashMap::new();

        // ── Request handlers ──
        requests.insert(requests::INITIALIZE, handlers::lifecycle::handle_initialize);
        requests.insert(requests::SHUTDOWN, handlers::lifecycle::handle_shutdown);
        requests.insert(requests::TEXT_DOCUMENT_HOVER, handlers::hover::handle_hover);
        requests.insert(requests::TEXT_DOCUMENT_COMPLETION, handlers::completion::handle_completion);
        requests.insert(requests::TEXT_DOCUMENT_DEFINITION, handlers::definition::handle_definition);
        requests.insert(requests::PROOF_GOALS, handlers::proof_goals::handle_proof_goals);

        // ── Notification handlers ──
        notifications.insert(notifications::INITIALIZED, handlers::lifecycle::handle_initialized);
        notifications.insert(notifications::EXIT, handlers::lifecycle::handle_exit);
        notifications.insert(notifications::TEXT_DOCUMENT_DID_OPEN, handlers::document::handle_did_open);
        notifications.insert(notifications::TEXT_DOCUMENT_DID_CHANGE, handlers::document::handle_did_change);
        notifications.insert(notifications::TEXT_DOCUMENT_DID_CLOSE, handlers::document::handle_did_close);
        notifications.insert(notifications::TEXT_DOCUMENT_DID_SAVE, handlers::document::handle_did_save);

        Router { requests, notifications }
    }

    /// Dispatch a JSON-RPC request to the registered handler.
    ///
    /// Returns `true` if a handler was found, `false` if no handler
    /// is registered for this method (caller should send MethodNotFound).
    pub fn route_request(&self, method: &str, ctx: &HandlerContext, req: JsonRpcRequest) -> bool {
        match self.requests.get(method) {
            Some(handler) => {
                handler(ctx, req);
                true
            }
            None => false,
        }
    }

    /// Dispatch a JSON-RPC notification to the registered handler.
    ///
    /// Returns `true` if a handler was found. Unknown notifications
    /// are silently ignored per LSP spec.
    pub fn route_notification(&self, method: &str, ctx: &mut HandlerContext, notif: JsonRpcNotification) -> bool {
        match self.notifications.get(method) {
            Some(handler) => {
                handler(ctx, notif);
                true
            }
            None => false,
        }
    }
}

impl Default for Router {
    fn default() -> Self {
        Self::new()
    }
}

// =========================================================================
// Tests
// =========================================================================

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
    fn test_router_has_hover_handler() {
        let router = Router::new();
        assert!(router.requests.contains_key(requests::TEXT_DOCUMENT_HOVER));
    }

    #[test]
    fn test_router_has_did_open_handler() {
        let router = Router::new();
        assert!(router.notifications.contains_key(notifications::TEXT_DOCUMENT_DID_OPEN));
    }

    #[test]
    fn test_router_method_not_found() {
        let router = Router::new();
        let ctx = make_ctx();
        let req = JsonRpcRequest {
            jsonrpc: "2.0".into(),
            id: RequestId::Number(1),
            method: "nonexistent/method".into(),
            params: serde_json::Value::Null,
        };
        let found = router.route_request("nonexistent/method", &ctx, req);
        assert!(!found);
    }

    #[test]
    fn test_router_unknown_notification_ignored() {
        let router = Router::new();
        let mut ctx = make_ctx();
        let notif = JsonRpcNotification {
            jsonrpc: "2.0".into(),
            method: "unknown/notification".into(),
            params: serde_json::Value::Null,
        };
        let found = router.route_notification("unknown/notification", &mut ctx, notif);
        assert!(!found);
    }
}
