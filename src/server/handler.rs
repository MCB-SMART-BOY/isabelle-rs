//! LSP request handler — dispatches LSP requests to the Flèche engine.
//!
//! This is the bridge between the JSON-RPC transport layer and the document
//! checking engine. It implements the full LSP lifecycle.

use std::sync::Arc;
use tokio::sync::mpsc;

use super::lsp_types::*;
use super::transport::{IncomingMessage, OutgoingMessage, Transport};
use crate::fleche::engine::Fleche;

/// The Isabelle LSP server.
///
/// Coordinates:
/// - LSP transport (JSON-RPC over stdio)
/// - Flèche document engine (incremental checking)
/// - Lifecycle state
pub struct IsabelleServer {
    transport: Option<Transport>,
    fleche: Arc<Fleche>,
    lifecycle: ServerLifecycle,
}

impl IsabelleServer {
    /// Create a new Isabelle LSP server.
    pub fn new(fleche: Arc<Fleche>) -> Self {
        IsabelleServer {
            transport: Some(Transport::new()),
            fleche,
            lifecycle: ServerLifecycle::Created,
        }
    }

    /// Run the main event loop.
    ///
    /// Blocks forever, processing incoming LSP messages.
    pub fn run(&mut self) {
        tracing::info!(" LSP server started, waiting for client...");

        while self.lifecycle != ServerLifecycle::Shutdown {
            let transport = self.transport.expect("transport required for sync mode");
            match transport.recv() {
                Some(msg) => self.handle_message(msg),
                None => {
                    tracing::info!(" Transport closed, shutting down.");
                    break;
                }
            }
        }

        tracing::info!(" Server stopped.");
    }

    /// Create an async server instance.
    pub fn new_async(fleche: Arc<Fleche>, _tx: mpsc::Sender<OutgoingMessage>) -> Self {
        IsabelleServer { transport: None, fleche, lifecycle: ServerLifecycle::Created }
    }

    /// Run the async event loop.
    pub async fn run_async(&mut self, rx: &mut mpsc::Receiver<IncomingMessage>) {
        tracing::info!("LSP server (async) started");
        while self.lifecycle != ServerLifecycle::Shutdown {
            match rx.recv().await {
                Some(msg) => self.handle_message(msg),
                None => { tracing::info!("Transport closed"); break; }
            }
        }
    }

    /// Dispatch an incoming message.
    fn handle_message(&mut self, msg: IncomingMessage) {
        match msg {
            IncomingMessage::Request(req) => self.handle_request(req),
            IncomingMessage::Notification(notif) => self.handle_notification(notif),
            IncomingMessage::Response(resp) => {
                tracing::info!(" Unexpected response: {:?}", resp.id);
            }
        }
    }

    // =================================================================
    // Request handlers
    // =================================================================

    fn handle_request(&mut self, req: JsonRpcRequest) {
        if !self.lifecycle.can_handle_requests()
            && req.method != requests::INITIALIZE
            && req.method != requests::SHUTDOWN
        {
            self.send_error(
                req.id,
                JsonRpcError::new(-32002, "Server not initialized"),
            );
            return;
        }

        match req.method.as_str() {
            requests::INITIALIZE => self.handle_initialize(req),
            requests::SHUTDOWN => self.handle_shutdown(req),
            requests::TEXT_DOCUMENT_HOVER => self.handle_hover(req),
            requests::TEXT_DOCUMENT_COMPLETION => self.handle_completion(req),
            requests::TEXT_DOCUMENT_DEFINITION => self.handle_definition(req),
            requests::PROOF_GOALS => self.handle_proof_goals(req),
            _ => {
                self.send_error(req.id, JsonRpcError::method_not_found(&req.method));
            }
        }
    }

    // =================================================================
    // Notification handlers
    // =================================================================

    fn handle_notification(&mut self, notif: JsonRpcNotification) {
        match notif.method.as_str() {
            notifications::INITIALIZED => {
                tracing::info!(" Client initialized.");
            }
            notifications::TEXT_DOCUMENT_DID_OPEN => {
                self.handle_did_open(notif);
            }
            notifications::TEXT_DOCUMENT_DID_CHANGE => {
                self.handle_did_change(notif);
            }
            notifications::TEXT_DOCUMENT_DID_CLOSE => {
                self.handle_did_close(notif);
            }
            notifications::TEXT_DOCUMENT_DID_SAVE => {
                self.handle_did_save(notif);
            }
            notifications::EXIT => {
                tracing::info!(" Client requested exit.");
                self.lifecycle = ServerLifecycle::ShuttingDown;
            }
            _ => {
                // Unknown notifications are silently ignored per LSP spec
            }
        }
    }

    // =================================================================
    // Lifecycle handlers
    // =================================================================

    fn handle_initialize(&mut self, req: JsonRpcRequest) {
        let _params: InitializeParams = match serde_json::from_value(req.params.clone()) {
            Ok(p) => p,
            Err(e) => {
                self.send_error(
                    req.id,
                    JsonRpcError::new(-32602, format!("Invalid params: {e}")),
                );
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

        self.send_result(req.id, serde_json::to_value(result).unwrap());
        self.lifecycle = ServerLifecycle::Initialized;

        tracing::info!(" Initialized — ready for requests!");
    }

    fn handle_shutdown(&mut self, req: JsonRpcRequest) {
        self.lifecycle = ServerLifecycle::ShuttingDown;
        self.send_result(req.id, serde_json::Value::Null);
        self.lifecycle = ServerLifecycle::Shutdown;
        tracing::info!(" Shutdown complete.");
    }

    // =================================================================
    // Document handlers
    // =================================================================

    fn handle_did_open(&mut self, notif: JsonRpcNotification) {
        let params: DidOpenTextDocumentParams =
            match serde_json::from_value(notif.params) {
                Ok(p) => p,
                Err(e) => {
                    tracing::info!(" Bad didOpen params: {e}");
                    return;
                }
            };

        let uri = &params.text_document.uri;
        let language_id = &params.text_document.language_id;

        tracing::info!(" Opened: {uri} (lang: {language_id})");

        let diags = self.fleche.open_file(uri, &params.text_document.text);
        self.publish_diagnostics(uri, &diags);
    }

    fn handle_did_change(&mut self, notif: JsonRpcNotification) {
        let params: DidChangeTextDocumentParams =
            match serde_json::from_value(notif.params) {
                Ok(p) => p,
                Err(e) => {
                    tracing::info!(" Bad didChange params: {e}");
                    return;
                }
            };

        let uri = &params.text_document.uri;

        // Apply changes (LSP sends incremental or full changes)
        let new_text = if let Some(change) = params.content_changes.first() {
            if change.range.is_none() {
                // Full document sync
                change.text.clone()
            } else {
                // Incremental sync — for now, just use the full text
                // (A real implementation would apply patches)
                change.text.clone()
            }
        } else {
            return;
        };

        let diags = self.fleche.update_file(uri, &new_text);
        self.publish_diagnostics(uri, &diags);
    }

    fn handle_did_close(&mut self, notif: JsonRpcNotification) {
        let params: DidCloseTextDocumentParams =
            match serde_json::from_value(notif.params) {
                Ok(p) => p,
                Err(e) => {
                    tracing::info!(" Bad didClose params: {e}");
                    return;
                }
            };

        tracing::info!(" Closed: {}", params.text_document.uri);
        self.fleche.close_file(&params.text_document.uri);
    }

    fn handle_did_save(&mut self, _notif: JsonRpcNotification) {
        // Re-check on save
        // Could trigger full compilation to .thy artifact
    }

    // =================================================================
    // Feature handlers
    // =================================================================

    fn handle_hover(&mut self, req: JsonRpcRequest) {
        let params: TextDocumentPositionParams =
            match serde_json::from_value(req.params) {
                Ok(p) => p,
                Err(e) => {
                    self.send_error(req.id, JsonRpcError::new(-32602, format!("{e}")));
                    return;
                }
            };

        let hover_text = self.fleche.get_hover(
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
                self.send_result(req.id, serde_json::to_value(hover).unwrap());
            }
            None => {
                self.send_result(req.id, serde_json::Value::Null);
            }
        }
    }

    fn handle_completion(&mut self, req: JsonRpcRequest) {
        // For now, return empty completion list
        let result = CompletionList {
            is_incomplete: false,
            items: vec![],
        };
        self.send_result(req.id, serde_json::to_value(result).unwrap());
    }

    fn handle_definition(&mut self, req: JsonRpcRequest) {
        // TODO: implement go-to-definition
        self.send_result(req.id, serde_json::Value::Null);
    }

    fn handle_proof_goals(&mut self, req: JsonRpcRequest) {
        let params: TextDocumentPositionParams =
            match serde_json::from_value(req.params) {
                Ok(p) => p,
                Err(e) => {
                    self.send_error(req.id, JsonRpcError::new(-32602, format!("{e}")));
                    return;
                }
            };

        let proof_state = self.fleche.get_proof_state(
            &params.text_document.uri,
            params.position.line,
        );

        match proof_state {
            Some(ps) => {
                self.send_result(req.id, serde_json::to_value(ps).unwrap());
            }
            None => {
                self.send_result(req.id, serde_json::Value::Null);
            }
        }
    }

    // =================================================================
    // Helpers
    // =================================================================

    /// Send a successful response.
    fn send_result(&self, id: RequestId, result: serde_json::Value) {
        self.transport.unwrap().send(OutgoingMessage::Response(JsonRpcResponse {
            jsonrpc: "2.0".into(),
            id,
            result: Some(result),
            error: None,
        }));
    }

    /// Send an error response.
    fn send_error(&self, id: RequestId, error: JsonRpcError) {
        self.transport.unwrap().send(OutgoingMessage::Response(JsonRpcResponse {
            jsonrpc: "2.0".into(),
            id,
            result: None,
            error: Some(error),
        }));
    }

    /// Publish diagnostics for a file.
    fn publish_diagnostics(&self, uri: &str, diags: &[Diagnostic]) {
        let params = serde_json::json!({
            "uri": uri,
            "diagnostics": diags,
        });

        self.transport.unwrap().send(OutgoingMessage::Notification(JsonRpcNotification {
            jsonrpc: "2.0".into(),
            method: notifications::PUBLISH_DIAGNOSTICS.into(),
            params,
        }));

        eprintln!(
            "[isabelle-rs] Published {} diagnostics for {}",
            diags.len(),
            uri
        );
    }
}
