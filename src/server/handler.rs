//! LSP request handler — dispatches LSP requests to the Flèche engine.
//!
//! This is the bridge between the JSON-RPC transport layer and the document
//! checking engine. It implements the full LSP lifecycle.

use std::{
    collections::HashMap,
    io,
    path::PathBuf,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

use super::{
    check_scheduler::{CheckScheduler, DefinitionQuery, ScheduleError},
    lsp_types::*,
    transport::{IncomingMessage, OutgoingMessage, Transport, TransportError},
};
use crate::fleche::engine::{CheckJob, Fleche};

const MAX_OPEN_DOCUMENTS: usize = 64;
const MAX_OPEN_DOCUMENT_BYTES: usize = 16 * 1024 * 1024;
const MAX_SINGLE_DOCUMENT_BYTES: usize = 1024 * 1024;
const MAX_OPEN_WORKSPACE_SNAPSHOTS: usize = 8192;
const MAX_SYMBOL_LINES: usize = 8192;
const MAX_URI_BYTES: usize = 4 * 1024;
const CANCEL_REQUEST: &str = "$/cancelRequest";
const REQUEST_CANCELLED: i32 = -32800;

#[derive(Debug, Clone)]
struct OpenDocument {
    version: i32,
    bytes: usize,
    revision: Arc<()>,
}

struct PendingDefinition {
    uri: String,
    revision: Arc<()>,
    cancellation: Arc<AtomicBool>,
}

#[derive(Debug, thiserror::Error)]
enum AdmissionError {
    #[error("the open-document limit has been reached")]
    TooManyDocuments,
    #[error("document exceeds the per-file memory limit")]
    DocumentTooLarge,
    #[error("documents exceed the shared memory limit")]
    WorkspaceTooLarge,
    #[error("document URI exceeds the accepted length")]
    UriTooLong,
    #[error("document update requires a complete full-sync snapshot")]
    IncompleteChange,
}

/// The Isabelle LSP server.
///
/// Coordinates:
/// - LSP transport (JSON-RPC over stdio)
/// - Flèche document engine (incremental checking)
/// - Lifecycle state
pub struct IsabelleServer {
    transport: Option<Transport>,
    fleche: Arc<Fleche>,
    worker_executable: PathBuf,
    scheduler: Option<CheckScheduler>,
    open_documents: HashMap<String, OpenDocument>,
    pending_definitions: HashMap<RequestId, PendingDefinition>,
    lifecycle: ServerLifecycle,
    communication_error: Option<TransportError>,
}

impl IsabelleServer {
    /// Create an LSP server with a trusted binary that implements `--compute-worker`.
    pub fn new(fleche: Arc<Fleche>, worker_executable: PathBuf) -> Self {
        IsabelleServer {
            transport: Some(Transport::new()),
            fleche,
            worker_executable,
            scheduler: None,
            open_documents: HashMap::new(),
            pending_definitions: HashMap::new(),
            communication_error: None,
            lifecycle: ServerLifecycle::Created,
        }
    }

    /// Run the protocol loop while one bounded CPU worker checks documents.
    pub fn run(&mut self) -> io::Result<()> {
        tracing::info!("LSP server started, waiting for client");
        let transport =
            self.transport.as_ref().ok_or_else(|| io::Error::other("missing transport"))?;
        self.scheduler = Some(CheckScheduler::new(
            Arc::clone(&self.fleche),
            transport.incoming_sender(),
            self.worker_executable.clone(),
        )?);

        while self.lifecycle != ServerLifecycle::Shutdown {
            match self.transport.as_ref().and_then(Transport::recv) {
                Some(message) => self.handle_message(message),
                None => break,
            }
        }
        self.cancel_pending_definitions();

        // Stop CPU work before draining the transport; either cleanup must run
        // even if the other fails.
        let worker_result =
            self.scheduler.take().ok_or_else(|| io::Error::other("missing scheduler"))?.shutdown();
        let wire_result =
            self.transport.take().ok_or_else(|| io::Error::other("missing transport"))?.finish();
        if let Err(error) = &worker_result {
            tracing::error!("LSP document worker did not stop cleanly: {error}");
        }
        if let Some(error) = self.communication_error.take() {
            return Err(io::Error::other(error));
        }
        wire_result.map_err(io::Error::other)?;
        worker_result
    }

    /// Dispatch an incoming message.
    fn handle_message(&mut self, msg: IncomingMessage) {
        match msg {
            IncomingMessage::Request(req) => self.handle_request(req),
            IncomingMessage::Notification(notif) => self.handle_notification(notif),
            IncomingMessage::CheckComplete(result) => {
                let uri = result.uri().to_string();
                if let Some(diagnostics) =
                    self.fleche.commit_snapshot_limited(result, MAX_OPEN_WORKSPACE_SNAPSHOTS)
                    && let Some(document) = self.open_documents.get(&uri)
                {
                    self.publish_diagnostics(&uri, Some(document.version), &diagnostics);
                }
            },
            IncomingMessage::DefinitionComplete { id, cancellation, result } => {
                self.complete_definition(id, &cancellation, result);
            },
            IncomingMessage::WorkerFailed(reason) => {
                tracing::error!("LSP compute worker stopped: {reason}");
                self.fail_pending_definitions(&reason);
                self.lifecycle = ServerLifecycle::Shutdown;
            },
            IncomingMessage::TransportError(error) => {
                tracing::error!("LSP transport failed: {error}");
                self.communication_error.get_or_insert(error);
                self.lifecycle = ServerLifecycle::Shutdown;
            },
            IncomingMessage::Response(_) => {
                tracing::warn!("unexpected client response");
            },
        }
    }

    // =================================================================
    // Request handlers
    // =================================================================

    fn handle_request(&mut self, req: JsonRpcRequest) {
        // An outstanding ID cannot identify two requests. End the original query
        // with one error and ignore any late completion for its canceled token.
        if let Some(pending) = self.pending_definitions.remove(&req.id) {
            pending.cancellation.store(true, Ordering::Release);
            self.send_error(
                req.id,
                JsonRpcError::new(-32600, "duplicate pending request ID; lookup canceled"),
            );
            return;
        }
        if !self.lifecycle.can_handle_requests()
            && req.method != requests::INITIALIZE
            && req.method != requests::SHUTDOWN
        {
            self.send_error(req.id, JsonRpcError::new(-32002, "Server not initialized"));
            return;
        }

        match req.method.as_str() {
            requests::INITIALIZE => self.handle_initialize(req),
            requests::SHUTDOWN => self.handle_shutdown(req),
            requests::TEXT_DOCUMENT_HOVER => self.handle_hover(req),
            requests::TEXT_DOCUMENT_COMPLETION => self.handle_completion(req),
            requests::TEXT_DOCUMENT_DEFINITION => self.handle_definition(req),
            requests::TEXT_DOCUMENT_DOCUMENT_SYMBOL => self.handle_document_symbol(req),
            requests::PROOF_GOALS => self.handle_proof_goals(req),
            _ => {
                self.send_error(req.id, JsonRpcError::method_not_found(&req.method));
            },
        }
    }

    // =================================================================
    // Notification handlers
    // =================================================================

    fn handle_notification(&mut self, notif: JsonRpcNotification) {
        match notif.method.as_str() {
            CANCEL_REQUEST => self.handle_cancel_request(notif),
            notifications::INITIALIZED => {
                tracing::info!(" Client initialized.");
            },
            notifications::TEXT_DOCUMENT_DID_OPEN => {
                self.handle_did_open(notif);
            },
            notifications::TEXT_DOCUMENT_DID_CHANGE => {
                self.handle_did_change(notif);
            },
            notifications::TEXT_DOCUMENT_DID_CLOSE => {
                self.handle_did_close(notif);
            },
            notifications::TEXT_DOCUMENT_DID_SAVE => {
                self.handle_did_save(notif);
            },
            notifications::EXIT => {
                tracing::info!(" Client requested exit.");
                self.cancel_pending_definitions();
                self.lifecycle = ServerLifecycle::Shutdown;
            },
            _ => {
                // Unknown notifications are silently ignored per LSP spec
            },
        }
    }

    // =================================================================
    // Lifecycle handlers
    // =================================================================

    fn handle_cancel_request(&mut self, notif: JsonRpcNotification) {
        #[derive(serde::Deserialize)]
        struct CancelRequestParams {
            id: RequestId,
        }

        let params: CancelRequestParams = match serde_json::from_value(notif.params) {
            Ok(params) => params,
            Err(error) => {
                tracing::warn!(category = ?error.classify(), "invalid cancelRequest parameters");
                return;
            },
        };
        if let Some(pending) = self.pending_definitions.remove(&params.id) {
            pending.cancellation.store(true, Ordering::Release);
            self.send_error(
                params.id,
                JsonRpcError::new(REQUEST_CANCELLED, "definition request canceled"),
            );
        }
    }

    fn handle_initialize(&mut self, req: JsonRpcRequest) {
        let _params: InitializeParams = match serde_json::from_value(req.params.clone()) {
            Ok(p) => p,
            Err(e) => {
                self.send_error(req.id, JsonRpcError::new(-32602, format!("Invalid params: {e}")));
                return;
            },
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

        self.lifecycle = ServerLifecycle::Initialized;
        self.send_result(req.id, serde_json::to_value(result).expect("Serialization failed"));

        tracing::info!(" Initialized — ready for requests!");
    }

    fn handle_shutdown(&mut self, req: JsonRpcRequest) {
        self.lifecycle = ServerLifecycle::ShuttingDown;
        self.cancel_pending_definitions();
        self.send_result(req.id, serde_json::Value::Null);
        self.lifecycle = ServerLifecycle::Shutdown;
        tracing::info!(" Shutdown complete.");
    }

    // =================================================================
    // Document handlers
    // =================================================================

    fn handle_did_open(&mut self, notif: JsonRpcNotification) {
        let params: DidOpenTextDocumentParams = match serde_json::from_value(notif.params) {
            Ok(params) => params,
            Err(error) => {
                tracing::warn!(category = ?error.classify(), "invalid didOpen parameters");
                return;
            },
        };
        let uri = &params.text_document.uri;
        let version = params.text_document.version;
        let content = &params.text_document.text;
        if uri.len() > MAX_URI_BYTES {
            tracing::warn!("didOpen rejected: document URI exceeds accepted length");
            return;
        }
        if let Err(error) = self.reserve_document(uri, version, content.len()) {
            if self.open_documents.contains_key(uri) {
                self.invalidate_document(uri, version);
            }
            self.publish_check_error(uri, Some(version), &error);
            return;
        }
        self.schedule_document_check(uri, version, self.fleche.open_queued_snapshot(uri, content));
    }

    fn handle_did_change(&mut self, notif: JsonRpcNotification) {
        let params: DidChangeTextDocumentParams = match serde_json::from_value(notif.params) {
            Ok(params) => params,
            Err(error) => {
                tracing::warn!(category = ?error.classify(), "invalid didChange parameters");
                return;
            },
        };
        let uri = &params.text_document.uri;
        let version = params.text_document.version;
        let Some(previous) = self.open_documents.get(uri) else {
            tracing::warn!("didChange for unopened document");
            return;
        };
        if version <= previous.version {
            tracing::warn!("stale didChange version {version}");
            return;
        }
        let Some(content) = extract_latest_full_content(&params.content_changes) else {
            self.invalidate_document(uri, version);
            self.publish_check_error(uri, Some(version), &AdmissionError::IncompleteChange);
            return;
        };
        if let Err(error) = self.reserve_document(uri, version, content.len()) {
            self.invalidate_document(uri, version);
            self.publish_check_error(uri, Some(version), &error);
            return;
        }
        self.schedule_document_check(
            uri,
            version,
            self.fleche.update_queued_snapshot(uri, content),
        );
    }

    fn handle_did_close(&mut self, notif: JsonRpcNotification) {
        let params: DidCloseTextDocumentParams = match serde_json::from_value(notif.params) {
            Ok(p) => p,
            Err(e) => {
                tracing::warn!(category = ?e.classify(), "invalid didClose parameters");
                return;
            },
        };
        if params.text_document.uri.len() > MAX_URI_BYTES {
            tracing::warn!("didClose rejected: document URI exceeds accepted length");
            return;
        }

        self.cancel_document_definitions(&params.text_document.uri);
        self.open_documents.remove(&params.text_document.uri);
        self.fleche.close_file(&params.text_document.uri);
        self.publish_diagnostics(&params.text_document.uri, None, &[]);
    }

    fn handle_did_save(&mut self, _notif: JsonRpcNotification) {
        // Re-check on save
        // Could trigger full compilation to .thy artifact
    }

    fn invalidate_document(&mut self, uri: &str, version: i32) {
        self.cancel_document_definitions(uri);
        self.fleche.close_file(uri);
        if let Some(document) = self.open_documents.get_mut(uri) {
            document.revision = Arc::new(());
            document.version = version;
            // Rejected content is not retained; the next full sync may retry.
            document.bytes = 0;
        }
    }

    fn reserve_document(
        &mut self,
        uri: &str,
        version: i32,
        bytes: usize,
    ) -> Result<(), AdmissionError> {
        if uri.len() > MAX_URI_BYTES {
            return Err(AdmissionError::UriTooLong);
        }
        if bytes > MAX_SINGLE_DOCUMENT_BYTES {
            return Err(AdmissionError::DocumentTooLarge);
        }
        if !self.open_documents.contains_key(uri) && self.open_documents.len() >= MAX_OPEN_DOCUMENTS
        {
            return Err(AdmissionError::TooManyDocuments);
        }
        let current_bytes = self.open_documents.get(uri).map_or(0, |document| document.bytes);
        let total_bytes: usize = self.open_documents.values().map(|document| document.bytes).sum();
        if total_bytes - current_bytes + bytes > MAX_OPEN_DOCUMENT_BYTES {
            return Err(AdmissionError::WorkspaceTooLarge);
        }
        self.cancel_document_definitions(uri);
        self.open_documents
            .insert(uri.to_string(), OpenDocument { version, bytes, revision: Arc::new(()) });
        Ok(())
    }

    fn schedule_document_check(&mut self, uri: &str, version: i32, job: CheckJob) {
        let result = self
            .scheduler
            .as_ref()
            .map_or(Err(ScheduleError::WorkerGone), |pool| pool.schedule(job));
        if let Err(error) = result {
            self.publish_check_error(uri, Some(version), &error);
        }
    }

    fn publish_check_error(
        &mut self,
        uri: &str,
        version: Option<i32>,
        error: &impl std::fmt::Display,
    ) {
        tracing::warn!("document check not run: {error}");
        let position = Position { line: 0, character: 0 };
        let diagnostic = Diagnostic {
            range: Range { start: position.clone(), end: position },
            severity: Some(DiagnosticSeverity::Error),
            code: Some("document-check-unavailable".into()),
            source: Some("isabelle-rs".into()),
            message: format!("Document was not checked: {error}"),
            related_information: None,
        };
        self.publish_diagnostics(uri, version, &[diagnostic]);
    }

    // =================================================================
    // Feature handlers
    // =================================================================

    fn handle_hover(&mut self, req: JsonRpcRequest) {
        let params: TextDocumentPositionParams = match serde_json::from_value(req.params) {
            Ok(p) => p,
            Err(e) => {
                self.send_error(req.id, JsonRpcError::new(-32602, format!("{e}")));
                return;
            },
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
                self.send_result(
                    req.id,
                    serde_json::to_value(hover).expect("Serialization failed"),
                );
            },
            None => {
                self.send_result(req.id, serde_json::Value::Null);
            },
        }
    }

    fn handle_completion(&mut self, req: JsonRpcRequest) {
        // For now, return empty completion list
        let result = CompletionList { is_incomplete: false, items: vec![] };
        self.send_result(req.id, serde_json::to_value(result).expect("Serialization failed"));
    }

    fn handle_definition(&mut self, req: JsonRpcRequest) {
        let params: TextDocumentPositionParams = match serde_json::from_value(req.params.clone()) {
            Ok(p) => p,
            Err(e) => {
                self.send_error(req.id, JsonRpcError::new(-32602, format!("{e}")));
                return;
            },
        };

        let uri = &params.text_document.uri;
        if uri.len() > MAX_URI_BYTES {
            self.send_error(
                req.id,
                JsonRpcError::new(-32602, "document URI exceeds accepted length"),
            );
            return;
        }

        let Some(text) = self.fleche.get_document_text(uri) else {
            self.send_result(req.id, serde_json::Value::Null);
            return;
        };

        // Find word at cursor position
        let word = match word_at_position(
            &text,
            params.position.line as usize,
            params.position.character as usize,
        ) {
            Some(w) => w,
            None => {
                self.send_result(req.id, serde_json::Value::Null);
                return;
            },
        };

        let Some(document) = self.open_documents.get(uri) else {
            self.send_result(req.id, serde_json::Value::Null);
            return;
        };
        let cancellation = Arc::new(AtomicBool::new(false));
        let query = DefinitionQuery {
            id: req.id.clone(),
            uri: uri.clone(),
            word,
            cancellation: Arc::clone(&cancellation),
        };
        let result = self.scheduler.as_ref().map_or(Err(ScheduleError::WorkerGone), |scheduler| {
            scheduler.schedule_definition(query)
        });
        match result {
            Ok(()) => {
                self.pending_definitions.insert(
                    req.id,
                    PendingDefinition {
                        uri: uri.clone(),
                        revision: Arc::clone(&document.revision),
                        cancellation,
                    },
                );
            },
            Err(error) => self.send_error(req.id, JsonRpcError::new(-32000, error.to_string())),
        }
    }

    fn complete_definition(
        &mut self,
        id: RequestId,
        cancellation: &Arc<AtomicBool>,
        result: Result<Option<Location>, String>,
    ) {
        if !self
            .pending_definitions
            .get(&id)
            .is_some_and(|pending| Arc::ptr_eq(&pending.cancellation, cancellation))
        {
            return;
        }
        let Some(pending) = self.pending_definitions.remove(&id) else {
            return;
        };
        let is_current = self
            .open_documents
            .get(&pending.uri)
            .is_some_and(|document| Arc::ptr_eq(&document.revision, &pending.revision));
        if !is_current {
            self.send_error(id, JsonRpcError::new(-32800, "document revision was replaced"));
            return;
        }
        match result {
            Ok(Some(location)) => match serde_json::to_value(location) {
                Ok(value) => self.send_result(id, value),
                Err(error) => self.send_error(
                    id,
                    JsonRpcError::internal_error(format!(
                        "failed to serialize definition: {error}"
                    )),
                ),
            },
            Ok(None) => self.send_result(id, serde_json::Value::Null),
            Err(error) => self.send_error(id, JsonRpcError::new(-32000, error)),
        }
    }

    fn cancel_pending_definitions(&mut self) {
        self.finish_pending_definitions(
            REQUEST_CANCELLED,
            "definition request canceled at shutdown",
        );
    }

    fn fail_pending_definitions(&mut self, reason: &str) {
        self.finish_pending_definitions(-32000, &format!("compute worker unavailable: {reason}"));
    }

    fn finish_pending_definitions(&mut self, code: i32, message: &str) {
        for (id, pending) in std::mem::take(&mut self.pending_definitions) {
            pending.cancellation.store(true, Ordering::Release);
            self.send_error(id, JsonRpcError::new(code, message));
        }
    }

    fn cancel_document_definitions(&mut self, uri: &str) {
        let mut canceled = Vec::new();
        self.pending_definitions.retain(|id, pending| {
            if pending.uri != uri {
                return true;
            }
            pending.cancellation.store(true, Ordering::Release);
            canceled.push(id.clone());
            false
        });
        for id in canceled {
            self.send_error(
                id,
                JsonRpcError::new(-32800, "document revision was replaced or closed"),
            );
        }
    }

    fn handle_document_symbol(&mut self, req: JsonRpcRequest) {
        let params: DocumentSymbolParams = match serde_json::from_value(req.params.clone()) {
            Ok(p) => p,
            Err(e) => {
                self.send_error(req.id, JsonRpcError::new(-32602, format!("{e}")));
                return;
            },
        };

        let uri = &params.text_document.uri;
        if uri.len() > MAX_URI_BYTES {
            self.send_error(
                req.id,
                JsonRpcError::new(-32602, "document URI exceeds accepted length"),
            );
            return;
        }
        let Some(text) = self.fleche.get_document_text(uri) else {
            self.send_result(req.id, serde_json::Value::Null);
            return;
        };
        if text.lines().take(MAX_SYMBOL_LINES + 1).count() > MAX_SYMBOL_LINES {
            self.send_error(
                req.id,
                JsonRpcError::new(-32000, "document symbol line limit exceeded"),
            );
            return;
        }

        let symbols = crate::lsp::handlers::symbols::parse_document_symbols_for_server(&text);
        self.send_result(req.id, serde_json::to_value(&symbols).expect("Serialization failed"));
    }

    fn handle_proof_goals(&mut self, req: JsonRpcRequest) {
        let params: TextDocumentPositionParams = match serde_json::from_value(req.params) {
            Ok(p) => p,
            Err(e) => {
                self.send_error(req.id, JsonRpcError::new(-32602, format!("{e}")));
                return;
            },
        };

        let proof_state =
            self.fleche.get_proof_state(&params.text_document.uri, params.position.line);

        match proof_state {
            Some(ps) => {
                self.send_result(req.id, serde_json::to_value(ps).expect("Serialization failed"));
            },
            None => {
                self.send_result(req.id, serde_json::Value::Null);
            },
        }
    }

    // =================================================================
    // Helpers
    // =================================================================

    fn send_result(&mut self, id: RequestId, result: serde_json::Value) {
        self.send_message(OutgoingMessage::Response(JsonRpcResponse {
            jsonrpc: "2.0".into(),
            id,
            result: Some(result),
            error: None,
        }));
    }

    fn send_error(&mut self, id: RequestId, error: JsonRpcError) {
        self.send_message(OutgoingMessage::Response(JsonRpcResponse {
            jsonrpc: "2.0".into(),
            id,
            result: None,
            error: Some(error),
        }));
    }

    fn publish_diagnostics(&mut self, uri: &str, version: Option<i32>, diags: &[Diagnostic]) {
        let mut params = serde_json::json!({ "uri": uri, "diagnostics": diags });
        if let Some(version) = version {
            params["version"] = serde_json::json!(version);
        }
        self.send_message(OutgoingMessage::Notification(JsonRpcNotification {
            jsonrpc: "2.0".into(),
            method: notifications::PUBLISH_DIAGNOSTICS.into(),
            params,
        }));
    }

    fn send_message(&mut self, message: OutgoingMessage) {
        let result = self
            .transport
            .as_ref()
            .map_or_else(|| Err(TransportError::Disconnected), |transport| transport.send(message));
        if let Err(error) = result {
            tracing::error!("failed to send LSP message: {error}");
            self.communication_error.get_or_insert(error);
            self.lifecycle = ServerLifecycle::Shutdown;
        }
    }
}

// =========================================================================
// Helper functions
// =========================================================================

/// Find the word at a given position in text.
fn word_at_position(text: &str, line: usize, char_pos: usize) -> Option<String> {
    let target_line = text.lines().nth(line)?;
    let end = utf16_column_to_byte(target_line, char_pos)?;
    let bytes = target_line.as_bytes();

    let mut start = end;
    while start > 0 && is_ident_char(bytes[start - 1]) {
        start -= 1;
    }
    let mut end = end;
    while end < bytes.len() && is_ident_char(bytes[end]) {
        end += 1;
    }

    let word = &target_line[start..end];
    if word.is_empty() { None } else { Some(word.to_string()) }
}

fn utf16_column_to_byte(line: &str, column: usize) -> Option<usize> {
    let mut utf16_offset = 0;
    for (byte_offset, character) in line.char_indices() {
        if utf16_offset == column {
            return Some(byte_offset);
        }
        utf16_offset += character.len_utf16();
        if utf16_offset > column {
            return None;
        }
    }
    (utf16_offset == column).then_some(line.len())
}

/// Check if a byte is a valid identifier character.
fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'.' || b == b'\''
}

#[cfg(test)]
mod tests {
    use std::sync::mpsc::{self, Receiver, Sender};

    use super::*;
    use crate::fleche::engine::RealExecutor;

    struct CapturedWriter {
        output: Sender<Vec<u8>>,
        bytes: Vec<u8>,
    }

    impl io::Write for CapturedWriter {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            self.bytes.extend_from_slice(bytes);
            Ok(bytes.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            self.output.send(std::mem::take(&mut self.bytes)).map_err(io::Error::other)
        }
    }

    fn make_server() -> (IsabelleServer, Receiver<Vec<u8>>) {
        let (output, received) = mpsc::channel();
        let writer = CapturedWriter { output, bytes: Vec::new() };
        let server = IsabelleServer {
            transport: Some(Transport::with_io(io::empty(), writer)),
            fleche: Arc::new(Fleche::new(Arc::new(RealExecutor::new()))),
            worker_executable: std::env::current_exe().unwrap(),
            scheduler: None,
            open_documents: HashMap::new(),
            pending_definitions: HashMap::new(),
            lifecycle: ServerLifecycle::Initialized,
            communication_error: None,
        };
        (server, received)
    }

    fn finish_responses(
        mut server: IsabelleServer,
        output: Receiver<Vec<u8>>,
    ) -> Vec<JsonRpcResponse> {
        server.transport.take().unwrap().finish().unwrap();
        output
            .try_iter()
            .map(|bytes| {
                let header_end = bytes.windows(4).position(|part| part == b"\r\n\r\n").unwrap();
                serde_json::from_slice(&bytes[header_end + 4..]).unwrap()
            })
            .collect()
    }

    fn finish_one_response(server: IsabelleServer, output: Receiver<Vec<u8>>) -> JsonRpcResponse {
        let mut responses = finish_responses(server, output);
        assert_eq!(responses.len(), 1, "one response only");
        responses.pop().unwrap()
    }

    fn insert_pending(server: &mut IsabelleServer, id: RequestId, cancellation: Arc<AtomicBool>) {
        server.pending_definitions.insert(
            id,
            PendingDefinition {
                uri: "file:///pending.thy".into(),
                revision: Arc::new(()),
                cancellation,
            },
        );
    }

    #[test]
    fn definition_duplicate_pending_id_cancels_original_with_one_error() {
        let (mut server, output) = make_server();
        let id = RequestId::Number(7);
        let cancellation = Arc::new(AtomicBool::new(false));
        insert_pending(&mut server, id.clone(), Arc::clone(&cancellation));
        server.handle_request(JsonRpcRequest {
            jsonrpc: "2.0".into(),
            id: id.clone(),
            method: requests::TEXT_DOCUMENT_DEFINITION.into(),
            params: serde_json::Value::Null,
        });
        assert!(!server.pending_definitions.contains_key(&id));
        assert!(cancellation.load(Ordering::Acquire));
        server.complete_definition(id, &cancellation, Ok(None));
        let answer = finish_one_response(server, output);
        assert_eq!(answer.error.unwrap().code, -32600);
    }

    #[test]
    fn definition_late_old_completion_preserves_reused_id() {
        let (mut server, output) = make_server();
        let id = RequestId::Number(7);
        let old = Arc::new(AtomicBool::new(true));
        let current = Arc::new(AtomicBool::new(false));
        insert_pending(&mut server, id.clone(), Arc::clone(&current));
        server.complete_definition(id.clone(), &old, Ok(None));
        assert!(Arc::ptr_eq(&server.pending_definitions[&id].cancellation, &current));
        server.open_documents.insert(
            "file:///pending.thy".into(),
            OpenDocument {
                version: 1,
                bytes: 0,
                revision: Arc::clone(&server.pending_definitions[&id].revision),
            },
        );
        server.complete_definition(
            id.clone(),
            &current,
            Ok(Some(Location {
                uri: "file:///definition.thy".into(),
                range: Range {
                    start: Position { line: 2, character: 1 },
                    end: Position { line: 2, character: 5 },
                },
            })),
        );
        assert!(!server.pending_definitions.contains_key(&id));
        let answer = finish_one_response(server, output);
        assert_eq!(answer.result.unwrap()["uri"], "file:///definition.thy");
    }

    #[test]
    fn worker_failure_terminates_all_pending_definitions_with_errors() {
        let (mut server, output) = make_server();
        let first = Arc::new(AtomicBool::new(false));
        let second = Arc::new(AtomicBool::new(false));
        insert_pending(&mut server, RequestId::Number(1), Arc::clone(&first));
        insert_pending(&mut server, RequestId::Number(2), Arc::clone(&second));
        server.handle_message(IncomingMessage::WorkerFailed("failed to reap compute child".into()));
        assert_eq!(server.lifecycle, ServerLifecycle::Shutdown);
        assert!(server.pending_definitions.is_empty());
        assert!(first.load(Ordering::Acquire) && second.load(Ordering::Acquire));
        server.complete_definition(RequestId::Number(2), &second, Ok(None));
        let responses = finish_responses(server, output);
        assert_eq!(responses.len(), 2);
        for response in responses {
            let error = response.error.expect("failure must not produce a success result");
            assert_eq!(error.code, -32000);
            assert!(error.message.contains("failed to reap compute child"));
        }
    }

    #[test]
    fn run_transport_failure_preserves_original_error_after_cleanup() {
        let (mut server, output) = make_server();
        server.handle_message(IncomingMessage::TransportError(TransportError::Io(Arc::new(
            io::Error::new(io::ErrorKind::InvalidData, "invalid JSON-RPC frame"),
        ))));
        let error = server.run().expect_err("wire failure must remain visible");
        assert!(error.to_string().contains("invalid JSON-RPC frame"));
        assert!(output.try_recv().is_err(), "failed input produces no reply");
    }

    #[test]
    fn cancel_request_pending_definition_replies_once_and_ignores_late_completion() {
        let (mut server, output) = make_server();
        let id = RequestId::String("lookup".into());
        let canceled = Arc::new(AtomicBool::new(false));
        insert_pending(&mut server, id.clone(), Arc::clone(&canceled));
        server.handle_notification(JsonRpcNotification {
            jsonrpc: "2.0".into(),
            method: CANCEL_REQUEST.into(),
            params: serde_json::json!({"id": "lookup"}),
        });
        assert!(canceled.load(Ordering::Acquire));
        server.complete_definition(id.clone(), &canceled, Ok(None));
        let current = Arc::new(AtomicBool::new(false));
        insert_pending(&mut server, id.clone(), Arc::clone(&current));
        server.complete_definition(id.clone(), &canceled, Ok(None));
        server.open_documents.insert(
            "file:///pending.thy".into(),
            OpenDocument {
                version: 1,
                bytes: 0,
                revision: Arc::clone(&server.pending_definitions[&id].revision),
            },
        );
        server.complete_definition(id.clone(), &current, Ok(None));
        let responses = finish_responses(server, output);
        assert_eq!(responses.len(), 2, "only cancellation and reused request terminate");
        assert_eq!(responses[0].id, id);
        assert_eq!(responses[0].error.as_ref().unwrap().code, REQUEST_CANCELLED);
        assert!(responses[0].result.is_none());
        assert_eq!(responses[1].id, id);
        // serde maps a JSON null into None when decoding Option<Value>.
        assert!(responses[1].result.is_none());
        assert!(responses[1].error.is_none());
    }

    #[test]
    fn cancel_request_unknown_id_preserves_pending_definition() {
        let (mut server, output) = make_server();
        let id = RequestId::Number(7);
        let cancellation = Arc::new(AtomicBool::new(false));
        insert_pending(&mut server, id.clone(), Arc::clone(&cancellation));
        server.handle_notification(JsonRpcNotification {
            jsonrpc: "2.0".into(),
            method: CANCEL_REQUEST.into(),
            params: serde_json::json!({"id": 8}),
        });
        assert!(!cancellation.load(Ordering::Acquire));
        server.handle_notification(JsonRpcNotification {
            jsonrpc: "2.0".into(),
            method: CANCEL_REQUEST.into(),
            params: serde_json::json!({"id": 7}),
        });
        let responses = finish_responses(server, output);
        assert_eq!(responses.len(), 1);
        assert_eq!(responses[0].id, id);
        assert_eq!(responses[0].error.as_ref().unwrap().code, REQUEST_CANCELLED);
    }
    #[test]
    fn definition_worker_failure_reports_error_instead_of_null() {
        let (mut server, output) = make_server();
        let id = RequestId::Number(3);
        let cancellation = Arc::new(AtomicBool::new(false));
        insert_pending(&mut server, id.clone(), Arc::clone(&cancellation));
        server.open_documents.insert(
            "file:///pending.thy".into(),
            OpenDocument {
                version: 1,
                bytes: 0,
                revision: Arc::clone(&server.pending_definitions[&id].revision),
            },
        );
        server.complete_definition(id.clone(), &cancellation, Err("compute worker exited".into()));
        assert!(!server.pending_definitions.contains_key(&id));
        let response = finish_one_response(server, output);
        assert_eq!(response.error.as_ref().map(|error| error.code), Some(-32000));
        assert!(response.result.is_none());
    }
}
