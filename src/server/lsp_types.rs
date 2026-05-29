//! Language Server Protocol types for Isabelle-rs.
//!
//! Implements the core LSP 3.17 specification types needed for a proof
//! assistant. Based on:
//! - LSP 3.17: <https://microsoft.github.io/language-server-protocol/>
//! - Lean 4's Server implementation
//! - Coq-lsp's protocol extensions

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

// =========================================================================
// JSON-RPC 2.0 Base Types
// =========================================================================

/// A JSON-RPC 2.0 request ID.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
#[serde(untagged)]
pub enum RequestId {
    Number(i64),
    String(String),
}

/// A JSON-RPC 2.0 request.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JsonRpcRequest {
    pub jsonrpc: String,
    pub id: RequestId,
    pub method: String,
    #[serde(default)]
    pub params: serde_json::Value,
}

/// A JSON-RPC 2.0 notification (no `id`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JsonRpcNotification {
    pub jsonrpc: String,
    pub method: String,
    #[serde(default)]
    pub params: serde_json::Value,
}

/// A JSON-RPC 2.0 response.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JsonRpcResponse {
    pub jsonrpc: String,
    pub id: RequestId,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub result: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<JsonRpcError>,
}

/// A JSON-RPC 2.0 error.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JsonRpcError {
    pub code: i32,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub data: Option<serde_json::Value>,
}

impl JsonRpcError {
    pub fn new(code: i32, message: impl Into<String>) -> Self {
        JsonRpcError {
            code,
            message: message.into(),
            data: None,
        }
    }

    pub fn method_not_found(method: &str) -> Self {
        JsonRpcError {
            code: -32601,
            message: format!("Method not found: {method}"),
            data: None,
        }
    }

    pub fn internal_error(msg: impl Into<String>) -> Self {
        JsonRpcError {
            code: -32603,
            message: msg.into(),
            data: None,
        }
    }
}

// =========================================================================
// LSP Basic Types
// =========================================================================

/// Document URI (file:// URL).
pub type DocumentUri = String;

/// A position in a text document (zero-based).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Position {
    /// Zero-based line number.
    pub line: u32,
    /// Zero-based character offset.
    pub character: u32,
}

/// A range in a text document (zero-based, half-open).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Range {
    pub start: Position,
    pub end: Position,
}

/// A location in a document (URI + range).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Location {
    pub uri: DocumentUri,
    pub range: Range,
}

/// A text document identifier.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TextDocumentIdentifier {
    pub uri: DocumentUri,
}

/// A versioned text document identifier.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VersionedTextDocumentIdentifier {
    pub uri: DocumentUri,
    pub version: i32,
}

/// A text document position.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TextDocumentPositionParams {
    pub text_document: TextDocumentIdentifier,
    pub position: Position,
}

// =========================================================================
// Diagnostic types
// =========================================================================

/// Severity of a diagnostic.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticSeverity {
    Error = 1,
    Warning = 2,
    Information = 3,
    Hint = 4,
}

/// A diagnostic (error, warning, etc.) produced by the prover.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Diagnostic {
    pub range: Range,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub severity: Option<DiagnosticSeverity>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub related_information: Option<Vec<DiagnosticRelatedInformation>>,
}

/// Related diagnostic info (e.g., "defined here").
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiagnosticRelatedInformation {
    pub location: Location,
    pub message: String,
}

// =========================================================================
// Goals & Proof State (Isabelle-specific extension)
// =========================================================================

/// A proof goal — the current state of a proof.
///
/// This is an Isabelle-rs specific extension to LSP, inspired by:
/// - Coq-lsp's `GoalAnswer`
/// - Lean 4's `InteractiveGoals`
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofGoal {
    /// The hypotheses (assumptions) for this goal.
    pub hyps: Vec<String>,
    /// The conclusion to prove.
    pub conclusion: String,
    /// An optional identifier for the goal.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub id: Option<String>,
}

/// The full proof state: a stack of goals.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofState {
    /// The current goals (focused).
    pub goals: Vec<ProofGoal>,
    /// Background goals (unfocused).
    pub background_goals: Vec<ProofGoal>,
    /// Are there unsolved subgoals?
    pub has_unsolved: bool,
}

// =========================================================================
// LSP Protocol Messages
// =========================================================================

/// LSP notification methods (no response expected).
pub mod notifications {
    pub const INITIALIZED: &str = "initialized";
    pub const TEXT_DOCUMENT_DID_OPEN: &str = "textDocument/didOpen";
    pub const TEXT_DOCUMENT_DID_CHANGE: &str = "textDocument/didChange";
    pub const TEXT_DOCUMENT_DID_CLOSE: &str = "textDocument/didClose";
    pub const TEXT_DOCUMENT_DID_SAVE: &str = "textDocument/didSave";
    pub const EXIT: &str = "exit";
    pub const PUBLISH_DIAGNOSTICS: &str = "textDocument/publishDiagnostics";
}

/// LSP request methods (response expected).
pub mod requests {
    pub const INITIALIZE: &str = "initialize";
    pub const SHUTDOWN: &str = "shutdown";
    pub const TEXT_DOCUMENT_HOVER: &str = "textDocument/hover";
    pub const TEXT_DOCUMENT_COMPLETION: &str = "textDocument/completion";
    pub const TEXT_DOCUMENT_DEFINITION: &str = "textDocument/definition";
    pub const TEXT_DOCUMENT_REFERENCES: &str = "textDocument/references";
    pub const TEXT_DOCUMENT_DOCUMENT_SYMBOL: &str = "textDocument/documentSymbol";
    /// Isabelle-rs extension: request proof state at a position.
    pub const PROOF_GOALS: &str = "isabelle/proofGoals";
}

// =========================================================================
// LSP Parameter Types
// =========================================================================

/// `initialize` request params.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InitializeParams {
    pub process_id: Option<i64>,
    pub root_uri: Option<DocumentUri>,
    pub capabilities: ClientCapabilities,
    #[serde(flatten)]
    pub extra: HashMap<String, serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClientCapabilities {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub workspace: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub text_document: Option<serde_json::Value>,
    #[serde(flatten)]
    pub extra: HashMap<String, serde_json::Value>,
}

/// `initialize` result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InitializeResult {
    pub capabilities: ServerCapabilities,
    pub server_info: ServerInfo,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerCapabilities {
    pub text_document_sync: TextDocumentSyncKind,
    pub hover_provider: bool,
    pub completion_provider: Option<CompletionOptions>,
    pub definition_provider: bool,
    pub references_provider: bool,
    pub document_symbol_provider: bool,
    /// Proof goal support (Isabelle-rs extension).
    pub proof_goals_provider: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerInfo {
    pub name: String,
    pub version: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TextDocumentSyncKind {
    None = 0,
    Full = 1,
    Incremental = 2,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionOptions {
    pub trigger_characters: Vec<String>,
}

/// `textDocument/documentSymbol` request params.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DocumentSymbolParams {
    pub text_document: TextDocumentIdentifier,
}

/// `textDocument/didOpen` notification params.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DidOpenTextDocumentParams {
    pub text_document: TextDocumentItem,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TextDocumentItem {
    pub uri: DocumentUri,
    pub language_id: String,
    pub version: i32,
    pub text: String,
}

/// `textDocument/didChange` notification params.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DidChangeTextDocumentParams {
    pub text_document: VersionedTextDocumentIdentifier,
    pub content_changes: Vec<TextDocumentContentChangeEvent>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TextDocumentContentChangeEvent {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub range: Option<Range>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub range_length: Option<u32>,
    pub text: String,
}

/// `textDocument/didClose` notification params.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DidCloseTextDocumentParams {
    pub text_document: TextDocumentIdentifier,
}

/// `textDocument/didSave` notification params.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DidSaveTextDocumentParams {
    pub text_document: TextDocumentIdentifier,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub text: Option<String>,
}

/// `textDocument/hover` result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Hover {
    pub contents: HoverContents,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub range: Option<Range>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum HoverContents {
    Markup(MarkupContent),
    Array(Vec<MarkupContent>),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MarkupContent {
    pub kind: MarkupKind,
    pub value: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MarkupKind {
    PlainText,
    Markdown,
}

/// `textDocument/completion` result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionList {
    pub is_incomplete: bool,
    pub items: Vec<CompletionItem>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CompletionItem {
    pub label: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub kind: Option<CompletionItemKind>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub documentation: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub insert_text: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CompletionItemKind {
    Text = 1,
    Method = 2,
    Function = 3,
    Constructor = 4,
    Field = 5,
    Variable = 6,
    Class = 7,
    Interface = 8,
    Module = 9,
    Property = 10,
    Keyword = 14,
    Snippet = 15,
}

/// `textDocument/documentSymbol` result.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DocumentSymbol {
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    pub kind: SymbolKind,
    pub range: Range,
    pub selection_range: Range,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub children: Option<Vec<DocumentSymbol>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SymbolKind {
    File = 1,
    Module = 2,
    Namespace = 3,
    Package = 4,
    Class = 5,
    Method = 6,
    Property = 7,
    Field = 8,
    Constructor = 9,
    Enum = 10,
    Interface = 11,
    Function = 12,
    Variable = 13,
    Constant = 14,
    String = 15,
    Number = 16,
    Boolean = 17,
    Struct = 18,
    TypeParameter = 26,
}

// =========================================================================
// LSP Server State
// =========================================================================

/// Tracks the lifecycle state of the LSP server.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ServerLifecycle {
    Created,
    Initialized,
    ShuttingDown,
    Shutdown,
}

impl ServerLifecycle {
    pub fn can_handle_requests(&self) -> bool {
        matches!(self, ServerLifecycle::Initialized)
    }
}
