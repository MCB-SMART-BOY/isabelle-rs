//! Isabelle-rs specific LSP extensions.
//!
//! These custom protocol extensions fill the gaps that standard LSP
//! doesn't cover for proof assistants. They are inspired by:
//! - Coq-lsp's `coq-lsp/*` extensions
//! - Lean 4's `$/lean/*` extensions
//!
//! ## Why extensions are needed
//!
//! PIDE's unique features that standard LSP cannot express:
//! 1. **Proof state streaming** — goals change as you write tactics
//! 2. **Command execution model** — commands have lifecycle (running/finished/failed)
//! 3. **Dynamic output** — prover messages that aren't diagnostics
//! 4. **Nested language markup** — ML inside Isabelle, SML inside ML, etc.
//!
//! ## Extension naming convention
//!
//! Following LSP convention:
//! - `$/isabelle/*` — server-to-client notifications (pushed)
//! - `isabelle/*` — client-to-server requests (pulled)

use super::lsp_types::*;
use serde::{Deserialize, Serialize};

// =========================================================================
// Extension method names
// =========================================================================

/// Custom notification methods (server → client).
pub mod custom_notifications {
    /// Proof state has changed. Sent whenever the proof state updates.
    /// Like Coq-lsp's `$/goals` and Lean 4's `$/lean/plainGoal`.
    pub const PROOF_STATE_CHANGED: &str = "$/isabelle/proofStateChanged";

    /// Command execution progress. Sent when commands start/finish executing.
    /// Like Lean 4's `$/lean/fileProgress`.
    pub const COMMAND_PROGRESS: &str = "$/isabelle/commandProgress";

    /// Dynamic output message (not a diagnostic).
    /// Like PIDE's Output panel.
    pub const OUTPUT_MESSAGE: &str = "$/isabelle/outputMessage";

    /// The theory being processed has changed (e.g., new constants defined).
    /// Allows the client to update completion/hover caches.
    pub const THEORY_UPDATED: &str = "$/isabelle/theoryUpdated";
}

/// Custom request methods (client → server).
pub mod custom_requests {
    /// Execute a proof command (like stepping forward in a proof).
    pub const PROOF_STEP: &str = "isabelle/proofStep";

    /// Undo the last proof step (like `undo` in Isabelle/jEdit).
    pub const PROOF_UNDO: &str = "isabelle/proofUndo";

    /// Get the current theory context (defined constants, types, etc.).
    pub const THEORY_CONTEXT: &str = "isabelle/theoryContext";

    /// Search for theorems/constants.
    pub const SEARCH: &str = "isabelle/search";

    /// Wait until the document is fully checked up to a position.
    /// Like Lean 4's `textDocument/waitForDiagnostics`.
    pub const WAIT_FOR_CHECKING: &str = "isabelle/waitForChecking";
}

// =========================================================================
// Proof State Extension
// =========================================================================

/// Notification sent when the proof state changes.
///
/// This is the LSP equivalent of PIDE's markup-based goal display.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofStateChanged {
    pub uri: DocumentUri,
    /// The version of the document this state corresponds to.
    pub version: i32,
    /// Which command produced this state.
    pub command_id: usize,
    /// The proof state.
    pub state: ProofState,
}

// =========================================================================
// Command Progress Extension
// =========================================================================

/// Execution status of a single command.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub enum CommandStatus {
    /// Command has been enqueued for execution.
    Forked,
    /// Command is currently being processed.
    Running,
    /// Command finished successfully.
    Finished,
    /// Command failed (error).
    Failed,
    /// Results have been merged into the document.
    Joined,
}

/// Notification sent when command execution status changes.
///
/// Corresponds to PIDE's `Markup.running`, `Markup.finished`, etc.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CommandProgress {
    pub uri: DocumentUri,
    pub version: i32,
    pub command_id: usize,
    pub status: CommandStatus,
    /// Optional message (e.g., timing info on finished).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
}

// =========================================================================
// Output Message Extension
// =========================================================================

/// Severity of an output message.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum OutputKind {
    /// Normal output (from `writeln`).
    Standard,
    /// Error output.
    Error,
    /// Tracing/debug output.
    Trace,
    /// System message.
    System,
}

/// A dynamic output message (not a diagnostic).
///
/// Corresponds to PIDE's Output panel content.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OutputMessage {
    pub uri: DocumentUri,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub position: Option<Position>,
    pub kind: OutputKind,
    pub content: String,
}

// =========================================================================
// Proof Step Request
// =========================================================================

/// Request to advance the proof by executing the next command.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofStepParams {
    pub uri: DocumentUri,
    /// Number of commands to step forward (default: 1).
    #[serde(default = "default_step")]
    pub count: usize,
}

fn default_step() -> usize {
    1
}

// =========================================================================
// Search Request
// =========================================================================

/// Request to search the theory context.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchParams {
    /// Search query string.
    pub query: String,
    /// What to search for.
    #[serde(default)]
    pub kind: SearchKind,
    /// Limit results.
    #[serde(default = "default_limit")]
    pub limit: usize,
}

fn default_limit() -> usize {
    50
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum SearchKind {
    #[default]
    All,
    Theorem,
    Constant,
    Type,
    Method,
}

/// Search result item.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchResult {
    pub name: String,
    pub kind: SearchKind,
    pub description: String,
    pub location: Option<Location>,
}

// =========================================================================
// Wait for Checking
// =========================================================================

/// Request to wait until checking is complete.
///
/// The server will respond when checking up to the given position
/// is complete. This is like Lean 4's `textDocument/waitForDiagnostics`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WaitForCheckingParams {
    pub uri: DocumentUri,
    /// Wait for checking up to this position.
    /// If None, wait for the entire document.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub position: Option<Position>,
}

// =========================================================================
// Theory Context
// =========================================================================

/// A constant defined in the current theory.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TheoryConstant {
    pub name: String,
    pub typ: String,
    pub definition: Option<String>,
}

/// A type defined in the current theory.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TheoryType {
    pub name: String,
    pub arity: usize,
    pub definition: Option<String>,
}

/// The current theory context — all definitions, types, etc.
/// This is used to populate completion lists and hover info.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TheoryContext {
    pub theory_name: String,
    pub constants: Vec<TheoryConstant>,
    pub types: Vec<TheoryType>,
    pub theorems: Vec<String>,
}
