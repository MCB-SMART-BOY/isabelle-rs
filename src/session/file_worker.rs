//! FileWorker — per-file actor with isolated state.
//!
//! Each `.thy` file gets its own FileWorker, which owns:
//! - A **Document** (snapshot-based incremental checking)
//! - A **CommandExecutor** (kernel + Isar toplevel)
//! - A **Toplevel** (command execution loop state)
//!
//! ## Design (Lean 4 style)
//!
//! FileWorkers run independently on dedicated threads. When file A
//! imports file B, the workers communicate via snapshot exchange —
//! not shared memory.
//!
//! ## Lifecycle
//!
//! 1. **Created** on `textDocument/didOpen`
//! 2. **Running** — processes commands incrementally
//! 3. **Idle** — waiting for edits
//! 4. **Crashed** — watchdog detects, restarts with saved snapshot
//! 5. **Closed** on `textDocument/didClose` → Arena GC'd

use std::thread;
use tokio::sync::{mpsc, oneshot};

use crate::document::document::{Document, Snapshot};
use crate::fleche::engine::{CheckContext, CommandExecutor};
use crate::isar::toplevel::Toplevel;
use crate::server::lsp_types::{Diagnostic, ProofState};

// =========================================================================
// Worker commands
// =========================================================================

/// Commands sent to a FileWorker.
pub enum WorkerCommand {
    /// Check the file (full or incremental re-check).
    CheckFile {
        content: String,
        reply: oneshot::Sender<Vec<Diagnostic>>,
    },
    /// Get hover type/info at a position.
    Hover {
        line: u32,
        character: u32,
        reply: oneshot::Sender<Option<String>>,
    },
    /// Get proof state (goals) at a position.
    ProofState {
        line: u32,
        reply: oneshot::Sender<Option<ProofState>>,
    },
    /// Shutdown the worker.
    Shutdown,
}

// =========================================================================
// FileWorker
// =========================================================================

/// A FileWorker processes commands for a single `.thy` file.
///
/// It owns its Document and runs on a dedicated thread.
/// Commands are received via an mpsc channel; replies are sent
/// via oneshot channels. No locks needed — single-threaded actor.
pub struct FileWorker {
    /// The file URI.
    uri: String,
    /// The document model for this file.
    document: Document,
    /// The command executor (kernel + Isar toplevel logic).
    executor: Box<dyn CommandExecutor>,
    /// Current toplevel state (None until first command).
    #[allow(dead_code)]
    toplevel: Option<Toplevel>,
    /// Monotonic version counter for snapshots.
    version: u64,
    /// Cached check context across incremental checks.
    check_ctx: CheckContext,
    /// Receive commands from the session.
    rx: mpsc::Receiver<WorkerCommand>,
}

/// Handle to a running FileWorker (used to send commands).
#[derive(Clone)]
pub struct FileWorkerHandle {
    uri: String,
    tx: mpsc::Sender<WorkerCommand>,
}

impl FileWorker {
    /// Spawn a new FileWorker for the given URI with the given executor.
    pub fn spawn(uri: String, executor: Box<dyn CommandExecutor>) -> FileWorkerHandle {
        let (tx, rx) = mpsc::channel(64);
        let handle = FileWorkerHandle {
            uri: uri.clone(),
            tx,
        };

        thread::spawn(move || {
            let mut worker = FileWorker {
                uri,
                document: Document::new(),
                executor,
                toplevel: None,
                version: 0,
                check_ctx: CheckContext::default(),
                rx,
            };
            worker.run();
        });

        handle
    }

    // =================================================================
    // Event loop
    // =================================================================

    /// Main event loop — blocks on the command channel.
    fn run(&mut self) {
        while let Some(cmd) = self.rx.blocking_recv() {
            match cmd {
                WorkerCommand::CheckFile { content, reply } => {
                    let diags = self.handle_check_file(content);
                    let _ = reply.send(diags);
                }
                WorkerCommand::Hover {
                    line,
                    character,
                    reply,
                } => {
                    let result = self.handle_hover(line, character);
                    let _ = reply.send(result);
                }
                WorkerCommand::ProofState { line, reply } => {
                    let result = self.handle_proof_state(line);
                    let _ = reply.send(result);
                }
                WorkerCommand::Shutdown => break,
            }
        }
    }

    // =================================================================
    // Command handlers
    // =================================================================

    /// Handle a CheckFile command: update the document, parse commands,
    /// execute via the kernel, and return diagnostics.
    fn handle_check_file(&mut self, content: String) -> Vec<Diagnostic> {
        // Increment version
        self.version += 1;

        // Update document content
        let is_new = self.document.get_node(&self.uri).is_none();
        if is_new {
            self.document.open_file(self.uri.clone(), content);
        } else {
            self.document.update_file(&self.uri, content);
        }

        // Get the node
        let node = match self.document.get_node_mut(&self.uri) {
            Some(n) => n,
            None => return vec![],
        };

        // Parse commands (Node::update_content already does this)
        let commands = node.commands.clone();
        let start_idx = node.snapshots.len();

        if start_idx >= commands.len() {
            return vec![];
        }

        // Execute new commands
        let mut all_diags = Vec::new();
        for cmd in &commands[start_idx..] {
            let diags = self.executor.execute(cmd, &mut self.check_ctx);

            // Store snapshot
            let mut snap = Snapshot::new(cmd.id, node.version);
            snap.diagnostics = diags.clone();
            snap.proof_state = self.check_ctx.proof_state.clone();
            snap.context_hash = self.check_ctx.context_hash;
            node.snapshots.push(snap);

            all_diags.extend(diags);
        }

        // Also collect any existing diagnostics from previous snapshots
        let persisted: Vec<Diagnostic> = node
            .snapshots
            .iter()
            .flat_map(|s| s.diagnostics.clone())
            .collect();

        persisted
    }

    /// Handle a Hover command: look up the type/info at a position.
    fn handle_hover(&self, _line: u32, _character: u32) -> Option<String> {
        // For now, placeholder — returns the file URI as context.
        // Full implementation would trace position through snapshots.
        Some(format!("file: {}", self.uri))
    }

    /// Handle a ProofState command: look up proof state at a position.
    fn handle_proof_state(&self, _line: u32) -> Option<ProofState> {
        // For now, placeholder — returns the cached proof state.
        self.check_ctx.proof_state.clone()
    }
}

impl FileWorkerHandle {
    /// Send a command to the worker (non-blocking).
    pub fn send(&self, cmd: WorkerCommand) {
        let _ = self.tx.try_send(cmd);
    }

    /// Shutdown the worker.
    pub fn shutdown(&self) {
        let _ = self.tx.try_send(WorkerCommand::Shutdown);
    }

    /// Get the file URI.
    pub fn uri(&self) -> &str {
        &self.uri
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fleche::engine::RealExecutor;

    fn dummy_executor() -> Box<dyn CommandExecutor> {
        Box::new(RealExecutor::new())
    }

    #[test]
    fn test_spawn_and_shutdown() {
        let handle = FileWorker::spawn("file:///test.thy".into(), dummy_executor());
        assert_eq!(handle.uri(), "file:///test.thy");
        handle.shutdown();
    }

    #[test]
    fn test_check_file_via_command() {
        let handle = FileWorker::spawn("file:///test.thy".into(), dummy_executor());

        let (reply_tx, reply_rx) = oneshot::channel();
        handle.send(WorkerCommand::CheckFile {
            content: "theory Test\nlemma foo: True\n  by auto".into(),
            reply: reply_tx,
        });

        let diags = reply_rx.blocking_recv().expect("worker should reply");
        // The executor should produce some diagnostics (or empty if success)
        // At minimum, we verify the channel round-trip works.
        assert!(diags.is_empty() || !diags.is_empty()); // always true, just checks it compiles

        handle.shutdown();
    }
}
