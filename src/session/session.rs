//! Session — the top-level orchestrator.
//!
//! A Session manages a collection of FileWorkers, one per open `.thy` file.
//! It replaces V1's `Mutex<Document>` with per-file actor isolation.
//!
//! ## Design
//!
//! - Each file gets a `FileWorker` actor with its own Document + Executor
//! - The Session routes LSP requests to the correct FileWorker
//! - FileWorkers communicate via async channels (mpsc + oneshot)
//! - The Watchdog monitors worker health
//!
//! ## Protocol
//!
//! ```text
//! LSP Request → Session → FileWorker → Document + Toplevel
//!                              ↓
//!                         Diagnostics
//! ```

use std::{collections::HashMap, sync::Arc};

use tokio::sync::oneshot;

use super::{
    file_worker::{FileWorker, FileWorkerHandle, WorkerCommand},
    watchdog::Watchdog,
};
use crate::{
    fleche::engine::CommandExecutor,
    server::lsp_types::{Diagnostic, ProofState},
};

// =========================================================================
// Session error
// =========================================================================

#[derive(Debug, Clone)]
pub enum SessionError {
    FileNotFound(String),
    WorkerGone(String),
    Timeout(String),
}

// =========================================================================
// Session
// =========================================================================

pub struct Session {
    workers: HashMap<String, FileWorkerHandle>,
    executor: Arc<dyn CommandExecutor>,
    _watchdog: Watchdog,
}

impl Session {
    pub fn new(executor: Arc<dyn CommandExecutor>) -> Self {
        Session { workers: HashMap::new(), executor, _watchdog: Watchdog::new() }
    }

    /// Open a file and run initial check. Returns diagnostics.
    pub fn open_file(&mut self, uri: &str, content: &str) -> Result<Vec<Diagnostic>, SessionError> {
        let handle = FileWorker::spawn(uri.to_string(), self.executor.clone_box());
        self.workers.insert(uri.to_string(), handle.clone());

        let (reply_tx, reply_rx) = oneshot::channel();
        handle.send(WorkerCommand::CheckFile { content: content.to_string(), reply: reply_tx });

        reply_rx.blocking_recv().map_err(|_| SessionError::WorkerGone(uri.to_string()))
    }

    /// Update a file and re-check incrementally.
    pub fn update_file(
        &mut self,
        uri: &str,
        content: &str,
    ) -> Result<Vec<Diagnostic>, SessionError> {
        let handle = self.get_handle(uri)?;

        let (reply_tx, reply_rx) = oneshot::channel();
        handle.send(WorkerCommand::CheckFile { content: content.to_string(), reply: reply_tx });

        reply_rx.blocking_recv().map_err(|_| SessionError::WorkerGone(uri.to_string()))
    }

    /// Get hover info at a position.
    pub fn hover(
        &self,
        uri: &str,
        line: u32,
        character: u32,
    ) -> Result<Option<String>, SessionError> {
        let handle = self.get_handle(uri)?;
        let (reply_tx, reply_rx) = oneshot::channel();
        handle.send(WorkerCommand::Hover { line, character, reply: reply_tx });
        reply_rx.blocking_recv().map_err(|_| SessionError::WorkerGone(uri.to_string()))
    }

    /// Get proof state at a position.
    pub fn proof_state(&self, uri: &str, line: u32) -> Result<Option<ProofState>, SessionError> {
        let handle = self.get_handle(uri)?;
        let (reply_tx, reply_rx) = oneshot::channel();
        handle.send(WorkerCommand::ProofState { line, reply: reply_tx });
        reply_rx.blocking_recv().map_err(|_| SessionError::WorkerGone(uri.to_string()))
    }

    /// Close a file and terminate its worker.
    pub fn close_file(&mut self, uri: &str) {
        if let Some(handle) = self.workers.remove(uri) {
            handle.shutdown();
        }
    }

    fn get_handle(&self, uri: &str) -> Result<&FileWorkerHandle, SessionError> {
        self.workers.get(uri).ok_or_else(|| SessionError::FileNotFound(uri.to_string()))
    }

    pub fn open_count(&self) -> usize {
        self.workers.len()
    }

    pub fn shutdown(&mut self) {
        for (_, handle) in self.workers.drain() {
            handle.shutdown();
        }
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fleche::engine::RealExecutor;

    fn dummy_session() -> Session {
        Session::new(Arc::new(RealExecutor::new()))
    }

    #[test]
    fn test_session_create() {
        let session = dummy_session();
        assert_eq!(session.open_count(), 0);
    }

    #[test]
    fn test_open_file_round_trip() {
        let mut session = dummy_session();

        let result =
            session.open_file("file:///test.thy", "theory Test\nlemma foo: True\n  by auto");
        assert!(result.is_ok(), "open_file should succeed: {:?}", result.err());
        assert_eq!(session.open_count(), 1);

        let diags = result.unwrap();
        // The RealExecutor processes the theory header and lemma
        // We don't assert specific diagnostics — just that the round-trip works
        let _ = diags;

        session.close_file("file:///test.thy");
        assert_eq!(session.open_count(), 0);
    }

    #[test]
    fn test_update_file_round_trip() {
        let mut session = dummy_session();

        // Open initial content
        session.open_file("file:///test.thy", "theory Test\nlemma foo: True\n  by auto").unwrap();

        // Update with new content
        let result = session
            .update_file("file:///test.thy", "theory Test\nlemma foo: True\nproof auto\nqed");
        assert!(result.is_ok());

        session.close_file("file:///test.thy");
    }

    #[test]
    fn test_hover_round_trip() {
        let mut session = dummy_session();

        session.open_file("file:///test.thy", "theory Test\nlemma foo: True\n  by auto").unwrap();

        let hover = session.hover("file:///test.thy", 0, 0).unwrap();
        assert!(hover.is_some());

        session.close_file("file:///test.thy");
    }

    #[test]
    fn test_proof_state_round_trip() {
        let mut session = dummy_session();

        session
            .open_file("file:///test.thy", "theory Test\nlemma foo: True\nproof auto\nqed")
            .unwrap();

        let ps = session.proof_state("file:///test.thy", 2).unwrap();
        // May be Some or None depending on execution state
        let _ = ps;

        session.close_file("file:///test.thy");
    }

    #[test]
    fn test_file_not_found() {
        let session = dummy_session();
        let result = session.hover("file:///nonexistent.thy", 0, 0);
        assert!(result.is_err());
    }
}
