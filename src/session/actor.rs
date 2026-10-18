//! Experimental Session orchestration for `.thy` files.
//!
//! Open files retain independent document state while a single shared
//! compute thread processes a bounded queue of checks and queries.

use std::{
    collections::HashMap,
    path::Path,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
        mpsc::{self, RecvTimeoutError},
    },
    time::{Duration, Instant},
};

use super::{
    file_worker::{
        FileWorkerHandle, FileWorkerPool, PoolShutdownError, WorkerCommand, WorkerSendError,
    },
    watchdog::Watchdog,
};
use crate::{
    fleche::engine::CommandExecutor,
    server::lsp_types::{Diagnostic, ProofState},
};

// =========================================================================
// Session error
// =========================================================================

/// Errors returned by experimental session operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SessionError {
    /// The requested document is not open.
    FileNotFound(String),
    /// The shared compute queue is full; the caller may retry later.
    QueueFull(String),
    /// The worker stopped or the document was closed while waiting.
    WorkerGone(String),
    /// The shared compute worker panicked while shutting down; contains its panic message.
    WorkerPanicked(String),
    /// A built-in executor needs an explicit, trusted compute-worker executable.
    Startup(String),
    /// The requested source exceeds the trusted compute protocol limit.
    SourceTooLarge { uri: String, max_bytes: usize },
    /// The isolated check failed; no diagnostics or proof state were published.
    Compute { uri: String, reason: String },
    /// A request or shutdown exceeded its deadline.
    Timeout(String),
}

// =========================================================================
// Session
// =========================================================================

pub struct Session {
    workers: HashMap<String, FileWorkerHandle>,
    executor: Arc<dyn CommandExecutor>,
    pool: FileWorkerPool,
    _watchdog: Watchdog,
}

impl Session {
    const REQUEST_TIMEOUT: Duration = Duration::from_secs(2);
    // Cold executable hashing, handshake and first legacy check share this budget.
    const PROCESS_REQUEST_TIMEOUT: Duration = Duration::from_secs(10);

    /// Create a cooperative Session for custom executors.
    pub fn new(executor: Arc<dyn CommandExecutor>) -> Result<Self, SessionError> {
        if executor.is_builtin_real() {
            return Err(SessionError::Startup(
                "built-in RealExecutor requires an explicit trusted --compute-worker binary; use Session::new_with_worker".into(),
            ));
        }
        Ok(Self::new_cooperative(executor))
    }

    /// Use a trusted compute executable for built-in RealExecutor checks.
    pub fn new_with_worker(
        executor: Arc<dyn CommandExecutor>,
        executable: impl AsRef<Path>,
    ) -> Result<Self, SessionError> {
        if !executor.is_builtin_real() {
            return Ok(Self::new_cooperative(executor));
        }
        let cwd = std::env::current_dir().map_err(|error| {
            SessionError::Startup(format!("locating compute working directory: {error}"))
        })?;
        Ok(Self::with_pool(
            executor,
            FileWorkerPool::new_process(executable.as_ref().to_path_buf(), cwd),
        ))
    }

    fn new_cooperative(executor: Arc<dyn CommandExecutor>) -> Self {
        Self::with_pool(executor, FileWorkerPool::new())
    }

    fn with_pool(executor: Arc<dyn CommandExecutor>, pool: FileWorkerPool) -> Self {
        Self { workers: HashMap::new(), executor, pool, _watchdog: Watchdog::new() }
    }

    fn check_timeout(&self) -> Duration {
        if self.executor.is_builtin_real() {
            Self::PROCESS_REQUEST_TIMEOUT
        } else {
            Self::REQUEST_TIMEOUT
        }
    }

    /// Open a file and run initial check. Returns diagnostics.
    pub fn open_file(&mut self, uri: &str, content: &str) -> Result<Vec<Diagnostic>, SessionError> {
        let handle = self.pool.open(uri.to_string(), self.executor.clone_box());
        let (reply_tx, reply_rx) = mpsc::channel();
        let is_cancelled = Arc::new(AtomicBool::new(false));
        let timeout = self.check_timeout();
        handle
            .send(WorkerCommand::CheckFile {
                content: content.to_string(),
                deadline: Instant::now() + timeout,
                is_cancelled: Arc::clone(&is_cancelled),
                reply: reply_tx,
            })
            .map_err(|error| Self::send_error(uri, error))?;
        if let Some(previous) = self.workers.insert(uri.to_string(), handle) {
            previous.shutdown();
        }
        Self::receive_check(uri, reply_rx, &is_cancelled, timeout)
    }

    /// Update a file and re-check incrementally.
    pub fn update_file(
        &mut self,
        uri: &str,
        content: &str,
    ) -> Result<Vec<Diagnostic>, SessionError> {
        let handle = self.get_handle(uri)?;

        let (reply_tx, reply_rx) = mpsc::channel();
        let is_cancelled = Arc::new(AtomicBool::new(false));
        let timeout = self.check_timeout();
        handle
            .send(WorkerCommand::CheckFile {
                content: content.to_string(),
                deadline: Instant::now() + timeout,
                is_cancelled: Arc::clone(&is_cancelled),
                reply: reply_tx,
            })
            .map_err(|error| Self::send_error(uri, error))?;
        Self::receive_check(uri, reply_rx, &is_cancelled, timeout)
    }

    /// Get hover info at a position.
    pub fn hover(
        &self,
        uri: &str,
        line: u32,
        character: u32,
    ) -> Result<Option<String>, SessionError> {
        let handle = self.get_handle(uri)?;
        let (reply_tx, reply_rx) = mpsc::channel();
        handle
            .send(WorkerCommand::Hover { line, character, reply: reply_tx })
            .map_err(|error| Self::send_error(uri, error))?;
        Self::receive(uri, reply_rx)
    }

    /// Get proof state at a position.
    pub fn proof_state(&self, uri: &str, line: u32) -> Result<Option<ProofState>, SessionError> {
        let handle = self.get_handle(uri)?;
        let (reply_tx, reply_rx) = mpsc::channel();
        handle
            .send(WorkerCommand::ProofState { line, reply: reply_tx })
            .map_err(|error| Self::send_error(uri, error))?;
        Self::receive(uri, reply_rx)?
    }

    /// Close a file and invalidate its queued and in-flight results.
    pub fn close_file(&mut self, uri: &str) {
        if let Some(handle) = self.workers.remove(uri) {
            handle.shutdown();
        }
    }

    fn receive_check(
        uri: &str,
        reply: mpsc::Receiver<Result<Vec<Diagnostic>, SessionError>>,
        is_cancelled: &AtomicBool,
        timeout: Duration,
    ) -> Result<Vec<Diagnostic>, SessionError> {
        let result = Self::receive_with_timeout(uri, reply, timeout);
        if matches!(&result, Err(SessionError::Timeout(_))) {
            is_cancelled.store(true, Ordering::Release);
        }
        result?
    }

    fn receive<T>(uri: &str, reply: mpsc::Receiver<T>) -> Result<T, SessionError> {
        Self::receive_with_timeout(uri, reply, Self::REQUEST_TIMEOUT)
    }

    fn receive_with_timeout<T>(
        uri: &str,
        reply: mpsc::Receiver<T>,
        timeout: Duration,
    ) -> Result<T, SessionError> {
        match reply.recv_timeout(timeout) {
            Ok(value) => Ok(value),
            Err(RecvTimeoutError::Timeout) => Err(SessionError::Timeout(format!(
                "request for {uri} timed out after {} ms",
                timeout.as_millis()
            ))),
            Err(RecvTimeoutError::Disconnected) => Err(SessionError::WorkerGone(uri.to_string())),
        }
    }

    fn get_handle(&self, uri: &str) -> Result<&FileWorkerHandle, SessionError> {
        self.workers.get(uri).ok_or_else(|| SessionError::FileNotFound(uri.to_string()))
    }

    fn send_error(uri: &str, error: WorkerSendError) -> SessionError {
        match error {
            WorkerSendError::QueueFull => SessionError::QueueFull(uri.to_string()),
            WorkerSendError::WorkerGone => SessionError::WorkerGone(uri.to_string()),
        }
    }

    pub fn open_count(&self) -> usize {
        self.workers.len()
    }

    /// Stop admission and join if the worker exits within its shutdown grace.
    /// Built-in checks terminate their isolated process; custom executors remain cooperative.
    pub fn shutdown(&mut self) -> Result<(), SessionError> {
        for (_, handle) in self.workers.drain() {
            handle.shutdown();
        }
        match self.pool.shutdown() {
            Ok(()) => Ok(()),
            Err(PoolShutdownError::Timeout) => Err(SessionError::Timeout(
                "shared Session compute worker still running after shutdown grace".into(),
            )),
            Err(PoolShutdownError::Compute(error)) => Err(SessionError::Compute {
                uri: "<session shutdown>".into(),
                reason: format!("stopping compute process: {error}"),
            }),
            Err(PoolShutdownError::WorkerPanicked(panic)) => {
                let reason = panic
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| panic.downcast_ref::<&str>().map(|message| (*message).to_string()))
                    .unwrap_or_else(|| "non-string panic payload".to_string());
                Err(SessionError::WorkerPanicked(reason))
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{document::Command, fleche::engine::CheckContext};
    use std::{
        sync::{Mutex, mpsc},
        time::Duration,
    };

    const WAIT_LIMIT: Duration = Duration::from_secs(5);

    #[derive(Clone)]
    struct StalledExecutor {
        started: mpsc::Sender<()>,
        release: Arc<Mutex<mpsc::Receiver<()>>>,
    }

    impl CommandExecutor for StalledExecutor {
        fn execute(&self, _command: &Command, _ctx: &mut CheckContext) -> Vec<Diagnostic> {
            self.started.send(()).unwrap();
            self.release
                .lock()
                .unwrap_or_else(|error| error.into_inner())
                .recv_timeout(WAIT_LIMIT)
                .unwrap();
            vec![]
        }

        fn clone_box(&self) -> Box<dyn CommandExecutor> {
            Box::new(self.clone())
        }
    }

    #[derive(Clone)]
    struct CooperativeRealExecutor(Arc<crate::fleche::engine::RealExecutor>);

    impl CommandExecutor for CooperativeRealExecutor {
        fn execute(&self, command: &Command, ctx: &mut CheckContext) -> Vec<Diagnostic> {
            self.0.execute(command, ctx)
        }

        fn clone_box(&self) -> Box<dyn CommandExecutor> {
            Box::new(self.clone())
        }
    }

    fn new_cooperative_session() -> Session {
        Session::new(Arc::new(CooperativeRealExecutor(Arc::new(
            crate::fleche::engine::RealExecutor::new(),
        ))))
        .unwrap()
    }

    #[test]
    fn session_builtin_without_explicit_worker_rejects_startup() {
        let result = Session::new(Arc::new(crate::fleche::engine::RealExecutor::new()));
        assert!(matches!(
            result,
            Err(SessionError::Startup(message)) if message.contains("Session::new_with_worker")
        ));
    }

    #[test]
    fn session_update_then_close_keeps_only_open_documents() {
        let mut session = new_cooperative_session();
        let uri = "file:///test.thy";
        session.open_file(uri, "theory First").unwrap();
        session.update_file(uri, "theory Second").unwrap();
        assert_eq!(session.open_count(), 1);

        session.close_file(uri);
        assert_eq!(session.open_count(), 0);
        assert!(matches!(
            session.update_file(uri, "theory Third"),
            Err(SessionError::FileNotFound(missing)) if missing == uri
        ));
        session.shutdown().unwrap();
    }

    #[test]
    fn session_duplicate_open_discards_previous_proof_state() {
        let mut session = new_cooperative_session();
        let uri = "file:///same.thy";
        session.open_file(uri, "lemma old: \"A\"").unwrap();
        assert!(session.proof_state(uri, 0).unwrap().is_some());
        session.open_file(uri, "theory New").unwrap();
        assert!(matches!(session.proof_state(uri, 0), Ok(None)));
        assert_eq!(session.open_count(), 1);
        session.shutdown().unwrap();
    }

    #[test]
    fn session_hover_without_position_support_returns_none() {
        let mut session = new_cooperative_session();
        let uri = "file:///test.thy";
        session.open_file(uri, "theory Test").unwrap();
        assert_eq!(session.hover(uri, 0, 0), Ok(None));
        session.shutdown().unwrap();
        assert_eq!(session.hover(uri, 0, 0), Err(SessionError::FileNotFound(uri.into())));
    }

    #[test]
    fn session_edit_to_empty_clears_previous_proof_goal() {
        let mut session = new_cooperative_session();
        let uri = "file:///session-edited.thy";
        session.open_file(uri, "theory Test\nlemma pending: \"A\"").unwrap();
        assert!(session.proof_state(uri, 0).unwrap().is_some());

        session.update_file(uri, "").unwrap();
        assert!(matches!(session.proof_state(uri, 0), Ok(None)));
        session.shutdown().unwrap();
    }

    #[test]
    fn session_shutdown_stops_new_admission() {
        let mut session = new_cooperative_session();
        session.shutdown().unwrap();
        assert!(matches!(
            session.open_file("file:///late.thy", "theory Late"),
            Err(SessionError::WorkerGone(uri)) if uri == "file:///late.thy"
        ));
        assert_eq!(session.open_count(), 0);
    }

    #[test]
    fn session_open_file_noncooperative_check_returns_timeout() {
        let (started_tx, started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let executor = Arc::new(StalledExecutor {
            started: started_tx,
            release: Arc::new(Mutex::new(release_rx)),
        });
        let (result_tx, result_rx) = mpsc::channel();
        let task = std::thread::spawn(move || {
            let mut session = Session::new(executor).unwrap();
            let result = session.open_file("file:///slow.thy", "theory Slow");
            assert!(result_tx.send((session, result)).is_ok());
        });
        started_rx.recv_timeout(WAIT_LIMIT).unwrap();
        let (mut session, result) = result_rx.recv_timeout(WAIT_LIMIT).unwrap();
        release_tx.send(()).unwrap();

        assert!(
            matches!(result, Err(SessionError::Timeout(reason)) if reason.contains("file:///slow.thy"))
        );
        session.shutdown().unwrap();
        task.join().unwrap();
    }

    #[test]
    fn session_shutdown_blocked_check_returns_timeout_then_joins_after_release() {
        let (started_tx, started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let release = Arc::new(Mutex::new(release_rx));
        let mut session = Session::new(Arc::new(StalledExecutor {
            started: started_tx,
            release: Arc::clone(&release),
        }))
        .unwrap();
        let uri = "file:///blocked.thy";
        let handle = session.pool.open(uri.into(), session.executor.clone_box());
        session.workers.insert(uri.into(), handle.clone());
        let (reply, checked) = mpsc::channel();
        handle
            .send(WorkerCommand::CheckFile {
                content: "theory Blocked".into(),
                deadline: Instant::now() + Session::REQUEST_TIMEOUT,
                is_cancelled: Arc::new(AtomicBool::new(false)),
                reply,
            })
            .unwrap();
        started_rx.recv_timeout(WAIT_LIMIT).unwrap();

        let result = session.shutdown();
        release_tx.send(()).unwrap();
        assert!(
            matches!(result, Err(SessionError::Timeout(reason)) if reason.contains("shutdown"))
        );
        assert!(matches!(checked.recv_timeout(WAIT_LIMIT), Err(RecvTimeoutError::Disconnected)));
        session.shutdown().unwrap();
    }
}
