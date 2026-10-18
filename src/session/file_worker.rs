//! Per-document state executed by a bounded, shared compute worker.
//!
//! The pool owns one OS thread and a bounded work queue. Each open file has
//! isolated document and execution state; queued commands carry that file's
//! lifetime flag so closing or reopening cannot publish an obsolete reply.

use std::{
    any::Any,
    path::PathBuf,
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, Ordering},
        mpsc::{self, RecvTimeoutError, SyncSender, TrySendError},
    },
    thread::{self, JoinHandle},
    time::{Duration, Instant},
};

use super::actor::SessionError;
use crate::{
    compute_worker::{
        CheckFailure, ComputeError, ComputeProcess, ComputeRequest, ComputeResponse, MAX_SOURCE,
        ProcessCheck,
    },
    document::{Document, Snapshot},
    fleche::engine::{CheckContext, CommandExecutor, Fleche},
    server::lsp_types::{Diagnostic, ProofState},
};

// =========================================================================
// Worker commands
// =========================================================================

/// Operations submitted to the shared compute queue.
pub enum WorkerCommand {
    CheckFile {
        content: String,
        deadline: Instant,
        is_cancelled: Arc<AtomicBool>,
        reply: mpsc::Sender<Result<Vec<Diagnostic>, SessionError>>,
    },
    Hover {
        line: u32,
        character: u32,
        reply: mpsc::Sender<Option<String>>,
    },
    ProofState {
        line: u32,
        reply: mpsc::Sender<Result<Option<ProofState>, SessionError>>,
    },
}

/// Admission failure, distinguished from a compute result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WorkerSendError {
    /// All waiting slots in the shared queue are occupied.
    QueueFull,
    /// This file was closed, or the compute worker has stopped.
    WorkerGone,
}

/// A file's serialized document and execution state.
pub struct FileWorker {
    uri: String,
    document: Document,
    executor: Box<dyn CommandExecutor>,
    check_ctx: CheckContext,
    check_error: Option<SessionError>,
    successful_check_cancel: Option<Arc<AtomicBool>>,
}

struct ProcessCheckRequest<'a> {
    deadline: Instant,
    is_cancelled: &'a AtomicBool,
    is_open: &'a AtomicBool,
    is_stopping: &'a AtomicBool,
    process_config: &'a Option<(PathBuf, PathBuf)>,
    process: &'a mut Option<ComputeProcess>,
    cleanup_failure: &'a mut Option<ComputeError>,
}

struct WorkItem {
    worker: Arc<Mutex<FileWorker>>,
    is_open: Arc<AtomicBool>,
    command: WorkerCommand,
}

struct PoolAdmission {
    sender: Mutex<Option<SyncSender<WorkItem>>>,
    is_stopping: Arc<AtomicBool>,
}

/// Failure while stopping the shared compute worker.
#[derive(Debug)]
pub(crate) enum PoolShutdownError {
    /// A running check did not reach a cooperative stop boundary in time.
    Timeout,
    /// The compute thread exited by panicking.
    WorkerPanicked(Box<dyn Any + Send>),
    /// The child could not be stopped and reaped during shutdown.
    Compute(ComputeError),
}

/// One compute thread and one waiting slot for all files in a Session.
pub(crate) struct FileWorkerPool {
    admission: Arc<PoolAdmission>,
    exit: Option<mpsc::Receiver<Result<(), ComputeError>>>,
    cleanup_failure: Option<ComputeError>,
    thread: Option<JoinHandle<()>>,
}

#[derive(Clone)]
pub struct FileWorkerHandle {
    uri: String,
    worker: Arc<Mutex<FileWorker>>,
    is_open: Arc<AtomicBool>,
    admission: Arc<PoolAdmission>,
}

fn is_active(is_open: &AtomicBool, is_stopping: &AtomicBool) -> bool {
    is_open.load(Ordering::Acquire) && !is_stopping.load(Ordering::Acquire)
}

fn preserve_cleanup_failure(slot: &mut Option<ComputeError>, error: ComputeError) {
    // Drop may detach before receiving the exit result; record every failure here too.
    eprintln!("experimental Session compute process cleanup failed: {error}");
    if slot.is_none() {
        *slot = Some(error);
    }
}

impl FileWorkerPool {
    const QUEUE_CAPACITY: usize = 1;
    const SHUTDOWN_GRACE: Duration = Duration::from_secs(1);

    pub(crate) fn new() -> Self {
        Self::new_inner(None)
    }

    pub(crate) fn new_process(executable: PathBuf, cwd: PathBuf) -> Self {
        Self::new_inner(Some((executable, cwd)))
    }

    fn new_inner(process_config: Option<(PathBuf, PathBuf)>) -> Self {
        let (sender, receiver) = mpsc::sync_channel::<WorkItem>(Self::QUEUE_CAPACITY);
        let (exit_tx, exit) = mpsc::channel();
        let is_stopping = Arc::new(AtomicBool::new(false));
        let stop_signal = Arc::clone(&is_stopping);
        let thread = thread::spawn(move || {
            let mut process = None;
            let mut cleanup_failure = None;
            while let Ok(item) = receiver.recv() {
                if !is_active(&item.is_open, &stop_signal) {
                    continue;
                }
                let mut worker = item.worker.lock().unwrap_or_else(|error| error.into_inner());
                if !is_active(&item.is_open, &stop_signal) {
                    continue;
                }
                worker.run(
                    item.command,
                    &item.is_open,
                    &stop_signal,
                    &process_config,
                    &mut process,
                    &mut cleanup_failure,
                );
            }
            if let Some(mut process) = process
                && let Err(error) = process.stop()
            {
                preserve_cleanup_failure(&mut cleanup_failure, error);
            }
            // After a timeout Drop may detach and discard the exit receiver.
            let _ = exit_tx.send(cleanup_failure.map_or(Ok(()), Err));
        });

        Self {
            admission: Arc::new(PoolAdmission { sender: Mutex::new(Some(sender)), is_stopping }),
            exit: Some(exit),
            cleanup_failure: None,
            thread: Some(thread),
        }
    }

    pub(crate) fn open(&self, uri: String, executor: Box<dyn CommandExecutor>) -> FileWorkerHandle {
        FileWorkerHandle {
            worker: Arc::new(Mutex::new(FileWorker {
                uri: uri.clone(),
                document: Document::new(),
                executor,
                check_ctx: CheckContext::default(),
                check_error: None,
                successful_check_cancel: None,
            })),
            uri,
            is_open: Arc::new(AtomicBool::new(true)),
            admission: Arc::clone(&self.admission),
        }
    }

    /// Stop admission, then join only after observing worker exit.
    /// A running noncooperative command may outlive the shutdown grace.
    pub(crate) fn shutdown(&mut self) -> Result<(), PoolShutdownError> {
        let mut sender = self.admission.sender.lock().unwrap_or_else(|error| error.into_inner());
        self.admission.is_stopping.store(true, Ordering::Release);
        sender.take();
        drop(sender);

        let deadline = Instant::now() + Self::SHUTDOWN_GRACE;
        if let Some(exit) = self.exit.as_ref() {
            self.cleanup_failure = match exit.recv_timeout(Self::SHUTDOWN_GRACE) {
                Ok(result) => result.err(),
                Err(RecvTimeoutError::Timeout) => return Err(PoolShutdownError::Timeout),
                Err(RecvTimeoutError::Disconnected) => Some(ComputeError::Ipc(
                    std::io::Error::other("Session worker exited without a cleanup result"),
                )),
            };
            // Consume the notification once, but retain its failure across join timeouts.
            self.exit.take();
        }
        // Notification precedes thread teardown; never join a thread still running.
        if let Some(thread) = self.thread.as_ref() {
            while !thread.is_finished() {
                if Instant::now() >= deadline {
                    return Err(PoolShutdownError::Timeout);
                }
                thread::yield_now();
            }
        }
        if let Some(thread) = self.thread.take()
            && let Err(panic) = thread.join()
        {
            if let Some(error) = self.cleanup_failure.take() {
                eprintln!("experimental Session cleanup failed before worker panic: {error}");
            }
            return Err(PoolShutdownError::WorkerPanicked(panic));
        }
        self.cleanup_failure.take().map_or(Ok(()), |error| Err(PoolShutdownError::Compute(error)))
    }
}

impl Drop for FileWorkerPool {
    fn drop(&mut self) {
        match self.shutdown() {
            Err(PoolShutdownError::Timeout) => {
                eprintln!(
                    "experimental Session compute worker still running after shutdown grace; detaching"
                );
                if let Some(error) = self.cleanup_failure.as_ref() {
                    eprintln!("experimental Session cleanup failed before detach: {error}");
                }
            },
            Err(PoolShutdownError::WorkerPanicked(_)) => {
                eprintln!("experimental Session compute worker panicked during pool drop");
            },
            Err(PoolShutdownError::Compute(error)) => {
                eprintln!("experimental Session compute process shutdown failed: {error}");
            },
            Ok(()) => {},
        }
    }
}

impl FileWorker {
    // =================================================================
    // Event loop
    // =================================================================

    fn run(
        &mut self,
        cmd: WorkerCommand,
        is_open: &AtomicBool,
        is_stopping: &AtomicBool,
        process_config: &Option<(PathBuf, PathBuf)>,
        process: &mut Option<ComputeProcess>,
        cleanup_failure: &mut Option<ComputeError>,
    ) {
        match cmd {
            WorkerCommand::CheckFile { content, deadline, is_cancelled, reply } => {
                self.successful_check_cancel = None;
                let result = if self.executor.is_builtin_real() {
                    self.handle_process_check(
                        content,
                        ProcessCheckRequest {
                            deadline,
                            is_cancelled: &is_cancelled,
                            is_open,
                            is_stopping,
                            process_config,
                            process,
                            cleanup_failure,
                        },
                    )
                } else {
                    Ok(self.handle_check_file(content, is_open, is_stopping))
                };
                if result.is_ok() {
                    // The caller may time out after the process check's last cancellation
                    // check or even after installation; proof queries must still see it.
                    self.successful_check_cancel = Some(Arc::clone(&is_cancelled));
                }
                if is_active(is_open, is_stopping) && !is_cancelled.load(Ordering::Acquire) {
                    let _ = reply.send(result);
                }
            },
            WorkerCommand::Hover { line, character, reply } => {
                let result = self.handle_hover(line, character);
                if is_active(is_open, is_stopping) {
                    let _ = reply.send(result);
                }
            },
            WorkerCommand::ProofState { line, reply } => {
                let result = self.handle_proof_state(line);
                if is_active(is_open, is_stopping) {
                    let _ = reply.send(result);
                }
            },
        }
    }

    // =================================================================
    // Command handlers
    // =================================================================

    fn handle_process_check(
        &mut self,
        content: String,
        mut request: ProcessCheckRequest<'_>,
    ) -> Result<Vec<Diagnostic>, SessionError> {
        let mut failure = match self.request_process_check(content, &mut request) {
            Ok(diagnostics) => return Ok(diagnostics),
            Err(error) => error,
        };
        self.clear_check_state();
        if !matches!(&failure, SessionError::SourceTooLarge { .. })
            && let Some(mut child) = request.process.take()
            && let Err(stop_error) = child.stop()
        {
            let reason = format!("stopping compute process after {failure:?}: {stop_error}");
            preserve_cleanup_failure(request.cleanup_failure, stop_error);
            failure = SessionError::Compute { uri: self.uri.clone(), reason };
        }
        self.check_error = Some(failure.clone());
        Err(failure)
    }

    fn clear_check_state(&mut self) {
        self.check_ctx = CheckContext::default();
        self.successful_check_cancel = None;
        if let Some(node) = self.document.get_node_mut(&self.uri) {
            node.snapshots.clear();
        }
    }

    fn request_process_check(
        &mut self,
        content: String,
        request: &mut ProcessCheckRequest<'_>,
    ) -> Result<Vec<Diagnostic>, SessionError> {
        if content.len() > MAX_SOURCE {
            return Err(SessionError::SourceTooLarge {
                uri: self.uri.clone(),
                max_bytes: MAX_SOURCE,
            });
        }
        let (executable, cwd) =
            request.process_config.as_ref().ok_or_else(|| SessionError::Compute {
                uri: self.uri.clone(),
                reason: "trusted compute executable not configured".into(),
            })?;
        let deadline = request.deadline;
        let is_cancelled = request.is_cancelled;
        let is_open = request.is_open;
        let is_stopping = request.is_stopping;
        let should_cancel = || {
            !is_active(is_open, is_stopping)
                || is_cancelled.load(Ordering::Acquire)
                || Instant::now() >= deadline
        };
        if request.process.is_none() {
            *request.process =
                Some(ComputeProcess::start_cancellable(executable, cwd, should_cancel).map_err(
                    |error| self.compute_error(error, deadline, request.cleanup_failure),
                )?);
        }
        let version = self.document.version() + 1;
        let worker = request.process.as_mut().ok_or_else(|| SessionError::Compute {
            uri: self.uri.clone(),
            reason: "compute worker missing after startup".into(),
        })?;
        let response = worker
            .request(ComputeRequest::Check { content: content.clone(), version }, should_cancel)
            .map_err(|error| self.compute_error(error, deadline, request.cleanup_failure))?;
        let ComputeResponse::Check(checked) = response else {
            return Err(SessionError::Compute {
                uri: self.uri.clone(),
                reason: "unexpected compute response kind".into(),
            });
        };
        let checked = checked.map_err(|failure| self.check_failure(failure))?;
        if !Fleche::is_valid_process_check(&checked, version) {
            return Err(SessionError::Compute {
                uri: self.uri.clone(),
                reason: "compute worker returned inconsistent snapshots".into(),
            });
        }
        if should_cancel() {
            return Err(SessionError::Timeout(format!(
                "request for {} cancelled or timed out",
                self.uri
            )));
        }
        self.install_checked_document(content, checked)
    }

    fn install_checked_document(
        &mut self,
        content: String,
        checked: ProcessCheck,
    ) -> Result<Vec<Diagnostic>, SessionError> {
        let commands = Arc::new(checked.commands);
        if self.document.get_node(&self.uri).is_none() {
            self.document.open_parsed_file(self.uri.clone(), content, commands);
        } else {
            self.document.update_parsed_file(&self.uri, content, commands);
        }
        let node = self.document.get_node_mut(&self.uri).ok_or_else(|| SessionError::Compute {
            uri: self.uri.clone(),
            reason: "checked document missing after update".into(),
        })?;
        node.snapshots = checked.snapshots;
        self.check_ctx.proof_state =
            node.snapshots.last().and_then(|snap| snap.proof_state.clone());
        self.check_error = None;
        Ok(node.snapshots.iter().flat_map(|snapshot| snapshot.diagnostics.clone()).collect())
    }

    fn compute_error(
        &self,
        error: ComputeError,
        deadline: Instant,
        cleanup_failure: &mut Option<ComputeError>,
    ) -> SessionError {
        let failure = if matches!(error, ComputeError::Cancelled) && Instant::now() >= deadline {
            SessionError::Timeout(format!("request for {} timed out", self.uri))
        } else {
            SessionError::Compute { uri: self.uri.clone(), reason: error.to_string() }
        };
        if matches!(error, ComputeError::Reap(_)) {
            preserve_cleanup_failure(cleanup_failure, error);
        }
        failure
    }

    fn check_failure(&self, failure: CheckFailure) -> SessionError {
        match failure {
            CheckFailure::Source => {
                SessionError::SourceTooLarge { uri: self.uri.clone(), max_bytes: MAX_SOURCE }
            },
            other => SessionError::Compute {
                uri: self.uri.clone(),
                reason: format!("compute check failed: {other:?}"),
            },
        }
    }

    /// Handle a CheckFile command: update the document, parse commands,
    /// execute via the kernel, and return diagnostics.
    fn handle_check_file(
        &mut self,
        content: String,
        is_open: &AtomicBool,
        is_stopping: &AtomicBool,
    ) -> Vec<Diagnostic> {
        // A retained snapshot does not include the complete CheckContext.
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

        node.snapshots.clear();
        self.check_ctx = CheckContext::default();
        for cmd in node.commands.iter() {
            if !is_active(is_open, is_stopping) {
                break;
            }
            let diags = self.executor.execute(cmd, &mut self.check_ctx);
            let mut snap = Snapshot::new(cmd.id, node.version);
            snap.diagnostics = diags;
            snap.proof_state = self.check_ctx.proof_state.clone();
            snap.context_hash = self.check_ctx.context_hash;
            node.snapshots.push(snap);
        }

        node.snapshots.iter().flat_map(|snapshot| snapshot.diagnostics.clone()).collect()
    }

    /// Hover is not supported until positions can be mapped to checked terms.
    fn handle_hover(&self, _line: u32, _character: u32) -> Option<String> {
        None
    }

    /// Handle a ProofState command: look up proof state at a position.
    fn handle_proof_state(&mut self, _line: u32) -> Result<Option<ProofState>, SessionError> {
        if self.successful_check_cancel.as_ref().is_some_and(|token| token.load(Ordering::Acquire))
        {
            self.clear_check_state();
        }
        if let Some(error) = &self.check_error {
            return Err(error.clone());
        }
        Ok(self.check_ctx.proof_state.as_deref().cloned())
    }
}

impl FileWorkerHandle {
    /// Attempt to enqueue a command without blocking on another file's check.
    pub fn send(&self, cmd: WorkerCommand) -> Result<(), WorkerSendError> {
        let admission = self.admission.sender.lock().unwrap_or_else(|error| error.into_inner());
        if self.admission.is_stopping.load(Ordering::Acquire)
            || !self.is_open.load(Ordering::Acquire)
        {
            return Err(WorkerSendError::WorkerGone);
        }
        let sender = admission.as_ref().ok_or(WorkerSendError::WorkerGone)?;
        sender
            .try_send(WorkItem {
                worker: Arc::clone(&self.worker),
                is_open: Arc::clone(&self.is_open),
                command: cmd,
            })
            .map_err(|error| match error {
                TrySendError::Full(_) => WorkerSendError::QueueFull,
                TrySendError::Disconnected(_) => WorkerSendError::WorkerGone,
            })
    }

    /// Invalidate outstanding work, including a check currently in progress.
    pub fn shutdown(&self) {
        self.is_open.store(false, Ordering::Release);
    }

    pub fn uri(&self) -> &str {
        &self.uri
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::document::Command;
    const WAIT_LIMIT: Duration = Duration::from_secs(5);

    #[derive(Clone)]
    struct BlockingExecutor {
        started: Arc<Mutex<Option<mpsc::Sender<()>>>>,
        release: Arc<Mutex<mpsc::Receiver<()>>>,
        calls: Arc<Mutex<Vec<String>>>,
    }

    impl CommandExecutor for BlockingExecutor {
        fn execute(&self, command: &Command, _ctx: &mut CheckContext) -> Vec<Diagnostic> {
            let started = self.started.lock().unwrap_or_else(|error| error.into_inner()).take();
            if let Some(started) = started {
                started.send(()).unwrap();
                self.release
                    .lock()
                    .unwrap_or_else(|error| error.into_inner())
                    .recv_timeout(WAIT_LIMIT)
                    .unwrap();
            }
            self.calls
                .lock()
                .unwrap_or_else(|error| error.into_inner())
                .push(command.source.clone());
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

    struct PanickingExecutor;

    impl CommandExecutor for PanickingExecutor {
        fn execute(&self, _command: &Command, _ctx: &mut CheckContext) -> Vec<Diagnostic> {
            panic!("controlled test worker failure")
        }

        fn clone_box(&self) -> Box<dyn CommandExecutor> {
            Box::new(Self)
        }
    }

    fn send_check(
        handle: &FileWorkerHandle,
        content: &str,
    ) -> mpsc::Receiver<Result<Vec<Diagnostic>, SessionError>> {
        send_check_with_token(handle, content, Arc::new(AtomicBool::new(false)))
    }

    fn send_check_with_token(
        handle: &FileWorkerHandle,
        content: &str,
        is_cancelled: Arc<AtomicBool>,
    ) -> mpsc::Receiver<Result<Vec<Diagnostic>, SessionError>> {
        let (reply, receiver) = mpsc::channel();
        handle
            .send(WorkerCommand::CheckFile {
                content: content.into(),
                deadline: Instant::now() + WAIT_LIMIT,
                is_cancelled,
                reply,
            })
            .unwrap();
        receiver
    }

    fn request_proof_state(handle: &FileWorkerHandle) -> Option<ProofState> {
        let (reply, receiver) = mpsc::channel();
        handle.send(WorkerCommand::ProofState { line: 0, reply }).unwrap();
        receiver.recv_timeout(WAIT_LIMIT).unwrap().unwrap()
    }

    #[test]
    fn worker_pool_cancelled_success_discards_proof_and_recovers_on_next_check() {
        let mut pool = FileWorkerPool::new();
        let executor =
            CooperativeRealExecutor(Arc::new(crate::fleche::engine::RealExecutor::new()));
        let handle = pool.open("file:///cancelled.thy".into(), Box::new(executor));
        let is_cancelled = Arc::new(AtomicBool::new(false));

        send_check_with_token(&handle, "lemma pending: \"A\"", Arc::clone(&is_cancelled))
            .recv_timeout(WAIT_LIMIT)
            .unwrap()
            .unwrap();
        assert!(request_proof_state(&handle).is_some());

        // The caller can time out after the check was installed and replied to.
        is_cancelled.store(true, Ordering::Release);
        assert!(request_proof_state(&handle).is_none());
        assert!(request_proof_state(&handle).is_none());

        send_check(&handle, "lemma fresh: \"B\"").recv_timeout(WAIT_LIMIT).unwrap().unwrap();
        assert!(request_proof_state(&handle).is_some());
        pool.shutdown().unwrap();
    }

    #[test]
    fn worker_pool_saturated_queue_reports_error_and_joins() {
        let (started_tx, started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let release = Arc::new(Mutex::new(release_rx));
        let executor = BlockingExecutor {
            started: Arc::new(Mutex::new(Some(started_tx))),
            release: Arc::clone(&release),
            calls: Arc::new(Mutex::new(Vec::new())),
        };
        let mut pool = FileWorkerPool::new();
        let handle = pool.open("file:///busy.thy".into(), Box::new(executor.clone()));
        let waiting = pool.open("file:///waiting.thy".into(), Box::new(executor.clone()));
        let rejected_handle = pool.open("file:///rejected.thy".into(), Box::new(executor));
        let first = send_check(&handle, "theory Active");
        started_rx.recv_timeout(WAIT_LIMIT).unwrap();
        let queued = send_check(&waiting, "theory Waiting");
        let (reply, rejected) = mpsc::channel();
        let failure = rejected_handle.send(WorkerCommand::Hover { line: 0, character: 0, reply });
        let is_stopping = Arc::clone(&pool.admission.is_stopping);
        let join = thread::spawn(move || pool.shutdown());
        let deadline = Instant::now() + WAIT_LIMIT;
        while !is_stopping.load(Ordering::Acquire) {
            assert!(Instant::now() < deadline, "shutdown did not stop admission");
            thread::yield_now();
        }
        release_tx.send(()).unwrap();

        assert_eq!(failure, Err(WorkerSendError::QueueFull));
        join.join().unwrap().unwrap();
        assert!(matches!(
            handle.send(WorkerCommand::Hover { line: 0, character: 0, reply: mpsc::channel().0 }),
            Err(WorkerSendError::WorkerGone)
        ));
        assert!(matches!(first.recv_timeout(WAIT_LIMIT), Err(RecvTimeoutError::Disconnected)));
        assert!(matches!(queued.recv_timeout(WAIT_LIMIT), Err(RecvTimeoutError::Disconnected)));
        assert!(matches!(rejected.recv_timeout(WAIT_LIMIT), Err(RecvTimeoutError::Disconnected)));
    }

    #[test]
    fn worker_pool_closed_generation_cannot_publish_into_reopened_file() {
        let (started_tx, started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let release = Arc::new(Mutex::new(release_rx));
        let calls = Arc::new(Mutex::new(Vec::new()));
        let executor = BlockingExecutor {
            started: Arc::new(Mutex::new(Some(started_tx))),
            release: Arc::clone(&release),
            calls: Arc::clone(&calls),
        };
        let mut pool = FileWorkerPool::new();
        let old = pool.open("file:///same.thy".into(), Box::new(executor.clone()));
        let running = send_check(&old, "theory Active");
        started_rx.recv_timeout(WAIT_LIMIT).unwrap();
        let stale = send_check(&old, "theory Stale");
        old.shutdown();
        release_tx.send(()).unwrap();
        assert!(matches!(running.recv_timeout(WAIT_LIMIT), Err(RecvTimeoutError::Disconnected)));
        assert!(matches!(stale.recv_timeout(WAIT_LIMIT), Err(RecvTimeoutError::Disconnected)));

        let fresh = pool.open("file:///same.thy".into(), Box::new(executor));
        assert!(
            send_check(&fresh, "theory Fresh")
                .recv_timeout(WAIT_LIMIT)
                .unwrap()
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            *calls.lock().unwrap_or_else(|error| error.into_inner()),
            ["theory Active", "theory Fresh"]
        );
        pool.shutdown().unwrap();
    }

    #[test]
    fn worker_pool_shutdown_join_timeout_preserves_cleanup_error_on_retry() {
        let (exit_tx, exit) = mpsc::channel();
        let (ready_tx, ready_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let worker = thread::spawn(move || {
            let error = std::io::Error::new(
                std::io::ErrorKind::PermissionDenied,
                "controlled child reaping failure",
            );
            exit_tx.send(Err(ComputeError::Reap(error))).unwrap();
            ready_tx.send(()).unwrap();
            release_rx.recv_timeout(WAIT_LIMIT).unwrap();
        });
        let mut pool = FileWorkerPool {
            admission: Arc::new(PoolAdmission {
                sender: Mutex::new(None),
                is_stopping: Arc::new(AtomicBool::new(false)),
            }),
            exit: Some(exit),
            cleanup_failure: None,
            thread: Some(worker),
        };
        ready_rx.recv_timeout(WAIT_LIMIT).unwrap();

        let first = pool.shutdown();
        release_tx.send(()).unwrap();
        let deadline = Instant::now() + WAIT_LIMIT;
        while !pool.thread.as_ref().unwrap().is_finished() {
            assert!(Instant::now() < deadline, "released worker did not exit");
            thread::yield_now();
        }
        assert!(matches!(first, Err(PoolShutdownError::Timeout)));
        assert!(matches!(
            pool.shutdown(),
            Err(PoolShutdownError::Compute(ComputeError::Reap(error)))
                if error.kind() == std::io::ErrorKind::PermissionDenied
        ));
    }

    #[test]
    fn worker_pool_crashed_worker_reports_exit() {
        let mut pool = FileWorkerPool::new();
        let handle = pool.open("file:///crash.thy".into(), Box::new(PanickingExecutor));
        assert!(matches!(
            send_check(&handle, "theory Crash").recv_timeout(WAIT_LIMIT),
            Err(RecvTimeoutError::Disconnected)
        ));
        let (reply, _) = mpsc::channel();
        assert_eq!(
            handle.send(WorkerCommand::Hover { line: 0, character: 0, reply }),
            Err(WorkerSendError::WorkerGone)
        );
        assert!(pool.shutdown().is_err());
    }

    #[test]
    fn worker_pool_drop_blocked_check_detaches_without_joining() {
        let (started_tx, started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let release = Arc::new(Mutex::new(release_rx));
        let executor = BlockingExecutor {
            started: Arc::new(Mutex::new(Some(started_tx))),
            release: Arc::clone(&release),
            calls: Arc::new(Mutex::new(Vec::new())),
        };
        let pool = FileWorkerPool::new();
        let handle = pool.open("file:///blocked.thy".into(), Box::new(executor));
        let running = send_check(&handle, "theory Blocked");
        started_rx.recv_timeout(WAIT_LIMIT).unwrap();
        drop(pool);

        let (reply, _) = mpsc::channel();
        assert_eq!(
            handle.send(WorkerCommand::Hover { line: 0, character: 0, reply }),
            Err(WorkerSendError::WorkerGone)
        );
        release_tx.send(()).unwrap();
        assert!(matches!(running.recv_timeout(WAIT_LIMIT), Err(RecvTimeoutError::Disconnected)));
    }
}
