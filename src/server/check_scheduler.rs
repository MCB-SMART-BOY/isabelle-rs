//! Bounded CPU scheduling for experimental LSP checks and definition queries.
//!
//! The protocol loop owns mutations and replies. The worker receives immutable
//! query inputs; Fleche validates check generations at commit.

use crate::{
    compute_worker::{CheckFailure, ComputeError, ComputeProcess, ComputeRequest, ComputeResponse},
    fleche::engine::{CheckJob, CheckResult, Fleche},
    hol::hol_loader::HolTheoremDb,
};
use std::{
    io,
    path::PathBuf,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
        mpsc::{self, Receiver, SyncSender, TrySendError},
    },
    thread::{self, JoinHandle},
    time::Duration,
};

use super::{
    lsp_types::{Location, Position, Range, RequestId},
    transport::IncomingMessage,
};

// One CPU worker limits simultaneous legacy search and its memory footprint.
const PENDING_WORK_CAPACITY: usize = 2;
const SHUTDOWN_GRACE: Duration = Duration::from_secs(1);
const SEND_RETRY: Duration = Duration::from_millis(10);

#[derive(Debug, thiserror::Error)]
pub enum ScheduleError {
    #[error("LSP CPU work queue is full")]
    QueueFull,
    #[error("LSP CPU worker has stopped")]
    WorkerGone,
}

pub struct DefinitionQuery {
    pub id: RequestId,
    pub uri: String,
    pub word: String,
    pub cancellation: Arc<AtomicBool>,
}

enum Work {
    Check(CheckJob),
    Definition(DefinitionQuery),
}
struct WorkerConfig {
    executable: PathBuf,
    cwd: PathBuf,
}

pub struct CheckScheduler {
    sender: Option<SyncSender<Work>>,
    cancelled: Arc<AtomicBool>,
    failed: Arc<AtomicBool>,
    worker: Option<JoinHandle<()>>,
    exited: Receiver<io::Result<()>>,
}

impl CheckScheduler {
    pub fn new(
        fleche: Arc<Fleche>,
        completed: SyncSender<IncomingMessage>,
        executable: PathBuf,
    ) -> io::Result<Self> {
        // Explicitly supplied by the LSP launcher: never guess an embedding
        // application's binary as the compute worker.
        let config = Some(WorkerConfig { executable, cwd: std::env::current_dir()? });
        Self::new_with_config(fleche, completed, Self::lookup_definition, config)
    }

    // Injectable lookup remains for cooperative custom-executor tests.
    #[cfg(test)]
    fn new_with_lookup(
        fleche: Arc<Fleche>,
        completed: SyncSender<IncomingMessage>,
        lookup: impl Fn(&DefinitionQuery) -> Option<Location> + Send + 'static,
    ) -> io::Result<Self> {
        Self::new_with_config(fleche, completed, lookup, None)
    }

    fn new_with_config(
        fleche: Arc<Fleche>,
        completed: SyncSender<IncomingMessage>,
        lookup: impl Fn(&DefinitionQuery) -> Option<Location> + Send + 'static,
        config: Option<WorkerConfig>,
    ) -> io::Result<Self> {
        let (sender, receiver) = mpsc::sync_channel(PENDING_WORK_CAPACITY);
        let (exited_tx, exited) = mpsc::sync_channel(1);
        let cancelled = Arc::new(AtomicBool::new(false));
        let failed = Arc::new(AtomicBool::new(false));
        let worker_cancelled = Arc::clone(&cancelled);
        let worker_failed = Arc::clone(&failed);
        let worker =
            thread::Builder::new().name("isabelle-document-check".into()).spawn(move || {
                let result = Self::run_worker(
                    fleche,
                    receiver,
                    completed,
                    worker_cancelled,
                    worker_failed,
                    lookup,
                    config,
                );
                let _ = exited_tx.send(result);
            })?;
        Ok(Self { sender: Some(sender), cancelled, failed, worker: Some(worker), exited })
    }

    pub fn schedule(&self, job: CheckJob) -> Result<(), ScheduleError> {
        self.schedule_work(Work::Check(job))
    }

    pub fn schedule_definition(&self, query: DefinitionQuery) -> Result<(), ScheduleError> {
        self.schedule_work(Work::Definition(query))
    }

    fn schedule_work(&self, work: Work) -> Result<(), ScheduleError> {
        if self.cancelled.load(Ordering::Acquire) || self.failed.load(Ordering::Acquire) {
            return Err(ScheduleError::WorkerGone);
        }
        match self.sender.as_ref().ok_or(ScheduleError::WorkerGone)?.try_send(work) {
            Ok(()) => Ok(()),
            Err(TrySendError::Full(_)) => Err(ScheduleError::QueueFull),
            Err(TrySendError::Disconnected(_)) => Err(ScheduleError::WorkerGone),
        }
    }

    fn run_worker(
        fleche: Arc<Fleche>,
        receiver: Receiver<Work>,
        completed: SyncSender<IncomingMessage>,
        cancelled: Arc<AtomicBool>,
        failed: Arc<AtomicBool>,
        lookup: impl Fn(&DefinitionQuery) -> Option<Location>,
        config: Option<WorkerConfig>,
    ) -> io::Result<()> {
        let mut process = None;
        let mut cleanup_failure = None;
        while let Ok(work) = receiver.recv() {
            if cancelled.load(Ordering::Acquire) {
                break;
            }
            let message = Self::handle_work(
                work,
                &fleche,
                &lookup,
                &config,
                &cancelled,
                &mut process,
                &mut cleanup_failure,
            );
            if cancelled.load(Ordering::Acquire) {
                break;
            }
            if let Some(message) = message
                && !Self::send_completion(&completed, message, &cancelled)
            {
                break;
            }
            if let Some(error) = cleanup_failure.as_ref() {
                failed.store(true, Ordering::Release);
                let _ = Self::send_completion(
                    &completed,
                    IncomingMessage::WorkerFailed(error.to_string()),
                    &cancelled,
                );
                break;
            }
        }
        Self::finish_process(process, cleanup_failure)
    }

    fn handle_work(
        work: Work,
        fleche: &Fleche,
        lookup: &impl Fn(&DefinitionQuery) -> Option<Location>,
        config: &Option<WorkerConfig>,
        cancelled: &AtomicBool,
        process: &mut Option<ComputeProcess>,
        cleanup_failure: &mut Option<ComputeError>,
    ) -> Option<IncomingMessage> {
        match work {
            Work::Check(job) => match config {
                Some(config) if fleche.uses_builtin_real() => {
                    Self::check_in_process(fleche, job, cancelled, config, process, cleanup_failure)
                },
                _ => fleche.run_snapshot_cancellable(job, cancelled),
            }
            .map(IncomingMessage::CheckComplete),
            Work::Definition(query) => {
                if query.cancellation.load(Ordering::Acquire) {
                    return None;
                }
                let result = match config {
                    Some(config) => Self::definition_in_process(
                        &query,
                        cancelled,
                        config,
                        process,
                        cleanup_failure,
                    ),
                    None => Ok(lookup(&query)),
                };
                if query.cancellation.load(Ordering::Acquire) {
                    return None;
                }
                Some(IncomingMessage::DefinitionComplete {
                    id: query.id,
                    cancellation: query.cancellation,
                    result,
                })
            },
        }
    }

    fn finish_process(
        process: Option<ComputeProcess>,
        cleanup_failure: Option<ComputeError>,
    ) -> io::Result<()> {
        if let Some(mut worker) = process {
            worker
                .stop()
                .map_err(|error| io::Error::other(format!("stopping compute worker: {error}")))?;
        }
        match cleanup_failure {
            Some(error) => Err(io::Error::other(error)),
            None => Ok(()),
        }
    }

    fn send_completion(
        completed: &SyncSender<IncomingMessage>,
        mut message: IncomingMessage,
        cancelled: &AtomicBool,
    ) -> bool {
        loop {
            if cancelled.load(Ordering::Acquire) {
                return false;
            }
            match completed.try_send(message) {
                Ok(()) => return true,
                Err(TrySendError::Disconnected(_)) => return false,
                Err(TrySendError::Full(queued)) => message = queued,
            }
            thread::park_timeout(SEND_RETRY);
        }
    }

    fn request_process(
        config: &WorkerConfig,
        process: &mut Option<ComputeProcess>,
        request: ComputeRequest,
        cancelled: impl Fn() -> bool,
        cleanup_failure: &mut Option<ComputeError>,
    ) -> Result<ComputeResponse, String> {
        if cancelled() {
            return Err("request cancelled".into());
        }
        if process.is_none() {
            *process = Some(
                ComputeProcess::start_cancellable(&config.executable, &config.cwd, &cancelled)
                    .map_err(|error| Self::record_failure(error, cleanup_failure))?,
            );
        }
        let response = process
            .as_mut()
            .ok_or("compute worker unavailable")?
            .request(request, cancelled)
            .map_err(|error| Self::record_failure(error, cleanup_failure));
        if response.is_err()
            && let Some(mut worker) = process.take()
            && let Err(error) = worker.stop()
        {
            cleanup_failure.get_or_insert(error);
        }
        response
    }

    fn record_failure(error: ComputeError, cleanup_failure: &mut Option<ComputeError>) -> String {
        let reason = error.to_string();
        if matches!(error, ComputeError::Reap(_)) {
            cleanup_failure.get_or_insert(error);
        }
        reason
    }

    fn check_in_process(
        fleche: &Fleche,
        job: CheckJob,
        cancelled: &AtomicBool,
        config: &WorkerConfig,
        process: &mut Option<ComputeProcess>,
        cleanup_failure: &mut Option<ComputeError>,
    ) -> Option<CheckResult> {
        let content = fleche.prepare_process_input(&job)?;
        let request = ComputeRequest::Check { content, version: job.version() };
        let response = Self::request_process(
            config,
            process,
            request,
            || cancelled.load(Ordering::Acquire) || job.is_cancelled(),
            cleanup_failure,
        );
        if cancelled.load(Ordering::Acquire) || job.is_cancelled() {
            return None;
        }
        let check = match response {
            Ok(ComputeResponse::Check(result)) => result,
            Ok(_) => Err(CheckFailure::Worker("unexpected compute response".into())),
            Err(error) => Err(CheckFailure::Worker(error)),
        };
        Some(fleche.complete_process_check(job, check))
    }

    fn definition_in_process(
        query: &DefinitionQuery,
        cancelled: &AtomicBool,
        config: &WorkerConfig,
        process: &mut Option<ComputeProcess>,
        cleanup_failure: &mut Option<ComputeError>,
    ) -> Result<Option<Location>, String> {
        let request =
            ComputeRequest::Definition { uri: query.uri.clone(), word: query.word.clone() };
        match Self::request_process(
            config,
            process,
            request,
            || cancelled.load(Ordering::Acquire) || query.cancellation.load(Ordering::Acquire),
            cleanup_failure,
        )? {
            ComputeResponse::Definition(location) => Ok(location),
            _ => Err("unexpected compute response to definition request".into()),
        }
    }

    fn lookup_definition(query: &DefinitionQuery) -> Option<Location> {
        let location = HolTheoremDb::global().get_definition_location(&query.word)?;
        let uri = if location.file == "<unknown>" {
            query.uri.clone()
        } else if location.file.starts_with("file://") {
            location.file.clone()
        } else if location.file.starts_with('/') {
            format!("file://{}", location.file)
        } else {
            format!("file:///{}", location.file)
        };
        let position = Position { line: (location.line as u32).saturating_sub(1), character: 0 };
        Some(Location { uri, range: Range { start: position.clone(), end: position } })
    }

    /// Stop admission independently of the bounded work queue; join if cooperative.
    pub fn shutdown(mut self) -> io::Result<()> {
        self.cancelled.store(true, Ordering::Release);
        self.sender.take();
        let exited = self.exited.recv_timeout(SHUTDOWN_GRACE);
        let worker = self.worker.take().expect("scheduler owns exactly one worker");
        match exited {
            Ok(cleanup) => {
                worker.join().map_err(|_| io::Error::other("document check worker panicked"))?;
                cleanup
            },
            Err(mpsc::RecvTimeoutError::Timeout) => Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "document check did not stop within the shutdown grace period",
            )),
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                worker.join().map_err(|_| io::Error::other("document check worker panicked"))?;
                Err(io::Error::other("document check worker exited without shutdown result"))
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::{
        Barrier,
        atomic::{AtomicBool, AtomicUsize, Ordering},
    };

    use super::*;
    use crate::{
        document::Command,
        fleche::engine::{CheckContext, CommandExecutor},
        server::lsp_types::Diagnostic,
    };

    struct BlockingExecutor {
        started: SyncSender<()>,
        release: Arc<AtomicBool>,
        calls: Arc<AtomicUsize>,
    }

    impl CommandExecutor for BlockingExecutor {
        fn execute(&self, _: &Command, _: &mut CheckContext) -> Vec<Diagnostic> {
            if self.calls.fetch_add(1, Ordering::SeqCst) == 0 {
                self.started.send(()).unwrap();
                let deadline = std::time::Instant::now() + Duration::from_secs(5);
                while !self.release.load(Ordering::Acquire) {
                    assert!(std::time::Instant::now() < deadline, "test executor was not released");
                    std::thread::yield_now();
                }
            }
            Vec::new()
        }

        fn clone_box(&self) -> Box<dyn CommandExecutor> {
            Box::new(Self {
                started: self.started.clone(),
                release: Arc::clone(&self.release),
                calls: Arc::clone(&self.calls),
            })
        }
    }

    struct BarrierExecutor {
        reached: Arc<Barrier>,
        resume: Arc<Barrier>,
        calls: Arc<AtomicUsize>,
    }

    impl CommandExecutor for BarrierExecutor {
        fn execute(&self, _: &Command, _: &mut CheckContext) -> Vec<Diagnostic> {
            if self.calls.fetch_add(1, Ordering::SeqCst) == 0 {
                self.reached.wait();
                self.resume.wait();
            }
            Vec::new()
        }

        fn clone_box(&self) -> Box<dyn CommandExecutor> {
            Box::new(Self {
                reached: Arc::clone(&self.reached),
                resume: Arc::clone(&self.resume),
                calls: Arc::clone(&self.calls),
            })
        }
    }

    #[test]
    fn scheduler_queued_canceled_definition_skips_lookup() {
        let reached = Arc::new(Barrier::new(2));
        let resume = Arc::new(Barrier::new(2));
        let executor = BarrierExecutor {
            reached: Arc::clone(&reached),
            resume: Arc::clone(&resume),
            calls: Arc::new(AtomicUsize::new(0)),
        };
        let fleche = Arc::new(Fleche::new(Arc::new(executor)));
        let (complete_tx, complete_rx) = mpsc::sync_channel(4);
        let lookups = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&lookups);
        let pool = CheckScheduler::new_with_lookup(Arc::clone(&fleche), complete_tx, move |_| {
            observed.fetch_add(1, Ordering::SeqCst);
            None
        })
        .unwrap();
        pool.schedule(fleche.open_snapshot("file:///blocking.thy", "theory Blocking\nbegin"))
            .unwrap();
        reached.wait();
        let cancellation = Arc::new(AtomicBool::new(false));
        pool.schedule_definition(DefinitionQuery {
            id: RequestId::Number(1),
            uri: "file:///blocking.thy".into(),
            word: "Blocking".into(),
            cancellation: Arc::clone(&cancellation),
        })
        .unwrap();
        pool.schedule(fleche.open_snapshot("file:///after.thy", "theory After\nbegin")).unwrap();
        cancellation.store(true, Ordering::Release);
        resume.wait();
        for _ in 0..2 {
            assert!(matches!(
                complete_rx.recv_timeout(Duration::from_secs(5)).unwrap(),
                IncomingMessage::CheckComplete(_)
            ));
        }
        assert_eq!(lookups.load(Ordering::SeqCst), 0);
        pool.shutdown().unwrap();
    }

    #[test]
    fn scheduler_occupied_worker_and_full_queue_reports_rejection() {
        let (started_tx, started_rx) = mpsc::sync_channel(1);
        let release = Arc::new(AtomicBool::new(false));
        let executor = BlockingExecutor {
            started: started_tx,
            release: Arc::clone(&release),
            calls: Arc::new(AtomicUsize::new(0)),
        };
        let fleche = Arc::new(Fleche::new(Arc::new(executor)));
        let (complete_tx, _complete_rx) = mpsc::sync_channel(4);
        let pool = CheckScheduler::new_with_lookup(
            Arc::clone(&fleche),
            complete_tx,
            CheckScheduler::lookup_definition,
        )
        .unwrap();
        pool.schedule(fleche.open_snapshot("file:///one.thy", "theory One\nbegin")).unwrap();
        started_rx.recv_timeout(Duration::from_secs(5)).unwrap();

        for index in 0..PENDING_WORK_CAPACITY {
            pool.schedule(
                fleche.open_snapshot(&format!("file:///{index}.thy"), "theory Other\nbegin"),
            )
            .unwrap();
        }
        let rejected = fleche.open_snapshot("file:///overflow.thy", "theory Overflow\nbegin");
        assert!(matches!(pool.schedule(rejected), Err(ScheduleError::QueueFull)));

        release.store(true, Ordering::Release);
        pool.shutdown().unwrap();
    }

    #[test]
    fn scheduler_superseded_document_keeps_worker_alive() {
        let (started_tx, started_rx) = mpsc::sync_channel(1);
        let release = Arc::new(AtomicBool::new(false));
        let executor = BlockingExecutor {
            started: started_tx,
            release: Arc::clone(&release),
            calls: Arc::new(AtomicUsize::new(0)),
        };
        let fleche = Arc::new(Fleche::new(Arc::new(executor)));
        let (complete_tx, complete_rx) = mpsc::sync_channel(2);
        let pool = CheckScheduler::new_with_lookup(
            Arc::clone(&fleche),
            complete_tx,
            CheckScheduler::lookup_definition,
        )
        .unwrap();
        let uri = "file:///replaced.thy";
        pool.schedule(fleche.open_snapshot(uri, "theory Old\nbegin")).unwrap();
        started_rx.recv_timeout(Duration::from_secs(5)).unwrap();
        pool.schedule(fleche.update_snapshot(uri, "theory New\nbegin")).unwrap();
        release.store(true, Ordering::Release);

        let next = complete_rx.recv_timeout(Duration::from_secs(5)).expect("new check completes");
        let IncomingMessage::CheckComplete(result) = next else {
            panic!("scheduler only sends check completions");
        };
        assert_eq!(result.uri(), uri);
        assert!(fleche.commit_snapshot(result).is_some());
        pool.schedule(fleche.open_snapshot("file:///third.thy", "theory Third")).unwrap();
        assert!(complete_rx.recv_timeout(Duration::from_secs(5)).is_ok());
        pool.shutdown().unwrap();
    }

    #[test]
    fn scheduler_failed_child_start_reports_unavailable_check() {
        let fleche = Arc::new(Fleche::new(Arc::new(crate::fleche::engine::RealExecutor::new())));
        let (completed, receiver) = mpsc::sync_channel(1);
        let pool = CheckScheduler::new_with_config(
            Arc::clone(&fleche),
            completed,
            CheckScheduler::lookup_definition,
            Some(WorkerConfig {
                executable: PathBuf::new(),
                cwd: std::env::current_dir().unwrap(),
            }),
        )
        .unwrap();
        pool.schedule(fleche.open_snapshot("file:///unavailable.thy", "theory Unavailable"))
            .unwrap();
        let IncomingMessage::CheckComplete(result) =
            receiver.recv_timeout(Duration::from_secs(5)).unwrap()
        else {
            panic!("expected check completion");
        };
        let diagnostics = fleche.commit_snapshot(result).expect("current revision");
        assert_eq!(diagnostics[0].code.as_deref(), Some("document-check-unavailable"));
        assert!(diagnostics[0].message.contains("failed to start compute worker"));
        pool.shutdown().unwrap();
    }
}
