use super::runtime::{verify_resource_events, verify_startup_report};
use super::*;
use crate::ml::host::lifecycle::LifecycleErrorKind;
use std::os::fd::AsRawFd;
use std::os::unix::net::UnixStream;
use std::process::{Child, ChildStdin, ChildStdout, ExitStatus};
use std::sync::{Arc, Condvar, Mutex};

const F_GETFL: i32 = 3;
const F_SETFL: i32 = 4;
const STREAM_CHUNK: usize = 8192;
const IO_QUANTUM_CHUNKS: usize = 64;
const MAX_REPORT: usize = 4096;
const CGROUP_EVENTS_BYTES: usize = 4096;

fn nonblocking(fd: RawFd, label: &'static str) -> Result<(), SolverError> {
    // SAFETY: fcntl changes only the owned pipe/socket descriptor flags.
    let flags = unsafe { fcntl(fd, F_GETFL) };
    if flags < 0 || unsafe { fcntl(fd, F_SETFL, flags | O_NONBLOCK) } < 0 {
        return Err(SolverError::io(
            SolverErrorKind::System,
            "set nonblocking solver stream",
            label,
            io::Error::last_os_error(),
        ));
    }
    Ok(())
}

struct Streams {
    stdin: Option<ChildStdin>,
    stdout: Option<ChildStdout>,
    report: Option<UnixStream>,
    input: Vec<u8>,
    written: usize,
    output: Vec<u8>,
    report_bytes: Vec<u8>,
}

impl Streams {
    fn new(child: &mut Child, report: UnixStream, input: Vec<u8>) -> Result<Self, SolverError> {
        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| prerequisite("supervise launcher", "missing stdin pipe"))?;
        let stdout = child
            .stdout
            .take()
            .ok_or_else(|| prerequisite("supervise launcher", "missing stdout pipe"))?;
        nonblocking(stdin.as_raw_fd(), "stdin pipe")?;
        nonblocking(stdout.as_raw_fd(), "merged output pipe")?;
        nonblocking(report.as_raw_fd(), "startup report socket")?;
        Ok(Self {
            stdin: Some(stdin),
            stdout: Some(stdout),
            report: Some(report),
            input,
            written: 0,
            output: Vec::new(),
            report_bytes: Vec::new(),
        })
    }

    fn pump_input(&mut self) -> Result<(), SolverError> {
        for _ in 0..IO_QUANTUM_CHUNKS {
            if self.written == self.input.len() {
                self.stdin.take();
                return Ok(());
            }
            let Some(stdin) = self.stdin.as_mut() else {
                return Ok(());
            };
            let end = (self.written + STREAM_CHUNK).min(self.input.len());
            match stdin.write(&self.input[self.written..end]) {
                Ok(0) => {
                    return Err(prerequisite(
                        "send solver input",
                        "stdin closed before input completed",
                    ));
                },
                Ok(count) => self.written += count,
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => break,
                Err(error) => {
                    return Err(SolverError::io(
                        SolverErrorKind::System,
                        "send solver input",
                        "stdin pipe",
                        error,
                    ));
                },
            }
        }
        if self.written == self.input.len() {
            self.stdin.take();
        }
        Ok(())
    }

    fn pump_output(&mut self) -> Result<(), SolverError> {
        let mut buffer = [0u8; STREAM_CHUNK];
        for _ in 0..IO_QUANTUM_CHUNKS {
            let Some(stdout) = self.stdout.as_mut() else {
                break;
            };
            match stdout.read(&mut buffer) {
                Ok(0) => {
                    self.stdout.take();
                    break;
                },
                Ok(count) if count <= MAX_OUTPUT - self.output.len() => {
                    self.output.extend_from_slice(&buffer[..count])
                },
                Ok(_) => {
                    return Err(SolverError::new(
                        SolverErrorKind::ResourceLimit,
                        "collect veriT output",
                        "256 MiB combined output bound exceeded",
                    ));
                },
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => break,
                Err(error) => {
                    return Err(SolverError::io(
                        SolverErrorKind::System,
                        "read veriT output",
                        "merged pipe",
                        error,
                    ));
                },
            }
        }
        Ok(())
    }

    fn pump_report(&mut self) -> Result<(), SolverError> {
        let Some(report) = self.report.as_mut() else {
            return Ok(());
        };
        let mut buffer = [0u8; STREAM_CHUNK];
        match report.read(&mut buffer) {
            Ok(0) => {
                self.report.take();
            },
            Ok(count) if count <= MAX_REPORT - self.report_bytes.len() => {
                self.report_bytes.extend_from_slice(&buffer[..count])
            },
            Ok(_) => {
                return Err(prerequisite(
                    "verify bwrap startup",
                    "status report exceeds expected bound",
                ));
            },
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => (),
            Err(error) => {
                return Err(SolverError::io(
                    SolverErrorKind::System,
                    "read bwrap status fd",
                    "trusted startup report",
                    error,
                ));
            },
        }
        Ok(())
    }

    fn is_done(&self) -> bool {
        self.stdin.is_none() && self.stdout.is_none() && self.report.is_none()
    }
}

fn check_population(domain: &Path) -> Result<bool, SolverError> {
    let path = domain.join("cgroup.events");
    let mut events = OpenOptions::new()
        .read(true)
        .custom_flags(O_NONBLOCK | O_NOFOLLOW)
        .open(&path)
        .map_err(|error| system("open cgroup population", &path, error))?;
    let mut bytes = [0u8; CGROUP_EVENTS_BYTES + 1];
    let count =
        events.read(&mut bytes).map_err(|error| system("read cgroup population", &path, error))?;
    if count > CGROUP_EVENTS_BYTES {
        return Err(prerequisite(
            "read cgroup population",
            format!("{} exceeds event bound", path.display()),
        ));
    }
    let text = std::str::from_utf8(&bytes[..count]).map_err(|error| {
        prerequisite("read cgroup population", format!("{} is not UTF-8: {error}", path.display()))
    })?;
    if text.lines().any(|line| line == "populated 0") {
        return Ok(false);
    }
    if text.lines().any(|line| line == "populated 1") {
        return Ok(true);
    }
    Err(prerequisite(
        "read cgroup population",
        format!("missing populated field in {}", path.display()),
    ))
}

fn stop_child(child: &mut Child) -> Result<bool, SolverError> {
    if child
        .try_wait()
        .map_err(|error| {
            SolverError::io(
                SolverErrorKind::CleanupFailure,
                "reap trusted launcher",
                "child process",
                error,
            )
        })?
        .is_some()
    {
        return Ok(true);
    }
    if let Err(error) = child.kill() {
        return child
            .try_wait()
            .map_err(|wait_error| {
                SolverError::io(
                    SolverErrorKind::CleanupFailure,
                    "reap trusted launcher after failed kill",
                    format!("kill failed: {error}"),
                    wait_error,
                )
            })?
            .map(|_| true)
            .ok_or_else(|| {
                SolverError::io(
                    SolverErrorKind::CleanupFailure,
                    "stop trusted launcher",
                    "child process",
                    error,
                )
            });
    }
    Ok(false)
}

fn cleanup_step(
    child: &mut Option<Child>,
    domain: &Path,
    should_kill: bool,
) -> Result<bool, SolverError> {
    let status = match child.as_mut() {
        Some(process) if should_kill => stop_child(process),
        Some(process) => process
            .try_wait()
            .map_err(|error| {
                SolverError::io(
                    SolverErrorKind::CleanupFailure,
                    "reap trusted launcher",
                    "child process",
                    error,
                )
            })
            .map(|status| status.is_some()),
        None => Ok(true),
    };
    let is_reaped = match status {
        Ok(is_reaped) => is_reaped,
        Err(error) => {
            if should_kill {
                signal_kill(domain).map_err(|kill_error| {
                    SolverError::io(
                        SolverErrorKind::CleanupFailure,
                        "terminate cgroup after launcher failure",
                        format!(
                            "{}; launcher: {error}; source: {:?}",
                            domain.display(),
                            error.source
                        ),
                        io::Error::other(kill_error),
                    )
                })?;
            }
            return Err(error);
        },
    };
    if is_reaped {
        child.take();
    }
    let populated = match check_population(domain) {
        Ok(populated) => populated,
        Err(error) => {
            if should_kill {
                signal_kill(domain).map_err(|kill_error| {
                    SolverError::io(
                        SolverErrorKind::CleanupFailure,
                        "terminate cgroup after population read failure",
                        format!("{}; read: {error}; source: {:?}", domain.display(), error.source),
                        io::Error::other(kill_error),
                    )
                })?;
            }
            return Err(error);
        },
    };
    if should_kill && populated {
        signal_kill(domain)?;
        return Ok(false);
    }
    Ok(is_reaped && !populated)
}

fn remove_empty_domain(domain: &Path) -> Result<(), SolverError> {
    fs::remove_dir(domain).map_err(|error| system("remove solver cgroup", domain, error))
}

fn cleanup_error(
    domain: &Path,
    prior: &Result<SolverOutput, SolverError>,
    error: SolverError,
) -> SolverError {
    let previous = prior
        .as_ref()
        .err()
        .map(|prior| format!("; prior: {prior}; prior source: {:?}", prior.source))
        .unwrap_or_default();
    SolverError::io(
        SolverErrorKind::CleanupFailure,
        "retire solver cgroup",
        format!("{}; cleanup: {error}{previous}", domain.display()),
        io::Error::other(error),
    )
}

struct Recovery {
    child: Option<Child>,
    domain: PathBuf,
    _permit: Option<SolverPermit>,
    lease: Option<TaskLease>,
}

impl Drop for Recovery {
    fn drop(&mut self) {
        if let Some(lease) = self.lease.take() {
            // A terminated recovery worker has not proved the process/domain empty.
            // Keep both the build pending and the process-wide concurrency gate held.
            std::mem::forget(lease);
            if let Some(permit) = self._permit.take() {
                std::mem::forget(permit);
            }
        }
    }
}

#[derive(Default)]
struct CleanupState {
    recovery: Option<Recovery>,
    is_closed: bool,
}

#[derive(Default)]
struct CleanupSignal {
    state: Mutex<CleanupState>,
    ready: Condvar,
}

pub(super) struct CleanupSupervisor {
    signal: Arc<CleanupSignal>,
    worker: Option<thread::JoinHandle<()>>,
    lifecycle: BuildLifecycle,
    lease: Option<TaskLease>,
}

impl CleanupSupervisor {
    pub(super) fn start(lifecycle: BuildLifecycle, lease: TaskLease) -> Result<Self, SolverError> {
        let signal = Arc::new(CleanupSignal::default());
        let worker_signal = Arc::clone(&signal);
        let worker = match thread::Builder::new()
            .name("solver-cleanup-supervisor".into())
            .spawn(move || await_recovery(&worker_signal))
        {
            Ok(worker) => worker,
            Err(error) => {
                let failure = SolverError::io(
                    SolverErrorKind::BlockedPrerequisite,
                    "start cleanup supervisor",
                    "before solver domain or process creation",
                    error,
                );
                if let Err(source) = lifecycle.cancel(failure.to_string()) {
                    tracing::error!(kind = ?source.kind, "failed to record supervisor startup failure");
                }
                if let Err(source) = lease.complete()
                    && source.kind != LifecycleErrorKind::Cancelled
                {
                    tracing::error!(kind = ?source.kind, "failed to release unstarted process lease");
                }
                return Err(failure);
            },
        };
        Ok(Self { signal, worker: Some(worker), lifecycle, lease: Some(lease) })
    }

    fn take_over(
        &mut self,
        child: Option<Child>,
        domain: PathBuf,
        permit: SolverPermit,
        failure: &SolverError,
    ) {
        let lease = self.transfer_lease_to_recovery(failure);
        let recovery = Recovery { child, domain, _permit: Some(permit), lease: Some(lease) };
        self.signal.state.lock().unwrap_or_else(std::sync::PoisonError::into_inner).recovery =
            Some(recovery);
        self.signal.ready.notify_one();
        self.worker.take();
    }
    fn transfer_lease_to_recovery(&mut self, failure: &SolverError) -> TaskLease {
        self.revoke(failure);
        // Invariant: start attaches exactly one Process lease to this invocation;
        // transfer is called at most once, exclusively after cleanup cannot finish.
        self.lease.take().expect("one solver invocation owns one Process lease")
    }

    pub(super) fn finish(
        mut self,
        prior: Result<SolverOutput, SolverError>,
    ) -> Result<SolverOutput, SolverError> {
        if let Err(error) = &prior {
            self.revoke(error);
        }
        self.close();
        if let Some(worker) = self.worker.take()
            && worker.join().is_err()
        {
            let error = SolverError::new(
                SolverErrorKind::CleanupFailure,
                "join cleanup supervisor",
                format!("supervisor panicked; prior error: {:?}", prior.err()),
            );
            self.revoke(&error);
            return Err(error);
        }
        if let Some(lease) = self.lease.take()
            && let Err(source) = lease.complete()
            && (prior.is_ok() || source.kind != LifecycleErrorKind::Cancelled)
        {
            return Err(SolverError::lifecycle(source));
        }
        prior
    }

    fn revoke(&self, failure: &SolverError) {
        if let Err(source) = self.lifecycle.cancel(failure.to_string()) {
            tracing::error!(kind = ?source.kind, "failed to record solver cleanup failure");
        }
    }

    fn close(&self) {
        self.signal.state.lock().unwrap_or_else(std::sync::PoisonError::into_inner).is_closed =
            true;
        self.signal.ready.notify_one();
    }
}
impl Drop for CleanupSupervisor {
    fn drop(&mut self) {
        self.close();
        if let Some(lease) = self.lease.take() {
            // Panics before synchronous cleanup leave unknown process ownership.
            if let Err(source) = self
                .lifecycle
                .cancel("solver cleanup supervisor exited before ownership was released".to_owned())
            {
                tracing::error!(kind = ?source.kind, "failed to stop interrupted cleanup");
            }
            std::mem::forget(lease);
        }
    }
}

fn await_recovery(signal: &CleanupSignal) {
    let mut state = signal.state.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    while state.recovery.is_none() && !state.is_closed {
        state = signal.ready.wait(state).unwrap_or_else(std::sync::PoisonError::into_inner);
    }
    let Some(mut recovery) = state.recovery.take() else {
        return;
    };
    drop(state);
    recover_until_empty(&mut recovery);
}

fn recover_until_empty(recovery: &mut Recovery) {
    let mut has_reported_failure = false;
    loop {
        let Recovery { child, domain, .. } = recovery;
        let result = cleanup_step(child, domain, true).and_then(|done| {
            if done {
                remove_empty_domain(domain)?;
            }
            Ok(done)
        });
        match result {
            Ok(true) => {
                if let Some(lease) = recovery.lease.take()
                    && let Err(source) = lease.complete()
                    && source.kind != LifecycleErrorKind::Cancelled
                {
                    tracing::error!(kind = ?source.kind, "failed to release recovered process lease");
                }
                return;
            },
            Err(error) if !has_reported_failure => {
                eprintln!("solver recovery remains active: {error}; source: {:?}", error.source);
                has_reported_failure = true;
            },
            // The caller already received fatal cleanup failure; keep ownership and retry.
            Ok(false) | Err(_) => {},
        }
        thread::sleep(POLL_INTERVAL);
    }
}

fn finish_cleanup(
    mut child: Option<Child>,
    domain: PathBuf,
    permit: SolverPermit,
    mut prior: Result<SolverOutput, SolverError>,
    cleanup_limit: Duration,
    supervisor: &mut CleanupSupervisor,
) -> Result<SolverOutput, SolverError> {
    let started = Instant::now();
    let mut should_kill = prior.is_err();
    let mut failure = None;
    loop {
        match cleanup_step(&mut child, &domain, should_kill) {
            Ok(true) => {
                if prior.is_ok()
                    && let Err(error) = verify_resource_events(&domain)
                {
                    prior = Err(error);
                }
                match remove_empty_domain(&domain) {
                    Ok(()) => {
                        return match failure {
                            Some(error) => Err(cleanup_error(&domain, &prior, error)),
                            None => prior,
                        };
                    },
                    Err(error) => {
                        failure.get_or_insert(error);
                        should_kill = true;
                    },
                }
            },
            Ok(false) => (),
            Err(error) => {
                failure.get_or_insert(error);
                should_kill = true;
            },
        }
        if started.elapsed() >= cleanup_limit {
            break;
        }
        thread::sleep(POLL_INTERVAL.min(cleanup_limit.saturating_sub(started.elapsed())));
    }
    let error = failure.unwrap_or_else(|| {
        SolverError::new(
            SolverErrorKind::CleanupFailure,
            "retire solver cgroup",
            format!("{} still has an unreaped process or populated domain", domain.display()),
        )
    });
    let result = cleanup_error(&domain, &prior, error);
    supervisor.take_over(child, domain, permit, &result);
    Err(result)
}

pub(super) fn retire_without_child(
    domain: PathBuf,
    permit: SolverPermit,
    error: SolverError,
    supervisor: &mut CleanupSupervisor,
) -> Result<SolverOutput, SolverError> {
    finish_cleanup(None, domain, permit, Err(error), CLEANUP_TIMEOUT, supervisor)
}

pub(super) struct Invocation {
    pub child: Child,
    pub report: UnixStream,
    pub auth: UnixStream,
    pub input: Vec<u8>,
    pub domain: PathBuf,
    pub limit: Duration,
}

pub(super) fn supervise(
    invocation: Invocation,
    cancellation: &Cancellation,
    permit: SolverPermit,
    supervisor: &mut CleanupSupervisor,
) -> Result<SolverOutput, SolverError> {
    let Invocation { mut child, report, auth, input, domain, limit } = invocation;
    let started = Instant::now();
    let mut streams = match Streams::new(&mut child, report, input) {
        Ok(streams) => streams,
        Err(error) => {
            drop(auth);
            return finish_cleanup(
                Some(child),
                domain,
                permit,
                Err(error),
                CLEANUP_TIMEOUT,
                supervisor,
            );
        },
    };
    let mut status: Option<ExitStatus> = None;
    let result = loop {
        if cancellation.is_requested() {
            break Err(SolverError::new(
                SolverErrorKind::Cancelled,
                "supervise veriT",
                "build cancellation requested",
            ));
        }
        if started.elapsed() >= limit {
            break Err(SolverError::new(
                SolverErrorKind::ResourceLimit,
                "supervise veriT",
                "wall budget expired",
            ));
        }
        if status.is_none() {
            match child.try_wait() {
                Ok(found) => status = found,
                Err(error) => {
                    break Err(SolverError::io(
                        SolverErrorKind::System,
                        "wait launcher",
                        "trusted child",
                        error,
                    ));
                },
            }
        }
        if let Err(error) = streams
            .pump_output()
            .and_then(|()| streams.pump_input())
            .and_then(|()| streams.pump_report())
        {
            break Err(error);
        }
        if let Some(status) = status.as_ref().filter(|_| streams.is_done()) {
            let Some(code) = status.code() else {
                break Err(SolverError::new(
                    SolverErrorKind::System,
                    "wait solver",
                    "solver terminated by signal",
                ));
            };
            if let Err(error) = verify_startup_report(&streams.report_bytes, code) {
                break Err(error);
            }
            break Ok(SolverOutput { code, output: std::mem::take(&mut streams.output) });
        }
        thread::sleep(POLL_INTERVAL.min(limit.saturating_sub(started.elapsed())));
    };
    drop(streams);
    drop(auth);
    finish_cleanup(Some(child), domain, permit, result, CLEANUP_TIMEOUT, supervisor)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ml::host::lifecycle::{BuildLifecycle, LifecycleErrorKind, RuntimePhase, WorkKind};
    use crate::ml::{DenyHost, Vm};

    fn create_process_lease() -> (Vm, BuildLifecycle, TaskLease) {
        let vm = Vm::new(DenyHost);
        let lifecycle = BuildLifecycle::new(vm.stop_handle());
        let root = lifecycle.start_root(WorkKind::Evaluation, "cleanup fixture").unwrap();
        let process = root.start_child(WorkKind::Process, "registered process").unwrap();
        root.complete().unwrap();
        lifecycle.begin_draining().unwrap();
        (vm, lifecycle, process)
    }

    #[test]
    fn cleanup_supervisor_synchronous_failure_releases_only_after_revocation() {
        let (_vm, lifecycle, process) = create_process_lease();
        let supervisor = CleanupSupervisor::start(lifecycle.clone(), process).unwrap();
        let error = SolverError::new(SolverErrorKind::System, "clean up", "controlled failure");
        assert!(matches!(
            supervisor.finish(Err(error)),
            Err(SolverError { kind: SolverErrorKind::System, .. })
        ));
        assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Process), 0);
        assert_eq!(lifecycle.phase().unwrap(), RuntimePhase::Cancelling);
        lifecycle.finish_failed().unwrap();
    }

    #[test]
    fn cleanup_supervisor_recovery_retains_lease_until_cleanup_completed() {
        let (_vm, lifecycle, process) = create_process_lease();
        let mut supervisor = CleanupSupervisor::start(lifecycle.clone(), process).unwrap();
        let error =
            SolverError::new(SolverErrorKind::CleanupFailure, "clean up", "controlled failure");
        let recovery_lease = supervisor.transfer_lease_to_recovery(&error);
        assert_eq!(lifecycle.pending_counts().unwrap().count(WorkKind::Process), 1);
        assert!(matches!(
            supervisor.finish(Err(error)),
            Err(SolverError { kind: SolverErrorKind::CleanupFailure, .. })
        ));
        assert_eq!(lifecycle.finish_failed().unwrap_err().kind, LifecycleErrorKind::PendingWork);
        // No OS process was started: this controlled recovery models the worker's
        // post-reap/post-domain-removal release point.
        assert_eq!(recovery_lease.complete().unwrap_err().kind, LifecycleErrorKind::Cancelled);
        lifecycle.finish_failed().unwrap();
    }

    #[test]
    fn solver_stream_eof_before_observed_exit_remains_complete() {
        let mut child =
            Command::new("true").stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
        let (report, writer) = UnixStream::pair().unwrap();
        drop(writer);
        let mut streams = Streams::new(&mut child, report, Vec::new()).unwrap();
        let started = Instant::now();
        while streams.stdout.is_some() {
            assert!(started.elapsed() < Duration::from_secs(5));
            streams.pump_output().unwrap();
            thread::yield_now();
        }
        // The process status has deliberately not been observed yet; a second EOF poll
        // cannot turn an already completed stream into a disconnected-reader error.
        streams.pump_output().unwrap();
        streams.pump_input().unwrap();
        streams.pump_report().unwrap();
        assert!(streams.is_done());
        while child.try_wait().unwrap().is_none() {
            assert!(started.elapsed() < Duration::from_secs(5));
            thread::yield_now();
        }
    }

    #[test]
    fn solver_cleanup_bad_population_still_kills_launcher() {
        let domain = std::env::temp_dir().join(format!(
            "solver-cleanup-{}-{:?}",
            std::process::id(),
            thread::current().id()
        ));
        fs::create_dir(&domain).unwrap();
        fs::write(domain.join("cgroup.events"), "invalid event").unwrap();
        fs::write(domain.join("cgroup.kill"), "").unwrap();
        let child =
            Command::new("cat").stdin(Stdio::piped()).stdout(Stdio::null()).spawn().unwrap();
        let mut child = Some(child);
        let error = cleanup_step(&mut child, &domain, true).unwrap_err();
        assert_eq!(error.kind, SolverErrorKind::BlockedPrerequisite);
        assert_eq!(fs::read(domain.join("cgroup.kill")).unwrap(), b"1");
        let started = Instant::now();
        while child.as_mut().unwrap().try_wait().unwrap().is_none() {
            assert!(started.elapsed() < Duration::from_secs(5));
            thread::yield_now();
        }
        fs::remove_dir_all(domain).unwrap();
    }
}
