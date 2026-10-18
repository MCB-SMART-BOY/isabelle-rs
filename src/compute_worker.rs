//! Framed, versioned IPC for the built-in RealExecutor. Custom executors remain in-process.
use std::{
    io::{self, Read, Write},
    path::Path,
    process::{Child, ChildStdin, ChildStdout, Command as ProcessCommand, Stdio},
    sync::mpsc::{self, RecvTimeoutError},
    thread,
    time::Duration,
};

use crate::{
    document::{Command, Snapshot},
    fleche::engine::Fleche,
    hol::hol_loader::HolTheoremDb,
    server::lsp_types::{Diagnostic, Location, Position, ProofState, Range},
};
use serde::{Deserialize, Serialize, ser::Serializer};
use sha2::{Digest, Sha256};

const MAGIC: [u8; 4] = *b"ISCP";
const PROTOCOL_VERSION: u16 = 1;
const MAX_FRAME: usize = 8 * 1024 * 1024;
pub(crate) const MAX_SOURCE: usize = 1024 * 1024;
const HEADER_SIZE: usize = 18;
const IO_POLL: Duration = Duration::from_millis(10);
const START_TIMEOUT: Duration = Duration::from_secs(5);
const PACKAGE_VERSION: &str = env!("CARGO_PKG_VERSION");
#[derive(Debug, thiserror::Error)]
#[error("unable to hash executable {path}: {source}")]
struct HashError {
    path: String,
    #[source]
    source: io::Error,
}

#[derive(Debug, thiserror::Error)]
#[error("compute frame magic/version mismatch")]
struct IdentityMismatch;
#[derive(Debug, thiserror::Error)]
#[error("compute startup was cancelled while hashing executable")]
struct HashCancelled;

fn executable_hash(path: &Path, cancel: &impl Fn() -> bool) -> io::Result<[u8; 32]> {
    let mut file = std::fs::File::open(path).map_err(|source| {
        io::Error::new(source.kind(), HashError { path: path.display().to_string(), source })
    })?;
    let mut hasher = Sha256::new();
    let mut chunk = [0u8; 16 * 1024];
    loop {
        if cancel() {
            return Err(io::Error::new(io::ErrorKind::Interrupted, HashCancelled));
        }
        let count = file.read(&mut chunk).map_err(|source| {
            io::Error::new(source.kind(), HashError { path: path.display().to_string(), source })
        })?;
        if count == 0 {
            break;
        }
        hasher.update(&chunk[..count]);
    }
    Ok(hasher.finalize().into())
}

#[derive(Debug, thiserror::Error)]
pub(crate) enum ComputeError {
    /// The trusted worker executable cannot be started.
    #[error("failed to start compute worker: {0}")]
    Spawn(#[source] io::Error),
    /// The IPC stream failed, was truncated, or violated its frame/size contract.
    #[error("compute worker IPC failed: {0}")]
    Ipc(#[source] io::Error),
    /// The child presented a wrong protocol, build identity, or response ID.
    #[error("compute worker identity mismatch: {0}")]
    Identity(&'static str),
    /// The caller cancelled the in-flight request; child was terminated and reaped.
    #[error("compute worker request cancelled")]
    Cancelled,
    /// The worker did not complete startup in time; child was terminated and reaped.
    #[error("compute worker startup timed out")]
    Timeout,
    /// The child could not be reaped; recovery is uncertain.
    #[error("failed to reap compute worker: {0}")]
    Reap(#[source] io::Error),
}

#[derive(Debug, Serialize, Deserialize)]
pub(crate) enum CheckFailure {
    /// Input exceeds the bounded source limit.
    Source,
    /// Bounded parsing exceeded the command count.
    Commands,
    /// Execution or encoding exceeded diagnostic/response limits.
    Diagnostics,
    /// The child could not check the document; caller publishes unavailable diagnostics.
    Worker(String),
}

#[derive(Debug)]
pub(crate) struct ProcessCheck {
    pub commands: Vec<Command>,
    pub snapshots: Vec<Snapshot>,
}

#[derive(Debug, Serialize, Deserialize)]
pub(crate) enum ComputeRequest {
    Check { content: String, version: i32 },
    Definition { uri: String, word: String },
}

#[derive(Debug)]
pub(crate) enum ComputeResponse {
    Check(Result<ProcessCheck, CheckFailure>),
    Definition(Option<Location>),
}

#[derive(Debug, Serialize, Deserialize)]
struct Hello {
    version: String,
    executable_hash: [u8; 32],
}

#[derive(Deserialize)]
struct WireCommand {
    source: String,
    range: Range,
    id: usize,
}

#[derive(Deserialize)]
struct WireSnapshot {
    command_id: usize,
    version: i32,
    diagnostics: Vec<Diagnostic>,
    proof_state: Option<ProofState>,
    context_hash: u64,
    stale: bool,
}

#[derive(Deserialize)]
struct WireCheck {
    commands: Vec<WireCommand>,
    snapshots: Vec<WireSnapshot>,
}

#[derive(Deserialize)]
enum WireResponse {
    Check(Result<WireCheck, CheckFailure>),
    Definition(Option<Location>),
}

#[derive(Serialize)]
struct WireCommandRef<'a> {
    source: &'a str,
    range: &'a Range,
    id: usize,
}

#[derive(Serialize)]
struct WireSnapshotRef<'a> {
    command_id: usize,
    version: i32,
    diagnostics: &'a [Diagnostic],
    proof_state: Option<&'a ProofState>,
    context_hash: u64,
    stale: bool,
}

#[derive(Serialize)]
struct WireCheckRef<'a> {
    #[serde(serialize_with = "serialize_commands")]
    commands: &'a [Command],
    #[serde(serialize_with = "serialize_snapshots")]
    snapshots: &'a [Snapshot],
}

#[derive(Serialize)]
enum WireResponseRef<'a> {
    Check(Result<WireCheckRef<'a>, &'a CheckFailure>),
    Definition(&'a Option<Location>),
}

fn serialize_commands<S: Serializer>(
    commands: &&[Command],
    serializer: S,
) -> Result<S::Ok, S::Error> {
    serializer.collect_seq(commands.iter().map(|command| WireCommandRef {
        source: &command.source,
        range: &command.range,
        id: command.id,
    }))
}

fn serialize_snapshots<S: Serializer>(
    snapshots: &&[Snapshot],
    serializer: S,
) -> Result<S::Ok, S::Error> {
    serializer.collect_seq(snapshots.iter().map(|snapshot| WireSnapshotRef {
        command_id: snapshot.command_id,
        version: snapshot.version,
        diagnostics: &snapshot.diagnostics,
        proof_state: snapshot.proof_state.as_deref(),
        context_hash: snapshot.context_hash,
        stale: snapshot.stale,
    }))
}

fn encode_response(response: &ComputeResponse) -> io::Result<Vec<u8>> {
    let borrowed = match response {
        ComputeResponse::Check(Ok(check)) => WireResponseRef::Check(Ok(WireCheckRef {
            commands: &check.commands,
            snapshots: &check.snapshots,
        })),
        ComputeResponse::Check(Err(failure)) => WireResponseRef::Check(Err(failure)),
        ComputeResponse::Definition(location) => WireResponseRef::Definition(location),
    };
    match encode(&borrowed) {
        Ok(body) => Ok(body),
        Err(error)
            if matches!(response, ComputeResponse::Check(_))
                && error.kind() == io::ErrorKind::InvalidData =>
        {
            let failure = CheckFailure::Diagnostics;
            encode(&WireResponseRef::Check(Err(&failure)))
        },
        Err(error) => Err(error),
    }
}

impl From<WireCheck> for ProcessCheck {
    fn from(check: WireCheck) -> Self {
        Self {
            commands: check
                .commands
                .into_iter()
                .map(|command| Command::new(command.source, command.range, command.id))
                .collect(),
            snapshots: check
                .snapshots
                .into_iter()
                .map(|snapshot| Snapshot {
                    command_id: snapshot.command_id,
                    version: snapshot.version,
                    diagnostics: snapshot.diagnostics,
                    proof_state: snapshot.proof_state.map(std::sync::Arc::new),
                    context_hash: snapshot.context_hash,
                    stale: snapshot.stale,
                })
                .collect(),
        }
    }
}

struct CappedBuffer(Vec<u8>);
impl Write for CappedBuffer {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if bytes.len() > MAX_FRAME.saturating_sub(self.0.len()) {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "compute frame exceeds limit"));
        }
        self.0.extend_from_slice(bytes);
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn encode<T: Serialize>(message: &T) -> io::Result<Vec<u8>> {
    let mut buffer = CappedBuffer(Vec::new());
    serde_json::to_writer(&mut buffer, message)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    Ok(buffer.0)
}

fn send_encoded(output: &mut impl Write, id: u64, body: &[u8]) -> io::Result<()> {
    let mut header = [0u8; HEADER_SIZE];
    header[..4].copy_from_slice(&MAGIC);
    header[4..6].copy_from_slice(&PROTOCOL_VERSION.to_be_bytes());
    header[6..14].copy_from_slice(&id.to_be_bytes());
    header[14..18].copy_from_slice(&(body.len() as u32).to_be_bytes());
    output.write_all(&header)?;
    output.write_all(body)?;
    output.flush()
}

fn send<T: Serialize>(output: &mut impl Write, id: u64, message: &T) -> io::Result<()> {
    send_encoded(output, id, &encode(message)?)
}

fn receive<T: for<'de> Deserialize<'de>>(input: &mut impl Read) -> io::Result<(u64, T)> {
    let mut header = [0u8; HEADER_SIZE];
    if input.read(&mut header[..1])? == 0 {
        return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "compute stream closed"));
    }
    input
        .read_exact(&mut header[1..])
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    if header[..4] != MAGIC || u16::from_be_bytes([header[4], header[5]]) != PROTOCOL_VERSION {
        return Err(io::Error::new(io::ErrorKind::InvalidData, IdentityMismatch));
    }
    let id =
        u64::from_be_bytes(header[6..14].try_into().map_err(|_| {
            io::Error::new(io::ErrorKind::InvalidData, "invalid compute request ID")
        })?);
    let length =
        u32::from_be_bytes(header[14..18].try_into().map_err(|_| {
            io::Error::new(io::ErrorKind::InvalidData, "invalid compute frame length")
        })?) as usize;
    if length == 0 || length > MAX_FRAME {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "compute frame exceeds limit"));
    }
    let mut body = vec![0; length];
    input
        .read_exact(&mut body)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    let message = serde_json::from_slice(&body)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    Ok((id, message))
}

pub(crate) struct ComputeProcess {
    child: Option<Child>,
    input: Option<ChildStdin>,
    output: Option<ChildStdout>,
    next_id: u64,
    io_thread: Option<thread::JoinHandle<()>>,
}

impl ComputeProcess {
    pub(crate) fn start_cancellable(
        executable: &Path,
        cwd: &Path,
        cancel: impl Fn() -> bool,
    ) -> Result<Self, ComputeError> {
        if cancel() {
            return Err(ComputeError::Cancelled);
        }
        if !executable.is_absolute() {
            return Err(ComputeError::Spawn(io::Error::new(
                io::ErrorKind::InvalidInput,
                "compute executable must be an absolute path",
            )));
        }
        let hash = executable_hash(executable, &cancel).map_err(|error| {
            if error.get_ref().is_some_and(|cause| cause.is::<HashCancelled>()) {
                ComputeError::Cancelled
            } else {
                ComputeError::Spawn(error)
            }
        })?;
        if cancel() {
            return Err(ComputeError::Cancelled);
        }
        let child = ProcessCommand::new(executable)
            .arg("--compute-worker")
            .current_dir(cwd)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .map_err(ComputeError::Spawn)?;
        let mut process =
            Self { child: Some(child), input: None, output: None, next_id: 1, io_thread: None };
        let Some(input) = process.child.as_mut().and_then(|child| child.stdin.take()) else {
            return Err(process.abort(ComputeError::Ipc(io::Error::other("missing compute stdin"))));
        };
        process.input = Some(input);
        let Some(output) = process.child.as_mut().and_then(|child| child.stdout.take()) else {
            return Err(
                process.abort(ComputeError::Ipc(io::Error::other("missing compute stdout")))
            );
        };
        process.output = Some(output);
        let hello = Hello { version: PACKAGE_VERSION.to_owned(), executable_hash: hash };
        let response: Hello = process.exchange(0, hello, cancel, Some(START_TIMEOUT))?;
        if response.version != PACKAGE_VERSION || response.executable_hash != hash {
            return Err(process.abort(ComputeError::Identity("worker executable/version")));
        }
        Ok(process)
    }

    pub(crate) fn request(
        &mut self,
        request: ComputeRequest,
        cancel: impl Fn() -> bool,
    ) -> Result<ComputeResponse, ComputeError> {
        if cancel() {
            return Err(self.abort(ComputeError::Cancelled));
        }
        if matches!(&request, ComputeRequest::Check { content, .. } if content.len() > MAX_SOURCE) {
            return Err(ComputeError::Ipc(io::Error::new(
                io::ErrorKind::InvalidInput,
                "compute source exceeds limit",
            )));
        }
        let is_check = matches!(&request, ComputeRequest::Check { .. });
        let id = self.next_id;
        self.next_id = self
            .next_id
            .checked_add(1)
            .ok_or_else(|| self.abort(ComputeError::Identity("request ID exhausted")))?;
        let response: WireResponse = self.exchange(id, request, cancel, None)?;
        match response {
            WireResponse::Check(check) if is_check => {
                Ok(ComputeResponse::Check(check.map(ProcessCheck::from)))
            },
            WireResponse::Definition(location) if !is_check => {
                Ok(ComputeResponse::Definition(location))
            },
            _ => Err(self.abort(ComputeError::Identity("response kind"))),
        }
    }

    fn exchange<Q, R>(
        &mut self,
        id: u64,
        request: Q,
        cancel: impl Fn() -> bool,
        timeout: Option<Duration>,
    ) -> Result<R, ComputeError>
    where
        Q: Serialize + Send + 'static,
        R: for<'de> Deserialize<'de> + Send + 'static,
    {
        let input = self.input.take().ok_or(ComputeError::Identity("worker stopped"))?;
        let output = self.output.take().ok_or(ComputeError::Identity("worker stopped"))?;
        let (sender, receiver) = mpsc::sync_channel(1);
        self.io_thread = Some(thread::spawn(move || {
            let mut input = input;
            let mut output = output;
            let result = send(&mut input, id, &request).and_then(|()| receive::<R>(&mut output));
            let _ = sender.send((result, input, output));
        }));
        let started = std::time::Instant::now();
        loop {
            if cancel() {
                return Err(self.abort(ComputeError::Cancelled));
            }
            if timeout.is_some_and(|limit| started.elapsed() >= limit) {
                return Err(self.abort(ComputeError::Timeout));
            }
            match receiver.recv_timeout(IO_POLL) {
                Ok((result, input, output)) => {
                    self.input = Some(input);
                    self.output = Some(output);
                    if let Err(error) = self.join_io() {
                        return Err(self.abort(error));
                    }
                    return match result {
                        Ok((response_id, response)) if response_id == id => Ok(response),
                        Ok(_) => Err(self.abort(ComputeError::Identity("response request ID"))),
                        Err(error)
                            if error
                                .get_ref()
                                .is_some_and(|cause| cause.is::<IdentityMismatch>()) =>
                        {
                            Err(self.abort(ComputeError::Identity("frame magic/version")))
                        },
                        Err(error) => Err(self.abort(ComputeError::Ipc(error))),
                    };
                },
                Err(RecvTimeoutError::Timeout) => {},
                Err(RecvTimeoutError::Disconnected) => {
                    return Err(self
                        .abort(ComputeError::Ipc(io::Error::other("compute IPC thread stopped"))));
                },
            }
        }
    }
    fn join_io(&mut self) -> Result<(), ComputeError> {
        if let Some(handle) = self.io_thread.take() {
            handle
                .join()
                .map_err(|_| ComputeError::Ipc(io::Error::other("compute IPC thread panicked")))?;
        }
        Ok(())
    }

    fn abort(&mut self, error: ComputeError) -> ComputeError {
        match self.stop() {
            Ok(()) => error,
            Err(reap) => reap,
        }
    }

    pub(crate) fn stop(&mut self) -> Result<(), ComputeError> {
        self.input.take();
        self.output.take();
        if let Some(child) = self.child.as_mut() {
            Self::stop_child(child)?;
        }
        self.child.take();
        self.join_io()
    }

    fn stop_child(child: &mut Child) -> Result<(), ComputeError> {
        let status_error = match child.try_wait() {
            Ok(Some(_)) => return Ok(()),
            Ok(None) => None,
            Err(error) => Some(error),
        };
        if let Err(error) = child.kill()
            && error.kind() != io::ErrorKind::InvalidInput
        {
            return Err(ComputeError::Reap(error));
        }
        child.wait().map_err(ComputeError::Reap)?;
        if let Some(error) = status_error {
            return Err(ComputeError::Reap(error));
        }
        Ok(())
    }
}

impl Drop for ComputeProcess {
    fn drop(&mut self) {
        let _ = self.stop();
    }
}

fn lookup_definition(uri: String, word: String) -> Option<Location> {
    let location = HolTheoremDb::global().get_definition_location(&word)?;
    let uri = if location.file == "<unknown>" {
        uri
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

fn compute(request: ComputeRequest) -> ComputeResponse {
    match request {
        ComputeRequest::Check { content, version } => {
            let checked = if content.len() > MAX_SOURCE {
                Err(CheckFailure::Source)
            } else {
                Fleche::check_process_content(&content, version)
            };
            ComputeResponse::Check(checked)
        },
        ComputeRequest::Definition { uri, word } => {
            ComputeResponse::Definition(lookup_definition(uri, word))
        },
    }
}

/// Run only as the trusted `--compute-worker` child. No server or logger is initialized.
pub fn run_stdio() -> io::Result<()> {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut input = stdin.lock();
    let mut output = stdout.lock();
    let (hello_id, hello): (u64, Hello) = receive(&mut input)?;
    if hello_id != 0 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "compute worker handshake ID mismatch",
        ));
    }
    let current_exe = std::env::current_exe()?;
    let identity = Hello {
        version: PACKAGE_VERSION.to_owned(),
        executable_hash: executable_hash(&current_exe, &|| false)?,
    };
    send(&mut output, 0, &identity)?;
    if hello.version != identity.version || hello.executable_hash != identity.executable_hash {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "compute worker build mismatch"));
    }
    let mut expected_id = 1u64;
    loop {
        let (id, request): (u64, ComputeRequest) = match receive(&mut input) {
            Ok(message) => message,
            Err(error) if error.kind() == io::ErrorKind::UnexpectedEof => return Ok(()),
            Err(error) => return Err(error),
        };
        if id != expected_id {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "compute request ID mismatch"));
        }
        expected_id = expected_id.checked_add(1).ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidData, "compute request ID exhausted")
        })?;
        let response = compute(request);
        let body = encode_response(&response)?;
        send_encoded(&mut output, id, &body)?;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wire_check_multiple_commands_preserves_diagnostics_and_goals() {
        let response = compute(ComputeRequest::Check {
            content: "theory Test\nlemma foo: \"A\"".into(),
            version: 7,
        });
        let mut frame = Vec::new();
        send_encoded(&mut frame, 1, &encode_response(&response).expect("bounded response"))
            .expect("framed response");
        let (id, decoded): (u64, WireResponse) = receive(&mut frame.as_slice()).expect("frame");
        assert_eq!(id, 1);
        let WireResponse::Check(Ok(checked)) = decoded else { panic!("expected checked document") };
        let restored = ProcessCheck::from(checked);
        assert_eq!(restored.commands.len(), restored.snapshots.len());
        assert!(restored.snapshots.iter().any(|snapshot| {
            snapshot
                .diagnostics
                .iter()
                .any(|item| item.code.as_deref() == Some("lemma-proof-pending"))
                && snapshot.proof_state.as_ref().is_some_and(|state| state.has_unsolved)
        }));
    }

    #[test]
    fn encode_response_shared_large_goal_returns_diagnostics_before_framing() {
        use std::sync::Arc;

        use crate::{document::Node, server::lsp_types::ProofGoal};

        const COMMAND_COUNT: usize = 4096;
        const GOAL_BYTES: usize = 512 * 1024;
        let name = "x".repeat(GOAL_BYTES);
        let content = format!("lemma {name}: \"A\"\n{}", "end\n".repeat(COMMAND_COUNT - 1));
        assert!(content.len() < MAX_SOURCE);
        let commands =
            Node::parse_commands_bounded(&content, COMMAND_COUNT).expect("bounded source");
        assert_eq!(commands.len(), COMMAND_COUNT);
        let shared_state = Arc::new(ProofState {
            goals: vec![ProofGoal { hyps: vec![], conclusion: name, id: None }],
            background_goals: vec![],
            has_unsolved: true,
        });
        let snapshots = commands
            .iter()
            .map(|command| {
                let mut snapshot = Snapshot::new(command.id, 1);
                snapshot.proof_state = Some(Arc::clone(&shared_state));
                snapshot
            })
            .collect();
        let response = ComputeResponse::Check(Ok(ProcessCheck { commands, snapshots }));
        let body = encode_response(&response).expect("bounded diagnostic failure");
        let mut frame = Vec::new();
        send_encoded(&mut frame, 1, &body).expect("framed diagnostic failure");
        let (id, decoded): (u64, WireResponse) = receive(&mut frame.as_slice()).expect("frame");
        assert_eq!(id, 1);
        assert!(matches!(decoded, WireResponse::Check(Err(CheckFailure::Diagnostics))));
    }

    #[test]
    fn wire_header_oversized_length_rejected_before_body_read() {
        let mut frame = Vec::new();
        send(&mut frame, 1, &Hello { version: PACKAGE_VERSION.into(), executable_hash: [0; 32] })
            .expect("frame");
        frame[14..18].copy_from_slice(&((MAX_FRAME + 1) as u32).to_be_bytes());
        let result: io::Result<(u64, Hello)> = receive(&mut frame.as_slice());
        assert_eq!(result.expect_err("oversized header").kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn wire_truncated_header_rejected_as_malformed() {
        let result: io::Result<(u64, Hello)> = receive(&mut [MAGIC[0]].as_slice());
        assert_eq!(result.expect_err("partial header").kind(), io::ErrorKind::InvalidData);
    }
    #[cfg(target_os = "linux")]
    #[test]
    fn process_start_cancellation_reaps_blocked_child() {
        use std::{
            cell::Cell,
            time::{Instant, SystemTime, UNIX_EPOCH},
        };

        const TEST_DEADLINE: Duration = Duration::from_secs(3);
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock after epoch")
            .as_nanos();
        let directory = std::env::temp_dir()
            .join(format!("isabelle-compute-cancel-{}-{nonce}", std::process::id()));
        std::fs::create_dir(&directory).expect("temporary directory");
        let executable = directory.join("no-hello");
        let marker = directory.join("pid");
        let compiler = std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
        let status = std::process::Command::new(compiler)
            .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/compute_no_hello.rs"))
            .arg("-o")
            .arg(&executable)
            .status()
            .expect("compile blocked Rust worker fixture");
        assert!(status.success(), "compile blocked Rust worker fixture");

        let started = Instant::now();
        let observed_pid = Cell::new(None);
        let result = ComputeProcess::start_cancellable(&executable, &directory, || {
            if let Ok(pid) = std::fs::read_to_string(&marker)
                && let Ok(pid) = pid.trim().parse::<u32>()
            {
                observed_pid.set(Some(pid));
                return true;
            }
            started.elapsed() >= TEST_DEADLINE
        });
        assert!(matches!(result, Err(ComputeError::Cancelled)));
        let pid = observed_pid.get().expect("child reached blocked startup");
        assert!(!Path::new("/proc").join(pid.to_string()).exists(), "worker was not reaped");
        std::fs::remove_file(marker).expect("remove pid marker");
        std::fs::remove_file(executable).expect("remove test executable");
        std::fs::remove_dir(directory).expect("remove temporary directory");
    }
}
