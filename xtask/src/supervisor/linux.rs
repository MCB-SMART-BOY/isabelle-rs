use std::{
    fs::{self, File, OpenOptions},
    io::{self, Write},
    os::unix::{
        fs::{DirBuilderExt, FileExt, OpenOptionsExt, PermissionsExt},
        process::ExitStatusExt,
    },
    path::{Path, PathBuf},
    process::{Command, ExitStatus, Stdio},
    thread,
    time::{Duration, Instant},
};

use serde_json::json;
use signal_hook::{
    consts::signal::{SIGINT, SIGKILL, SIGTERM},
    iterator::Signals,
};

use crate::runner::{StepError, io_error};

mod child;

const MAX_TIMEOUT_SECS: u64 = 86_400;
const MAX_MEMORY_MIB: u64 = 65_536;
const MAX_AUTO_LIMIT: u64 = 10_000;
const MIB: u64 = 1024 * 1024;
const LOG_BYTES: u64 = 8 * MIB;
const LAUNCHER_DIAGNOSTIC_BYTES: usize = 1024;
const KILL_GRACE_SECS: u64 = 2;
const POLL_INTERVAL: Duration = Duration::from_millis(10);

#[derive(Default)]
struct Options {
    timeout_secs: u64,
    memory_mib: u64,
    output_dir: PathBuf,
    source_root: String,
    theory: String,
    lemma: String,
    context_root: String,
    manifest_in: String,
    auto_limit: String,
    scale_mode: String,
    worker: Option<PathBuf>,
    has_single_lemma_args: bool,
}

fn input(message: impl Into<String>) -> StepError {
    StepError::Input(format!("profile-hol: {}", message.into()))
}

fn parse_number(value: &str, name: &str, maximum: u64) -> Result<u64, StepError> {
    if value.is_empty()
        || value.len() > maximum.ilog10() as usize + 1
        || !value.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err(input(format!("{name} must be a positive integer at most {maximum}")));
    }
    let number = value
        .parse::<u64>()
        .map_err(|_| input(format!("{name} must be a positive integer at most {maximum}")))?;
    if number == 0 || number > maximum {
        return Err(input(format!("{name} must be a positive integer at most {maximum}")));
    }
    Ok(number)
}

fn parse_options(args: &[String], allow_worker: bool) -> Result<Options, StepError> {
    let mut options = Options::default();
    let mut timeout = None;
    let mut memory = None;
    let mut output = None;
    let (pairs, remainder) = args.as_chunks::<2>();
    for pair in pairs {
        let (key, value) = (pair[0].as_str(), pair[1].as_str());
        match key {
            "--timeout-secs" => {
                timeout = Some(parse_number(value, "timeout-secs", MAX_TIMEOUT_SECS)?)
            },
            "--memory-mib" => memory = Some(parse_number(value, "memory-mib", MAX_MEMORY_MIB)?),
            "--output-dir" => output = Some(PathBuf::from(value)),
            "--source-root" => {
                options.has_single_lemma_args = true;
                options.source_root = value.into();
            },
            "--theory" => {
                options.has_single_lemma_args = true;
                options.theory = value.into();
            },
            "--lemma" => {
                options.has_single_lemma_args = true;
                options.lemma = value.into();
            },
            "--context-root" => {
                options.has_single_lemma_args = true;
                options.context_root = value.into();
            },
            "--manifest-in" => {
                options.has_single_lemma_args = true;
                options.manifest_in = value.into();
            },
            "--auto-limit" => {
                options.has_single_lemma_args = true;
                options.auto_limit = value.into();
            },
            "--scale-mode" if !value.is_empty() => options.scale_mode = value.into(),
            "--worker" if allow_worker && !value.is_empty() => options.worker = Some(value.into()),
            "--worker" if !allow_worker => {
                return Err(input("--worker cannot override selected diagnostic worker"));
            },
            "--worker" => return Err(input("worker must not be empty")),
            "--scale-mode" => return Err(input("scale-mode must not be empty")),
            _ => return Err(input(format!("unknown argument: {key}"))),
        }
    }
    if !remainder.is_empty() {
        return Err(input(format!("missing value for {}", remainder[0])));
    }
    options.timeout_secs = timeout.ok_or_else(|| input("missing resource or output argument"))?;
    options.memory_mib = memory.ok_or_else(|| input("missing resource or output argument"))?;
    options.output_dir = output
        .filter(|path| !path.as_os_str().is_empty())
        .ok_or_else(|| input("missing resource or output argument"))?;
    validate_workload(&options)?;
    Ok(options)
}

fn validate_workload(options: &Options) -> Result<(), StepError> {
    if !options.scale_mode.is_empty() {
        if options.has_single_lemma_args {
            return Err(input(
                "scale-mode cannot be combined with single-lemma or manifest arguments",
            ));
        }
        return Ok(());
    }
    if options.source_root.is_empty() || options.theory.is_empty() || options.lemma.is_empty() {
        return Err(input("missing single-lemma arguments"));
    }
    if !Path::new(&options.source_root).is_dir() {
        return Err(input(format!("source root does not exist: {}", options.source_root)));
    }
    if !options.manifest_in.is_empty() && !Path::new(&options.manifest_in).is_file() {
        return Err(input(format!("manifest does not exist: {}", options.manifest_in)));
    }
    if !options.auto_limit.is_empty() {
        parse_number(&options.auto_limit, "auto-limit", MAX_AUTO_LIMIT)?;
    }
    Ok(())
}

fn append_worker_args(command: &mut Command, options: &Options, output_dir: &Path) {
    if !options.scale_mode.is_empty() {
        command.args(["--", &options.scale_mode]);
        return;
    }
    command.args([
        "--source-root",
        &options.source_root,
        "--theory",
        &options.theory,
        "--lemma",
        &options.lemma,
    ]);
    if !options.context_root.is_empty() {
        command.args(["--context-root", &options.context_root]);
    }
    if !options.manifest_in.is_empty() {
        command.args(["--manifest-in", &options.manifest_in]);
    } else {
        command.arg("--manifest-out").arg(output_dir.join("manifest.json"));
    }
    if !options.auto_limit.is_empty() {
        command.args(["--auto-limit", &options.auto_limit]);
    }
}

fn open_new(path: &Path) -> Result<File, StepError> {
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
        .map_err(|source| io_error(format!("create supervised output {}", path.display()), source))
}

fn make_output(options: &mut Options) -> Result<(File, File, File), StepError> {
    let path = &options.output_dir;
    fs::DirBuilder::new().mode(0o700).create(path).map_err(|source| {
        if source.kind() == io::ErrorKind::AlreadyExists {
            input(format!("output directory already exists: {}", path.display()))
        } else {
            io_error(format!("create new private output directory {}", path.display()), source)
        }
    })?;
    options.output_dir = path.canonicalize().map_err(|source| {
        io_error(format!("canonicalize output directory {}", path.display()), source)
    })?;
    let timeout_log = OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(options.output_dir.join("timeout.log"))
        .map_err(|source| io_error("create namespace launcher log", source))?;
    Ok((
        open_new(&options.output_dir.join("events.jsonl"))?,
        timeout_log,
        open_new(&options.output_dir.join("stderr.log"))?,
    ))
}

fn write_report(options: &Options, status: &str, code: i32) -> Result<(), StepError> {
    let path = options.output_dir.join("supervisor.json");
    let mut file = open_new(&path)?;
    let report = json!({
        "status": status, "exit_code": code, "timeout_secs": options.timeout_secs,
        "memory_mib": options.memory_mib, "cpu_secs": options.timeout_secs + KILL_GRACE_SECS + 1,
        "max_log_bytes": LOG_BYTES, "resource_scope": "per_process",
        "theory": options.theory, "lemma": options.lemma, "scale_mode": options.scale_mode,
    });
    serde_json::to_writer(&mut file, &report).map_err(|source| StepError::Json {
        operation: format!("write supervisor report {}", path.display()),
        source,
    })?;
    file.write_all(b"\n").map_err(|source| {
        io_error(format!("finish supervisor report {}", path.display()), source)
    })?;
    file.sync_all()
        .map_err(|source| io_error(format!("sync supervisor report {}", path.display()), source))
}

fn require_worker(worker: &Path) -> Result<(), StepError> {
    let metadata = match fs::metadata(worker) {
        Ok(metadata) => metadata,
        Err(source) if source.kind() == io::ErrorKind::NotFound => {
            return Err(input(format!(
                "worker is not executable: {} (build the selected diagnostic binary first)",
                worker.display()
            )));
        },
        Err(source) => {
            return Err(io_error(
                format!("inspect diagnostic worker {}", worker.display()),
                source,
            ));
        },
    };
    if !metadata.is_file() || metadata.permissions().mode() & 0o111 == 0 {
        return Err(input(format!(
            "worker is not executable: {} (build the selected diagnostic binary first)",
            worker.display()
        )));
    }
    Ok(())
}

fn require_unshare() -> Result<(), StepError> {
    let output = Command::new("unshare").arg("--version").output().map_err(|source| {
        if source.kind() == io::ErrorKind::NotFound {
            input("missing required command: unshare")
        } else {
            io_error("check unshare --version", source)
        }
    })?;
    if !output.status.success() {
        return Err(input(format!("invalid unshare --version: {}", output.status)));
    }
    let version = String::from_utf8(output.stdout).map_err(|source| StepError::Utf8 {
        operation: "decode unshare --version".into(),
        source,
    })?;
    if !version.contains("util-linux") {
        return Err(input("util-linux unshare is required"));
    }
    Ok(())
}

pub(super) fn run_cli(root: &Path, args: &[String]) -> Result<(), StepError> {
    let mut options = parse_options(args, true)?;
    let is_scale_mode = !options.scale_mode.is_empty();
    let worker = options.worker.take().unwrap_or_else(|| {
        root.join(if is_scale_mode {
            "target/debug/isabelle-scale-hol"
        } else {
            "target/debug/isabelle-profile-hol"
        })
    });
    supervise(None, &worker, options)
}

pub(super) fn run(root: &Path, worker: &Path, args: &[String]) -> Result<(), StepError> {
    supervise(Some(root), worker, parse_options(args, false)?)
}

fn supervise(
    working_dir: Option<&Path>,
    worker: &Path,
    mut options: Options,
) -> Result<(), StepError> {
    require_worker(worker)?;
    require_unshare()?;
    let mut signals = Signals::new([SIGINT, SIGTERM])
        .map_err(|source| io_error("register supervisor cancellation signals", source))?;
    let (events, timeout_log, stderr_log) = make_output(&mut options)?;
    let timeout_reader = timeout_log
        .try_clone()
        .map_err(|source| io_error("retain namespace launcher log reader", source))?;
    let mut child = match launch(working_dir, worker, &options, events, timeout_log, stderr_log) {
        Ok(child) => child,
        Err(error) => {
            write_report(&options, "error", 1)?;
            return Err(error);
        },
    };
    let started = Instant::now();
    let result = wait_supervised(
        &mut child,
        &mut signals,
        Duration::from_secs(options.timeout_secs),
        started,
    );
    let (classification, code) = match result {
        Ok(outcome) => outcome,
        Err(error) => {
            terminate_namespace(&child, SIGKILL)?;
            child
                .wait()
                .map_err(|source| io_error("reap supervisor after wait failure", source))?;
            write_report(&options, "error", 1)?;
            return Err(error);
        },
    };
    write_report(&options, classification, code)?;
    if code == 0 {
        return Ok(());
    }
    let mut operation = format!("supervise {}", worker.display());
    match read_launcher_failure(&timeout_reader, &options.output_dir, code) {
        Ok(Some(diagnostic)) => operation.push_str(&format!(
            " (user/PID namespace launcher failed: {diagnostic}; check runner user namespace and AppArmor policy)"
        )),
        Ok(None) => {},
        Err(error) => eprintln!("{error}"),
    }
    Err(StepError::Exit { operation, status: ExitStatus::from_raw(code << 8) })
}

fn read_launcher_failure(
    file: &File,
    output_dir: &Path,
    code: i32,
) -> Result<Option<String>, StepError> {
    if code != 1 {
        return Ok(None);
    }
    let path = output_dir.join("timeout.log");
    let mut bytes = [0; LAUNCHER_DIAGNOSTIC_BYTES];
    let count = file.read_at(&mut bytes, 0).map_err(|source| {
        io_error(format!("read namespace launcher log {}", path.display()), source)
    })?;
    let message = String::from_utf8_lossy(&bytes[..count]);
    let Some(line) =
        message.lines().next().filter(|line| line.starts_with("unshare: unshare failed:"))
    else {
        return Ok(None);
    };
    Ok(Some(format!("{line:?}")))
}

fn launch(
    working_dir: Option<&Path>,
    worker: &Path,
    options: &Options,
    events: File,
    timeout_log: File,
    stderr_log: File,
) -> Result<std::process::Child, StepError> {
    use std::os::unix::process::CommandExt;
    let executable =
        std::env::current_exe().map_err(|source| io_error("find supervisor executable", source))?;
    let mut command = Command::new("unshare");
    command
        .args([
            "--user",
            "--map-current-user",
            "--pid",
            "--fork",
            "--forward-signals",
            "--kill-child",
            "--",
        ])
        .arg(executable)
        .arg("__supervisor-child")
        .arg(worker)
        .arg(options.output_dir.join("stderr.log"))
        .arg((options.memory_mib * MIB).to_string())
        .arg((options.timeout_secs + KILL_GRACE_SECS + 1).to_string());
    append_worker_args(&mut command, options, &options.output_dir);
    command.stdin(Stdio::null()).stdout(Stdio::from(events)).stderr(Stdio::from(timeout_log));
    if let Some(directory) = working_dir {
        command.current_dir(directory);
    }
    drop(stderr_log);
    // Safety: setsid is async-signal-safe, has no Rust state, and reports errno through pre_exec.
    unsafe {
        command
            .pre_exec(|| if libc::setsid() < 0 { Err(io::Error::last_os_error()) } else { Ok(()) });
    }
    command.spawn().map_err(|source| {
        io_error(format!("launch PID namespace for {}", worker.display()), source)
    })
}

fn wait_supervised(
    child: &mut std::process::Child,
    signals: &mut Signals,
    timeout: Duration,
    started: Instant,
) -> Result<(&'static str, i32), StepError> {
    let mut requested = None;
    loop {
        for signal in signals.pending() {
            if requested.is_none() {
                requested = Some(signal);
            }
        }
        if let Some(signal) = requested {
            terminate_namespace(child, SIGTERM)?;
            reap_after_grace(child)?;
            return Ok(("error", 128 + signal));
        }
        if let Some(status) =
            child.try_wait().map_err(|source| io_error("poll supervised PID namespace", source))?
        {
            let code = status.code().unwrap_or_else(|| 128 + status.signal().unwrap_or(SIGKILL));
            return Ok((if code == 0 { "completed" } else { "error" }, code));
        }
        if started.elapsed() >= timeout {
            terminate_namespace(child, SIGTERM)?;
            reap_after_grace(child)?;
            return Ok(("timed_out", 124));
        }
        thread::sleep(POLL_INTERVAL);
    }
}

fn terminate_namespace(child: &std::process::Child, signal: i32) -> Result<(), StepError> {
    // Negative PID addresses the private session's process group; a signalled launcher
    // forwards to its namespace init, including when cancellation precedes init startup.
    let result = unsafe { libc::kill(-(child.id() as i32), signal) };
    if result != 0 {
        let source = io::Error::last_os_error();
        if source.raw_os_error() != Some(libc::ESRCH) {
            return Err(io_error(format!("signal namespace launcher {}", child.id()), source));
        }
    }
    Ok(())
}

fn reap_after_grace(child: &mut std::process::Child) -> Result<(), StepError> {
    let deadline = Instant::now() + Duration::from_secs(KILL_GRACE_SECS);
    loop {
        if child
            .try_wait()
            .map_err(|source| io_error("poll terminated PID namespace", source))?
            .is_some()
        {
            return Ok(());
        }
        if Instant::now() >= deadline {
            break;
        }
        thread::sleep(POLL_INTERVAL);
    }
    terminate_namespace(child, SIGKILL)?;
    child.wait().map_err(|source| io_error("reap killed PID namespace", source))?;
    Ok(())
}

pub(super) fn run_internal(args: &[String]) -> Result<i32, StepError> {
    child::run(args)
}
