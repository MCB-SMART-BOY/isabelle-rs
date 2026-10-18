//! Namespace PID 1: reaps the worker and lets Linux kill every residual descendant on exit.
use std::{
    fs::OpenOptions,
    io,
    os::unix::{
        fs::OpenOptionsExt,
        process::{CommandExt, ExitStatusExt},
    },
    path::Path,
    process::{Command, Stdio},
    thread,
    time::Duration,
};

use signal_hook::{
    consts::signal::{SIGINT, SIGTERM},
    iterator::Signals,
};

use crate::runner::{StepError, io_error};

const POLL_INTERVAL: Duration = Duration::from_millis(10);
const LOG_BYTES: u64 = 8 * 1024 * 1024;

fn parse_limit(value: &str, name: &str) -> Result<libc::rlim_t, StepError> {
    value
        .parse::<libc::rlim_t>()
        .map_err(|_| StepError::Input(format!("invalid supervisor child {name}: {value}")))
}

fn set_limit(resource: libc::__rlimit_resource_t, value: libc::rlim_t) -> io::Result<()> {
    let limits = libc::rlimit { rlim_cur: value, rlim_max: value };
    // Safety: setrlimit is async-signal-safe; the constant resource and rlimit struct
    // are allocated before this syscall. Errors propagate as worker spawn failures.
    if unsafe { libc::setrlimit(resource, &limits) } == -1 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

fn signal_worker(pid: u32, signal: i32) -> Result<(), StepError> {
    // Worker is in the same PID namespace; its descendants die when PID 1 exits.
    if unsafe { libc::kill(pid as i32, signal) } == -1 {
        let source = io::Error::last_os_error();
        if source.raw_os_error() != Some(libc::ESRCH) {
            return Err(io_error(format!("signal diagnostic worker {pid}"), source));
        }
    }
    Ok(())
}

pub(super) fn run(args: &[String]) -> Result<i32, StepError> {
    if args.len() < 5 {
        return Err(StepError::Input("invalid supervisor child argument count".into()));
    }
    let memory = parse_limit(&args[3], "memory byte limit")?;
    let cpu = parse_limit(&args[4], "CPU second limit")?;
    let worker = Path::new(&args[1]);
    let stderr_path = Path::new(&args[2]);
    let stderr =
        OpenOptions::new().append(true).custom_flags(libc::O_NOFOLLOW).open(stderr_path).map_err(
            |source| io_error(format!("open worker stderr {}", stderr_path.display()), source),
        )?;
    let mut signals = Signals::new([SIGINT, SIGTERM])
        .map_err(|source| io_error("register PID 1 cancellation handlers", source))?;
    let mut command = Command::new(worker);
    command
        .args(&args[5..])
        .stdin(Stdio::null())
        .stdout(Stdio::inherit())
        .stderr(Stdio::from(stderr));
    // Safety: only raw syscalls and no allocations/locks are used after fork.
    unsafe {
        command.pre_exec(move || {
            set_limit(libc::RLIMIT_AS, memory)?;
            set_limit(libc::RLIMIT_CPU, cpu)?;
            set_limit(libc::RLIMIT_FSIZE, LOG_BYTES)?;
            Ok(())
        });
    }
    let mut child = command.spawn().map_err(|source| {
        io_error(format!("launch diagnostic worker {}", worker.display()), source)
    })?;
    loop {
        if let Some(signal) = signals.pending().next() {
            signal_worker(child.id(), SIGTERM)?;
            return Ok(128 + signal);
        }
        if let Some(status) = child.try_wait().map_err(|source| {
            io_error(format!("poll diagnostic worker {}", worker.display()), source)
        })? {
            return Ok(status.code().unwrap_or_else(|| 128 + status.signal().unwrap_or(SIGTERM)));
        }
        thread::sleep(POLL_INTERVAL);
    }
}
