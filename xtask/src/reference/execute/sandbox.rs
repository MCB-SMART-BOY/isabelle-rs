#[cfg(unix)]
pub(super) mod v2;

use std::ffi::OsString;
use std::fs::OpenOptions;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use serde_json::Value;

use super::super::{artifacts, trace};
use super::{OBSERVER_FILES, build_options, inventory_options};
use crate::runner::{StepError, io_error};

#[cfg(unix)]
struct Cancellation {
    requested: std::sync::Arc<std::sync::atomic::AtomicBool>,
    handlers: Vec<signal_hook::SigId>,
}

#[cfg(unix)]
impl Cancellation {
    fn install() -> Result<Self, StepError> {
        let requested = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let mut handlers = Vec::new();
        for signal in [libc::SIGINT, libc::SIGTERM] {
            match signal_hook::flag::register(signal, requested.clone()) {
                Ok(id) => handlers.push(id),
                Err(source) => {
                    for handler in handlers {
                        signal_hook::low_level::unregister(handler);
                    }
                    return Err(io_error("install reference cancellation handler", source));
                },
            }
        }
        Ok(Self { requested, handlers })
    }

    fn requested(&self) -> bool {
        self.requested.load(std::sync::atomic::Ordering::SeqCst)
    }
}

#[cfg(unix)]
impl Drop for Cancellation {
    fn drop(&mut self) {
        for handler in self.handlers.drain(..) {
            signal_hook::low_level::unregister(handler);
        }
    }
}

const MAX_RUNTIME: Duration = Duration::from_secs(7200);
const TERM_GRACE: Duration = Duration::from_secs(30);
const POLL_INTERVAL: Duration = Duration::from_millis(100);

const SANDBOX_FLAGS: &[&str] = &[
    "--unshare-all",
    "--die-with-parent",
    "--new-session",
    "--cap-drop",
    "ALL",
    "--clearenv",
    "--dir",
    "/nix",
    "--ro-bind",
    "/nix/store",
    "/nix/store",
    "--ro-bind",
    "/run/current-system",
    "/run/current-system",
    "--dir",
    "/lib64",
    "--ro-bind",
    "/lib64/ld-linux-x86-64.so.2",
    "/lib64/ld-linux-x86-64.so.2",
    "--proc",
    "/proc",
    "--dev",
    "/dev",
    "--tmpfs",
    "/tmp",
    "--dir",
    "/bin",
    "--dir",
    "/usr/bin",
    "--symlink",
    "/run/current-system/sw/bin/bash",
    "/bin/bash",
    "--symlink",
    "/run/current-system/sw/bin/bash",
    "/bin/sh",
    "--symlink",
    "/run/current-system/sw/bin/env",
    "/usr/bin/env",
];

fn mount(args: &mut Vec<OsString>, flag: &str, host: &Path, guest: &str) {
    args.push(flag.into());
    args.push(host.as_os_str().into());
    args.push(guest.into());
}

fn mount_inventory_inputs(
    args: &mut Vec<OsString>,
    repository: &Path,
    workspace: &Path,
    run: &Path,
    build_run: Option<&Path>,
) -> Result<(), StepError> {
    let build =
        build_run.ok_or_else(|| StepError::Input("inventory requires --build-run".into()))?;
    let heaps = build.join("home/.isabelle/p0-reference/heaps");
    artifacts::require_managed_directory(&heaps, workspace)?;
    artifacts::require_managed_directory(&run.join("inventory"), workspace)?;
    mount(args, "--ro-bind", &heaps, "/work/empty-system-heaps");
    args.extend(["--dir".into(), "/work/session".into()]);
    mount(args, "--bind", &run.join("inventory"), "/work/inventory");
    for name in OBSERVER_FILES {
        mount(
            args,
            "--ro-bind",
            &repository.join("scripts/reference").join(name),
            &format!("/work/session/{name}"),
        );
    }
    Ok(())
}

const SANDBOX_ENVIRONMENT: &[(&str, &str)] = &[
    ("HOME", "/work/home"),
    ("USER_HOME", "/work/home"),
    ("USER", "reference"),
    ("LOGNAME", "reference"),
    ("PATH", "/run/current-system/sw/bin"),
    ("LANG", "C.UTF-8"),
    ("TMPDIR", "/work/tmp"),
    ("XDG_CACHE_HOME", "/work/tmp/cache"),
    ("ISABELLE_IDENTIFIER", "p0-reference"),
    ("NIX_LD", "/run/current-system/sw/share/nix-ld/lib/ld.so"),
    ("NIX_LD_LIBRARY_PATH", "/run/current-system/sw/share/nix-ld/lib"),
];

pub(super) fn construct_command(
    repository: &Path,
    workspace: &Path,
    run: &Path,
    build_run: Option<&Path>,
    operation: &str,
    bwrap: &Path,
) -> Result<(Vec<OsString>, Vec<String>), StepError> {
    for name in ["home", "tmp", "generated-classes", "generated-demo"] {
        artifacts::require_managed_directory(&run.join(name), workspace)?;
    }
    let mut args: Vec<OsString> = vec![bwrap.as_os_str().into()];
    args.extend(SANDBOX_FLAGS.iter().map(OsString::from));
    mount(&mut args, "--ro-bind", &workspace.join("etc"), "/etc");
    args.extend(["--dir".into(), "/work".into()]);
    mount(&mut args, "--bind", &run.join("home"), "/work/home");
    mount(
        &mut args,
        "--ro-bind",
        &run.join("home/.isabelle/p0-reference/etc"),
        "/work/home/.isabelle/p0-reference/etc",
    );
    mount(&mut args, "--bind", &run.join("tmp"), "/work/tmp");
    mount(
        &mut args,
        "--ro-bind",
        &workspace.join("empty-system-heaps"),
        "/work/empty-system-heaps",
    );
    mount(&mut args, "--ro-bind", &workspace.join("distribution"), "/work/distribution");
    mount(&mut args, "--ro-bind", &workspace.join("fixed-source"), "/work/fixed-source");
    mount(&mut args, "--bind", &run.join("generated-classes"), "/work/fixed-source/lib/classes");
    mount(
        &mut args,
        "--bind",
        &run.join("generated-demo"),
        "/work/fixed-source/src/Tools/Demo/lib",
    );
    if operation == "inventory" {
        mount_inventory_inputs(&mut args, repository, workspace, run, build_run)?;
    }
    args.extend(["--chdir".into(), "/work".into()]);
    for &(key, value) in SANDBOX_ENVIRONMENT {
        args.extend(["--setenv".into(), key.into(), value.into()]);
    }
    args.push("/work/fixed-source/bin/isabelle".into());
    let options = if operation == "build" { build_options() } else { inventory_options() };
    args.extend(options.iter().map(OsString::from));
    Ok((args, options))
}

#[cfg(unix)]
fn signal_group(child: &std::process::Child, signal: i32) -> Result<(), StepError> {
    // Child starts its own session; negative PID addresses only its sandbox process group.
    if unsafe { libc::kill(-(child.id() as i32), signal) } == 0 {
        return Ok(());
    }
    let source = std::io::Error::last_os_error();
    if source.raw_os_error() == Some(libc::ESRCH) {
        return Ok(());
    }
    Err(io_error(format!("signal reference process group {} with {signal}", child.id()), source))
}

#[cfg(unix)]
fn stop_group(child: &mut std::process::Child) -> Result<(), StepError> {
    signal_group(child, libc::SIGTERM)?;
    let deadline = Instant::now() + TERM_GRACE;
    while Instant::now() < deadline {
        if child.try_wait().map_err(|e| io_error("wait for sandbox termination", e))?.is_some() {
            return Ok(());
        }
        std::thread::sleep(POLL_INTERVAL);
    }
    signal_group(child, libc::SIGKILL)?;
    child.wait().map_err(|e| io_error("reap isolated sandbox", e))?;
    Ok(())
}

#[cfg(unix)]
fn wait_for_reference(
    child: &mut std::process::Child,
    run: &Path,
    cancellation: &Cancellation,
    started: Instant,
) -> Result<(Option<i32>, Option<String>), StepError> {
    loop {
        if cancellation.requested() {
            stop_group(child)?;
            return Ok((
                None,
                Some(format!("recoverable: reference interrupted on {}", run.display())),
            ));
        }
        match child.try_wait() {
            Ok(Some(exit)) => return Ok((exit.code(), None)),
            Ok(None) => {},
            Err(error) => {
                stop_group(child)?;
                return Err(io_error("wait for reference sandbox", error));
            },
        }
        if started.elapsed() >= MAX_RUNTIME {
            stop_group(child)?;
            return Ok((
                None,
                Some(format!("recoverable: reference runtime timeout on {}", run.display())),
            ));
        }
        std::thread::sleep(POLL_INTERVAL);
    }
}

#[cfg(unix)]
pub(super) fn run_traced_reference(
    run: &Path,
    argv: &[OsString],
) -> Result<(Option<i32>, Option<String>, Value, f64), StepError> {
    use std::os::unix::process::CommandExt;
    let mut capture = trace::TraceCapture::new(&run.join("events.jsonl"))?;
    let out = OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(run.join("stdout.log"))
        .map_err(|e| io_error("create reference stdout", e))?;
    let err = OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(run.join("stderr.log"))
        .map_err(|e| io_error("create reference stderr", e))?;
    let cancellation = Cancellation::install()?;
    let started = Instant::now();
    let mut command = Command::new(capture.executable()?);
    command
        .args(capture.wrap(argv)?)
        .env_clear()
        .env("PATH", "/run/current-system/sw/bin")
        .stdout(Stdio::from(out))
        .stderr(Stdio::from(err));
    unsafe {
        command.pre_exec(|| {
            if libc::setsid() == -1 { Err(std::io::Error::last_os_error()) } else { Ok(()) }
        });
    }
    let mut spawn = command.spawn();
    if let Err(error) = capture.close_parent_writer() {
        if let Ok(child) = &mut spawn {
            stop_group(child)?;
        }
        return Err(error);
    }
    let (exit_code, mut interruption) = match spawn {
        Ok(mut child) => wait_for_reference(&mut child, run, &cancellation, started)?,
        Err(error) => {
            (None, Some(format!("recoverable: launch sandbox on {}: {error}", run.display())))
        },
    };
    let trace = capture.finish()?;
    if (trace["complete"] != true || trace["event_count"].as_u64().unwrap_or(0) == 0)
        && interruption.is_none()
    {
        interruption = Some(format!(
            "user-fixable: incomplete syscall observation on {}: {}",
            run.display(),
            trace["errors"]
        ));
    }
    Ok((exit_code, interruption, trace, started.elapsed().as_secs_f64()))
}

#[cfg(not(unix))]
pub(super) fn run_traced_reference(
    _run: &Path,
    _argv: &[OsString],
) -> Result<(Option<i32>, Option<String>, Value, f64), StepError> {
    Err(StepError::Input("reference sandbox requires Unix process groups".into()))
}
