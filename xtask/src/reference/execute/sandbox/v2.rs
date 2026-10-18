use std::ffi::OsString;
use std::fs::{self, OpenOptions};
use std::os::unix::process::CommandExt;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use serde_json::Value;

use super::super::super::{approved_identity::ResourceBudget, artifacts, trace};
use super::super::{build_options, cgroup, inventory_options};
use super::{Cancellation, POLL_INTERVAL, SANDBOX_ENVIRONMENT, SANDBOX_FLAGS, mount};
use crate::runner::{StepError, io_error};

fn mount_v2_inputs(
    args: &mut Vec<OsString>,
    workspace: &Path,
    run: &Path,
    build: Option<&Path>,
    operation: &str,
) -> Result<(), StepError> {
    mount(args, "--ro-bind", &workspace.join("etc"), "/etc");
    args.extend(["--dir".into(), "/work".into()]);
    mount(args, "--bind", &run.join("home"), "/work/home");
    mount(
        args,
        "--ro-bind",
        &run.join("home/.isabelle/p0-reference/etc"),
        "/work/home/.isabelle/p0-reference/etc",
    );
    mount(args, "--bind", &run.join("tmp"), "/work/tmp");
    mount(args, "--ro-bind", &workspace.join("empty-system-heaps"), "/work/empty-system-heaps");
    mount(args, "--ro-bind", &workspace.join("distribution"), "/work/distribution");
    mount(args, "--ro-bind", &run.join("fixed-source"), "/work/fixed-source");
    args.extend(["--dir".into(), "/work/inventory".into()]);
    mount(args, "--bind", &run.join("inventory"), "/work/inventory");
    if operation == "inventory" {
        let _build = build.ok_or_else(|| StepError::Input("v2 inventory requires build".into()))?;
        let heap = run.join("pure-heap");
        artifacts::require_managed_directory(&heap, workspace)?;
        mount(args, "--ro-bind", &heap, "/work/empty-system-heaps");
        args.extend(["--dir".into(), "/work/session".into()]);
        mount(args, "--ro-bind", &run.join("session"), "/work/session");
    }
    Ok(())
}

pub(in crate::reference::execute) fn construct_command(
    workspace: &Path,
    run: &Path,
    build: Option<&Path>,
    operation: &str,
    bwrap: &Path,
) -> Result<(Vec<OsString>, Vec<String>), StepError> {
    for name in ["home", "tmp", "inventory"] {
        artifacts::require_managed_directory(&run.join(name), workspace)?;
    }
    let mut argv: Vec<OsString> = vec![bwrap.as_os_str().into()];
    argv.extend(SANDBOX_FLAGS.iter().map(OsString::from));
    mount_v2_inputs(&mut argv, workspace, run, build, operation)?;
    argv.extend(["--chdir".into(), "/work".into()]);
    for &(key, value) in SANDBOX_ENVIRONMENT {
        argv.extend(["--setenv".into(), key.into(), value.into()]);
    }
    let run_id = run
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| StepError::Input("non-UTF8 reference run ID".into()))?;
    let root0_id = format!("{run_id}:Pure:ROOT0.ML:0");
    let root_id = format!("{run_id}:Pure:ROOT.ML:1");
    for (key, value) in [
        ("REFERENCE_OBSERVATION_RUN_ID", run_id),
        ("REFERENCE_OBSERVATION_PHASE", operation),
        ("REFERENCE_OBSERVATION_RAW", "/work/inventory/observer-raw"),
        ("ISABELLE_REFERENCE_OBSERVER_RAW", "/work/inventory/observer-raw"),
        ("REFERENCE_OBSERVATION_SOURCE_HASHES", "/work/source-hashes.tsv"),
        ("REFERENCE_OBSERVATION_SOURCE_ROOT", "/work/fixed-source"),
        ("REFERENCE_OBSERVATION_SESSION_ROOT", "/work/session"),
        ("REFERENCE_OBSERVATION_ROOT0_LOAD_ID", &root0_id),
        ("REFERENCE_OBSERVATION_ROOT_LOAD_ID", &root_id),
    ] {
        argv.extend(["--setenv".into(), key.into(), value.into()]);
    }
    mount(&mut argv, "--ro-bind", &run.join("source-hashes.tsv"), "/work/source-hashes.tsv");
    argv.push("/work/fixed-source/bin/isabelle".into());
    let options = if operation == "build" { build_options() } else { inventory_options() };
    argv.extend(options.iter().map(OsString::from));
    Ok((argv, options))
}

fn accumulated_size(path: &Path, budget: u64) -> Result<u64, StepError> {
    let mut size = 0u64;
    for entry in fs::read_dir(path).map_err(|source| io_error("scan reference scratch", source))? {
        let entry = entry.map_err(|source| io_error("read reference scratch entry", source))?;
        let kind =
            entry.file_type().map_err(|source| io_error("inspect reference scratch", source))?;
        let length = if kind.is_dir() {
            accumulated_size(&entry.path(), budget)?
        } else if kind.is_file() {
            entry.metadata().map_err(|source| io_error("stat reference scratch", source))?.len()
        } else {
            return Err(StepError::Input(
                "reference scratch contains an unsafe link or device".into(),
            ));
        };
        size = size
            .checked_add(length)
            .ok_or_else(|| StepError::Input("reference scratch size overflow".into()))?;
        if size > budget {
            return Err(StepError::Input("reference scratch exceeds preapproved limit".into()));
        }
    }
    Ok(size)
}

fn enforce_outputs(run: &Path, budget: &ResourceBudget) -> Result<(), StepError> {
    let mut total = 0u64;
    for name in ["home", "tmp", "inventory"] {
        total = total
            .checked_add(accumulated_size(&run.join(name), budget.scratch_bytes)?)
            .ok_or_else(|| StepError::Input("reference scratch overflow".into()))?;
        if total > budget.scratch_bytes {
            return Err(StepError::Input("reference scratch exceeds preapproved limit".into()));
        }
    }
    for name in ["events.jsonl", "stdout.log", "stderr.log"] {
        total = total
            .checked_add(
                fs::metadata(run.join(name))
                    .map_err(|source| io_error("stat reference output", source))?
                    .len(),
            )
            .ok_or_else(|| StepError::Input("reference output overflow".into()))?;
    }
    if total > budget.scratch_bytes {
        return Err(StepError::Input("reference logs exceed preapproved limit".into()));
    }
    let raw = run.join("inventory/observer-raw");
    if raw.exists()
        && fs::metadata(&raw).map_err(|source| io_error("stat observer raw", source))?.len()
            > budget.raw_total_bytes
    {
        return Err(StepError::Input("reference raw observer output exceeds preapproval".into()));
    }
    Ok(())
}

fn monitor(
    mut child: std::process::Child,
    domain: &cgroup::Domain,
    run: &Path,
    budget: &ResourceBudget,
    cancel: &Cancellation,
    started: Instant,
) -> Result<i32, StepError> {
    loop {
        let is_interrupted =
            cancel.requested() || started.elapsed() >= Duration::from_secs(budget.wall_seconds);
        let budget_status = enforce_outputs(run, budget);
        if is_interrupted || budget_status.is_err() {
            domain.terminate_and_drain()?;
            child.wait().map_err(|source| io_error("reap reference after cgroup kill", source))?;
            budget_status?;
            return Err(StepError::Input(format!(
                "reference interrupted or timed out in {}",
                run.display()
            )));
        }
        let status = match child.try_wait() {
            Ok(status) => status,
            Err(source) => {
                domain.terminate_and_drain()?;
                child.wait().map_err(|cause| io_error("reap failed reference wait", cause))?;
                return Err(io_error("wait reference domain", source));
            },
        };
        if let Some(status) = status {
            domain.drain()?;
            return status
                .code()
                .ok_or_else(|| StepError::Input("reference terminated by signal".into()));
        }
        std::thread::sleep(POLL_INTERVAL);
    }
}

pub(in crate::reference::execute) fn run_reference(
    run: &Path,
    argv: &[OsString],
    budget: &ResourceBudget,
) -> Result<(Option<i32>, Option<String>, Value, f64), StepError> {
    let domain = cgroup::Domain::create(run, budget)?;
    let execution = run_in_domain(&domain, run, argv, budget);
    let drained = domain.is_empty()?;
    if !drained {
        domain.terminate_and_drain()?;
    }
    domain.remove()?;
    execution
}

fn run_in_domain(
    domain: &cgroup::Domain,
    run: &Path,
    argv: &[OsString],
    budget: &ResourceBudget,
) -> Result<(Option<i32>, Option<String>, Value, f64), StepError> {
    let mut trace = trace::TraceCapture::new(&run.join("events.jsonl"))?;
    let stdout = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(run.join("stdout.log"))
        .map_err(|source| io_error("create bounded reference stdout", source))?;
    let stderr = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(run.join("stderr.log"))
        .map_err(|source| io_error("create bounded reference stderr", source))?;
    let cancellation = Cancellation::install()?;
    let started = Instant::now();
    let mut command = Command::new(trace.executable()?);
    command
        .args(trace.wrap(argv)?)
        .env_clear()
        .env("PATH", "/run/current-system/sw/bin")
        .stdout(Stdio::from(stdout))
        .stderr(Stdio::from(stderr));
    let membership = domain.clone_membership()?;
    // The closure owns the already-open membership fd; only async-signal-safe calls run after fork.
    unsafe {
        command.pre_exec(move || {
            cgroup::Domain::join_before_exec(&membership)?;
            if libc::setsid() == -1 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
    let mut spawned = command.spawn();
    if let Err(error) = trace.close_parent_writer() {
        if let Ok(child) = &mut spawned {
            domain.terminate_and_drain()?;
            child.wait().map_err(|source| io_error("reap failed reference trace", source))?;
        }
        return Err(error);
    }
    let child =
        spawned.map_err(|source| io_error("launch preapproved reference cgroup", source))?;
    let status = monitor(child, domain, run, budget, &cancellation, started);
    let observed = trace.finish()?;
    let exit_code = status?;
    enforce_outputs(run, budget)?;
    if observed["complete"] != true || observed["event_count"].as_u64().unwrap_or(0) == 0 {
        return Err(StepError::Input("reference syscall trace is incomplete".into()));
    }
    Ok((Some(exit_code), None, observed, started.elapsed().as_secs_f64()))
}
