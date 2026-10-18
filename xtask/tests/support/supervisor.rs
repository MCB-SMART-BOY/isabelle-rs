use std::{
    fs,
    os::unix::process::CommandExt,
    path::{Path, PathBuf},
    process::{Child, Command, ExitStatus},
    sync::atomic::{AtomicU64, Ordering},
    thread,
    time::{Duration, Instant},
};

use serde_json::Value;

static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);
pub const WAIT_LIMIT: Duration = Duration::from_secs(12);
pub const CANCEL_LIMIT: Duration = Duration::from_secs(6);
pub const LOG_BYTES: u64 = 8 * 1024 * 1024;

pub struct Fixture {
    pub root: PathBuf,
}

impl Fixture {
    pub fn create() -> Self {
        let number = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir()
            .join(format!("hol-supervisor-rust-{}-{number}", std::process::id()));
        fs::create_dir(&root).expect("create isolated fixture");
        Self { root }
    }

    pub fn worker(&self) -> PathBuf {
        let path = self.root.join("fixture-worker");
        let source =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/support/supervisor_worker.rs");
        let status = Command::new("rustc")
            .args(["--edition=2024", "-o"])
            .arg(&path)
            .arg(&source)
            .status()
            .expect("compile Rust fixture worker");
        assert!(status.success(), "compile Rust fixture worker");
        path
    }

    pub fn command(&self, worker: &Path, output_dir: &Path, mode: &str) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_xtask"));
        command
            .env("PROFILE_PID_DIR", &self.root)
            .env("SUPERVISOR_WORKER_MODE", mode)
            .arg("supervise")
            .args(["--timeout-secs", "1", "--memory-mib", "512", "--output-dir"])
            .arg(output_dir)
            .arg("--worker")
            .arg(worker)
            .arg("--source-root")
            .arg(&self.root)
            .args(["--theory", "Fixture", "--lemma", "lemma"]);
        command
    }

    pub fn scale_command(&self, worker: &Path, output_dir: &Path, mode: &str) -> Command {
        let mut scale = Command::new(env!("CARGO_BIN_EXE_xtask"));
        scale
            .env("PROFILE_PID_DIR", &self.root)
            .env("SUPERVISOR_WORKER_MODE", "waiting-descendant")
            .current_dir(&self.root)
            .arg("supervise")
            .args(["--timeout-secs", "1", "--memory-mib", "512", "--output-dir"])
            .arg(output_dir)
            .arg("--worker")
            .arg(worker)
            .args(["--scale-mode", mode]);
        scale
    }

    pub fn install_barrier_unshare(&self, worker: &Path) -> (PathBuf, PathBuf, PathBuf) {
        let bin_dir = self.root.join("bin");
        fs::create_dir(&bin_dir).expect("create fixture bin");
        let barrier = self.root.join("unshare-entered");
        let release = self.root.join("unshare-release");
        fs::copy(worker, bin_dir.join("unshare")).expect("install Rust unshare barrier");
        (bin_dir, barrier, release)
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.root).expect("remove isolated fixture");
    }
}

pub fn read_report(output_dir: &Path) -> Value {
    serde_json::from_slice(
        &fs::read(output_dir.join("supervisor.json")).expect("read supervisor report"),
    )
    .expect("valid supervisor JSON")
}

pub fn find_executable(name: &str) -> PathBuf {
    std::env::split_paths(&std::env::var_os("PATH").expect("PATH is set"))
        .map(|dir| dir.join(name))
        .find(|path| path.is_file())
        .unwrap_or_else(|| panic!("missing executable: {name}"))
}

pub fn signal_process(pid: u32, signal: i32) {
    assert_eq!(unsafe { libc::kill(pid as i32, signal) }, 0, "signal {signal} to {pid}");
}

pub fn stop_stalled_supervisor(child: &mut Child) {
    let _ = unsafe { libc::kill(child.id() as i32, libc::SIGTERM) };
    let deadline = Instant::now() + WAIT_LIMIT;
    while Instant::now() < deadline {
        if child.try_wait().expect("check stopped supervisor").is_some() {
            return;
        }
        thread::yield_now();
    }
    child.kill().expect("force stop stalled supervisor");
    child.wait().expect("reap force-stopped supervisor");
}

pub fn wait_for_exit(child: &mut Child) -> ExitStatus {
    let deadline = Instant::now() + WAIT_LIMIT;
    loop {
        if let Some(status) = child.try_wait().expect("check supervisor") {
            return status;
        }
        if Instant::now() >= deadline {
            stop_stalled_supervisor(child);
            panic!("supervisor failed to exit within {WAIT_LIMIT:?}");
        }
        thread::yield_now();
    }
}

pub fn wait_for_file(child: &mut Child, path: &Path) {
    let deadline = Instant::now() + WAIT_LIMIT;
    loop {
        let has_exited = child.try_wait().expect("check supervisor").is_some();
        if path.exists() {
            return;
        }
        assert!(!has_exited, "supervisor exited before creating {}", path.display());
        if Instant::now() >= deadline {
            stop_stalled_supervisor(child);
            panic!("supervisor never created {}", path.display());
        }
        thread::yield_now();
    }
}

pub fn wait_for_pid_file(child: &mut Child, path: &Path) -> u32 {
    let deadline = Instant::now() + WAIT_LIMIT;
    loop {
        let has_exited = child.try_wait().expect("check supervisor").is_some();
        if let Ok(contents) = fs::read_to_string(path)
            && let Ok(pid) = contents.trim().parse()
        {
            return pid;
        }
        assert!(!has_exited, "supervisor exited before writing {}", path.display());
        if Instant::now() >= deadline {
            stop_stalled_supervisor(child);
            panic!("worker never wrote {}", path.display());
        }
        thread::yield_now();
    }
}

pub fn assert_process_reaped(pid: u32) {
    assert!(!Path::new(&format!("/proc/{pid}")).exists(), "process {pid} remains in /proc");
}

pub fn set_permissive_umask(command: &mut Command) {
    // Safety: umask is async-signal-safe; no locks or allocations occur after fork.
    unsafe {
        command.pre_exec(|| {
            libc::umask(0);
            Ok(())
        });
    }
}

pub fn set_barrier_env(command: &mut Command, bin_dir: PathBuf, barrier: &Path, release: &Path) {
    let inherited_path = std::env::var_os("PATH").expect("PATH is set");
    let mut paths = vec![bin_dir];
    paths.extend(std::env::split_paths(&inherited_path));
    command.env("PATH", std::env::join_paths(paths).expect("join PATH"));
    command.env("REAL_UNSHARE", find_executable("unshare"));
    command.env("PROFILE_START_BARRIER", barrier).env("PROFILE_START_RELEASE", release);
}
