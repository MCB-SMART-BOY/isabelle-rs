//! A delegated cgroup is the complete process domain, not a best-effort process group.
use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::os::fd::AsRawFd;
use std::os::unix::fs::MetadataExt;
use std::path::{Component, Path, PathBuf};
use std::time::{Duration, Instant};

use super::super::approved_identity::ResourceBudget;
use crate::runner::{StepError, io_error};

const DRAIN_DEADLINE: Duration = Duration::from_secs(30);
const POLL_INTERVAL: Duration = Duration::from_millis(100);
const CGROUP2_MAGIC: libc::c_long = 0x6367_7270;

pub(super) struct Domain {
    path: PathBuf,
    membership: File,
}

fn write_control(path: &Path, value: impl AsRef<[u8]>) -> Result<(), StepError> {
    let mut file = OpenOptions::new()
        .write(true)
        .open(path)
        .map_err(|source| io_error(format!("open cgroup control {}", path.display()), source))?;
    file.write_all(value.as_ref())
        .map_err(|source| io_error(format!("set cgroup control {}", path.display()), source))
}

fn require_delegated(parent: &Path) -> Result<(), StepError> {
    let valid = parent.is_absolute()
        && parent.starts_with("/sys/fs/cgroup/")
        && parent
            .components()
            .all(|part| matches!(part, Component::RootDir | Component::Normal(_)));
    if !valid {
        return Err(StepError::Input(
            "reference cgroup must be a delegated /sys/fs/cgroup child".into(),
        ));
    }
    let resolved = parent
        .canonicalize()
        .map_err(|source| io_error("resolve reference cgroup parent", source))?;
    if resolved != parent {
        return Err(StepError::Input("reference cgroup path contains a symlink".into()));
    }
    let c_path = std::ffi::CString::new(parent.as_os_str().as_encoded_bytes())
        .map_err(|_| StepError::Input("invalid reference cgroup path".into()))?;
    let mut stat = unsafe { std::mem::zeroed::<libc::statfs>() };
    if unsafe { libc::statfs(c_path.as_ptr(), &mut stat) } != 0 {
        return Err(io_error("stat delegated cgroup filesystem", std::io::Error::last_os_error()));
    }
    if stat.f_type != CGROUP2_MAGIC {
        return Err(StepError::Input("reference containment requires cgroup v2".into()));
    }
    let metadata =
        fs::metadata(parent).map_err(|source| io_error("inspect delegated cgroup", source))?;
    if metadata.uid() != unsafe { libc::geteuid() } {
        return Err(StepError::Input("reference cgroup is not delegated to this user".into()));
    }
    let enabled = fs::read_to_string(parent.join("cgroup.subtree_control"))
        .map_err(|source| io_error("read delegated cgroup controllers", source))?;
    if !["cpu", "memory", "pids"]
        .iter()
        .all(|part| enabled.split_whitespace().any(|item| item == *part))
    {
        return Err(StepError::Input(
            "reference cgroup lacks delegated cpu/memory/pids controllers".into(),
        ));
    }
    Ok(())
}

impl Domain {
    pub(super) fn create(run: &Path, budget: &ResourceBudget) -> Result<Self, StepError> {
        let parent = std::env::var_os("REFERENCE_CGROUP_PARENT").ok_or_else(|| {
            StepError::Input("REFERENCE_CGROUP_PARENT delegated cgroup is required".into())
        })?;
        let parent = Path::new(&parent);
        require_delegated(parent)?;
        let name =
            run.file_name().ok_or_else(|| StepError::Input("reference run id missing".into()))?;
        let path = parent.join(name);
        fs::create_dir(&path).map_err(|source| {
            io_error(format!("create reference cgroup {}", path.display()), source)
        })?;
        let limits = [
            ("memory.max", budget.memory_bytes.to_string()),
            ("memory.swap.max", budget.swap_bytes.to_string()),
            ("pids.max", budget.pids.to_string()),
            ("cpu.max", format!("{} {}", budget.cpu_quota_us, budget.cpu_period_us)),
        ];
        for (file, value) in limits {
            write_control(&path.join(file), value)?;
        }
        let membership = OpenOptions::new()
            .write(true)
            .open(path.join("cgroup.procs"))
            .map_err(|source| io_error("open reference cgroup membership", source))?;
        Ok(Self { path, membership })
    }

    pub(super) fn clone_membership(&self) -> Result<File, StepError> {
        self.membership
            .try_clone()
            .map_err(|source| io_error("duplicate reference cgroup membership", source))
    }

    /// Called only in pre_exec: decimal PID formatting and write use no allocator or locks.
    pub(super) unsafe fn join_before_exec(membership: &File) -> std::io::Result<()> {
        let pid = unsafe { libc::getpid() };
        let mut digits = [0u8; 16];
        let mut value = pid as usize;
        let mut start = digits.len();
        while value > 0 {
            start -= 1;
            digits[start] = b'0' + (value % 10) as u8;
            value /= 10;
        }
        let length = digits.len() - start;
        let written =
            unsafe { libc::write(membership.as_raw_fd(), digits[start..].as_ptr().cast(), length) };
        if written != length as isize {
            return Err(std::io::Error::last_os_error());
        }
        Ok(())
    }

    pub(super) fn is_empty(&self) -> Result<bool, StepError> {
        let events = fs::read_to_string(self.path.join("cgroup.events"))
            .map_err(|source| io_error("inspect reference cgroup population", source))?;
        Ok(events.lines().any(|line| line == "populated 0"))
    }

    pub(super) fn terminate_and_drain(&self) -> Result<(), StepError> {
        write_control(&self.path.join("cgroup.kill"), "1")?;
        self.drain()
    }

    pub(super) fn drain(&self) -> Result<(), StepError> {
        let start = Instant::now();
        while !self.is_empty()? {
            if start.elapsed() >= DRAIN_DEADLINE {
                return Err(StepError::Input(format!(
                    "reference cgroup failed to drain: {}",
                    self.path.display()
                )));
            }
            std::thread::sleep(POLL_INTERVAL);
        }
        Ok(())
    }

    pub(super) fn remove(self) -> Result<(), StepError> {
        self.drain()?;
        drop(self.membership);
        fs::remove_dir(&self.path).map_err(|source| {
            io_error(format!("remove drained cgroup {}", self.path.display()), source)
        })
    }
}
