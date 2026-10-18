#[path = "linux/runtime.rs"]
mod runtime;
#[path = "linux/supervision.rs"]
mod supervision;

use super::{
    MAX_OUTPUT, MAX_WALL, SolverConfig, SolverError, SolverErrorKind, SolverOutput, SolverRequest,
};
use crate::ml::host::lifecycle::{BuildLifecycle, Cancellation, TaskLease};
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::os::fd::{AsRawFd, RawFd};
use std::os::unix::fs::MetadataExt;
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant};
const VERIT_HASH: &str = "b7cb42f384bcabd156ef3176e3706b5cb3479f1769d9be716d339568faa81526";
const LOADER_HASH: &str = "e2e9975273f65f7cb730f4fcc8a9a5aae62763b6263de877a8b896311819d7b6";
const LIBC_HASH: &str = "ef3843ed24108fc3cfde4095cdb12e0643b9953f4b902bad8152d002fc0cbbe3";
const LIBM_HASH: &str = "935fd3fa15c35746041cfa475003571dc51b9ce0c395034ac9d50bb8e1583919";
const LIBGMP_HASH: &str = "40922323f119e29040c63b5f7562c74aed5f3f653d23ad510812c845faf0ed02";
const BWRAP_HASH: &str = "57ab9a14f8e1a432b54096aa259ea730de0d16cca09406721b30d1c717a46cf1";
const MAX_ELF_BYTES: u64 = 64 * 1024 * 1024;
const O_NONBLOCK: i32 = 0o4000;
const O_NOFOLLOW: i32 = 0o400000;
const MEMORY_BYTES: &str = "2147483648";
const CPU_QUOTA: &str = "100000 100000";
const PIDS: &str = "16";
const CLEANUP_TIMEOUT: Duration = Duration::from_secs(15);
const POLL_INTERVAL: Duration = Duration::from_millis(10);
const INTERNAL_FLAG: &str = "--internal-solver-launcher";
const CGROUP2_MAGIC: i64 = 0x6367_7270;
const MFD_ALLOW_SEALING: u32 = 0x0002;
const F_ADD_SEALS: i32 = 1033;
const F_GET_SEALS: i32 = 1034;
const F_GETFD: i32 = 1;
const F_SETFD: i32 = 2;
const FD_CLOEXEC: i32 = 1;
const F_SEAL_SEAL: i32 = 1;
const F_SEAL_SHRINK: i32 = 2;
const F_SEAL_GROW: i32 = 4;
const F_SEAL_WRITE: i32 = 8;
const SEALED: i32 = F_SEAL_SEAL | F_SEAL_SHRINK | F_SEAL_GROW | F_SEAL_WRITE;
const PR_SET_NO_NEW_PRIVS: i32 = 38;
const RLIMIT_CPU: i32 = 0;
static NEXT_DOMAIN: AtomicU64 = AtomicU64::new(0);
static SOLVER_ACTIVE: AtomicBool = AtomicBool::new(false);
struct SolverPermit;

impl SolverPermit {
    fn acquire() -> Result<Self, SolverError> {
        SOLVER_ACTIVE.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed).map_err(
            |_| {
                SolverError::new(
                    SolverErrorKind::Permission,
                    "run solver",
                    "trusted supervisor already active or cleanup incomplete",
                )
            },
        )?;
        Ok(Self)
    }
}

impl Drop for SolverPermit {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            SOLVER_ACTIVE.store(false, Ordering::Release);
        }
    }
}

#[repr(C)]
struct Rlimit {
    current: u64,
    maximum: u64,
}
// Linux x86_64 libc ABI. Calls are confined to trusted, fixed control data; ML never sees an fd.
unsafe extern "C" {
    fn memfd_create(name: *const i8, flags: u32) -> i32;
    fn fcntl(fd: i32, command: i32, ...) -> i32;
    fn dup2(old: i32, new: i32) -> i32;
    fn setrlimit(resource: i32, limit: *const Rlimit) -> i32;
    fn prctl(option: i32, ...) -> i32;
    fn getpid() -> i32;
    fn fstatfs(fd: i32, buffer: *mut u8) -> i32;
}

fn system(operation: &'static str, path: &Path, error: io::Error) -> SolverError {
    SolverError::io(SolverErrorKind::System, operation, format!("{}", path.display()), error)
}
fn prerequisite(operation: &'static str, reason: impl Into<String>) -> SolverError {
    SolverError::new(SolverErrorKind::BlockedPrerequisite, operation, reason)
}

fn check_owned_directory(path: &Path) -> Result<File, SolverError> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| system("inspect trusted directory", path, error))?;
    if !metadata.is_dir() || metadata.file_type().is_symlink() || metadata.mode() & 0o022 != 0 {
        return Err(prerequisite(
            "inspect trusted directory",
            format!("unsafe writable or non-directory {}", path.display()),
        ));
    }
    File::open(path).map_err(|error| system("open trusted directory", path, error))
}

pub(super) fn check_config(config: &SolverConfig) -> Result<(), SolverError> {
    if [
        &config.executable,
        &config.staging_root,
        &config.delegated_cgroup_root,
        &config.bubblewrap,
        &config.elf_loader,
        &config.libc,
        &config.libm,
        &config.libgmp,
    ]
    .iter()
    .any(|path| !path.is_absolute())
    {
        return Err(prerequisite(
            "validate solver configuration",
            "all infrastructure paths must be absolute",
        ));
    }
    let _staging = check_owned_directory(&config.staging_root)?;
    let root = check_owned_directory(&config.delegated_cgroup_root)?;
    let mut statfs = [0u8; 128];
    // SAFETY: `statfs` has space for Linux x86_64 struct statfs (120 bytes).
    if unsafe { fstatfs(root.as_raw_fd(), statfs.as_mut_ptr()) } != 0 {
        return Err(system(
            "inspect cgroup filesystem",
            &config.delegated_cgroup_root,
            io::Error::last_os_error(),
        ));
    }
    if i64::from_ne_bytes(
        statfs[..8]
            .try_into()
            .map_err(|_| prerequisite("inspect cgroup", "invalid statfs layout"))?,
    ) != CGROUP2_MAGIC
    {
        return Err(prerequisite("inspect cgroup filesystem", "delegated root is not cgroup v2"));
    }
    let controllers = fs::read_to_string(config.delegated_cgroup_root.join("cgroup.controllers"))
        .map_err(|error| {
        system("read cgroup controllers", &config.delegated_cgroup_root, error)
    })?;
    if !["cpu", "memory", "pids"]
        .iter()
        .all(|controller| controllers.split_whitespace().any(|found| found == *controller))
    {
        return Err(prerequisite(
            "inspect cgroup controllers",
            "cpu, memory, and pids must be delegated",
        ));
    }
    for (path, expected) in [
        (&config.executable, VERIT_HASH),
        (&config.elf_loader, LOADER_HASH),
        (&config.libc, LIBC_HASH),
        (&config.libm, LIBM_HASH),
        (&config.libgmp, LIBGMP_HASH),
        (&config.bubblewrap, BWRAP_HASH),
    ] {
        let mut file = open_approved_file(path)?;
        if hash_file(&mut file).map_err(|error| system("hash approved executable", path, error))?
            != expected
        {
            return Err(prerequisite(
                "authenticate approved executable",
                format!("{} digest differs from fixed profile", path.display()),
            ));
        }
    }
    Ok(())
}

fn open_approved_file(path: &Path) -> Result<File, SolverError> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(O_NONBLOCK | O_NOFOLLOW)
        .open(path)
        .map_err(|error| system("open approved executable", path, error))?;
    let metadata =
        file.metadata().map_err(|error| system("inspect approved executable", path, error))?;
    if !metadata.is_file() || metadata.len() > MAX_ELF_BYTES || metadata.len() == 0 {
        return Err(prerequisite(
            "inspect approved executable",
            format!("{} must be a bounded regular file", path.display()),
        ));
    }
    Ok(file)
}

fn hash_file(file: &mut File) -> io::Result<String> {
    let mut sha = Sha256::new();
    let mut buffer = [0u8; 65536];
    let mut remaining = MAX_ELF_BYTES;
    loop {
        let count = file.read(&mut buffer[..65536.min((remaining + 1) as usize)])?;
        if count == 0 {
            break;
        }
        if count as u64 > remaining {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "executable grew beyond 64 MiB",
            ));
        }
        remaining -= count as u64;
        sha.update(&buffer[..count]);
    }
    Ok(base16ct::lower::encode_string(&sha.finalize()))
}

fn write_checked(domain: &Path, name: &str, value: &str) -> Result<(), SolverError> {
    let file = domain.join(name);
    fs::write(&file, value).map_err(|error| system("set cgroup limit", &file, error))?;
    let readback =
        fs::read_to_string(&file).map_err(|error| system("verify cgroup limit", &file, error))?;
    if !readback.split_whitespace().eq(value.split_whitespace()) {
        return Err(prerequisite(
            "verify cgroup limit",
            format!("{} did not accept required value", file.display()),
        ));
    }
    Ok(())
}

fn create_domain(
    config: &SolverConfig,
    incomplete: &mut Option<PathBuf>,
) -> Result<PathBuf, SolverError> {
    for _ in 0..64 {
        let id = NEXT_DOMAIN.fetch_add(1, Ordering::Relaxed);
        let name = format!(
            "solver-{}-{}-{id}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map_err(|_| prerequisite("create cgroup", "system clock precedes epoch"))?
                .as_nanos()
        );
        let domain = config.delegated_cgroup_root.join(name);
        match fs::create_dir(&domain) {
            Ok(()) => {
                if let Err(error) = (|| {
                    write_checked(&domain, "memory.max", MEMORY_BYTES)?;
                    write_checked(&domain, "memory.swap.max", "0")?;
                    write_checked(&domain, "pids.max", PIDS)?;
                    write_checked(&domain, "cpu.max", CPU_QUOTA)?;
                    Ok::<_, SolverError>(())
                })() {
                    if let Err(cleanup_error) = fs::remove_dir(&domain) {
                        *incomplete = Some(domain.clone());
                        return Err(SolverError::io(
                            SolverErrorKind::CleanupFailure,
                            "retire partially configured cgroup",
                            format!(
                                "{}; configuration failure: {error}; source: {:?}",
                                domain.display(),
                                error.source
                            ),
                            cleanup_error,
                        ));
                    }
                    return Err(error);
                }
                return Ok(domain);
            },
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(system("create delegated cgroup", &domain, error)),
        }
    }
    Err(prerequisite("create delegated cgroup", "unique cgroup names exhausted"))
}

fn signal_kill(domain: &Path) -> Result<(), SolverError> {
    let path = domain.join("cgroup.kill");
    let mut file = OpenOptions::new()
        .write(true)
        .custom_flags(O_NONBLOCK | O_NOFOLLOW)
        .open(&path)
        .map_err(|error| system("open cgroup kill control", &path, error))?;
    match file.write(b"1").map_err(|error| system("terminate cgroup", &path, error))? {
        1 => Ok(()),
        _ => Err(prerequisite("terminate cgroup", format!("short write to {}", path.display()))),
    }
}

// Copies only from the already opened fd. The pinned bwrap copies this sealed
// snapshot into a private read-only mount, without reopening its source pathname.
fn seal_file(source: &mut File, expected: &str) -> Result<File, SolverError> {
    source.seek(SeekFrom::Start(0)).map_err(|error| {
        SolverError::io(SolverErrorKind::System, "rewind executable fd", "approved source", error)
    })?;
    // SAFETY: constant NUL-terminated name; memfd_create returns an owned fd on success.
    let descriptor = unsafe { memfd_create(c"isabelle-verit".as_ptr(), MFD_ALLOW_SEALING) };
    if descriptor < 0 {
        return Err(prerequisite(
            "create sealed executable snapshot",
            io::Error::last_os_error().to_string(),
        ));
    }
    use std::os::fd::FromRawFd;
    // SAFETY: descriptor is uniquely owned and >= 0.
    let mut sealed = unsafe { File::from_raw_fd(descriptor) };
    let copied = io::copy(&mut source.take(MAX_ELF_BYTES + 1), &mut sealed).map_err(|error| {
        SolverError::io(
            SolverErrorKind::System,
            "copy approved executable fd",
            "snapshot source",
            error,
        )
    })?;
    if copied > MAX_ELF_BYTES {
        return Err(prerequisite("seal executable snapshot", "input exceeds 64 MiB"));
    }
    // SAFETY: fcntl acts only on this owned fd with a fixed seal mask.
    if unsafe { fcntl(descriptor, F_ADD_SEALS, SEALED) } != 0 {
        return Err(prerequisite(
            "seal executable snapshot",
            io::Error::last_os_error().to_string(),
        ));
    }
    if unsafe { fcntl(descriptor, F_GET_SEALS) } != SEALED {
        return Err(prerequisite(
            "verify executable seals",
            "complete immutable seals not present",
        ));
    }
    sealed.seek(SeekFrom::Start(0)).map_err(|error| {
        SolverError::io(SolverErrorKind::System, "rewind executable snapshot", "sealed fd", error)
    })?;
    if hash_file(&mut sealed).map_err(|error| {
        SolverError::io(SolverErrorKind::System, "hash sealed executable", "sealed fd", error)
    })? != expected
    {
        return Err(prerequisite(
            "authenticate sealed executable",
            "snapshot digest differs from fixed profile",
        ));
    }
    Ok(sealed)
}

fn set_fd_inheritance(fd: RawFd, should_inherit: bool) -> io::Result<()> {
    // SAFETY: trusted fd created by parent, fcntl changes only its CLOEXEC flag.
    let flags = unsafe { fcntl(fd, F_GETFD) };
    if flags < 0 {
        return Err(io::Error::last_os_error());
    }
    let flags = if should_inherit { flags & !FD_CLOEXEC } else { flags | FD_CLOEXEC };
    if unsafe { fcntl(fd, F_SETFD, flags) } < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

fn same_executable() -> Result<File, SolverError> {
    let current = File::open("/proc/self/exe").map_err(|error| {
        SolverError::io(SolverErrorKind::System, "open current executable", "/proc/self/exe", error)
    })?;
    let current_meta = current.metadata().map_err(|error| {
        SolverError::io(
            SolverErrorKind::System,
            "inspect current executable",
            "/proc/self/exe",
            error,
        )
    })?;
    let pathname = std::env::current_exe().map_err(|error| {
        SolverError::io(SolverErrorKind::System, "locate current executable", "current_exe", error)
    })?;
    let path_meta = fs::metadata(&pathname)
        .map_err(|error| system("inspect current executable path", &pathname, error))?;
    if current_meta.ino() != path_meta.ino() || current_meta.dev() != path_meta.dev() {
        return Err(prerequisite(
            "authenticate trusted launcher",
            "current executable path changed since process start",
        ));
    }
    Ok(current)
}

pub(super) use runtime::{run, run_launcher_if_requested};

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;
    use std::os::unix::ffi::OsStrExt;

    unsafe extern "C" {
        fn mkfifo(path: *const i8, mode: u32) -> i32;
    }

    #[test]
    fn approved_file_fifo_and_oversized_file_rejected_before_read() {
        let root =
            std::env::temp_dir().join(format!("isabelle-solver-open-{}", std::process::id()));
        fs::create_dir(&root).unwrap();
        let fifo = root.join("fifo");
        let fifo_name = CString::new(fifo.as_os_str().as_bytes()).unwrap();
        assert_eq!(unsafe { mkfifo(fifo_name.as_ptr(), 0o600) }, 0);
        assert_eq!(
            open_approved_file(&fifo).err().unwrap().kind,
            SolverErrorKind::BlockedPrerequisite
        );
        let oversized = root.join("oversized");
        File::create(&oversized).unwrap().set_len(MAX_ELF_BYTES + 1).unwrap();
        assert_eq!(
            open_approved_file(&oversized).err().unwrap().kind,
            SolverErrorKind::BlockedPrerequisite
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn approved_file_symlink_and_unpinned_snapshot_rejected() {
        let root =
            std::env::temp_dir().join(format!("isabelle-solver-link-{}", std::process::id()));
        fs::create_dir(&root).unwrap();
        let target = root.join("binary");
        fs::write(&target, b"untrusted executable").unwrap();
        let link = root.join("link");
        std::os::unix::fs::symlink(&target, &link).unwrap();
        assert!(open_approved_file(&link).is_err());
        let mut source = open_approved_file(&target).unwrap();
        assert_eq!(
            seal_file(&mut source, BWRAP_HASH).err().unwrap().kind,
            SolverErrorKind::BlockedPrerequisite
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn supervisor_second_permit_rejected_until_first_released() {
        let first = SolverPermit::acquire().unwrap();
        assert_eq!(SolverPermit::acquire().err().unwrap().kind, SolverErrorKind::Permission);
        drop(first);
        let _third = SolverPermit::acquire().unwrap();
    }
}
