use super::*;
use std::ffi::OsString;
use std::mem::ManuallyDrop;
use std::os::fd::FromRawFd;
use std::os::unix::fs::{FileTypeExt, MetadataExt};
use std::os::unix::net::UnixStream;
use std::os::unix::process::CommandExt;

const SIGNAL_KILL: i32 = 9;
const PR_SET_PDEATHSIG: i32 = 1;
const MAX_FD: u32 = u32::MAX;
const SOL_SOCKET: i32 = 1;
const SO_PEERCRED: i32 = 17;
const SO_TYPE: i32 = 3;
const SOCK_STREAM: i32 = 1;
const O_DIRECTORY: i32 = 0o200000;
const PEER_CREDENTIAL_BYTES: usize = 12;

unsafe extern "C" {
    fn close_range(first: u32, last: u32, flags: u32) -> i32;
    fn getppid() -> i32;
    fn getsockopt(fd: i32, level: i32, option: i32, value: *mut u8, length: *mut u32) -> i32;
    fn getuid() -> u32;
    fn getgid() -> u32;
}

struct Snapshots {
    binary: File,
    loader: File,
    libc: File,
    libm: File,
    libgmp: File,
}

impl Snapshots {
    fn create(config: &SolverConfig) -> Result<Self, SolverError> {
        fn open_sealed(path: &Path, expected: &str) -> Result<File, SolverError> {
            let mut source = open_approved_file(path)?;
            seal_file(&mut source, expected)
        }
        Ok(Self {
            binary: open_sealed(&config.executable, VERIT_HASH)?,
            loader: open_sealed(&config.elf_loader, LOADER_HASH)?,
            libc: open_sealed(&config.libc, LIBC_HASH)?,
            libm: open_sealed(&config.libm, LIBM_HASH)?,
            libgmp: open_sealed(&config.libgmp, LIBGMP_HASH)?,
        })
    }

    fn descriptors(&self) -> [RawFd; 5] {
        [
            self.binary.as_raw_fd(),
            self.loader.as_raw_fd(),
            self.libc.as_raw_fd(),
            self.libm.as_raw_fd(),
            self.libgmp.as_raw_fd(),
        ]
    }
}

fn keep_only_fds(sorted: &[RawFd], executable_fd: RawFd) -> io::Result<()> {
    let mut first = 3u32;
    for &fd in sorted {
        if fd < 3 {
            continue;
        }
        let fd = fd as u32;
        if fd > first {
            // SAFETY: close_range closes only gaps between trusted, explicitly kept descriptors.
            if unsafe { close_range(first, fd - 1, 0) } < 0 {
                return Err(io::Error::last_os_error());
            }
        }
        // The ELF path is resolved before exec closes its own descriptor.
        set_fd_inheritance(fd as i32, fd as i32 != executable_fd)?;
        first = fd + 1;
    }
    // SAFETY: remaining fds are unneeded and are closed before executing another image.
    if unsafe { close_range(first, MAX_FD, 0) } < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

fn start_launcher(
    config: &SolverConfig,
    domain: &Path,
    args: &[String],
    snapshots: &Snapshots,
) -> Result<(std::process::Child, UnixStream, UnixStream), SolverError> {
    let self_exe = same_executable()?;
    let mut bwrap_source = open_approved_file(&config.bubblewrap)?;
    let bwrap = seal_file(&mut bwrap_source, BWRAP_HASH)?;
    let (report_reader, report_writer) = UnixStream::pair().map_err(|error| {
        SolverError::io(
            SolverErrorKind::System,
            "create bwrap startup channel",
            "trusted launcher",
            error,
        )
    })?;
    let (auth_parent, auth_child) = UnixStream::pair().map_err(|error| {
        SolverError::io(
            SolverErrorKind::System,
            "create launcher credential channel",
            "trusted launcher",
            error,
        )
    })?;
    let self_fd = self_exe.as_raw_fd();
    let bwrap_fd = bwrap.as_raw_fd();
    let report_fd = report_writer.as_raw_fd();
    let auth_fd = auth_child.as_raw_fd();
    let descriptors = snapshots.descriptors();
    let mut fds = [
        self_fd,
        bwrap_fd,
        report_fd,
        auth_fd,
        descriptors[0],
        descriptors[1],
        descriptors[2],
        descriptors[3],
        descriptors[4],
    ];
    fds.sort_unstable();
    let parent_pid = std::process::id() as i32;
    let mut command = Command::new(format!("/proc/self/fd/{self_fd}"));
    command
        .arg(INTERNAL_FLAG)
        .arg(domain)
        .arg(bwrap_fd.to_string())
        .arg(report_fd.to_string())
        .arg(auth_fd.to_string());
    for fd in snapshots.descriptors() {
        command.arg(fd.to_string());
    }
    command
        .args(args)
        .env_clear()
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null());
    // SAFETY: after fork only async-signal-safe libc calls operate on inherited fixed fds.
    unsafe {
        command.pre_exec(move || {
            if prctl(PR_SET_PDEATHSIG, SIGNAL_KILL, 0, 0, 0) < 0 || getppid() != parent_pid {
                return Err(io::Error::last_os_error());
            }
            if dup2(1, 2) < 0 {
                return Err(io::Error::last_os_error());
            }
            keep_only_fds(&fds, self_fd)
        });
    }
    let child = command.spawn().map_err(|error| {
        SolverError::io(
            SolverErrorKind::BlockedPrerequisite,
            "start trusted launcher",
            "same-image fd",
            error,
        )
    })?;
    drop(auth_child);
    drop(report_writer);
    Ok((child, report_reader, auth_parent))
}

fn event_count(domain: &Path, filename: &str, field: &str) -> Result<u64, SolverError> {
    const EVENT_BYTES: usize = 4096;
    let path = domain.join(filename);
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(O_NONBLOCK | O_NOFOLLOW)
        .open(&path)
        .map_err(|error| system("open solver resource events", &path, error))?;
    let mut buffer = [0u8; EVENT_BYTES + 1];
    let count = file
        .read(&mut buffer)
        .map_err(|error| system("read solver resource events", &path, error))?;
    if count > EVENT_BYTES {
        return Err(prerequisite(
            "read solver resource events",
            format!("{} exceeds event bound", path.display()),
        ));
    }
    let events = std::str::from_utf8(&buffer[..count]).map_err(|error| {
        prerequisite(
            "read solver resource events",
            format!("invalid UTF-8 in {}: {error}", path.display()),
        )
    })?;
    let line = events
        .lines()
        .find_map(|line| line.strip_prefix(field).and_then(|rest| rest.strip_prefix(' ')))
        .ok_or_else(|| {
            prerequisite(
                "read solver resource events",
                format!("missing {field} in {}", path.display()),
            )
        })?;
    line.parse().map_err(|_| {
        prerequisite(
            "read solver resource events",
            format!("invalid {field} in {}", path.display()),
        )
    })
}

pub(super) fn verify_resource_events(domain: &Path) -> Result<(), SolverError> {
    if event_count(domain, "memory.events", "oom")? != 0
        || event_count(domain, "memory.events", "oom_kill")? != 0
        || event_count(domain, "pids.events", "max")? != 0
    {
        return Err(SolverError::new(
            SolverErrorKind::ResourceLimit,
            "verify solver resources",
            "memory or process hard limit reached",
        ));
    }
    Ok(())
}

pub(super) fn verify_startup_report(bytes: &[u8], code: i32) -> Result<(), SolverError> {
    if bytes.len() > 4096 {
        return Err(prerequisite("verify bwrap startup", "status report exceeds expected bound"));
    }
    let mut has_child = false;
    let mut exit_code = None;
    for line in bytes.split(|byte| *byte == b'\n').filter(|line| !line.is_empty()) {
        let entry: serde_json::Value = serde_json::from_slice(line).map_err(|error| {
            prerequisite("verify bwrap startup", format!("malformed trusted status: {error}"))
        })?;
        if entry.get("child-pid").and_then(serde_json::Value::as_u64).is_some() {
            has_child = true;
        }
        if let Some(value) = entry.get("exit-code").and_then(serde_json::Value::as_i64) {
            exit_code = Some(value);
        }
    }
    if !has_child || exit_code != Some(i64::from(code)) {
        return Err(prerequisite(
            "verify bwrap startup",
            format!("sandbox did not complete verified startup/exit (launcher status {code})"),
        ));
    }
    Ok(())
}

pub(in crate::ml::host::solver) fn run(
    config: &SolverConfig,
    args: &[String],
    request: SolverRequest,
    cancellation: &Cancellation,
    lifecycle: &BuildLifecycle,
    process: TaskLease,
) -> Result<SolverOutput, SolverError> {
    let mut supervisor = super::supervision::CleanupSupervisor::start(lifecycle.clone(), process)?;
    let result = (|| {
        let permit = SolverPermit::acquire()?;
        check_config(config)?;
        let snapshots = Snapshots::create(config)?;
        run_supervised(config, args, request, cancellation, snapshots, permit, &mut supervisor)
    })();
    supervisor.finish(result)
}

fn run_supervised(
    config: &SolverConfig,
    args: &[String],
    request: SolverRequest,
    cancellation: &Cancellation,
    snapshots: Snapshots,
    permit: SolverPermit,
    supervisor: &mut super::supervision::CleanupSupervisor,
) -> Result<SolverOutput, SolverError> {
    let mut incomplete = None;
    let domain = match create_domain(config, &mut incomplete) {
        Ok(domain) => domain,
        Err(error) => {
            return match incomplete {
                Some(domain) => {
                    super::supervision::retire_without_child(domain, permit, error, supervisor)
                },
                None => Err(error),
            };
        },
    };
    let limit = if request.timeout.is_zero() { MAX_WALL } else { request.timeout.min(MAX_WALL) };
    match start_launcher(config, &domain, args, &snapshots) {
        Ok((child, report, auth)) => super::supervision::supervise(
            super::supervision::Invocation {
                child,
                report,
                auth,
                input: request.input,
                domain,
                limit,
            },
            cancellation,
            permit,
            supervisor,
        ),
        Err(error) => super::supervision::retire_without_child(domain, permit, error, supervisor),
    }
}

fn read_descriptor(value: &std::ffi::OsStr) -> Result<RawFd, SolverError> {
    let text =
        value.to_str().ok_or_else(|| prerequisite("parse launcher fd", "non-UTF-8 descriptor"))?;
    let fd: RawFd =
        text.parse().map_err(|_| prerequisite("parse launcher fd", "invalid descriptor"))?;
    if fd < 3 {
        return Err(prerequisite("parse launcher fd", "reserved descriptor"));
    }
    Ok(fd)
}

fn socket_option<const N: usize>(fd: RawFd, option: i32) -> Result<[u8; N], SolverError> {
    let mut bytes = [0u8; N];
    let mut length = N as u32;
    // SAFETY: getsockopt writes at most N bytes into initialized storage.
    if unsafe { getsockopt(fd, SOL_SOCKET, option, bytes.as_mut_ptr(), &mut length) } != 0 {
        return Err(SolverError::io(
            SolverErrorKind::BlockedPrerequisite,
            "authenticate launcher socket",
            format!("fd {fd}"),
            io::Error::last_os_error(),
        ));
    }
    if length as usize != N {
        return Err(prerequisite(
            "authenticate launcher socket",
            format!("fd {fd} returned unexpected option length"),
        ));
    }
    Ok(bytes)
}

fn socket_type(fd: RawFd) -> Result<i32, SolverError> {
    Ok(i32::from_ne_bytes(socket_option::<4>(fd, SO_TYPE)?))
}

fn authenticate_parent(auth_fd: RawFd) -> Result<(), SolverError> {
    if socket_type(auth_fd)? != SOCK_STREAM {
        return Err(prerequisite(
            "authenticate launcher parent",
            "credential channel is not a stream socket",
        ));
    }
    let peer = socket_option::<PEER_CREDENTIAL_BYTES>(auth_fd, SO_PEERCRED)?;
    let peer_pid = i32::from_ne_bytes(
        peer[..4]
            .try_into()
            .map_err(|_| prerequisite("authenticate launcher parent", "invalid peer PID"))?,
    );
    let peer_uid = u32::from_ne_bytes(
        peer[4..8]
            .try_into()
            .map_err(|_| prerequisite("authenticate launcher parent", "invalid peer UID"))?,
    );
    let peer_gid = u32::from_ne_bytes(
        peer[8..12]
            .try_into()
            .map_err(|_| prerequisite("authenticate launcher parent", "invalid peer GID"))?,
    );
    let parent_pid = unsafe { getppid() };
    if peer_pid != parent_pid || peer_uid != unsafe { getuid() } || peer_gid != unsafe { getgid() }
    {
        return Err(prerequisite(
            "authenticate launcher parent",
            "credential peer is not the live parent identity",
        ));
    }
    let parent_exe = PathBuf::from(format!("/proc/{parent_pid}/exe"));
    let parent = fs::metadata(&parent_exe)
        .map_err(|error| system("inspect launcher parent executable", &parent_exe, error))?;
    let current = fs::metadata("/proc/self/exe").map_err(|error| {
        SolverError::io(
            SolverErrorKind::BlockedPrerequisite,
            "inspect launcher executable",
            "/proc/self/exe",
            error,
        )
    })?;
    if parent.dev() != current.dev()
        || parent.ino() != current.ino()
        || unsafe { getppid() } != parent_pid
    {
        return Err(prerequisite(
            "authenticate launcher parent",
            "parent is not the same live executable",
        ));
    }
    Ok(())
}

fn authenticate_snapshot(fd: RawFd, expected: &str) -> Result<(u64, u64), SolverError> {
    if unsafe { fcntl(fd, F_GET_SEALS) } != SEALED {
        return Err(prerequisite(
            "authenticate launcher snapshot",
            format!("fd {fd} is not fully sealed"),
        ));
    }
    // SAFETY: borrowed descriptor ownership is suppressed; the launcher retains the original fd.
    let mut file = ManuallyDrop::new(unsafe { File::from_raw_fd(fd) });
    let metadata = file.metadata().map_err(|error| {
        SolverError::io(
            SolverErrorKind::BlockedPrerequisite,
            "inspect launcher snapshot",
            format!("fd {fd}"),
            error,
        )
    })?;
    if !metadata.is_file() || metadata.len() == 0 || metadata.len() > MAX_ELF_BYTES {
        return Err(prerequisite(
            "authenticate launcher snapshot",
            format!("fd {fd} is not a bounded regular file"),
        ));
    }
    file.seek(SeekFrom::Start(0)).map_err(|error| {
        SolverError::io(
            SolverErrorKind::BlockedPrerequisite,
            "rewind launcher snapshot",
            format!("fd {fd}"),
            error,
        )
    })?;
    if hash_file(&mut file).map_err(|error| {
        SolverError::io(
            SolverErrorKind::BlockedPrerequisite,
            "hash launcher snapshot",
            format!("fd {fd}"),
            error,
        )
    })? != expected
    {
        return Err(prerequisite(
            "authenticate launcher snapshot",
            format!("fd {fd} digest differs from fixed profile"),
        ));
    }
    file.seek(SeekFrom::Start(0)).map_err(|error| {
        SolverError::io(
            SolverErrorKind::BlockedPrerequisite,
            "rewind verified snapshot",
            format!("fd {fd}"),
            error,
        )
    })?;
    Ok((metadata.dev(), metadata.ino()))
}

fn socket_identity(fd: RawFd) -> Result<(u64, u64), SolverError> {
    // SAFETY: borrowed descriptor is never dropped; the launcher retains its ownership.
    let file = ManuallyDrop::new(unsafe { File::from_raw_fd(fd) });
    let metadata = file.metadata().map_err(|error| {
        SolverError::io(
            SolverErrorKind::BlockedPrerequisite,
            "inspect launcher socket fd",
            format!("fd {fd}"),
            error,
        )
    })?;
    if !metadata.file_type().is_socket() {
        return Err(prerequisite(
            "authenticate launcher socket fd",
            format!("fd {fd} is not a Unix socket"),
        ));
    }
    Ok((metadata.dev(), metadata.ino()))
}

fn authenticate_descriptors(
    bwrap_fd: RawFd,
    report_fd: RawFd,
    auth_fd: RawFd,
    snapshots: &[RawFd; 5],
) -> Result<(), SolverError> {
    let mut descriptors = [
        bwrap_fd,
        report_fd,
        auth_fd,
        snapshots[0],
        snapshots[1],
        snapshots[2],
        snapshots[3],
        snapshots[4],
    ];
    descriptors.sort_unstable();
    if descriptors.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(prerequisite("authenticate launcher fds", "duplicate descriptor numbers"));
    }
    if socket_type(report_fd)? != SOCK_STREAM {
        return Err(prerequisite(
            "authenticate launcher report",
            "report fd is not a stream socket",
        ));
    }
    if socket_identity(report_fd)? == socket_identity(auth_fd)? {
        return Err(prerequisite(
            "authenticate launcher fds",
            "credential and report socket identity reused",
        ));
    }
    let mut identities = [(0u64, 0u64); 6];
    for (index, (fd, digest)) in [
        (bwrap_fd, BWRAP_HASH),
        (snapshots[0], VERIT_HASH),
        (snapshots[1], LOADER_HASH),
        (snapshots[2], LIBC_HASH),
        (snapshots[3], LIBM_HASH),
        (snapshots[4], LIBGMP_HASH),
    ]
    .into_iter()
    .enumerate()
    {
        let identity = authenticate_snapshot(fd, digest)?;
        if identities[..index].contains(&identity) {
            return Err(prerequisite("authenticate launcher fds", "snapshot file identity reused"));
        }
        identities[index] = identity;
    }
    Ok(())
}

fn inspect_domain(domain: &Path) -> Result<(), SolverError> {
    if !domain.is_absolute()
        || domain.components().any(|part| matches!(part, std::path::Component::ParentDir))
    {
        return Err(prerequisite("inspect launcher cgroup", "noncanonical cgroup path"));
    }
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(O_DIRECTORY | O_NOFOLLOW | O_NONBLOCK)
        .open(domain)
        .map_err(|error| system("open launcher cgroup", domain, error))?;
    let mut statfs = [0u8; 128];
    // SAFETY: Linux x86_64 statfs occupies 120 bytes; fd is the opened domain.
    if unsafe { fstatfs(file.as_raw_fd(), statfs.as_mut_ptr()) } != 0 {
        return Err(system(
            "inspect launcher cgroup filesystem",
            domain,
            io::Error::last_os_error(),
        ));
    }
    if i64::from_ne_bytes(
        statfs[..8]
            .try_into()
            .map_err(|_| prerequisite("inspect launcher cgroup", "invalid statfs layout"))?,
    ) != CGROUP2_MAGIC
    {
        return Err(prerequisite("inspect launcher cgroup", "domain is not on cgroup v2"));
    }
    Ok(())
}

fn verify_limits(domain: &Path) -> Result<(), SolverError> {
    for (name, value) in [
        ("memory.max", MEMORY_BYTES),
        ("memory.swap.max", "0"),
        ("pids.max", PIDS),
        ("cpu.max", CPU_QUOTA),
    ] {
        let read = fs::read_to_string(domain.join(name))
            .map_err(|error| system("verify launcher cgroup", domain, error))?;
        if !read.split_whitespace().eq(value.split_whitespace()) {
            return Err(prerequisite(
                "verify launcher cgroup",
                format!("{name} changed before execution"),
            ));
        }
    }
    Ok(())
}

fn enter_domain(domain: &Path) -> Result<(), SolverError> {
    inspect_domain(domain)?;
    verify_limits(domain)?;
    let pid = unsafe { getpid() };
    fs::write(domain.join("cgroup.procs"), pid.to_string())
        .map_err(|error| system("enter delegated solver cgroup", domain, error))?;
    verify_limits(domain)?;
    let populated = fs::read_to_string(domain.join("cgroup.events"))
        .map_err(|error| system("verify launcher cgroup population", domain, error))?;
    if !populated.lines().any(|line| line == "populated 1") {
        return Err(prerequisite("verify launcher membership", "solver cgroup not populated"));
    }
    let members = fs::read_to_string(domain.join("cgroup.procs"))
        .map_err(|error| system("verify launcher cgroup membership", domain, error))?;
    if !members.split_whitespace().any(|member| member == pid.to_string()) {
        return Err(prerequisite(
            "verify launcher membership",
            "launcher PID absent from requested cgroup",
        ));
    }
    Ok(())
}

fn bind_snapshot(command: &mut Command, fd: RawFd, target: &str, permissions: &str) {
    // Pinned bwrap copies directly from the authenticated sealed fd into a private
    // read-only mount. Its path-based bind modes cannot resolve anonymous memfds.
    command.args(["--perms", permissions, "--ro-bind-data"]).arg(fd.to_string()).arg(target);
}

fn run_bwrap(
    bwrap_fd: RawFd,
    report_fd: RawFd,
    snapshots: [RawFd; 5],
    args: &[OsString],
) -> Result<i32, SolverError> {
    let mut command = Command::new(format!("/proc/self/fd/{bwrap_fd}"));
    command.env_clear().stdin(Stdio::inherit()).stdout(Stdio::inherit()).stderr(Stdio::inherit());
    command.args([
        "--unshare-user",
        "--unshare-ipc",
        "--unshare-pid",
        "--unshare-net",
        "--unshare-uts",
        "--unshare-cgroup",
        "--disable-userns",
        "--die-with-parent",
        "--new-session",
        "--cap-drop",
        "ALL",
        "--clearenv",
        "--setenv",
        "LC_ALL",
        "C",
        "--setenv",
        "PWD",
        "/tmp",
        "--setenv",
        "TMPDIR",
        "/tmp",
        "--dir",
        "/solver",
        "--dir",
        "/lib",
        "--dir",
        "/lib64",
        "--dev",
        "/dev",
        "--perms",
        "0700",
        "--size",
        "67108864",
        "--tmpfs",
        "/tmp",
    ]);
    command.arg("--json-status-fd").arg(report_fd.to_string());
    for (fd, (target, permissions)) in snapshots.into_iter().zip([
        ("/solver/veriT", "0500"),
        ("/lib64/ld-linux-x86-64.so.2", "0500"),
        ("/lib/libc.so.6", "0400"),
        ("/lib/libm.so.6", "0400"),
        ("/solver/libgmp.so.10", "0400"),
    ]) {
        bind_snapshot(&mut command, fd, target, permissions);
    }
    command.args([
        "--remount-ro",
        "/",
        "--chdir",
        "/tmp",
        "--",
        "/lib64/ld-linux-x86-64.so.2",
        "--inhibit-cache",
        "--library-path",
        "/lib:/solver",
        "/solver/veriT",
    ]);
    command.args(args);
    let mut keep =
        [bwrap_fd, report_fd, snapshots[0], snapshots[1], snapshots[2], snapshots[3], snapshots[4]];
    keep.sort_unstable();
    // SAFETY: before exec only close_range and fcntl operate on fixed inherited descriptors.
    unsafe {
        command.pre_exec(move || keep_only_fds(&keep, bwrap_fd));
    }
    let status = command.status().map_err(|error| {
        SolverError::io(
            SolverErrorKind::BlockedPrerequisite,
            "execute sealed bwrap",
            "trusted bubblewrap fd",
            error,
        )
    })?;
    status
        .code()
        .ok_or_else(|| prerequisite("wait Bubblewrap", "namespace init terminated by signal"))
}

pub(in crate::ml::host::solver) fn run_launcher_if_requested() -> Result<Option<i32>, SolverError> {
    let arguments: Vec<OsString> = std::env::args_os().skip(1).collect();
    if arguments.first().map(OsString::as_os_str) != Some(std::ffi::OsStr::new(INTERNAL_FLAG)) {
        return Ok(None);
    }
    if arguments.len() < 10 {
        return Err(prerequisite("parse internal launcher", "missing fixed control descriptors"));
    }
    let auth_fd = read_descriptor(&arguments[4])?;
    authenticate_parent(auth_fd)?;
    let domain = PathBuf::from(&arguments[1]);
    let bwrap_fd = read_descriptor(&arguments[2])?;
    let report_fd = read_descriptor(&arguments[3])?;
    let fds = [
        read_descriptor(&arguments[5])?,
        read_descriptor(&arguments[6])?,
        read_descriptor(&arguments[7])?,
        read_descriptor(&arguments[8])?,
        read_descriptor(&arguments[9])?,
    ];
    authenticate_descriptors(bwrap_fd, report_fd, auth_fd, &fds)?;
    crate::ml::host::solver::argv::validate_arguments(&arguments[10..])?;
    enter_domain(&domain)?;
    let limit = Rlimit { current: 120, maximum: 120 };
    // SAFETY: RLIMIT_CPU is a fixed per-process kernel limit; no ML-provided resource number.
    if unsafe { setrlimit(RLIMIT_CPU, &limit) } != 0 {
        return Err(prerequisite(
            "set solver CPU hard limit",
            io::Error::last_os_error().to_string(),
        ));
    }
    // SAFETY: fixed no_new_privs flag is inherited by all descendants.
    if unsafe { prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) } != 0 {
        return Err(prerequisite("set no_new_privs", io::Error::last_os_error().to_string()));
    }
    let status = run_bwrap(bwrap_fd, report_fd, fds, &arguments[10..])?;
    Ok(Some(status))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn launcher_duplicate_descriptors_rejected_before_execution() {
        let error = authenticate_descriptors(3, 3, 4, &[5, 6, 7, 8, 9]).unwrap_err();
        assert_eq!(error.kind, SolverErrorKind::BlockedPrerequisite);
    }

    #[test]
    fn launcher_aliased_credential_and_report_socket_rejected() {
        let (report, _peer) = UnixStream::pair().unwrap();
        let alias = report.try_clone().unwrap();
        let error = authenticate_descriptors(
            99,
            report.as_raw_fd(),
            alias.as_raw_fd(),
            &[100, 101, 102, 103, 104],
        )
        .unwrap_err();
        assert_eq!(error.kind, SolverErrorKind::BlockedPrerequisite);
    }

    #[test]
    fn launcher_same_process_socket_does_not_authenticate_as_parent() {
        let (first, _second) = UnixStream::pair().unwrap();
        let error = authenticate_parent(first.as_raw_fd()).unwrap_err();
        assert_eq!(error.kind, SolverErrorKind::BlockedPrerequisite);
    }

    #[test]
    fn launcher_ordinary_directory_rejected_as_cgroup() {
        let root = std::env::temp_dir();
        let error = inspect_domain(&root).unwrap_err();
        assert_eq!(error.kind, SolverErrorKind::BlockedPrerequisite);
    }
}
