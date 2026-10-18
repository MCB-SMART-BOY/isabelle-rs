//! Compiled by the integration fixture as an actual executable, not a script.
use std::{env, fs, io::{self, Write}, os::unix::process::CommandExt, path::Path, process::{self, Command}, thread, time::{Duration, Instant}};

unsafe extern "C" {
    fn signal(number: i32, handler: usize) -> usize;
    fn setsid() -> i32;
}

fn write_pid(name: &str) {
    let dir = env::var("PROFILE_PID_DIR").expect("PID directory");
    // /proc is the host mount, while getpid() would return namespace-relative PID.
    let stat = fs::read_to_string("/proc/self/stat").expect("read host-mounted proc stat");
    let host_pid = stat.split_whitespace().next().expect("host PID field");
    fs::write(Path::new(&dir).join(name), format!("{host_pid}\n")).expect("record host PID");
}

fn ignore_term() {
    unsafe { signal(15, 1); signal(2, 1); signal(1, 1); }
}

fn run_barrier() -> ! {
    let real = env::var("REAL_UNSHARE").expect("real unshare");
    if env::args_os().nth(1).as_deref() == Some(std::ffi::OsStr::new("--version")) {
        let error = Command::new(real).arg("--version").exec();
        panic!("exec real unshare version: {error}");
    }
    if env::var_os("PROFILE_DENY_NAMESPACE").is_some() {
        eprintln!("unshare: unshare failed: Operation not permitted");
        process::exit(1);
    }
    let entered = env::var("PROFILE_START_BARRIER").expect("barrier path");
    let released = env::var("PROFILE_START_RELEASE").expect("release path");
    fs::write(&entered, b"ready").expect("record launcher entry");
    let deadline = Instant::now() + Duration::from_secs(12);
    while !Path::new(&released).exists() {
        assert!(Instant::now() < deadline, "launcher release timed out");
        thread::sleep(Duration::from_millis(5));
    }
    let error = Command::new(real).args(env::args_os().skip(1)).exec();
    panic!("exec real unshare: {error}");
}

fn replace_timeout_log() -> ! {
    let path = env::var("PROFILE_TIMEOUT_LOG").expect("launcher log path");
    fs::remove_file(&path).expect("remove original launcher log");
    match env::var("PROFILE_LOG_REPLACEMENT").as_deref() {
        Ok("fifo") => {
            assert!(Command::new("mkfifo").arg(&path).status().unwrap().success());
        },
        Ok("symlink") => {
            let target = env::var("PROFILE_LOG_TARGET").expect("symlink target");
            std::os::unix::fs::symlink(target, &path).expect("replace log with symlink");
        },
        mode => panic!("unknown log replacement: {mode:?}"),
    }
    process::exit(1);
}

fn main() {
    if env::args_os().next().as_deref().and_then(|path| Path::new(path).file_name()) == Some(std::ffi::OsStr::new("unshare")) {
        run_barrier();
    }
    match env::var("SUPERVISOR_WORKER_MODE").as_deref() {
        Ok("success") => {},
        Ok("replace-timeout-log") => replace_timeout_log(),
        Ok("failure") => {
            eprintln!("worker failure");
            process::exit(env::var("SUPERVISOR_WORKER_EXIT").unwrap().parse().unwrap());
        },
        Ok("stderr") => {
            let chunk = vec![b'X'; 102_400];
            for _ in 0..100 {
                if io::stderr().write_all(&chunk).is_err() { process::exit(42); }
            }
        },
        Ok("normal-descendant") | Ok("waiting-descendant") => {
            let waiting = env::var("SUPERVISOR_WORKER_MODE").unwrap() == "waiting-descendant";
            ignore_term();
            write_pid("worker-pid");
            let mut descendant = Command::new(env::current_exe().unwrap())
                .env("SUPERVISOR_WORKER_MODE", "descendant")
                .spawn().expect("spawn descendant");
            let child_path = Path::new(&env::var("PROFILE_PID_DIR").unwrap()).join("child-pid");
            let deadline = Instant::now() + Duration::from_secs(6);
            while !child_path.exists() {
                assert!(Instant::now() < deadline, "descendant failed to record PID");
                thread::sleep(Duration::from_millis(5));
            }
            if waiting { descendant.wait().expect("reap descendant"); }
        },
        Ok("descendant") => {
            assert!(unsafe { setsid() } > 0, "descendant must escape the process group");
            ignore_term();
            write_pid("child-pid");
            loop { thread::park_timeout(Duration::from_secs(1)); }
        },
        mode => panic!("unknown worker fixture mode: {mode:?}"),
    }
}
