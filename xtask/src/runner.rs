use std::fmt;
use std::io::{self, Write};
use std::path::Path;
use std::process::{Command, ExitStatus, Stdio};

/// A user-correctable argument or prerequisite error, or a failed external operation.
#[derive(Debug)]
pub enum StepError {
    /// A malformed option or unavailable prerequisite.
    Input(String),
    /// A failed filesystem or process I/O operation, retaining its original cause.
    Io { operation: String, source: io::Error },
    /// A subprocess returned unsuccessfully or was killed by a signal.
    Exit { operation: String, status: ExitStatus },
    /// Cargo emitted malformed JSON, retaining the parser cause.
    Json { operation: String, source: serde_json::Error },
    /// A subprocess path was not valid UTF-8, retaining the conversion cause.
    Utf8 { operation: String, source: std::string::FromUtf8Error },
    /// A Cargo protocol or artifact invariant was violated.
    Protocol { operation: String, detail: String },
}

impl fmt::Display for StepError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Input(detail) => write!(f, "invalid input or prerequisite: {detail}"),
            Self::Io { operation, source } => write!(f, "{operation}: {source}"),
            Self::Exit { operation, status } => write!(f, "{operation}: {status}"),
            Self::Json { operation, source } => write!(f, "{operation}: {source}"),
            Self::Utf8 { operation, source } => write!(f, "{operation}: {source}"),
            Self::Protocol { operation, detail } => write!(f, "{operation}: {detail}"),
        }
    }
}

impl std::error::Error for StepError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io { source, .. } => Some(source),
            Self::Json { source, .. } => Some(source),
            Self::Utf8 { source, .. } => Some(source),
            _ => None,
        }
    }
}

pub fn io_error(operation: impl Into<String>, source: io::Error) -> StepError {
    StepError::Io { operation: operation.into(), source }
}

pub fn report_line(message: impl fmt::Display) -> Result<(), StepError> {
    writeln!(io::stderr().lock(), "{message}")
        .map_err(|source| io_error("write xtask diagnostics to stderr", source))
}

pub fn run_command(mut command: Command, operation: &str, root: &Path) -> Result<(), StepError> {
    let status = command
        .current_dir(root)
        .stdin(Stdio::inherit())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .status()
        .map_err(|source| io_error(format!("start {operation} in {}", root.display()), source))?;
    if status.success() {
        Ok(())
    } else {
        Err(StepError::Exit { operation: operation.into(), status })
    }
}

enum Outcome {
    Passed,
    Failed(StepError),
    Blocked(Vec<String>),
}

/// Run independent steps after failures, but never execute a dependent step after failure.
#[derive(Default)]
pub struct Runner {
    labels: Vec<String>,
    outcomes: Vec<Outcome>,
}

impl Runner {
    pub fn new() -> Self {
        Self { labels: Vec::new(), outcomes: Vec::new() }
    }

    pub fn step(
        &mut self,
        label: impl Into<String>,
        dependencies: &[usize],
        run: impl FnOnce() -> Result<(), StepError>,
    ) -> usize {
        let label = label.into();
        let index = self.outcomes.len();
        let blocked: Vec<String> = dependencies
            .iter()
            .copied()
            .filter(|&dependency| !matches!(self.outcomes.get(dependency), Some(Outcome::Passed)))
            .map(|dependency| {
                self.labels
                    .get(dependency)
                    .cloned()
                    .unwrap_or_else(|| format!("missing step #{dependency}"))
            })
            .collect();
        let outcome = if blocked.is_empty() {
            match report_line(format_args!("=== {label} ===")).and_then(|()| run()) {
                Ok(()) => Outcome::Passed,
                Err(error) => Outcome::Failed(error),
            }
        } else {
            Outcome::Blocked(blocked)
        };
        self.labels.push(label);
        self.outcomes.push(outcome);
        index
    }

    pub fn finish(self) -> bool {
        let mut success = report_line("=== xtask step summary ===").is_ok();
        for (label, outcome) in self.labels.iter().zip(self.outcomes) {
            let result = match outcome {
                Outcome::Passed => report_line(format_args!("PASS {label}")),
                Outcome::Failed(error) => {
                    success = false;
                    report_line(format_args!("FAIL {label}: {error}"))
                },
                Outcome::Blocked(dependencies) => {
                    success = false;
                    report_line(format_args!(
                        "BLOCKED {label}: prerequisite(s) {}",
                        dependencies.join(", ")
                    ))
                },
            };
            if result.is_err() {
                success = false;
            }
        }
        success
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::fs;
    use std::os::unix::process::ExitStatusExt;
    use std::time::{SystemTime, UNIX_EPOCH};

    struct Scratch(std::path::PathBuf);

    impl Scratch {
        fn create() -> Self {
            let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
            let path =
                std::env::temp_dir().join(format!("xtask runner {} {nonce}", std::process::id()));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }

    fn fixture_command() -> Command {
        // Immutable compiled test fixture, retained for every subprocess in this test binary.
        static FIXTURE: std::sync::LazyLock<tempfile::TempDir> = std::sync::LazyLock::new(|| {
            let directory = tempfile::tempdir().unwrap();
            let source =
                Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/runner_worker.rs");
            let compiler = std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
            let status = Command::new(compiler)
                .arg(source)
                .arg("-o")
                .arg(directory.path().join("runner-worker"))
                .status()
                .unwrap();
            assert!(status.success(), "compile Rust runner fixture");
            directory
        });
        Command::new(FIXTURE.path().join("runner-worker"))
    }

    #[test]
    fn runner_failed_build_blocks_worker_but_runs_independent_step() {
        let scratch = Scratch::create();
        let blocked_marker = scratch.0.join("blocked marker");
        let independent_marker = scratch.0.join("independent marker");
        let mut runner = Runner::new();
        let mut build = fixture_command();
        build.arg("exit");
        let dependency = runner.step("build", &[], || run_command(build, "build", &scratch.0));
        let mut blocked = fixture_command();
        blocked.arg("touch").arg(&blocked_marker);
        runner.step("worker", &[dependency], || run_command(blocked, "worker", &scratch.0));
        let mut independent = fixture_command();
        independent.arg("touch").arg(&independent_marker);
        runner.step("independent", &[], || run_command(independent, "independent", &scratch.0));
        assert!(!runner.finish());
        assert!(!blocked_marker.exists());
        assert!(independent_marker.is_file());
    }

    #[test]
    fn runner_missing_executable_does_not_hide_later_failure() {
        let scratch = Scratch::create();
        let marker = scratch.0.join("ran after spawn error");
        let mut runner = Runner::new();
        let missing = Command::new(scratch.0.join("missing executable"));
        runner.step("missing", &[], || run_command(missing, "missing", &scratch.0));
        let mut failure = fixture_command();
        failure.arg("fail").arg(&marker);
        runner.step("failure", &[], || run_command(failure, "failure", &scratch.0));
        assert!(!runner.finish());
        assert!(marker.is_file());
    }

    #[test]
    fn runner_signal_exit_preserves_signal_and_runs_independent_step() {
        let scratch = Scratch::create();
        let marker = scratch.0.join("independent after signal");
        let mut observed_signal = None;
        let mut runner = Runner::new();
        let mut terminated = fixture_command();
        terminated.arg("signal");
        runner.step("terminated", &[], || {
            match run_command(terminated, "terminated", &scratch.0) {
                Err(StepError::Exit { operation, status }) => {
                    observed_signal = status.signal();
                    Err(StepError::Exit { operation, status })
                },
                result => result,
            }
        });
        let mut independent = fixture_command();
        independent.arg("touch").arg(&marker);
        runner.step("independent", &[], || run_command(independent, "independent", &scratch.0));
        assert!(!runner.finish());
        assert_eq!(observed_signal, Some(15));
        assert!(marker.is_file());
    }

    #[test]
    fn runner_argument_paths_with_spaces_remain_single_arguments() {
        let scratch = Scratch::create();
        let input = scratch.0.join("input with spaces");
        let result = scratch.0.join("output with spaces");
        fs::write(&input, b"payload").unwrap();
        let mut command = fixture_command();
        command.arg("copy").args([&input, &result]);
        let mut runner = Runner::new();
        runner.step("copy", &[], || run_command(command, "copy", &scratch.0));
        assert!(runner.finish());
        assert_eq!(fs::read(&result).unwrap(), b"payload");
    }
}
