use std::io::{self, BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};

use serde_json::Value;

use crate::runner::{StepError, io_error};

const MAX_JSON_LINE_BYTES: usize = 8 * 1024 * 1024;
const MAX_METADATA_BYTES: u64 = 8 * 1024 * 1024;

pub fn cargo_command() -> Command {
    let executable = std::env::var_os("CARGO")
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| "cargo".into());
    let mut command = Command::new(executable);
    // Cargo.lock identifies the bundled libzstd source, not a system library
    // selected by zstd-sys' environment-variable override.
    command.env_remove("ZSTD_SYS_USE_PKG_CONFIG").env_remove("ZSTD_SYS_NO_HIDE_SYMBOLS");
    command
}

fn parse_json(line: &[u8], operation: &str) -> Result<Value, StepError> {
    serde_json::from_slice(line)
        .map_err(|source| StepError::Json { operation: operation.into(), source })
}

fn read_line_bounded(
    reader: &mut impl BufRead,
    buffer: &mut Vec<u8>,
    operation: &str,
) -> Result<usize, StepError> {
    buffer.clear();
    loop {
        let chunk = reader
            .fill_buf()
            .map_err(|source| io_error(format!("read {operation} stdout"), source))?;
        if chunk.is_empty() {
            return Ok(buffer.len());
        }
        let count = chunk.iter().position(|byte| *byte == b'\n').map_or(chunk.len(), |pos| pos + 1);
        if buffer.len() + count > MAX_JSON_LINE_BYTES {
            return Err(StepError::Protocol {
                operation: operation.into(),
                detail: format!("Cargo JSON line exceeds {MAX_JSON_LINE_BYTES} bytes"),
            });
        }
        buffer.extend_from_slice(&chunk[..count]);
        reader.consume(count);
        if buffer.last() == Some(&b'\n') {
            return Ok(buffer.len());
        }
    }
}

fn terminate_for_cleanup(child: &mut Child, operation: &str) -> Result<(), StepError> {
    match child.kill() {
        Ok(()) => Ok(()),
        // The child may exit between detecting a stream error and the cleanup attempt.
        Err(source) if source.kind() == io::ErrorKind::InvalidInput => Ok(()),
        Err(source) => Err(io_error(format!("terminate {operation} after output error"), source)),
    }
}

#[cfg(unix)]
fn is_executable(path: &Path) -> bool {
    use std::os::unix::fs::PermissionsExt;
    path.metadata()
        .is_ok_and(|metadata| metadata.is_file() && metadata.permissions().mode() & 0o111 != 0)
}

#[cfg(not(unix))]
fn is_executable(path: &Path) -> bool {
    path.is_file()
}

pub fn root_package_id(root: &Path) -> Result<String, StepError> {
    let metadata = metadata(root)?;
    let packages = metadata["packages"].as_array().ok_or_else(|| StepError::Protocol {
        operation: "parse cargo metadata".into(),
        detail: "packages is not an array".into(),
    })?;
    let manifest = root.join("Cargo.toml");
    let package = packages.iter().find(|package| {
        package["name"] == "isabelle-rs"
            && package["manifest_path"].as_str().is_some_and(|path| Path::new(path) == manifest)
    });
    package.and_then(|package| package["id"].as_str()).map(str::to_string).ok_or_else(|| {
        StepError::Protocol {
            operation: "parse cargo metadata".into(),
            detail: format!("root package {} not found", manifest.display()),
        }
    })
}

pub fn root_version(root: &Path) -> Result<String, StepError> {
    let metadata = metadata(root)?;
    let manifest = root.join("Cargo.toml");
    metadata["packages"]
        .as_array()
        .and_then(|packages| {
            packages.iter().find(|package| {
                package["name"] == "isabelle-rs"
                    && package["manifest_path"]
                        .as_str()
                        .is_some_and(|path| Path::new(path) == manifest)
            })
        })
        .and_then(|package| package["version"].as_str())
        .map(str::to_string)
        .ok_or_else(|| StepError::Protocol {
            operation: "parse cargo metadata".into(),
            detail: format!("root version for {} missing", manifest.display()),
        })
}

fn metadata(root: &Path) -> Result<Value, StepError> {
    let mut command = cargo_command();
    command.args(["metadata", "--locked", "--no-deps", "--format-version", "1"]);
    let mut child =
        command.current_dir(root).stdout(Stdio::piped()).stderr(Stdio::inherit()).spawn().map_err(
            |source| io_error(format!("start cargo metadata in {}", root.display()), source),
        )?;
    let mut output = Vec::new();
    let result = child
        .stdout
        .take()
        .ok_or_else(|| StepError::Protocol {
            operation: "cargo metadata".into(),
            detail: "stdout pipe missing".into(),
        })?
        .take(MAX_METADATA_BYTES + 1)
        .read_to_end(&mut output);
    let cleanup_error = if result.is_err() || output.len() as u64 > MAX_METADATA_BYTES {
        terminate_for_cleanup(&mut child, "cargo metadata").err()
    } else {
        None
    };
    let status = child.wait().map_err(|source| io_error("wait for cargo metadata", source))?;
    if let Some(error) = cleanup_error {
        return Err(error);
    }
    result.map_err(|source| io_error("read cargo metadata", source))?;
    if output.len() as u64 > MAX_METADATA_BYTES {
        return Err(StepError::Protocol {
            operation: "cargo metadata".into(),
            detail: "output exceeds 8 MiB".into(),
        });
    }
    if !status.success() {
        return Err(StepError::Exit { operation: "cargo metadata".into(), status });
    }
    parse_json(&output, "cargo metadata")
}

fn inspect_artifact(
    message: &Value,
    package_id: &str,
    target: &str,
    executable: &mut Option<PathBuf>,
    root: &Path,
) -> Result<(), StepError> {
    if message["reason"] == "compiler-message"
        && let Some(rendered) = message["message"]["rendered"].as_str()
    {
        io::stderr()
            .write_all(rendered.as_bytes())
            .map_err(|source| io_error("print Cargo compiler message", source))?;
    }
    if message["reason"] != "compiler-artifact"
        || message["package_id"] != package_id
        || message["target"]["name"] != target
        || !message["target"]["kind"]
            .as_array()
            .is_some_and(|kinds| kinds.iter().any(|kind| kind == "bin"))
    {
        return Ok(());
    }
    let path = message["executable"].as_str().ok_or_else(|| StepError::Protocol {
        operation: format!("build {target}"),
        detail: "matching artifact lacks executable".into(),
    })?;
    if executable.is_some() {
        return Err(StepError::Protocol {
            operation: format!("build {target}"),
            detail: "multiple matching executable artifacts".into(),
        });
    }
    let path = Path::new(path);
    *executable = Some(if path.is_absolute() { path.into() } else { root.join(path) });
    Ok(())
}

pub fn build_worker(root: &Path, package_id: &str, target: &str) -> Result<PathBuf, StepError> {
    build_worker_with(root, package_id, target, |_| {})
}

fn read_artifact_stream(
    reader: &mut impl BufRead,
    root: &Path,
    package_id: &str,
    target: &str,
    operation: &str,
) -> Result<Option<PathBuf>, StepError> {
    let mut buffer = Vec::new();
    let mut executable = None;
    while read_line_bounded(reader, &mut buffer, operation)? != 0 {
        let message = parse_json(&buffer, operation)?;
        inspect_artifact(&message, package_id, target, &mut executable, root)?;
    }
    Ok(executable)
}

fn build_worker_with(
    root: &Path,
    package_id: &str,
    target: &str,
    configure: impl FnOnce(&mut Command),
) -> Result<PathBuf, StepError> {
    let mut command = cargo_command();
    command.args([
        "build",
        "--locked",
        "-p",
        "isabelle-rs",
        "--bin",
        target,
        "--message-format=json",
    ]);
    configure(&mut command);
    let mut child =
        command.current_dir(root).stdout(Stdio::piped()).stderr(Stdio::inherit()).spawn().map_err(
            |source| {
                io_error(format!("start cargo build for {target} in {}", root.display()), source)
            },
        )?;
    let operation = format!("build {target}");
    let mut reader = BufReader::new(child.stdout.take().ok_or_else(|| StepError::Protocol {
        operation: format!("build {target}"),
        detail: "stdout pipe missing".into(),
    })?);
    let artifact = read_artifact_stream(&mut reader, root, package_id, target, &operation);
    let cleanup_error =
        if artifact.is_err() { terminate_for_cleanup(&mut child, &operation).err() } else { None };
    let status = child
        .wait()
        .map_err(|source| io_error(format!("wait for cargo build {target}"), source))?;
    if let Some(error) = cleanup_error {
        return Err(error);
    }
    let executable = artifact?;
    if !status.success() {
        return Err(StepError::Exit { operation: format!("cargo build {target}"), status });
    }
    let executable = executable.ok_or_else(|| StepError::Protocol {
        operation: format!("build {target}"),
        detail: "successful Cargo build provided no matching executable artifact".into(),
    })?;
    if !is_executable(&executable) {
        return Err(StepError::Protocol {
            operation: format!("build {target}"),
            detail: format!("artifact is not an executable file: {}", executable.display()),
        });
    }
    Ok(executable)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runner::{Runner, run_command};
    use std::fs;
    use std::time::{SystemTime, UNIX_EPOCH};

    struct CargoFixture(PathBuf);

    impl CargoFixture {
        fn create(source: &str) -> Self {
            let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
            let path = std::env::temp_dir()
                .join(format!("xtask cargo fixture {} {nonce}", std::process::id()));
            fs::create_dir_all(path.join("src/bin")).unwrap();
            fs::create_dir(path.join(".cargo")).unwrap();
            fs::write(
                path.join("Cargo.toml"),
                "[package]\nname = \"isabelle-rs\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
            )
            .unwrap();
            fs::write(
                path.join(".cargo/config.toml"),
                "[build]\ntarget-dir = \"build with spaces\"\n",
            )
            .unwrap();
            fs::write(path.join("src/bin/isabelle-scale-hol.rs"), source).unwrap();
            let status = cargo_command()
                .args(["generate-lockfile", "--offline"])
                .current_dir(&path)
                .env_remove("CARGO_TARGET_DIR")
                .env_remove("RUSTFLAGS")
                .env_remove("CARGO_ENCODED_RUSTFLAGS")
                .status()
                .unwrap();
            assert!(status.success());
            Self(path)
        }
    }

    impl Drop for CargoFixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }

    fn build_fixture_worker(root: &Path, package_id: &str) -> Result<PathBuf, StepError> {
        build_worker_with(root, package_id, "isabelle-scale-hol", |command| {
            command
                .env_remove("CARGO_TARGET_DIR")
                .env_remove("RUSTFLAGS")
                .env_remove("CARGO_ENCODED_RUSTFLAGS")
                .env_remove("RUSTC_WRAPPER")
                .env_remove("RUSTC_WORKSPACE_WRAPPER");
        })
    }

    #[test]
    fn worker_custom_target_dir_uses_cargo_reported_executable() {
        let fixture = CargoFixture::create("fn main() { std::process::exit(23); }\n");
        let package_id = root_package_id(&fixture.0).unwrap();
        assert_eq!(root_version(&fixture.0).unwrap(), "0.1.0");
        let artifact = build_fixture_worker(&fixture.0, &package_id).unwrap();
        assert!(artifact.to_string_lossy().contains("build with spaces"));
        assert_eq!(Command::new(&artifact).status().unwrap().code(), Some(23));
        let wrong_package = build_fixture_worker(&fixture.0, "wrong package");
        assert!(matches!(wrong_package, Err(StepError::Protocol { .. })));
    }

    #[test]
    fn worker_failed_build_blocks_observable_stale_executable() {
        let source = "fn main() { if let Some(path) = std::env::args_os().nth(1) { std::fs::write(path, b\"stale\").unwrap(); } }\n";
        let fixture = CargoFixture::create(source);
        let package_id = root_package_id(&fixture.0).unwrap();
        let old_artifact = build_fixture_worker(&fixture.0, &package_id).unwrap();
        fs::write(
            fixture.0.join("src/bin/isabelle-scale-hol.rs"),
            "fn main() { this_is_not_a_function(); }\n",
        )
        .unwrap();
        let marker = fixture.0.join("stale worker ran");
        let mut runner = Runner::new();
        let build = runner.step("worker build", &[], || {
            build_fixture_worker(&fixture.0, &package_id).map(|_| ())
        });
        let mut stale = Command::new(&old_artifact);
        stale.arg(&marker);
        runner
            .step("worker execution", &[build], || run_command(stale, "stale worker", &fixture.0));
        assert!(!runner.finish());
        assert!(!marker.exists());
        assert!(old_artifact.is_file());
    }
}
