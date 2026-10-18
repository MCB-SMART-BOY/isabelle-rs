//! Bounded strace observation: neither argv nor environment are persisted.
use std::collections::HashMap;
use std::env;
use std::ffi::{OsStr, OsString};
use std::fs::{File, OpenOptions};
use std::io::{self, BufWriter, Read, Write};
use std::os::fd::{AsRawFd, OwnedFd};
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::sync::mpsc::{self, Receiver};
use std::thread;
use std::time::Duration;

use serde_json::{Value, json};

use crate::runner::{StepError, io_error};

const MAX_TRACE_LINE_BYTES: usize = 4 * 1024 * 1024;
const MAX_TRACE_STRING_BYTES: usize = 65_536;
const MAX_TRACE_ERRORS: usize = 16;
const TRACE_DRAIN_SECONDS: u64 = 10;
pub const SYSCALLS: [&str; 4] = ["execve", "execveat", "open", "openat"];

#[derive(Clone)]
struct Event {
    tid: u64,
    timestamp: String,
    syscall: String,
    path: String,
}

struct TraceState {
    output: BufWriter<File>,
    pending: HashMap<u64, Event>,
    errors: Vec<String>,
    error_count: u64,
    event_count: u64,
    unresolved_relative_paths: u64,
}

impl TraceState {
    fn record_error(&mut self, detail: &str) {
        self.error_count += 1;
        if self.errors.len() < MAX_TRACE_ERRORS {
            self.errors.push(detail.to_owned());
        }
    }

    fn consume(&mut self, mut source: impl Read) -> Result<(), StepError> {
        let mut chunk = [0u8; 8192];
        let mut line = Vec::new();
        let mut oversized = false;
        loop {
            let count = source
                .read(&mut chunk)
                .map_err(|cause| io_error("read private strace stream", cause))?;
            if count == 0 {
                break;
            }
            for &byte in &chunk[..count] {
                if byte == b'\n' {
                    if oversized {
                        self.record_error(
                            "trace record exceeded the bounded line limit or was cut off",
                        );
                    } else {
                        self.accept_line(&line)?;
                    }
                    line.clear();
                    oversized = false;
                } else if line.len() < MAX_TRACE_LINE_BYTES {
                    line.push(byte);
                } else {
                    oversized = true;
                }
            }
        }
        if oversized || !line.is_empty() {
            self.record_error("trace record exceeded the bounded line limit or was cut off");
        }
        self.output.flush().map_err(|cause| io_error("flush sanitized strace event file", cause))
    }

    fn accept_line(&mut self, line: &[u8]) -> Result<(), StepError> {
        let text = match std::str::from_utf8(line) {
            Ok(text) => text,
            Err(_) => {
                self.record_error("incomplete trace record: non-ASCII or invalid UTF-8");
                return Ok(());
            },
        };
        if split_prefix(text).is_none() {
            self.record_error("incomplete trace record: unrecognized trace record prefix");
            return Ok(());
        }
        match self.parse_line(text) {
            Ok(Some(event)) => self.write_event(event),
            Ok(None) => Ok(()),
            Err(()) => {
                self.record_error("incomplete trace record: invalid or unsupported syscall record");
                Ok(())
            },
        }
    }

    fn parse_line(&mut self, line: &str) -> Result<Option<Value>, ()> {
        let (tid, timestamp, body) = split_prefix(line).ok_or(())?;
        if body.starts_with("--- ") || body.starts_with("+++ ") {
            return Ok(None);
        }
        let event = if let Some((syscall, args)) = split_start(body) {
            if self.pending.contains_key(&tid) {
                return Err(());
            }
            let event = Event {
                tid,
                timestamp: timestamp.into(),
                syscall: syscall.into(),
                path: decode_path(syscall, args)?,
            };
            if body.contains("<unfinished ...>") {
                self.pending.insert(tid, event);
                return Ok(None);
            }
            event
        } else {
            let resumed = body.strip_prefix("<... ").ok_or(())?;
            let syscall = SYSCALLS
                .iter()
                .find(|&&name| {
                    resumed.starts_with(name) && resumed[name.len()..].starts_with(" resumed>")
                })
                .ok_or(())?;
            let event = self.pending.remove(&tid).ok_or(())?;
            if event.syscall != *syscall {
                return Err(());
            }
            event
        };
        let (result, rest) = parse_result(body)?;
        let resolved_path = if matches!(event.syscall.as_str(), "open" | "openat")
            && result.bytes().all(|b| b.is_ascii_digit())
        {
            read_descriptor_path(rest)
        } else {
            None
        };
        let mut observation = json!({"tid": event.tid, "timestamp": event.timestamp, "syscall": event.syscall, "path": event.path, "result": result});
        if let Some(path) = resolved_path {
            observation["resolved_path"] = json!(path);
        }
        Ok(Some(observation))
    }

    fn write_event(&mut self, mut event: Value) -> Result<(), StepError> {
        self.event_count += 1;
        if !event["path"].as_str().is_some_and(|path| path.starts_with('/'))
            && event.get("resolved_path").is_none()
        {
            self.unresolved_relative_paths += 1;
        }
        event["sequence"] = json!(self.event_count);
        serde_json::to_writer(&mut self.output, &event).map_err(|source| StepError::Json {
            operation: "serialize sanitized strace event".into(),
            source,
        })?;
        self.output
            .write_all(b"\n")
            .map_err(|cause| io_error("write sanitized strace event", cause))
    }

    fn finish(mut self) -> Value {
        if !self.pending.is_empty() {
            self.record_error("trace ended with unresolved syscalls");
        }
        if self.event_count == 0 {
            self.record_error("trace captured no selected syscalls");
        }
        json!({"complete": self.error_count == 0, "event_count": self.event_count, "error_count": self.error_count, "errors": self.errors, "scope": SYSCALLS, "relative_paths_resolved": self.unresolved_relative_paths == 0, "unresolved_relative_paths": self.unresolved_relative_paths, "argv_recorded": false, "environment_recorded": false})
    }
}

fn split_prefix(line: &str) -> Option<(u64, &str, &str)> {
    let tid_end = line.find(char::is_whitespace)?;
    let tid = line[..tid_end].parse().ok()?;
    let rest = line[tid_end..].trim_start_matches(char::is_whitespace);
    let timestamp_end = rest.find(char::is_whitespace)?;
    let timestamp = &rest[..timestamp_end];
    let (seconds, fractional) = timestamp.split_once('.')?;
    if seconds.is_empty()
        || fractional.is_empty()
        || !seconds.bytes().chain(fractional.bytes()).all(|byte| byte.is_ascii_digit())
    {
        return None;
    }
    let body = rest[timestamp_end..].trim_start_matches(char::is_whitespace);
    if body.is_empty() {
        return None;
    }
    Some((tid, timestamp, body))
}

fn split_start(body: &str) -> Option<(&str, &str)> {
    SYSCALLS.iter().find_map(|&name| {
        body.strip_prefix(name).and_then(|rest| rest.strip_prefix('(')).map(|args| (name, args))
    })
}

fn hex_path(text: &str, quoted: bool) -> Option<(String, &str)> {
    let mut rest = if quoted { text.strip_prefix('"')? } else { text };
    let mut bytes = Vec::new();
    while let Some(encoded) = rest.strip_prefix("\\x") {
        let (pair, after) = encoded.split_at_checked(2)?;
        bytes.push(u8::from_str_radix(pair, 16).ok()?);
        if bytes.len() > MAX_TRACE_STRING_BYTES {
            return None;
        }
        rest = after;
    }
    if bytes.is_empty() {
        return None;
    }
    let rest = if quoted { rest.strip_prefix('"')? } else { rest };
    let path = String::from_utf8(bytes).ok()?;
    if path.contains('\0') {
        return None;
    }
    Some((path, rest))
}

fn valid_directory(text: &str) -> bool {
    let (descriptor, annotation) =
        text.split_once('<').map_or((text, None), |(fd, rest)| (fd, Some(rest)));
    if descriptor != "AT_FDCWD" && descriptor.parse::<i32>().is_err() {
        return false;
    }
    annotation.is_none_or(|data| {
        data.strip_suffix('>').is_some_and(|hex| {
            let bytes = hex.as_bytes();
            bytes.len() <= MAX_TRACE_STRING_BYTES * 4
                && bytes.len() % 4 == 0
                && bytes.as_chunks::<4>().0.iter().all(|chunk| {
                    chunk[0] == b'\\'
                        && chunk[1] == b'x'
                        && chunk[2].is_ascii_hexdigit()
                        && chunk[3].is_ascii_hexdigit()
                })
        })
    })
}

fn decode_path(syscall: &str, args: &str) -> Result<String, ()> {
    let args = if matches!(syscall, "openat" | "execveat") {
        let (directory, remaining) = args.split_once(", ").ok_or(())?;
        if !valid_directory(directory) {
            return Err(());
        }
        remaining
    } else {
        args
    };
    let (path, rest) = hex_path(args, true).ok_or(())?;
    if path.is_empty() || !rest.starts_with(',') {
        return Err(());
    }
    Ok(path)
}

fn parse_result(body: &str) -> Result<(&str, &str), ()> {
    let after = body
        .rmatch_indices(')')
        .find_map(|(index, _)| {
            body[index + 1..].trim_ascii_start().strip_prefix('=').map(str::trim_ascii_start)
        })
        .ok_or(())?;
    let index = after.find(|c: char| c.is_whitespace() || c == '<').unwrap_or(after.len());
    let (result, rest) = after.split_at(index);
    let digits = result.strip_prefix('-').unwrap_or(result);
    if result != "?" && (digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit())) {
        return Err(());
    }
    Ok((result, rest))
}

fn read_descriptor_path(text: &str) -> Option<String> {
    let (path, rest) = hex_path(text.strip_prefix('<')?, false)?;
    if rest.strip_prefix('>').is_some_and(|suffix| {
        suffix.is_empty() || suffix.chars().next().is_some_and(char::is_whitespace)
    }) && path.starts_with('/')
    {
        Some(path)
    } else {
        None
    }
}

/// Reader owns the only raw trace stream. Call `finish` after child teardown.
pub struct TraceCapture {
    executable: PathBuf,
    writer: Option<OwnedFd>,
    reader: Option<Receiver<Result<Value, StepError>>>,
}

impl TraceCapture {
    pub fn new(event_path: &Path) -> Result<Self, StepError> {
        let executable = find_strace()?;
        let (source, writer) = rustix::pipe::pipe_with(rustix::pipe::PipeFlags::CLOEXEC)
            .map_err(|cause| io_error("create private strace channel", io::Error::from(cause)))?;
        let source = File::from(source);
        rustix::io::fcntl_setfd(&writer, rustix::io::FdFlags::empty()).map_err(|cause| {
            io_error("inherit private strace writer in child", io::Error::from(cause))
        })?;
        let output =
            OpenOptions::new().write(true).create_new(true).open(event_path).map_err(|cause| {
                io_error(
                    format!("create sanitized trace event file {}", event_path.display()),
                    cause,
                )
            })?;
        let state = TraceState {
            output: BufWriter::new(output),
            pending: HashMap::new(),
            errors: Vec::new(),
            error_count: 0,
            event_count: 0,
            unresolved_relative_paths: 0,
        };
        let (sender, receiver) = mpsc::channel();
        thread::spawn(move || {
            let mut state = state;
            let result = state.consume(source).map(|()| state.finish());
            let _ = sender.send(result);
        });
        Ok(Self { executable, writer: Some(writer), reader: Some(receiver) })
    }

    pub fn executable(&self) -> Result<&Path, StepError> {
        Ok(&self.executable)
    }

    pub fn wrap(&self, command: &[OsString]) -> Result<Vec<OsString>, StepError> {
        let fd = self
            .writer
            .as_ref()
            .ok_or_else(|| StepError::Protocol {
                operation: "wrap reference strace command".into(),
                detail: "writer already closed".into(),
            })?
            .as_raw_fd();
        let mut args: Vec<OsString> = [
            "-f",
            "-qq",
            "-yy",
            "-ttt",
            "-xx",
            "-s",
            "65536",
            "-e",
            "trace=execve,execveat,open,openat",
            "-o",
        ]
        .iter()
        .map(OsString::from)
        .collect();
        args.push(format!("/proc/self/fd/{fd}").into());
        args.push("--".into());
        args.extend_from_slice(command);
        Ok(args)
    }

    pub fn close_parent_writer(&mut self) -> Result<(), StepError> {
        self.writer.take();
        Ok(())
    }

    pub fn finish(mut self) -> Result<Value, StepError> {
        self.close_parent_writer()?;
        let reader = self.reader.take().ok_or_else(|| StepError::Protocol {
            operation: "finish private strace observation".into(),
            detail: "missing reader".into(),
        })?;
        reader.recv_timeout(Duration::from_secs(TRACE_DRAIN_SECONDS)).map_err(|error| {
            StepError::Protocol {
                operation: "finish private strace observation".into(),
                detail: format!("trace channel remained open after child teardown: {error}"),
            }
        })?
    }
}

fn find_strace() -> Result<PathBuf, StepError> {
    for directory in env::split_paths(&env::var_os("PATH").unwrap_or_default()) {
        let candidate = directory.join(OsStr::new("strace"));
        if candidate
            .metadata()
            .is_ok_and(|meta| meta.is_file() && meta.permissions().mode() & 0o111 != 0)
        {
            return Ok(candidate);
        }
    }
    Err(StepError::Input("reference observation requires strace on PATH".into()))
}

#[cfg(test)]
mod tests;
