use std::{
    io::{self, BufRead, BufReader, Write},
    process::{Child, ChildStdin, Command, Stdio},
    sync::mpsc::{self, Receiver},
    thread,
    time::{Duration, Instant},
};

use serde_json::{Value, json};

const DEADLINE: Duration = Duration::from_secs(10);

struct LspClient {
    child: Child,
    input: Option<ChildStdin>,
    frames: Receiver<io::Result<Value>>,
}

impl LspClient {
    fn start() -> Self {
        let mut child = Command::new(env!("CARGO_BIN_EXE_isabelle-rs"))
            .arg("--lsp")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("start real LSP server");
        let input = child.stdin.take().expect("LSP stdin");
        let output = child.stdout.take().expect("LSP stdout");
        let (sender, frames) = mpsc::channel();
        thread::spawn(move || {
            let mut reader = BufReader::new(output);
            loop {
                match read_frame(&mut reader) {
                    Ok(None) => break,
                    Ok(Some(frame)) => {
                        if sender.send(Ok(frame)).is_err() {
                            break;
                        }
                    },
                    Err(error) => {
                        let _ = sender.send(Err(error));
                        break;
                    },
                }
            }
        });
        Self { child, input: Some(input), frames }
    }

    fn send(&mut self, message: Value) {
        let bytes = serde_json::to_vec(&message).expect("serializable LSP message");
        let input = self.input.as_mut().expect("LSP input remains open");
        write!(input, "Content-Length: {}\r\n\r\n", bytes.len()).expect("frame header");
        input.write_all(&bytes).expect("frame body");
        input.flush().expect("flush LSP message");
    }

    fn receive_until(&self, predicate: impl Fn(&Value) -> bool) -> Value {
        let deadline = Instant::now() + DEADLINE;
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            let frame = self
                .frames
                .recv_timeout(remaining)
                .expect("expected LSP frame before deadline")
                .expect("valid LSP frame");
            if predicate(&frame) {
                return frame;
            }
        }
    }

    fn finish(mut self) -> Vec<Value> {
        self.input.take();
        let deadline = Instant::now() + DEADLINE;
        let mut frames = Vec::new();
        loop {
            match self.frames.recv_timeout(deadline.saturating_duration_since(Instant::now())) {
                Ok(Ok(frame)) => frames.push(frame),
                Ok(Err(error)) => panic!("reading LSP output: {error}"),
                Err(mpsc::RecvTimeoutError::Disconnected) => break,
                Err(mpsc::RecvTimeoutError::Timeout) => {
                    let _ = self.child.kill();
                    let _ = self.child.wait();
                    panic!("LSP server did not close stdout before deadline");
                },
            }
        }
        assert!(self.child.wait().expect("reap LSP server").success(), "LSP server failed");
        frames
    }
}

impl Drop for LspClient {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn read_frame(reader: &mut impl BufRead) -> io::Result<Option<Value>> {
    let mut header = String::new();
    if reader.read_line(&mut header)? == 0 {
        return Ok(None);
    }
    let length = header
        .trim_end_matches(['\r', '\n'])
        .strip_prefix("Content-Length: ")
        .and_then(|length| length.parse::<usize>().ok())
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "invalid LSP header"))?;
    header.clear();
    reader.read_line(&mut header)?;
    if header != "\r\n" {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "invalid LSP separator"));
    }
    let mut bytes = vec![0; length];
    reader.read_exact(&mut bytes)?;
    serde_json::from_slice(&bytes).map(Some).map_err(io::Error::other)
}

fn initialize(client: &mut LspClient) {
    client.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"process_id":null,"root_uri":null,"capabilities":{}}}));
    let response = client.receive_until(|frame| frame["id"] == 1);
    assert!(response.get("result").is_some(), "initialize must succeed: {response}");
}

fn has_diagnostic(frame: &Value, uri: &str, version: i32, code: &str) -> bool {
    frame["method"] == "textDocument/publishDiagnostics"
        && frame["params"]["uri"] == uri
        && frame["params"]["version"] == version
        && frame["params"]["diagnostics"].as_array().is_some_and(|diagnostics| {
            diagnostics.iter().any(|diagnostic| diagnostic["code"] == code)
        })
}

fn shutdown(client: &mut LspClient) {
    client.send(json!({"jsonrpc":"2.0","id":9,"method":"shutdown","params":null}));
}

fn assert_shutdown_response(frames: &[Value]) {
    assert!(
        frames.iter().any(|frame| frame["id"] == 9
            && frame.get("result") == Some(&Value::Null)
            && frame.get("error").is_none()),
        "shutdown must return success"
    );
}

#[cfg(target_os = "linux")]
fn find_compute_child(parent: u32) -> io::Result<Option<u32>> {
    let task_dir = format!("/proc/{parent}/task");
    for entry in std::fs::read_dir(task_dir)? {
        let task = entry?;
        let children = match std::fs::read_to_string(task.path().join("children")) {
            Ok(children) => children,
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => return Err(error),
        };
        for pid in children.split_whitespace() {
            let pid: u32 = pid.parse().map_err(io::Error::other)?;
            let args = std::fs::read(format!("/proc/{pid}/cmdline"))?;
            if args.split(|byte| *byte == 0).any(|arg| arg == b"--compute-worker") {
                return Ok(Some(pid));
            }
        }
    }
    Ok(None)
}

#[test]
fn lsp_real_executor_open_change_publishes_checked_diagnostics_and_reaps_worker() {
    let uri = "file:///process-contract.thy";
    let mut client = LspClient::start();
    initialize(&mut client);
    client.send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"text_document":{"uri":uri,"language_id":"isabelle","version":1,"text":"theory ProcessContract\nlemma pending: \"A\""}}}));
    let opened = client.receive_until(|frame| has_diagnostic(frame, uri, 1, "lemma-proof-pending"));
    assert!(opened["params"]["diagnostics"].as_array().is_some_and(|diagnostics| {
        diagnostics.iter().any(|diagnostic| {
            diagnostic["message"].as_str().is_some_and(|message| {
                message.contains("declaration alone is not a verified theorem")
            })
        })
    }));
    client.send(json!({"jsonrpc":"2.0","id":2,"method":"isabelle/proofGoals","params":{"text_document":{"uri":uri},"position":{"line":1,"character":0}}}));
    let goals = client.receive_until(|frame| frame["id"] == 2);
    assert_eq!(goals["result"]["has_unsolved"], true, "pending lemma must retain an open goal");
    client.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"text_document":{"uri":uri,"version":2},"content_changes":[{"text":"theory ProcessContract\ndefinition sample where \"sample = True\""}]}}));
    let changed =
        client.receive_until(|frame| has_diagnostic(frame, uri, 2, "definition-unchecked"));
    assert!(changed["params"]["diagnostics"].as_array().is_some_and(|diagnostics| {
        diagnostics.iter().any(|diagnostic| {
            diagnostic["message"]
                .as_str()
                .is_some_and(|message| message.contains("not kernel-accepted"))
        })
    }));
    #[cfg(target_os = "linux")]
    let compute_pid = if std::path::Path::new("/proc/self/task").exists() {
        Some(
            find_compute_child(client.child.id())
                .expect("inspect Linux child processes")
                .expect("completed RealExecutor checks retain a compute child until shutdown"),
        )
    } else {
        None
    };
    shutdown(&mut client);
    let remaining = client.finish();
    assert_shutdown_response(&remaining);
    #[cfg(target_os = "linux")]
    if let Some(compute_pid) = compute_pid {
        assert!(
            !std::path::Path::new(&format!("/proc/{compute_pid}")).exists(),
            "shutdown must reap the compute child"
        );
    }
}

#[test]
fn lsp_real_executor_close_pending_change_discards_stale_diagnostics_and_shuts_down() {
    let uri = "file:///closed-process-contract.thy";
    let mut client = LspClient::start();
    initialize(&mut client);
    client.send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"text_document":{"uri":uri,"language_id":"isabelle","version":1,"text":"theory CloseContract\nlemma first: \"A\""}}}));
    client.receive_until(|frame| has_diagnostic(frame, uri, 1, "lemma-proof-pending"));
    client.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"text_document":{"uri":uri,"version":2},"content_changes":[{"text":"theory CloseContract\nlemma stale: \"B\""}]}}));
    client.send(json!({"jsonrpc":"2.0","method":"textDocument/didClose","params":{"text_document":{"uri":uri}}}));
    let cleared = client.receive_until(|frame| {
        frame["method"] == "textDocument/publishDiagnostics"
            && frame["params"]["uri"] == uri
            && frame["params"].get("version").is_none()
    });
    assert_eq!(cleared["params"]["diagnostics"], json!([]));
    shutdown(&mut client);
    let remaining = client.finish();
    assert_shutdown_response(&remaining);
    assert!(
        !remaining.iter().any(|frame| has_diagnostic(frame, uri, 2, "lemma-proof-pending")),
        "closed revision must not publish a late successful check"
    );
}
