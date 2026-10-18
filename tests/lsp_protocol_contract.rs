use std::{
    io::Write,
    process::{Child, Command, Output, Stdio},
    thread,
    time::{Duration, Instant},
};

use serde_json::{Value, json};

const PROCESS_DEADLINE: Duration = Duration::from_secs(10);
const WAIT_POLL_INTERVAL: Duration = Duration::from_millis(10);

fn frame(value: &Value) -> Vec<u8> {
    let body = serde_json::to_vec(value).expect("valid request");
    let mut framed = format!("Content-Length: {}\r\n\r\n", body.len()).into_bytes();
    framed.extend_from_slice(&body);
    framed
}

fn wait_for_exit(mut child: Child) -> Output {
    let start = Instant::now();
    loop {
        match child.try_wait().expect("query LSP process") {
            Some(_) => return child.wait_with_output().expect("read LSP process output"),
            None if start.elapsed() < PROCESS_DEADLINE => thread::sleep(WAIT_POLL_INTERVAL),
            None => {
                child.kill().expect("stop stalled LSP process");
                let _ = child.wait();
                panic!("LSP process did not exit before deadline");
            },
        }
    }
}

fn read_frames(mut bytes: &[u8]) -> Vec<Value> {
    let mut frames = Vec::new();
    while !bytes.is_empty() {
        let header_end =
            bytes.windows(4).position(|window| window == b"\r\n\r\n").expect("LSP frame header");
        let header = std::str::from_utf8(&bytes[..header_end]).expect("ASCII LSP header");
        let size: usize = header
            .strip_prefix("Content-Length: ")
            .expect("only LSP frames on stdout")
            .parse()
            .expect("numeric frame size");
        bytes = &bytes[header_end + 4..];
        assert!(bytes.len() >= size, "complete LSP frame");
        frames.push(serde_json::from_slice(&bytes[..size]).expect("JSON-RPC frame"));
        bytes = &bytes[size..];
    }
    frames
}

fn run_lsp(messages: &[Value]) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_isabelle-rs"))
        .arg("--lsp")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start LSP server");
    let mut input = child.stdin.take().expect("client stdin");
    for message in messages {
        input.write_all(&frame(message)).expect("send LSP frame");
    }
    drop(input);
    wait_for_exit(child)
}

#[test]
fn lsp_malformed_frame_exits_without_stderr_lock_deadlock() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_isabelle-rs"))
        .arg("--lsp")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start LSP server");
    let mut input = child.stdin.take().expect("client stdin");
    input.write_all(b"Content-Length: invalid\r\n\r\n").expect("send malformed frame");
    drop(input);
    let output = wait_for_exit(child);
    assert!(!output.status.success(), "malformed frame must fail the server");
}

#[test]
fn lsp_shutdown_immediate_returns_framed_responses() {
    let output = run_lsp(&[
        json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"process_id":null,"root_uri":null,"capabilities":{}}}),
        json!({"jsonrpc":"2.0","id":2,"method":"shutdown","params":null}),
    ]);
    assert!(output.status.success(), "server exit: {}", String::from_utf8_lossy(&output.stderr));
    let responses = read_frames(&output.stdout);
    assert_eq!(responses.len(), 2);
    assert_eq!(responses[0]["id"], 1);
    assert_eq!(responses[0]["result"]["capabilities"]["text_document_sync"], 1);
    assert_eq!(responses[1]["id"], 2);
    assert_eq!(responses[1].get("result"), Some(&Value::Null));
    assert!(responses[1].get("error").is_none());
}

#[test]
fn lsp_cancel_request_without_pending_definition_does_not_consume_future_request() {
    let output = run_lsp(&[
        json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"process_id":null,"root_uri":null,"capabilities":{}}}),
        json!({"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":"next"}}),
        json!({"jsonrpc":"2.0","id":"next","method":"textDocument/documentSymbol","params":{"text_document":{"uri":"file:///not-open.thy"}}}),
        json!({"jsonrpc":"2.0","id":3,"method":"shutdown","params":null}),
    ]);
    assert!(output.status.success(), "server exit: {}", String::from_utf8_lossy(&output.stderr));
    let frames = read_frames(&output.stdout);
    let answers: Vec<_> = frames.iter().filter(|frame| frame["id"] == "next").collect();
    assert_eq!(answers.len(), 1, "canceling an unknown ID must not reply or affect its reuse");
    assert_eq!(answers[0].get("result"), Some(&Value::Null));
    assert!(answers[0].get("error").is_none());
    assert!(frames.iter().any(|frame| frame["id"] == 3 && frame["result"].is_null()));
}

#[test]
fn lsp_definition_utf16_surrogate_position_returns_null_without_crashing() {
    let output = run_lsp(&[
        json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"process_id":null,"root_uri":null,"capabilities":{}}}),
        json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"text_document":{"uri":"file:///utf16.thy","language_id":"isabelle","version":1,"text":"text \"😀A\""}}}),
        json!({"jsonrpc":"2.0","id":3,"method":"textDocument/definition","params":{"text_document":{"uri":"file:///utf16.thy"},"position":{"line":0,"character":7}}}),
        json!({"jsonrpc":"2.0","id":4,"method":"shutdown","params":null}),
    ]);
    assert!(output.status.success(), "server exit: {}", String::from_utf8_lossy(&output.stderr));
    let frames = read_frames(&output.stdout);
    let answer = frames.iter().find(|frame| frame["id"] == 3).expect("definition response");
    assert_eq!(
        answer.get("result"),
        Some(&Value::Null),
        "inside a UTF-16 surrogate pair has no word"
    );
    assert!(answer.get("error").is_none());
}

#[test]
fn lsp_oversized_uri_notifications_do_not_echo_client_input() {
    let uri = format!("file:///{}", "x".repeat(8192));
    let output = run_lsp(&[
        json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"process_id":null,"root_uri":null,"capabilities":{}}}),
        json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"text_document":{"uri":uri,"language_id":"isabelle","version":1,"text":"theory Test"}}}),
        json!({"jsonrpc":"2.0","method":"textDocument/didClose","params":{"text_document":{"uri":uri}}}),
        json!({"jsonrpc":"2.0","id":2,"method":"shutdown","params":null}),
    ]);
    assert!(output.status.success(), "server exit: {}", String::from_utf8_lossy(&output.stderr));
    let frames = read_frames(&output.stdout);
    assert_eq!(frames.len(), 2, "oversized notifications do not publish diagnostics");
    assert!(!output.stdout.windows(uri.len()).any(|window| window == uri.as_bytes()));
}

#[test]
fn lsp_oversized_uri_definition_returns_bounded_error() {
    let uri = format!("file:///{}", "x".repeat(8192));
    let output = run_lsp(&[
        json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"process_id":null,"root_uri":null,"capabilities":{}}}),
        json!({"jsonrpc":"2.0","id":3,"method":"textDocument/definition","params":{"text_document":{"uri":uri},"position":{"line":0,"character":0}}}),
        json!({"jsonrpc":"2.0","id":4,"method":"shutdown","params":null}),
    ]);
    assert!(output.status.success(), "server exit: {}", String::from_utf8_lossy(&output.stderr));
    let frames = read_frames(&output.stdout);
    let answer = frames.iter().find(|frame| frame["id"] == 3).expect("bounded error response");
    assert_eq!(answer["error"]["code"], -32602);
    assert!(answer.get("result").is_none());
    assert!(!output.stdout.windows(uri.len()).any(|window| window == uri.as_bytes()));
}

#[test]
fn lsp_rejected_full_sync_invalidates_old_symbols_and_later_recovers() {
    let uri = "file:///rejected-full-sync.thy";
    let oversized = "X".repeat(1024 * 1024 + 1);
    let output = run_lsp(&[
        json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"process_id":null,"root_uri":null,"capabilities":{}}}),
        json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"text_document":{"uri":uri,"language_id":"isabelle","version":1,"text":"theory Old\nbegin\nlemma stale: \"A\""}}}),
        json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"text_document":{"uri":uri,"version":2},"content_changes":[{"text":oversized}]}}),
        json!({"jsonrpc":"2.0","id":3,"method":"textDocument/documentSymbol","params":{"text_document":{"uri":uri}}}),
        json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"text_document":{"uri":uri,"version":3},"content_changes":[{"text":"theory New\nbegin\nlemma fresh: \"B\""}]}}),
        json!({"jsonrpc":"2.0","id":4,"method":"textDocument/documentSymbol","params":{"text_document":{"uri":uri}}}),
        json!({"jsonrpc":"2.0","id":5,"method":"shutdown","params":null}),
    ]);
    assert!(output.status.success(), "server exit: {}", String::from_utf8_lossy(&output.stderr));
    let frames = read_frames(&output.stdout);
    let rejected = frames.iter().find(|frame| frame["id"] == 3).expect("rejected revision query");
    assert_eq!(rejected.get("result"), Some(&Value::Null));
    let recovered = frames.iter().find(|frame| frame["id"] == 4).expect("recovered revision query");
    assert_eq!(recovered["result"][0]["children"][0]["name"], "fresh");
    assert!(frames.iter().any(|frame| frame["method"] == "textDocument/publishDiagnostics"
        && frame["params"]["version"] == 2));
}

#[test]
fn lsp_unopened_file_symbol_query_does_not_read_disk() {
    let uri = format!("file://{}/tests/fixtures/TrustedTrueI.thy", env!("CARGO_MANIFEST_DIR"));
    let output = run_lsp(&[
        json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"process_id":null,"root_uri":null,"capabilities":{}}}),
        json!({"jsonrpc":"2.0","id":2,"method":"textDocument/documentSymbol","params":{"text_document":{"uri":uri}}}),
        json!({"jsonrpc":"2.0","id":3,"method":"shutdown","params":null}),
    ]);
    assert!(output.status.success(), "server exit: {}", String::from_utf8_lossy(&output.stderr));
    let frames = read_frames(&output.stdout);
    let symbols = frames.iter().find(|frame| frame["id"] == 2).expect("symbol response");
    assert_eq!(symbols.get("result"), Some(&Value::Null));
}

#[test]
fn lsp_large_unexpected_response_id_does_not_block_or_log_client_input() {
    let client_id = "X".repeat(256 * 1024);
    let output = run_lsp(&[
        json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"process_id":null,"root_uri":null,"capabilities":{}}}),
        json!({"jsonrpc":"2.0","id":client_id,"result":null}),
        json!({"jsonrpc":"2.0","id":3,"method":"shutdown","params":null}),
    ]);
    assert!(output.status.success(), "server exit: {}", String::from_utf8_lossy(&output.stderr));
    assert!(read_frames(&output.stdout).iter().any(|frame| frame["id"] == 3));
    assert!(!output.stderr.windows(client_id.len()).any(|window| window == client_id.as_bytes()));
}

#[test]
fn lsp_definition_lookup_does_not_block_symbol_query_or_shutdown() {
    let uri = "file:///query.thy";
    let output = run_lsp(&[
        json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"process_id":null,"root_uri":null,"capabilities":{}}}),
        json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"text_document":{"uri":uri,"language_id":"isabelle","version":1,"text":"theory Sample\nbegin\nlemma fresh: \"A\""}}}),
        json!({"jsonrpc":"2.0","id":2,"method":"textDocument/definition","params":{"text_document":{"uri":uri},"position":{"line":0,"character":8}}}),
        json!({"jsonrpc":"2.0","id":3,"method":"textDocument/documentSymbol","params":{"text_document":{"uri":uri}}}),
        json!({"jsonrpc":"2.0","id":4,"method":"shutdown","params":null}),
    ]);
    let frames = read_frames(&output.stdout);
    let definition = frames.iter().find(|frame| frame["id"] == 2).expect("definition terminates");
    assert!(
        definition.get("result").is_some() || definition["error"]["code"] == -32800,
        "successful or canceled definition must terminate"
    );
    let symbols = frames.iter().find(|frame| frame["id"] == 3).expect("symbol response");
    assert_eq!(symbols["result"][0]["children"][0]["name"], "fresh");
    assert!(
        frames.iter().any(|frame| frame["id"] == 4 && frame.get("result") == Some(&Value::Null))
    );
    if !output.status.success() {
        assert_eq!(definition["error"]["code"], -32800, "only an unfinished lookup may time out");
    }
}

#[test]
fn lsp_definition_replacement_rejection_and_close_reply_once_per_query() {
    let uri = "file:///definition-cancel.thy";
    let replacement = json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"text_document":{"uri":uri,"version":2},"content_changes":[{"text":"theory Second\nbegin"}]}});
    let rejection = json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"text_document":{"uri":uri,"version":2},"content_changes":[{"range":{"start":{"line":0,"character":0},"end":{"line":0,"character":1}},"text":"T"}]}});
    let close = json!({"jsonrpc":"2.0","method":"textDocument/didClose","params":{"text_document":{"uri":uri}}});
    for mutation in [replacement, rejection, close] {
        let output = run_lsp(&[
            json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"process_id":null,"root_uri":null,"capabilities":{}}}),
            json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"text_document":{"uri":uri,"language_id":"isabelle","version":1,"text":"theory First\nbegin"}}}),
            json!({"jsonrpc":"2.0","id":2,"method":"textDocument/definition","params":{"text_document":{"uri":uri},"position":{"line":0,"character":8}}}),
            mutation,
            json!({"jsonrpc":"2.0","id":3,"method":"shutdown","params":null}),
        ]);
        let frames = read_frames(&output.stdout);
        let answers: Vec<_> = frames.iter().filter(|frame| frame["id"] == 2).collect();
        assert_eq!(answers.len(), 1, "one reply to each accepted definition");
        assert!(
            answers[0].get("result").is_some() || answers[0]["error"]["code"] == -32800,
            "definition completed before mutation or was canceled"
        );
        assert!(frames.iter().any(|frame| frame["id"] == 3 && frame["result"].is_null()));
    }
}

#[test]
fn lsp_document_symbol_dense_input_reports_explicit_limit() {
    let uri = "file:///many-symbols.thy";
    let text = "lemma a: \"A\"\n".repeat(8193);
    let output = run_lsp(&[
        json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"process_id":null,"root_uri":null,"capabilities":{}}}),
        json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"text_document":{"uri":uri,"language_id":"isabelle","version":1,"text":text}}}),
        json!({"jsonrpc":"2.0","id":2,"method":"textDocument/documentSymbol","params":{"text_document":{"uri":uri}}}),
        json!({"jsonrpc":"2.0","id":3,"method":"shutdown","params":null}),
    ]);
    let frames = read_frames(&output.stdout);
    let symbols = frames.iter().find(|frame| frame["id"] == 2).expect("bounded symbol response");
    assert_eq!(symbols["error"]["code"], -32000);
    assert!(frames.iter().any(|frame| frame["id"] == 3));
}
