use std::fs::{self, OpenOptions};
use std::io::{BufWriter, Write};
use std::os::unix::net::UnixStream;

use serde_json::{Value, json};

use super::TraceState;

fn encoded_path(text: &str) -> String {
    format!(
        "\"{}\"",
        text.as_bytes().iter().map(|byte| format!("\\x{byte:02x}")).collect::<String>()
    )
}

fn capture_records(records: &str) -> (Value, Vec<Value>, String) {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("events.jsonl");
    let output =
        BufWriter::new(OpenOptions::new().write(true).create_new(true).open(&path).unwrap());
    let mut state = TraceState {
        output,
        pending: Default::default(),
        errors: Vec::new(),
        error_count: 0,
        event_count: 0,
        unresolved_relative_paths: 0,
    };
    let (source, mut writer) = UnixStream::pair().unwrap();
    let payload = records.as_bytes().to_vec();
    let writing = std::thread::spawn(move || writer.write_all(&payload).unwrap());
    state.consume(source).unwrap();
    writing.join().unwrap();
    let summary = state.finish();
    let text = fs::read_to_string(path).unwrap();
    let events = text.lines().map(|line| serde_json::from_str(line).unwrap()).collect();
    (summary, events, text)
}

#[test]
fn trace_execve_persists_only_path_without_arguments() {
    let argument = encoded_path("argument excluded from persisted reference evidence");
    let record =
        format!("21 1.000001 execve({}, [{argument}], 0x1) = 0\n", encoded_path("/bin/tool"));
    let (summary, events, persisted) = capture_records(&record);
    assert_eq!(summary["complete"], true);
    assert_eq!(
        events,
        vec![
            json!({"sequence": 1, "tid": 21, "timestamp": "1.000001", "syscall": "execve", "path": "/bin/tool", "result": "0"})
        ]
    );
    assert!(!persisted.contains(&argument));
}

#[test]
fn trace_interleaved_syscalls_preserve_order_paths_and_results() {
    let lines = format!(
        "21 1.000001 openat(AT_FDCWD, {}, O_RDONLY <unfinished ...>\n22 1.000002 openat(AT_FDCWD, {}, O_RDONLY) = -1 ENOENT\n21 1.000003 <... openat resumed>) = 4\n",
        encoded_path("first.ML"),
        encoded_path("second.ML")
    );
    let (summary, events, _) = capture_records(&lines);
    assert_eq!(summary["complete"], true);
    assert_eq!(
        events
            .iter()
            .map(|event| (
                event["tid"].as_u64().unwrap(),
                event["path"].as_str().unwrap(),
                event["result"].as_str().unwrap()
            ))
            .collect::<Vec<_>>(),
        [(22, "second.ML", "-1"), (21, "first.ML", "4")]
    );
    assert_eq!(summary["relative_paths_resolved"], false);
}

#[test]
fn trace_unfinished_syscall_does_not_produce_complete_evidence() {
    let lines = format!(
        "21 1.000001 openat(AT_FDCWD, {}, 0 <unfinished ...>\n",
        encoded_path("missing.ML")
    );
    let (summary, events, _) = capture_records(&lines);
    assert_eq!(summary["complete"], false);
    assert!(
        summary["errors"]
            .as_array()
            .unwrap()
            .contains(&json!("trace ended with unresolved syscalls"))
    );
    assert!(events.is_empty());
}

#[test]
fn trace_malformed_record_does_not_leak_raw_diagnostic() {
    let malformed = "unrecognized record containing private runtime input";
    let (summary, events, persisted) = capture_records(&format!("{malformed}\n"));
    assert_eq!(summary["complete"], false);
    assert!(!summary.to_string().contains(malformed));
    assert!(!persisted.contains(malformed));
    assert!(events.is_empty());
}

#[test]
fn trace_unreadable_path_does_not_become_later_argument() {
    let argument = encoded_path("argument must not replace an unreadable filename");
    let (summary, events, _) =
        capture_records(&format!("21 1.000001 execve(NULL, [{argument}], 0x1) = -1 EFAULT\n"));
    assert_eq!(summary["complete"], false);
    assert!(events.is_empty());
}

#[test]
fn trace_execveat_uses_second_argument_as_path() {
    let (summary, events, _) = capture_records(&format!(
        "21 1.000001 execveat(AT_FDCWD, {}, [], 0x1, 0) = 0\n",
        encoded_path("/bin/tool")
    ));
    assert_eq!(summary["complete"], true);
    assert_eq!(events[0]["path"], "/bin/tool");
}

#[test]
fn trace_annotated_openat_resolves_returned_file() {
    let dir = encoded_path("/fixed/src/Pure");
    let resource = encoded_path("/fixed/src/Pure/ROOT.ML");
    let lines = format!(
        "21 1.000001 openat(AT_FDCWD<{}>, {}, O_RDONLY) = 3<{}>\n",
        &dir[1..dir.len() - 1],
        encoded_path("ROOT.ML"),
        &resource[1..resource.len() - 1]
    );
    let (summary, events, _) = capture_records(&lines);
    assert_eq!(summary["complete"], true);
    assert_eq!(events[0]["resolved_path"], "/fixed/src/Pure/ROOT.ML");
    assert_eq!(summary["relative_paths_resolved"], true);
}

#[test]
fn trace_resumed_open_binds_returned_descriptor_not_arguments() {
    let resource = encoded_path("/fixed/src/Pure/ROOT.ML");
    let lines = format!(
        "21 1.000001 open({}, O_RDONLY <unfinished ...>\n21 1.000002 <... open resumed>) = 3<{}>\n",
        encoded_path("ROOT.ML"),
        &resource[1..resource.len() - 1]
    );
    let (summary, events, _) = capture_records(&lines);
    assert_eq!(summary["complete"], true);
    assert_eq!(events[0]["resolved_path"], "/fixed/src/Pure/ROOT.ML");
}

#[test]
fn trace_non_file_descriptor_stays_unresolved() {
    let (summary, events, _) = capture_records(&format!(
        "21 1.000001 openat(AT_FDCWD, {}, O_RDONLY) = 3<pipe:[42]>\n",
        encoded_path("pipe")
    ));
    assert_eq!(summary["complete"], true);
    assert!(events[0].get("resolved_path").is_none());
    assert_eq!(summary["relative_paths_resolved"], false);
}

#[test]
fn trace_oversized_record_is_bounded_and_does_not_persist() {
    let private = "private syscall argument ";
    let lines = format!(
        "{}\n21 1.000001 open({}, O_RDONLY) = 3\n",
        private.repeat(super::MAX_TRACE_LINE_BYTES / private.len() + 1),
        encoded_path("/tmp/next")
    );
    let (summary, events, persisted) = capture_records(&lines);
    assert_eq!(summary["complete"], false);
    assert_eq!(events.len(), 1);
    assert!(!persisted.contains(private));
}

#[test]
fn trace_unmatched_or_mismatched_resume_rejects_complete_evidence() {
    let (summary, events, _) = capture_records("21 1.000001 <... open resumed>) = 3\n");
    assert_eq!(summary["complete"], false);
    assert!(events.is_empty());
    let lines = format!(
        "21 1.000001 open({}, O_RDONLY <unfinished ...>\n21 1.000002 <... execve resumed>) = 0\n",
        encoded_path("secrets.ML")
    );
    let (summary, events, persisted) = capture_records(&lines);
    assert_eq!(summary["complete"], false);
    assert!(events.is_empty());
    assert!(!persisted.contains("secrets.ML"));
}

#[test]
fn trace_error_messages_are_bounded_without_raw_input() {
    let lines = "private malformed input\n".repeat(super::MAX_TRACE_ERRORS + 4);
    let (summary, events, persisted) = capture_records(&lines);
    assert_eq!(summary["error_count"], (super::MAX_TRACE_ERRORS + 5) as u64);
    assert_eq!(summary["errors"].as_array().unwrap().len(), super::MAX_TRACE_ERRORS);
    assert!(events.is_empty());
    assert!(!summary.to_string().contains("private malformed input"));
    assert!(!persisted.contains("private malformed input"));
}

#[test]
fn trace_aligned_result_columns_preserve_complete_events() {
    let lines = format!(
        "21 1.000001 open({}, O_RDONLY)          = 3\n21 1.000002 open({}, O_RDONLY <unfinished ...>\n21 1.000003 <... open resumed>) \t = 4\n",
        encoded_path("/fixed/first.ML"),
        encoded_path("/fixed/second.ML")
    );
    let (summary, events, _) = capture_records(&lines);
    assert_eq!(summary["complete"], true, "{summary}");
    assert_eq!(
        events
            .iter()
            .map(|event| (event["path"].as_str().unwrap(), event["result"].as_str().unwrap()))
            .collect::<Vec<_>>(),
        [("/fixed/first.ML", "3"), ("/fixed/second.ML", "4")]
    );
}
