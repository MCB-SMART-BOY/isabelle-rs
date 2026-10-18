use std::{
    path::Path,
    process::{Command, Stdio},
    sync::Arc,
};

use isabelle_rs::{
    fleche::engine::RealExecutor,
    session::{Session, SessionError},
};

const MAX_SOURCE_BYTES: usize = 1024 * 1024;

#[test]
fn session_real_executor_isolates_checks_and_recovers_after_rejected_source() {
    let binary = Path::new(env!("CARGO_BIN_EXE_isabelle-rs"));
    let mut session = Session::new_with_worker(Arc::new(RealExecutor::new()), binary).unwrap();
    let uri = "file:///session-process.thy";

    let diagnostics = session.open_file(uri, "theory Test\nlemma pending: \"A\"").unwrap();
    assert!(diagnostics.iter().any(|diag| diag.code.as_deref() == Some("lemma-proof-pending")));
    assert!(session.proof_state(uri, 0).unwrap().is_some());

    let oversized = " ".repeat(MAX_SOURCE_BYTES + 1);
    assert!(matches!(
        session.update_file(uri, &oversized),
        Err(SessionError::SourceTooLarge { uri: bad_uri, .. }) if bad_uri == uri
    ));
    assert!(matches!(session.proof_state(uri, 0), Err(SessionError::SourceTooLarge { .. })));

    let diagnostics = session.update_file(uri, "theory Recovered").unwrap();
    assert!(diagnostics.iter().any(|diag| diag.code.as_deref() == Some("theory-header")));
    assert!(matches!(session.proof_state(uri, 0), Ok(None)));

    session.open_file(uri, "lemma replaced: \"A\"").unwrap();
    assert!(session.proof_state(uri, 0).unwrap().is_some());
    session.open_file(uri, "theory Replacement").unwrap();
    assert!(matches!(session.proof_state(uri, 0), Ok(None)));

    session.close_file(uri);
    session.open_file(uri, "lemma reopened: \"B\"").unwrap();
    assert!(session.proof_state(uri, 0).unwrap().is_some());
    session.shutdown().unwrap();
}

#[test]
fn session_unavailable_compute_executable_reports_uri_and_can_retry() {
    let mut session = Session::new_with_worker(
        Arc::new(RealExecutor::new()),
        Path::new("/definitely-not-present-isabelle-rs-compute-worker"),
    )
    .unwrap();
    let uri = "file:///unavailable.thy";
    for result in
        [session.open_file(uri, "theory First"), session.update_file(uri, "theory Second")]
    {
        assert!(matches!(result, Err(SessionError::Compute { uri: failed_uri, reason })
            if failed_uri == uri && reason.contains("start compute worker")));
    }
    assert!(matches!(session.proof_state(uri, 0), Err(SessionError::Compute { .. })));
    session.shutdown().unwrap();
}

#[test]
fn compute_worker_closed_stdin_exits_without_demo_output() {
    let output = Command::new(env!("CARGO_BIN_EXE_isabelle-rs"))
        .arg("--compute-worker")
        .stdin(Stdio::null())
        .output()
        .expect("start compute worker with closed input");
    assert!(!output.status.success(), "a worker without a handshake must fail");
    assert!(output.stdout.is_empty(), "worker mode must not run the demo or LSP server");
}
