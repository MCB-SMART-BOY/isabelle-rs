//! Flèche — incremental document checking engine.
//!
//! Coordinates document management, command execution via the
//! Isabelle kernel and Isar toplevel.

use std::sync::{
    Arc, Mutex,
    atomic::{AtomicBool, Ordering},
};

use crate::compute_worker::{CheckFailure, MAX_SOURCE, ProcessCheck};
use crate::{
    core::theory::Theory, document::*, hol::hol_loader::parse_lemmas, isar::toplevel::Toplevel,
    server::lsp_types::*,
};

// =========================================================================
// Checking Context
// =========================================================================

#[derive(Debug, Clone, Default)]
pub struct CheckContext {
    pub proof_state: Option<Arc<ProofState>>,
    pub context_hash: u64,
    pub in_proof: bool,
    pub proof_depth: u32,
}

// =========================================================================
// CommandExecutor trait
// =========================================================================

pub trait CommandExecutor: Send + Sync {
    fn execute(&self, command: &Command, ctx: &mut CheckContext) -> Vec<Diagnostic>;
    fn clone_box(&self) -> Box<dyn CommandExecutor>;
    /// Only the built-in RealExecutor is safe to run in the isolated child.
    /// Third-party implementations remain cooperative and in-process.
    fn is_builtin_real(&self) -> bool {
        false
    }
}

// =========================================================================
// Real executor — uses the actual Isabelle kernel + Isar toplevel
// =========================================================================

pub struct RealExecutor {
    theory: Arc<Theory>,
}

impl Default for RealExecutor {
    fn default() -> Self {
        Self::new()
    }
}

impl RealExecutor {
    pub fn new() -> Self {
        RealExecutor { theory: Theory::pure() }
    }
}

impl CommandExecutor for RealExecutor {
    fn clone_box(&self) -> Box<dyn CommandExecutor> {
        Box::new(RealExecutor { theory: Arc::clone(&self.theory) })
    }
    fn is_builtin_real(&self) -> bool {
        true
    }

    fn execute(&self, cmd: &Command, ctx: &mut CheckContext) -> Vec<Diagnostic> {
        let mut diags = Vec::new();

        // Classify the command
        let trimmed = cmd.source.trim();
        let first_word = trimmed.split_whitespace().next().unwrap_or("");

        match first_word {
            "theory" => {
                // Theory header — always OK
                ctx.in_proof = false;
                ctx.proof_state = None;
                diags.push(Diagnostic {
                    range: cmd.range.clone(),
                    severity: Some(DiagnosticSeverity::Information),
                    code: Some("theory-header".into()),
                    source: Some("isabelle-rs".into()),
                    message: format!("Theory {}", trimmed),
                    related_information: None,
                });
            },
            "lemma" | "theorem" | "corollary" | "proposition" => {
                // A declaration is not a completed proof. The experimental document
                // executor does not yet retain and classify the full proof block, so
                // it must leave the goal open rather than call `verify_lemma` here.
                let parsed = parse_lemmas(trimmed);
                if let Some(lem) = parsed.first() {
                    diags.push(Diagnostic {
                        range: cmd.range.clone(),
                        severity: Some(DiagnosticSeverity::Warning),
                        code: Some("lemma-proof-pending".into()),
                        source: Some("isabelle-rs".into()),
                        message: format!(
                            "Proof pending for {}; declaration alone is not a verified theorem",
                            lem.name
                        ),
                        related_information: None,
                    });
                    ctx.in_proof = true;
                    ctx.proof_state = Some(Arc::new(ProofState {
                        goals: vec![ProofGoal {
                            hyps: vec![],
                            conclusion: lem.name.clone(),
                            id: Some(format!("goal-{}", cmd.id)),
                        }],
                        background_goals: vec![],
                        has_unsolved: true,
                    }));
                } else {
                    diags.push(Diagnostic {
                        range: cmd.range.clone(),
                        severity: Some(DiagnosticSeverity::Error),
                        code: Some("parse-error".into()),
                        source: Some("isabelle-rs".into()),
                        message: format!("Could not parse lemma: {}", trimmed),
                        related_information: None,
                    });
                }
            },
            "definition" | "fun" | "primrec" | "datatype" | "inductive" => {
                // The document skeleton records the declaration but does not turn it
                // into a kernel theorem or conservative definition certificate.
                diags.push(Diagnostic {
                    range: cmd.range.clone(),
                    severity: Some(DiagnosticSeverity::Information),
                    code: Some("definition-unchecked".into()),
                    source: Some("isabelle-rs".into()),
                    message: format!(
                        "Definition parsed but not kernel-accepted: {}",
                        trimmed.chars().take(80).collect::<String>()
                    ),
                    related_information: None,
                });
            },
            _ => {
                // Unknown/other commands — try the toplevel executor as fallback
                let mut top = Toplevel::new(Arc::clone(&self.theory));
                match top.exec(&cmd.source) {
                    Ok(msg) => {
                        if msg.contains("unknown") {
                            diags.push(Diagnostic {
                                range: cmd.range.clone(),
                                severity: Some(DiagnosticSeverity::Warning),
                                code: Some("unknown-command".into()),
                                source: Some("isabelle-rs".into()),
                                message: msg,
                                related_information: None,
                            });
                        }
                    },
                    Err(e) => {
                        diags.push(Diagnostic {
                            range: cmd.range.clone(),
                            severity: Some(DiagnosticSeverity::Error),
                            code: Some("exec-error".into()),
                            source: Some("isabelle-rs".into()),
                            message: e,
                            related_information: None,
                        });
                    },
                }
            },
        }
        diags
    }
}

// =========================================================================
// Flèche Engine
// =========================================================================

/// Immutable input captured under the document lock; checking it needs no document access.
#[derive(Debug)]
pub struct CheckJob {
    uri: String,
    generation: u64,
    lifetime: Arc<()>,
    is_cancelled: Arc<AtomicBool>,
    version: i32,
    // None means the bounded check worker must tokenize the stored revision.
    commands: Option<Arc<Vec<Command>>>,
}
impl CheckJob {
    pub(crate) fn version(&self) -> i32 {
        self.version
    }

    pub(crate) fn is_cancelled(&self) -> bool {
        self.is_cancelled.load(Ordering::Acquire)
    }
}

/// Executed snapshots awaiting a generation-checked commit.
#[derive(Debug)]
pub struct CheckResult {
    uri: String,
    generation: u64,
    lifetime: Arc<()>,
    commands: Option<Vec<Command>>,
    snapshots: Vec<Snapshot>,
    limit: Option<CheckLimitError>,
}

impl CheckResult {
    /// URI of the document that produced this check.
    pub fn uri(&self) -> &str {
        &self.uri
    }
}

const MAX_CHECK_COMMANDS: usize = 4096;
const MAX_CHECK_DIAGNOSTICS: usize = 1024;
const MAX_CHECK_DIAGNOSTIC_BYTES: usize = 1024 * 1024;
const MAX_WORKER_REASON_BYTES: usize = 512;

#[derive(Debug, thiserror::Error)]
enum CheckLimitError {
    #[error("document has too many commands for the LSP checker")]
    Commands,
    #[error("document produces too many diagnostics for the LSP checker")]
    Diagnostics,
    #[error("document source exceeds the LSP checker size limit")]
    Source,
    #[error("open documents exceed the shared command snapshot limit")]
    WorkspaceCommands,
    #[error("compute worker returned inconsistent command snapshots")]
    InvalidResponse,
    #[error("compute worker unavailable: {0}")]
    Worker(String),
}

pub struct Fleche {
    document: Arc<Mutex<Document>>,
    executor: Arc<dyn CommandExecutor>,
}

impl Fleche {
    pub fn new(executor: Arc<dyn CommandExecutor>) -> Self {
        Fleche { document: Arc::new(Mutex::new(Document::new())), executor }
    }

    /// Run the same bounded command/check pipeline in the isolated built-in worker.
    pub(crate) fn check_process_content(
        content: &str,
        version: i32,
    ) -> Result<ProcessCheck, CheckFailure> {
        if content.len() > MAX_SOURCE {
            return Err(CheckFailure::Source);
        }
        let commands = Node::parse_commands_bounded(content, MAX_CHECK_COMMANDS)
            .ok_or(CheckFailure::Commands)?;
        let executor = RealExecutor::new();
        let mut context = CheckContext::default();
        let mut snapshots = Vec::with_capacity(commands.len());
        let mut diagnostic_count = 0usize;
        let mut diagnostic_bytes = 0usize;
        for command in &commands {
            let mut snapshot = Snapshot::new(command.id, version);
            snapshot.diagnostics = executor.execute(command, &mut context);
            diagnostic_count += snapshot.diagnostics.len();
            diagnostic_bytes +=
                snapshot.diagnostics.iter().map(|item| item.message.len()).sum::<usize>();
            if diagnostic_count > MAX_CHECK_DIAGNOSTICS
                || diagnostic_bytes > MAX_CHECK_DIAGNOSTIC_BYTES
            {
                return Err(CheckFailure::Diagnostics);
            }
            snapshot.proof_state = context.proof_state.clone();
            snapshot.context_hash = context.context_hash;
            snapshots.push(snapshot);
        }
        Ok(ProcessCheck { commands, snapshots })
    }
    pub(crate) fn uses_builtin_real(&self) -> bool {
        self.executor.is_builtin_real()
    }

    /// Copy only the current revision; the parent retains the job's Arc identity.
    pub(crate) fn prepare_process_input(&self, job: &CheckJob) -> Option<String> {
        if job.is_cancelled() {
            return None;
        }
        let doc = self.document.lock().expect("Document lock poisoned while reading revision");
        let node = doc.get_node(&job.uri)?;
        if node.generation != job.generation || !Arc::ptr_eq(&node.lifetime, &job.lifetime) {
            return None;
        }
        Some(node.content.clone())
    }

    /// Child metadata has no revision authority: the original job alone identifies the commit.
    pub(crate) fn complete_process_check(
        &self,
        job: CheckJob,
        outcome: Result<ProcessCheck, CheckFailure>,
    ) -> CheckResult {
        match outcome {
            Ok(checked) if Self::is_valid_process_check(&checked, job.version) => CheckResult {
                uri: job.uri.clone(),
                generation: job.generation,
                lifetime: Arc::clone(&job.lifetime),
                snapshots: checked.snapshots,
                commands: Some(checked.commands),
                limit: None,
            },
            Ok(_) => Self::limited_check(&job, CheckLimitError::InvalidResponse),
            Err(CheckFailure::Commands) => Self::limited_check(&job, CheckLimitError::Commands),
            Err(CheckFailure::Source) => Self::limited_check(&job, CheckLimitError::Source),
            Err(CheckFailure::Diagnostics) => {
                Self::limited_check(&job, CheckLimitError::Diagnostics)
            },
            Err(CheckFailure::Worker(reason)) => Self::failed_process_check(job, reason),
        }
    }
    pub(crate) fn is_valid_process_check(checked: &ProcessCheck, version: i32) -> bool {
        if checked.commands.len() != checked.snapshots.len()
            || checked.commands.len() > MAX_CHECK_COMMANDS
        {
            return false;
        }
        let mut diagnostic_count = 0usize;
        let mut diagnostic_bytes = 0usize;
        for (index, (command, snapshot)) in
            checked.commands.iter().zip(&checked.snapshots).enumerate()
        {
            if command.id != index
                || snapshot.command_id != command.id
                || snapshot.version != version
                || snapshot.stale
            {
                return false;
            }
            diagnostic_count += snapshot.diagnostics.len();
            diagnostic_bytes +=
                snapshot.diagnostics.iter().map(|item| item.message.len()).sum::<usize>();
            if diagnostic_count > MAX_CHECK_DIAGNOSTICS
                || diagnostic_bytes > MAX_CHECK_DIAGNOSTIC_BYTES
            {
                return false;
            }
        }
        true
    }

    fn failed_process_check(job: CheckJob, mut reason: String) -> CheckResult {
        if reason.len() > MAX_WORKER_REASON_BYTES {
            let mut boundary = MAX_WORKER_REASON_BYTES;
            while !reason.is_char_boundary(boundary) {
                boundary -= 1;
            }
            reason.truncate(boundary);
        }
        CheckResult {
            uri: job.uri,
            generation: job.generation,
            lifetime: job.lifetime,
            snapshots: Vec::new(),
            commands: None,
            limit: Some(CheckLimitError::Worker(reason)),
        }
    }

    pub fn open_file(&self, uri: &str, content: &str) -> Vec<Diagnostic> {
        let job = self.open_snapshot(uri, content);
        self.run_snapshot(job).and_then(|result| self.commit_snapshot(result)).unwrap_or_default()
    }

    pub fn update_file(&self, uri: &str, content: &str) -> Vec<Diagnostic> {
        let job = self.update_snapshot(uri, content);
        self.run_snapshot(job).and_then(|result| self.commit_snapshot(result)).unwrap_or_default()
    }

    /// Parse without holding the shared document lock, then install the result.
    pub fn open_snapshot(&self, uri: &str, content: &str) -> CheckJob {
        let commands = Arc::new(Node::parse_commands(content));
        self.install_snapshot(uri, content, Some(commands), true)
    }

    /// Apply an edit (or open an absent file) and capture its commands.
    pub fn update_snapshot(&self, uri: &str, content: &str) -> CheckJob {
        let commands = Arc::new(Node::parse_commands(content));
        self.install_snapshot(uri, content, Some(commands), false)
    }

    /// Admit a revision immediately; parsing happens on the bounded worker.
    pub fn open_queued_snapshot(&self, uri: &str, content: &str) -> CheckJob {
        self.install_snapshot(uri, content, None, true)
    }

    /// Replace a queued revision and revoke its previous check immediately.
    pub fn update_queued_snapshot(&self, uri: &str, content: &str) -> CheckJob {
        self.install_snapshot(uri, content, None, false)
    }

    fn install_snapshot(
        &self,
        uri: &str,
        content: &str,
        commands: Option<Arc<Vec<Command>>>,
        is_open: bool,
    ) -> CheckJob {
        let stored_commands = commands.clone().unwrap_or_else(|| Arc::new(Vec::new()));
        let mut doc = self.document.lock().expect("Document lock poisoned while installing file");
        let node = if is_open || doc.get_node(uri).is_none() {
            doc.open_parsed_file(uri.to_owned(), content.to_owned(), stored_commands)
        } else {
            doc.update_parsed_file(uri, content.to_owned(), stored_commands)
                .expect("File was present before updating");
            doc.get_node(uri).expect("File was present and just updated")
        };
        let mut job = Self::capture_snapshot(node);
        job.commands = commands;
        job
    }

    fn capture_snapshot(node: &Node) -> CheckJob {
        CheckJob {
            uri: node.uri.clone(),
            generation: node.generation,
            lifetime: Arc::clone(&node.lifetime),
            is_cancelled: Arc::clone(&node.is_cancelled),
            version: node.version,
            commands: Some(node.commands.clone()),
        }
    }

    /// Execute every command against a fresh context, without holding the document lock.
    /// A stored Snapshot does not contain the complete CheckContext needed for replay.
    /// Queued revisions already invalidated by an edit or close return None.
    pub fn run_snapshot(&self, job: CheckJob) -> Option<CheckResult> {
        self.execute_snapshot(job, None)
    }

    /// Cooperatively abandon a check between commands when shutdown or its
    /// document revision is cancelled; a running legacy command is not preempted.
    pub fn run_snapshot_cancellable(
        &self,
        job: CheckJob,
        cancelled: &AtomicBool,
    ) -> Option<CheckResult> {
        self.execute_snapshot(job, Some(cancelled))
    }

    fn execute_snapshot(
        &self,
        job: CheckJob,
        cancelled: Option<&AtomicBool>,
    ) -> Option<CheckResult> {
        let commands = if let Some(commands) = job.commands.as_ref() {
            Arc::clone(commands)
        } else {
            match self.parse_queued_snapshot(&job, cancelled) {
                Ok(Some(commands)) => commands,
                Ok(None) => return None,
                Err(error) => return Some(Self::limited_check(&job, error)),
            }
        };
        let should_cancel = || {
            cancelled.is_some_and(|global| {
                global.load(Ordering::Acquire) || job.is_cancelled.load(Ordering::Acquire)
            })
        };
        let mut ctx = CheckContext::default();
        let mut snapshots = Vec::with_capacity(commands.len());
        let mut diagnostic_count = 0;
        let mut diagnostic_bytes = 0;
        for command in commands.iter() {
            if should_cancel() {
                return None;
            }
            let mut snapshot = Snapshot::new(command.id, job.version);
            snapshot.diagnostics = self.executor.execute(command, &mut ctx);
            diagnostic_count += snapshot.diagnostics.len();
            diagnostic_bytes += snapshot
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.message.len())
                .sum::<usize>();
            if diagnostic_count > MAX_CHECK_DIAGNOSTICS
                || diagnostic_bytes > MAX_CHECK_DIAGNOSTIC_BYTES
            {
                return Some(Self::limited_check(&job, CheckLimitError::Diagnostics));
            }
            snapshot.proof_state = ctx.proof_state.clone();
            snapshot.context_hash = ctx.context_hash;
            snapshots.push(snapshot);
        }
        if should_cancel() {
            return None;
        }
        Some(CheckResult {
            uri: job.uri,
            generation: job.generation,
            lifetime: job.lifetime,
            snapshots,
            limit: None,
            commands: None,
        })
    }

    fn limited_check(job: &CheckJob, error: CheckLimitError) -> CheckResult {
        CheckResult {
            uri: job.uri.clone(),
            generation: job.generation,
            lifetime: Arc::clone(&job.lifetime),
            snapshots: Vec::new(),
            limit: Some(error),
            commands: None,
        }
    }

    fn parse_queued_snapshot(
        &self,
        job: &CheckJob,
        cancelled: Option<&AtomicBool>,
    ) -> Result<Option<Arc<Vec<Command>>>, CheckLimitError> {
        let is_cancelled = || {
            cancelled.is_some_and(|global| global.load(Ordering::Acquire))
                || job.is_cancelled.load(Ordering::Acquire)
        };
        if is_cancelled() {
            return Ok(None);
        }
        let content = {
            let doc = self.document.lock().expect("Document lock poisoned while reading revision");
            let Some(node) = doc.get_node(&job.uri) else {
                return Ok(None);
            };
            if node.generation != job.generation || !Arc::ptr_eq(&node.lifetime, &job.lifetime) {
                return Ok(None);
            }
            node.content.clone()
        };
        let commands = Arc::new(
            Node::parse_commands_bounded(&content, MAX_CHECK_COMMANDS)
                .ok_or(CheckLimitError::Commands)?,
        );
        if is_cancelled() {
            return Ok(None);
        }
        let mut doc =
            self.document.lock().expect("Document lock poisoned while installing commands");
        let Some(node) = doc.get_node_mut(&job.uri) else {
            return Ok(None);
        };
        if node.generation != job.generation || !Arc::ptr_eq(&node.lifetime, &job.lifetime) {
            return Ok(None);
        }
        node.commands = Arc::clone(&commands);
        Ok(Some(commands))
    }

    /// Commit only while both the exact revision and its open lifetime are current.
    /// Returns the full diagnostics for publishing, or None for a stale result.
    pub fn commit_snapshot(&self, result: CheckResult) -> Option<Vec<Diagnostic>> {
        self.commit_snapshot_budgeted(result, None)
    }

    pub(crate) fn commit_snapshot_limited(
        &self,
        result: CheckResult,
        max_workspace_snapshots: usize,
    ) -> Option<Vec<Diagnostic>> {
        self.commit_snapshot_budgeted(result, Some(max_workspace_snapshots))
    }

    fn commit_snapshot_budgeted(
        &self,
        mut result: CheckResult,
        max_workspace_snapshots: Option<usize>,
    ) -> Option<Vec<Diagnostic>> {
        let mut doc = self.document.lock().expect("Document lock poisoned while committing check");
        let node = doc.get_node(&result.uri)?;
        if node.generation != result.generation || !Arc::ptr_eq(&node.lifetime, &result.lifetime) {
            return None;
        }
        if result.limit.is_none()
            && let Some(maximum) = max_workspace_snapshots
        {
            let existing = node.snapshots.len();
            let retained: usize = doc.nodes().map(|node| node.snapshots.len()).sum();
            if retained - existing + result.snapshots.len() > maximum {
                result.limit = Some(CheckLimitError::WorkspaceCommands);
            }
        }
        let node = doc.get_node_mut(&result.uri)?;
        if let Some(error) = result.limit {
            let position = Position { line: 0, character: 0 };
            let diagnostic = Diagnostic {
                range: Range { start: position.clone(), end: position },
                severity: Some(DiagnosticSeverity::Error),
                code: Some("document-check-unavailable".into()),
                source: Some("isabelle-rs".into()),
                message: format!("Document was not checked: {error}"),
                related_information: None,
            };
            node.commands = Arc::new(Vec::new());
            node.snapshots.clear();
            node.pending_diagnostics = vec![diagnostic.clone()];
            return Some(vec![diagnostic]);
        }
        node.pending_diagnostics.clear();
        let diagnostics =
            result.snapshots.iter().flat_map(|snap| snap.diagnostics.iter().cloned()).collect();
        if let Some(commands) = result.commands {
            node.commands = Arc::new(commands);
        }
        node.snapshots = result.snapshots;
        Some(diagnostics)
    }

    pub fn close_file(&self, uri: &str) {
        let mut doc = self.document.lock().expect("Document lock poisoned");
        doc.close_file(uri);
    }

    pub fn get_proof_state(&self, uri: &str, line: u32) -> Option<ProofState> {
        let doc = self.document.lock().expect("Document lock poisoned");
        let node = doc.get_node(uri)?;
        node.commands
            .iter()
            .zip(&node.snapshots)
            .filter(|(command, _)| command.range.start.line <= line)
            .rev()
            .find_map(|(_, snapshot)| snapshot.proof_state.as_deref().cloned())
    }

    pub fn get_hover(&self, _uri: &str, _line: u32, _character: u32) -> Option<String> {
        None
    }

    /// Get the full text of a document by URI.
    pub fn get_document_text(&self, uri: &str) -> Option<String> {
        let doc = self.document.lock().expect("Document lock poisoned");
        doc.get_text(uri)
    }

    pub fn get_diagnostics(&self, uri: &str) -> Vec<Diagnostic> {
        let doc = self.document.lock().expect("Document lock poisoned");
        doc.diagnostics(uri)
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lemma_declaration_remains_pending() {
        let exec = RealExecutor::new();
        let cmd = Command::new(
            "lemma foo: \"A\"".into(),
            Range {
                start: Position { line: 0, character: 0 },
                end: Position { line: 0, character: 16 },
            },
            0,
        );
        let mut ctx = CheckContext::default();

        let diags = exec.execute(&cmd, &mut ctx);

        assert!(ctx.in_proof, "a declaration must not close the LSP proof state");
        assert!(ctx.proof_state.as_ref().is_some_and(|state| state.has_unsolved));
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code.as_deref(), Some("lemma-proof-pending"));
        assert!(diags[0].message.contains("declaration alone is not a verified theorem"));
    }

    #[test]
    fn full_document_does_not_verify_a_declaration_before_proof_close() {
        let engine = Fleche::new(Arc::new(RealExecutor::new()));
        let uri = "file:///test.thy";
        let diags = engine.open_file(
            uri,
            "theory Test\nimports HOL\nbegin\nlemma foo: \"A\"\nproof\napply rule\ndone\nend",
        );

        assert!(
            diags.iter().any(|diag| diag.code.as_deref() == Some("lemma-proof-pending")),
            "the document parser must expose the lemma declaration to the executor"
        );
        assert!(!diags.iter().any(|diag| {
            matches!(
                diag.code.as_deref(),
                Some("lemma-transitional-strict-closed" | "lemma-verified")
            )
        }));
        assert!(engine.get_proof_state(uri, 4).is_some_and(|state| state.has_unsolved));
    }

    #[test]
    fn process_check_multiple_commands_commits_diagnostics_and_goals() {
        let engine = Fleche::new(Arc::new(RealExecutor::new()));
        let uri = "file:///process.thy";
        let text = "theory Test\nlemma foo: \"A\"";
        let job = engine.open_queued_snapshot(uri, text);
        assert_eq!(engine.prepare_process_input(&job).as_deref(), Some(text));
        let checked = Fleche::check_process_content(text, job.version()).expect("bounded check");
        let result = engine.complete_process_check(job, Ok(checked));
        let diagnostics = engine.commit_snapshot(result).expect("current revision");
        assert!(diagnostics.iter().any(|diag| diag.code.as_deref() == Some("lemma-proof-pending")));
        assert!(engine.get_proof_state(uri, 2).is_some_and(|state| state.has_unsolved));
    }

    #[test]
    fn process_check_stale_revision_does_not_replace_current_commands() {
        let engine = Fleche::new(Arc::new(RealExecutor::new()));
        let uri = "file:///process-stale.thy";
        let old = engine.open_queued_snapshot(uri, "theory Old");
        let checked = Fleche::check_process_content("theory Old", old.version()).expect("check");
        let new = engine.update_queued_snapshot(uri, "theory New");
        assert!(engine.prepare_process_input(&old).is_none());
        assert!(engine.commit_snapshot(engine.complete_process_check(old, Ok(checked))).is_none());
        assert_eq!(engine.prepare_process_input(&new).as_deref(), Some("theory New"));
    }

    #[test]
    fn process_check_empty_revision_clears_previous_snapshot() {
        let engine = Fleche::new(Arc::new(RealExecutor::new()));
        let uri = "file:///process-empty.thy";
        engine.open_file(uri, "lemma foo: \"A\"");
        let empty = engine.update_queued_snapshot(uri, "");
        let checked = Fleche::check_process_content("", empty.version()).expect("empty check");
        let result = engine.complete_process_check(empty, Ok(checked));
        assert!(engine.commit_snapshot(result).expect("empty commit").is_empty());
        assert!(engine.get_proof_state(uri, 1).is_none());
    }

    #[test]
    fn process_check_worker_failure_reports_unavailable() {
        let engine = Fleche::new(Arc::new(RealExecutor::new()));
        let uri = "file:///process-failure.thy";
        let job = engine.open_queued_snapshot(uri, "lemma foo: \"A\"");
        let result =
            engine.complete_process_check(job, Err(CheckFailure::Worker("worker exited".into())));
        let diagnostics = engine.commit_snapshot(result).expect("failure commit");
        assert_eq!(diagnostics[0].code.as_deref(), Some("document-check-unavailable"));
        assert!(engine.get_proof_state(uri, 1).is_none());
    }

    #[test]
    fn process_check_source_limit_reports_unavailable() {
        let engine = Fleche::new(Arc::new(RealExecutor::new()));
        let uri = "file:///process-limit.thy";
        let oversized = engine.open_queued_snapshot(uri, &"x".repeat(MAX_SOURCE + 1));
        let result = engine.complete_process_check(oversized, Err(CheckFailure::Source));
        let diagnostics = engine.commit_snapshot(result).expect("limit commit");
        assert_eq!(diagnostics[0].code.as_deref(), Some("document-check-unavailable"));
    }

    struct ContextExecutor;

    impl CommandExecutor for ContextExecutor {
        fn clone_box(&self) -> Box<dyn CommandExecutor> {
            Box::new(Self)
        }

        fn execute(&self, command: &Command, ctx: &mut CheckContext) -> Vec<Diagnostic> {
            ctx.proof_depth += 1;
            let depth = ctx.proof_depth.to_string();
            ctx.proof_state = Some(Arc::new(ProofState {
                goals: vec![ProofGoal { hyps: vec![], conclusion: depth.clone(), id: None }],
                background_goals: vec![],
                has_unsolved: true,
            }));
            vec![Diagnostic {
                range: command.range.clone(),
                severity: None,
                code: None,
                source: None,
                message: depth,
                related_information: None,
            }]
        }
    }

    #[test]
    fn snapshot_older_edit_does_not_replace_newer_result() {
        let engine = Fleche::new(Arc::new(ContextExecutor));
        let uri = "file:///stale.thy";
        let old = engine.open_snapshot(uri, "theory Old");
        let new = engine.update_snapshot(uri, "theory New");

        assert!(
            engine.run_snapshot(old).and_then(|result| engine.commit_snapshot(result)).is_none()
        );
        let diagnostics = engine.commit_snapshot(engine.run_snapshot(new).unwrap()).unwrap();
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(engine.get_document_text(uri).as_deref(), Some("theory New"));
        assert_eq!(engine.get_diagnostics(uri).len(), 1);
    }

    #[test]
    fn snapshot_closed_and_reopened_same_content_rejects_old_lifetime() {
        let engine = Fleche::new(Arc::new(ContextExecutor));
        let uri = "file:///reopened.thy";
        let old = engine.open_snapshot(uri, "theory Test");
        engine.close_file(uri);
        let reopened = engine.open_snapshot(uri, "theory Test");

        assert!(
            engine.run_snapshot(old).and_then(|result| engine.commit_snapshot(result)).is_none()
        );
        assert!(engine.get_diagnostics(uri).is_empty());
        assert_eq!(
            engine.commit_snapshot(engine.run_snapshot(reopened).unwrap()).unwrap().len(),
            1
        );
    }

    #[test]
    fn snapshot_update_absent_file_opens_and_empty_edit_clears_diagnostics() {
        let engine = Fleche::new(Arc::new(ContextExecutor));
        let uri = "file:///absent.thy";
        let opened = engine.update_snapshot(uri, "theory Test");
        assert_eq!(engine.commit_snapshot(engine.run_snapshot(opened).unwrap()).unwrap().len(), 1);

        let empty = engine.update_snapshot(uri, "");
        assert!(engine.commit_snapshot(engine.run_snapshot(empty).unwrap()).unwrap().is_empty());
        assert!(engine.get_diagnostics(uri).is_empty());
        assert!(engine.get_proof_state(uri, 0).is_none());
    }

    #[test]
    fn queued_snapshot_stale_edit_discards_old_commands_and_proof_state() {
        let engine = Fleche::new(Arc::new(ContextExecutor));
        let uri = "file:///queued.thy";
        let old = engine.open_queued_snapshot(uri, "theory Old\nlemma old: \"A\"");
        let new = engine.update_queued_snapshot(uri, "theory New");
        assert_eq!(engine.get_document_text(uri).as_deref(), Some("theory New"));
        assert!(engine.get_proof_state(uri, 0).is_none());
        let cancelled = AtomicBool::new(false);
        assert!(engine.run_snapshot_cancellable(old, &cancelled).is_none());
        let result = engine.run_snapshot_cancellable(new, &cancelled).unwrap();
        assert_eq!(engine.commit_snapshot(result).unwrap().len(), 1);
        assert_eq!(engine.get_diagnostics(uri).len(), 1);
    }

    #[test]
    fn queued_snapshot_close_reopen_rejects_previous_lifetime() {
        let engine = Fleche::new(Arc::new(ContextExecutor));
        let uri = "file:///queued-lifetime.thy";
        let old = engine.open_queued_snapshot(uri, "theory Test");
        engine.close_file(uri);
        let new = engine.open_queued_snapshot(uri, "theory Test");
        let cancelled = AtomicBool::new(false);
        assert!(engine.run_snapshot_cancellable(old, &cancelled).is_none());
        assert!(
            engine
                .commit_snapshot(engine.run_snapshot_cancellable(new, &cancelled).unwrap())
                .is_some()
        );
    }

    #[test]
    fn queued_snapshot_stale_synchronous_execution_returns_no_result() {
        let engine = Fleche::new(Arc::new(ContextExecutor));
        let uri = "file:///queued-sync.thy";
        let old = engine.open_queued_snapshot(uri, "theory Old");
        engine.update_queued_snapshot(uri, "theory New");
        assert!(engine.run_snapshot(old).is_none());
    }

    #[test]
    fn queued_snapshot_command_budget_rejects_dense_source_without_checking() {
        let engine = Fleche::new(Arc::new(RealExecutor::new()));
        let uri = "file:///dense.thy";
        let source = "theory X;\n".repeat(MAX_CHECK_COMMANDS + 1);
        let job = engine.open_queued_snapshot(uri, &source);
        let result = engine.run_snapshot(job).expect("current revision");
        let diagnostics = engine.commit_snapshot(result).expect("current revision");
        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].message.contains("too many commands"));
        assert_eq!(
            engine.get_diagnostics(uri)[0].code.as_deref(),
            Some("document-check-unavailable")
        );
        assert!(engine.get_proof_state(uri, 0).is_none());
    }

    #[test]
    fn queued_snapshot_diagnostic_budget_rejects_output_expansion() {
        let engine = Fleche::new(Arc::new(RealExecutor::new()));
        let uri = "file:///noisy.thy";
        let source = "theory X;\n".repeat(MAX_CHECK_DIAGNOSTICS + 1);
        let job = engine.open_queued_snapshot(uri, &source);
        let result = engine.run_snapshot(job).expect("current revision");
        let diagnostics = engine.commit_snapshot(result).expect("current revision");
        assert_eq!(diagnostics.len(), 1);
        assert!(diagnostics[0].message.contains("too many diagnostics"));
        assert!(engine.get_proof_state(uri, 0).is_none());
    }

    #[test]
    fn queued_snapshot_workspace_budget_rejects_third_file_without_partial_proof_state() {
        let engine = Fleche::new(Arc::new(RealExecutor::new()));
        for name in ["first", "second"] {
            let uri = format!("file:///{name}.thy");
            let job = engine.open_queued_snapshot(&uri, "theory X");
            let diagnostics = engine.commit_snapshot_limited(engine.run_snapshot(job).unwrap(), 2);
            assert_eq!(diagnostics.unwrap()[0].code.as_deref(), Some("theory-header"));
        }
        let uri = "file:///third.thy";
        let job = engine.open_queued_snapshot(uri, "theory X");
        let diagnostics = engine
            .commit_snapshot_limited(engine.run_snapshot(job).unwrap(), 2)
            .expect("current revision");
        assert!(diagnostics[0].message.contains("shared command snapshot limit"));
        assert!(engine.get_proof_state(uri, 0).is_none());
        engine.close_file("file:///first.thy");
        let job = engine.update_queued_snapshot(uri, "theory X");
        let diagnostics = engine.commit_snapshot_limited(engine.run_snapshot(job).unwrap(), 2);
        assert_eq!(diagnostics.unwrap()[0].code.as_deref(), Some("theory-header"));
    }

    #[test]
    fn snapshot_replays_prefix_context_and_diagnostics_after_edit() {
        let engine = Fleche::new(Arc::new(ContextExecutor));
        let uri = "file:///prefix.thy";
        let original = "theory Test\nlemma foo: \"A\"";
        let updated = "theory Test\nlemma foo: \"A\"\nlemma bar: \"B\"";
        assert_eq!(engine.open_file(uri, original).len(), 2);

        let diagnostics = engine.update_file(uri, updated);
        let messages: Vec<_> = diagnostics.iter().map(|diag| diag.message.as_str()).collect();
        assert_eq!(messages, vec!["1", "2", "3"]);
        assert_eq!(engine.get_proof_state(uri, 2).unwrap().goals[0].conclusion, "3");
        assert_eq!(engine.get_proof_state(uri, 1).unwrap().goals[0].conclusion, "2");
        assert_eq!(engine.get_diagnostics(uri).len(), 3);
    }

    struct BlockingExecutor {
        started: std::sync::mpsc::Sender<()>,
        proceed: Arc<AtomicBool>,
    }

    impl CommandExecutor for BlockingExecutor {
        fn clone_box(&self) -> Box<dyn CommandExecutor> {
            Box::new(Self { started: self.started.clone(), proceed: Arc::clone(&self.proceed) })
        }

        fn execute(&self, _command: &Command, _ctx: &mut CheckContext) -> Vec<Diagnostic> {
            self.started.send(()).expect("Test receiver available");
            let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
            while !self.proceed.load(Ordering::Acquire) {
                assert!(std::time::Instant::now() < deadline, "Test release timed out");
                std::thread::yield_now();
            }
            Vec::new()
        }
    }

    #[test]
    fn snapshot_blocked_executor_does_not_hold_document_lock() {
        use std::{sync::mpsc, thread, time::Duration};

        let (started_tx, started_rx) = mpsc::channel();
        let proceed = Arc::new(AtomicBool::new(false));
        let engine = Arc::new(Fleche::new(Arc::new(BlockingExecutor {
            started: started_tx,
            proceed: Arc::clone(&proceed),
        })));
        let job = engine.open_snapshot("file:///blocked.thy", "theory Blocked");
        engine.open_snapshot("file:///other.thy", "theory Other");
        let worker_engine = Arc::clone(&engine);
        let worker = thread::spawn(move || worker_engine.run_snapshot(job));
        started_rx.recv_timeout(Duration::from_secs(5)).expect("Executor reached");

        let (query_tx, query_rx) = mpsc::channel();
        let query_engine = Arc::clone(&engine);
        let query = thread::spawn(move || {
            query_engine.update_snapshot("file:///other.thy", "theory Changed");
            query_tx.send(query_engine.get_document_text("file:///other.thy")).unwrap();
        });
        let other_text = query_rx.recv_timeout(Duration::from_secs(5));
        proceed.store(true, Ordering::Release);
        worker.join().expect("Checker finished");
        query.join().expect("Document query finished");
        assert_eq!(other_text.unwrap().as_deref(), Some("theory Changed"));
    }

    #[test]
    fn snapshot_cancelled_between_commands_returns_no_result() {
        use std::{sync::mpsc, thread, time::Duration};

        let (started_tx, started_rx) = mpsc::channel();
        let proceed = Arc::new(AtomicBool::new(false));
        let engine = Arc::new(Fleche::new(Arc::new(BlockingExecutor {
            started: started_tx,
            proceed: Arc::clone(&proceed),
        })));
        let uri = "file:///cancelled.thy";
        let job = engine.open_snapshot(uri, "theory Test\nlemma foo: \"A\"");
        let cancelled = Arc::new(AtomicBool::new(false));
        let worker_engine = Arc::clone(&engine);
        let worker_flag = Arc::clone(&cancelled);
        let worker =
            thread::spawn(move || worker_engine.run_snapshot_cancellable(job, &worker_flag));
        started_rx.recv_timeout(Duration::from_secs(5)).expect("First command started");

        cancelled.store(true, Ordering::Release);
        proceed.store(true, Ordering::Release);
        assert!(worker.join().expect("Checker finished").is_none());
        assert!(started_rx.try_recv().is_err(), "Second command must not execute");
        assert!(engine.get_diagnostics(uri).is_empty());
    }

    fn assert_superseded_check_stops(change: impl FnOnce(&Fleche, &str)) {
        use std::{sync::mpsc, thread, time::Duration};

        let (started_tx, started_rx) = mpsc::channel();
        let proceed = Arc::new(AtomicBool::new(false));
        let engine = Arc::new(Fleche::new(Arc::new(BlockingExecutor {
            started: started_tx,
            proceed: Arc::clone(&proceed),
        })));
        let uri = "file:///superseded.thy";
        let job = engine.open_snapshot(uri, "theory Test\nlemma foo: \"A\"");
        let worker_engine = Arc::clone(&engine);
        let worker = thread::spawn(move || {
            worker_engine.run_snapshot_cancellable(job, &AtomicBool::new(false))
        });
        started_rx.recv_timeout(Duration::from_secs(5)).expect("First command started");

        change(&engine, uri);
        proceed.store(true, Ordering::Release);
        assert!(worker.join().expect("Checker finished").is_none());
        assert!(started_rx.try_recv().is_err(), "Second command must not execute");
    }

    #[test]
    fn snapshot_edit_while_executing_abandons_remaining_commands() {
        assert_superseded_check_stops(|engine, uri| {
            engine.update_snapshot(uri, "theory Edited");
        });
    }

    #[test]
    fn snapshot_close_while_executing_abandons_remaining_commands() {
        assert_superseded_check_stops(|engine, uri| engine.close_file(uri));
    }

    #[test]
    fn snapshot_reopen_while_executing_abandons_remaining_commands() {
        assert_superseded_check_stops(|engine, uri| {
            engine.open_snapshot(uri, "theory Reopened");
        });
    }
}
