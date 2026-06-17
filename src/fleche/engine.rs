//! Flèche — incremental document checking engine.
//!
//! Coordinates document management, command execution via the
//! Isabelle kernel and Isar toplevel.

use std::sync::{Arc, Mutex};

use crate::{
    core::theory::Theory, document::document::*, hol::hol_loader::parse_lemmas,
    isar::toplevel::Toplevel, server::lsp_types::*,
};

// =========================================================================
// Checking Context
// =========================================================================

#[derive(Debug, Clone)]
#[derive(Default)]
pub struct CheckContext {
    pub proof_state: Option<ProofState>,
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
                // Try to verify this lemma using the HOL theorem database
                let parsed = parse_lemmas(trimmed);
                if let Some(lem) = parsed.first() {
                    match crate::isar::method::verify_lemma(lem) {
                        Some(_thm) => {
                            // Success! The lemma is verified.
                            diags.push(Diagnostic {
                                range: cmd.range.clone(),
                                severity: Some(DiagnosticSeverity::Information),
                                code: Some("lemma-verified".into()),
                                source: Some("isabelle-rs".into()),
                                message: format!("✅ Verified: {}", lem.name),
                                related_information: None,
                            });
                            ctx.in_proof = false;
                            ctx.proof_state = Some(ProofState {
                                goals: vec![],
                                background_goals: vec![],
                                has_unsolved: false,
                            });
                        },
                        None => {
                            // Verification failed — report as warning with proof state
                            diags.push(Diagnostic {
                                range: cmd.range.clone(),
                                severity: Some(DiagnosticSeverity::Warning),
                                code: Some("lemma-unverified".into()),
                                source: Some("isabelle-rs".into()),
                                message: format!(
                                    "⚠️ Unverified: {} (proof script may be incomplete or method \
                                     not supported)",
                                    lem.name
                                ),
                                related_information: None,
                            });
                            ctx.in_proof = true;
                            ctx.proof_state = Some(ProofState {
                                goals: vec![ProofGoal {
                                    hyps: vec![],
                                    conclusion: lem.name.clone(),
                                    id: Some(format!("goal-{}", cmd.id)),
                                }],
                                background_goals: vec![],
                                has_unsolved: true,
                            });
                        },
                    }
                } else {
                    // Couldn't parse
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
                // Definitions are always "accepted" (they're axiomatic in our kernel)
                diags.push(Diagnostic {
                    range: cmd.range.clone(),
                    severity: Some(DiagnosticSeverity::Information),
                    code: Some("definition-accepted".into()),
                    source: Some("isabelle-rs".into()),
                    message: format!("📝 {}", trimmed.chars().take(80).collect::<String>()),
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

pub struct Fleche {
    document: Arc<Mutex<Document>>,
    executor: Arc<dyn CommandExecutor>,
}

impl Fleche {
    pub fn new(executor: Arc<dyn CommandExecutor>) -> Self {
        Fleche { document: Arc::new(Mutex::new(Document::new())), executor }
    }

    pub fn open_file(&self, uri: &str, content: &str) -> Vec<Diagnostic> {
        let mut doc = self.document.lock().expect("Document lock poisoned");
        doc.open_file(uri.to_string(), content.to_string());
        drop(doc);
        self.check_file(uri)
    }

    pub fn update_file(&self, uri: &str, content: &str) -> Vec<Diagnostic> {
        let result = {
            let mut doc = self.document.lock().expect("Document lock poisoned");
            doc.update_file(uri, content.to_string())
        };
        if result.is_none() {
            return self.open_file(uri, content);
        }
        self.check_file(uri)
    }

    pub fn close_file(&self, uri: &str) {
        let mut doc = self.document.lock().expect("Document lock poisoned");
        doc.close_file(uri);
    }

    fn check_file(&self, uri: &str) -> Vec<Diagnostic> {
        let mut doc = self.document.lock().expect("Document lock poisoned");
        let node = match doc.get_node_mut(uri) {
            Some(n) => n,
            None => return Vec::new(),
        };

        let mut ctx = CheckContext::default();
        let mut all_diags = Vec::new();
        let commands = node.commands.clone();
        let start_idx = node.snapshots.len();

        for cmd in &commands[start_idx..] {
            let diags = self.executor.execute(cmd, &mut ctx);
            let mut snap = Snapshot::new(cmd.id, node.version);
            snap.diagnostics = diags.clone();
            snap.proof_state = ctx.proof_state.clone();
            snap.context_hash = ctx.context_hash;
            node.snapshots.push(snap);
            all_diags.extend(diags);
        }
        all_diags
    }

    pub fn get_proof_state(&self, uri: &str, _line: u32) -> Option<ProofState> {
        let doc = self.document.lock().expect("Document lock poisoned");
        let node = doc.get_node(uri)?;
        node.snapshots.iter().rev().find_map(|s| s.proof_state.clone())
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
    fn test_real_executor_lemma() {
        let exec = RealExecutor::new();
        // Lemma "A" can be verified (axiom acceptance), so in_proof should be false
        let cmd = Command::new(
            "lemma foo: \"A\"".into(),
            Range {
                start: Position { line: 0, character: 0 },
                end: Position { line: 0, character: 16 },
            },
            0,
        );
        let mut ctx = CheckContext::default();
        let _diags = exec.execute(&cmd, &mut ctx);
        // Verified lemma — not in proof mode
        assert!(!ctx.in_proof, "Verified lemma should exit proof mode");
    }

    #[test]
    fn test_fleche_with_real_executor() {
        let engine = Fleche::new(Arc::new(RealExecutor::new()));
        let diags = engine.open_file(
            "file:///test.thy",
            "theory Test\nlemma foo: \"A\"\nproof\napply rule\ndone",
        );
        for d in &diags {
            println!("  diag: {:?}", d.message);
        }
    }
}
