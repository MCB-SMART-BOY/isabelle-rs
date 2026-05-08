//! Document model — the heart of incremental proof checking.
//!
//! ## Architecture
//!
//! Inspired by:
//! - **Isabelle PIDE**: `Document.Node`, `Command`, snapshots
//! - **Lean 4**: `Snapshot` tree, `InfoTree`, per-command processing
//! - **Coq-lsp/Flèche**: versioned document states, cache-aware rechecking
//!
//! ## Key concepts
//!
//! 1. **Document**: A mutable workspace containing open files
//! 2. **Node**: One theory file (`.thy`), consisting of a list of commands
//! 3. **Command**: A single toplevel command (lemma, definition, proof block, etc.)
//! 4. **Snapshot**: An immutable checkpoint of a command's execution state
//! 5. **Version**: Documents are versioned — each edit creates a new version
//!
//! ## Incremental checking strategy
//!
//! When a document changes:
//! 1. Compute the diff: which commands changed?
//! 2. Find the last unchanged command (the "fork point")
//! 3. Re-execute from the fork point onward
//! 4. Preserve old snapshots for unchanged prefixes
//!
//! This is exactly what Lean 4's `Snapshot` tree and Flèche's cache do.

use std::collections::HashMap;

use super::super::core::{Thm, Typ, Term};
use super::super::server::lsp_types::*;

// =========================================================================
// Commands
// =========================================================================

/// The kind of a toplevel Isabelle command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommandKind {
    /// `theory Foo imports Bar begin`
    TheoryHeader,
    /// `definition x where ...`
    Definition,
    /// `lemma name: "statement"`
    Lemma,
    /// `theorem name: "statement"`
    Theorem,
    /// `proof ... qed` (a proof block)
    Proof,
    /// `by method` (a terminal proof)
    By,
    /// `apply method` (a tactic application)
    Apply,
    /// `fun f where ...` (function definition)
    Function,
    /// `inductive pred where ...`
    Inductive,
    /// `datatype t = ...`
    Datatype,
    /// `class c = ...`
    Class,
    /// `instance ...`
    Instance,
    /// `locale loc = ...`
    Locale,
    /// `interpretation ...`
    Interpretation,
    /// Other/unknown command
    Other(String),
}

impl CommandKind {
    /// Classify a command from its raw text.
    pub fn classify(text: &str) -> Self {
        let trimmed = text.trim();
        if trimmed.is_empty() {
            return CommandKind::Other("empty".into());
        }
        let first_word = trimmed.split_whitespace().next().unwrap_or("");
        match first_word {
            "theory" => CommandKind::TheoryHeader,
            "definition" | "abbreviation" | "notation" => CommandKind::Definition,
            "lemma" | "proposition" | "corollary" => CommandKind::Lemma,
            "theorem" => CommandKind::Theorem,
            "proof" => CommandKind::Proof,
            "by" | "done" | "." | "qed" => CommandKind::By,
            "apply" => CommandKind::Apply,
            "fun" | "function" | "primrec" => CommandKind::Function,
            "inductive" | "coinductive" | "inductive_set" => CommandKind::Inductive,
            "datatype" | "record" | "type_synonym" => CommandKind::Datatype,
            "class" | "subclass" => CommandKind::Class,
            "instance" | "instantiation" => CommandKind::Instance,
            "locale" | "sublocale" => CommandKind::Locale,
            "interpretation" | "interpret" => CommandKind::Interpretation,
            _ => CommandKind::Other(first_word.to_string()),
        }
    }

    /// Is this command a proof block opener?
    pub fn opens_proof(&self) -> bool {
        matches!(self, CommandKind::Lemma | CommandKind::Theorem)
    }

    /// Is this command a proof block closer?
    pub fn closes_proof(&self) -> bool {
        matches!(self, CommandKind::By)
    }
}

/// A single command in a theory file.
///
/// Corresponds to `Command` in Isabelle PIDE and `Syntax.Command` in Lean 4.
#[derive(Debug, Clone)]
pub struct Command {
    /// The raw source text of this command.
    pub source: String,
    /// The kind of command.
    pub kind: CommandKind,
    /// Byte range of this command in the document.
    pub range: Range,
    /// Unique command ID (within a node).
    pub id: usize,
}

impl Command {
    pub fn new(source: String, range: Range, id: usize) -> Self {
        let kind = CommandKind::classify(&source);
        Command {
            source,
            kind,
            range,
            id,
        }
    }
}

// =========================================================================
// Snapshot — immutable checkpoint
// =========================================================================

/// A snapshot captures the proof state after executing a command.
///
/// This is the key data structure for incremental checking:
/// - Unchanged commands keep their snapshots
/// - Changed commands produce new snapshots
/// - The snapshot tree forms a chain (like Lean 4's snapshot chain)
#[derive(Debug, Clone)]
pub struct Snapshot {
    /// The command that produced this snapshot.
    pub command_id: usize,
    /// The document version this snapshot belongs to.
    pub version: i32,
    /// Diagnostic messages produced by this command.
    pub diagnostics: Vec<Diagnostic>,
    /// The proof state after this command (if in a proof).
    pub proof_state: Option<ProofState>,
    /// The theory context after this command.
    /// In a real implementation, this would be a `Theory` or `Context` handle.
    pub context_hash: u64,
    /// Is this snapshot "stale" (needs recomputation)?
    pub stale: bool,
}

impl Snapshot {
    /// Create a new snapshot for a successfully executed command.
    pub fn new(command_id: usize, version: i32) -> Self {
        Snapshot {
            command_id,
            version,
            diagnostics: Vec::new(),
            proof_state: None,
            context_hash: 0,
            stale: false,
        }
    }

    /// Mark this snapshot as stale (needs recomputation).
    pub fn mark_stale(&mut self) {
        self.stale = true;
    }
}

// =========================================================================
// Node — a single theory file
// =========================================================================

/// A document node represents one theory file being edited.
///
/// Inspired by `Document.Node` in Isabelle PIDE.
#[derive(Debug, Clone)]
pub struct Node {
    /// The URI of this file.
    pub uri: DocumentUri,
    /// The current version of this document.
    pub version: i32,
    /// The full text content.
    pub content: String,
    /// The parsed commands (toplevel structure).
    pub commands: Vec<Command>,
    /// Snapshots for each command (may be fewer than commands if incomplete).
    pub snapshots: Vec<Snapshot>,
    /// Is the document currently being processed?
    pub processing: bool,
    /// Pending diagnostics to publish.
    pub pending_diagnostics: Vec<Diagnostic>,
}

impl Node {
    /// Create a new empty node.
    pub fn new(uri: DocumentUri) -> Self {
        Node {
            uri,
            version: 0,
            content: String::new(),
            commands: Vec::new(),
            snapshots: Vec::new(),
            processing: false,
            pending_diagnostics: Vec::new(),
        }
    }

    /// Update the content and increment the version.
    /// Returns the set of commands that changed.
    pub fn update_content(&mut self, new_content: String, new_version: i32) -> UpdateResult {
        self.version = new_version;
        let old_content = std::mem::replace(&mut self.content, new_content);
        let old_commands = std::mem::take(&mut self.commands);
        let mut old_snapshots = std::mem::take(&mut self.snapshots);

        // Re-parse commands (simplified: split by `;` or `\n\n` for now)
        let new_commands = Self::parse_commands(&self.content);

        // Find the fork point: last command that is unchanged
        let fork_point = Self::find_fork_point(&old_commands, &new_commands);

        // Keep snapshots up to and including the fork point
        let mut new_snapshots: Vec<Snapshot> = Vec::new();
        for snap in &mut old_snapshots {
            if snap.command_id <= fork_point {
                new_snapshots.push(snap.clone());
            } else {
                break;
            }
        }

        self.commands = new_commands;
        self.snapshots = new_snapshots;

        UpdateResult {
            fork_point,
            total_commands: self.commands.len(),
            snapshots_kept: self.snapshots.len(),
        }
    }

    /// Parse the document into commands using the Isabelle tokenizer.
    /// Commands are separated by semicolons or toplevel keyword boundaries.
    fn parse_commands(content: &str) -> Vec<Command> {
        use crate::isar::token::{Lexer, TokenKind};

        let tokens = Lexer::new(content).tokenize();
        let mut commands = Vec::new();
        let mut current = String::new();
        let mut start_offset = 0;
        let mut id = 0;

        for tok in &tokens {
            match &tok.kind {
                TokenKind::EOF => {
                    if !current.trim().is_empty() {
                        let range = Range {
                            start: Position { line: offset_to_line(content, start_offset), character: 0 },
                            end: Position { line: offset_to_line(content, tok.offset), character: 0 },
                        };
                        commands.push(Command::new(current.trim().to_string(), range, id));
                        id += 1;
                    }
                }
                TokenKind::Semicolon => {
                    // Semicolon ends a command
                    if !current.trim().is_empty() {
                        let range = Range {
                            start: Position { line: offset_to_line(content, start_offset), character: 0 },
                            end: Position { line: offset_to_line(content, tok.offset + 1), character: 0 },
                        };
                        commands.push(Command::new(current.trim().to_string(), range, id));
                        id += 1;
                        current = String::new();
                        start_offset = tok.offset + 1;
                    }
                }
                TokenKind::Keyword(kw) if kw.as_ref() == "theory" && !current.is_empty() => {
                    // New theory command starts — flush previous
                    let range = Range {
                        start: Position { line: offset_to_line(content, start_offset), character: 0 },
                        end: Position { line: offset_to_line(content, tok.offset), character: 0 },
                    };
                    if !current.trim().is_empty() {
                        commands.push(Command::new(current.trim().to_string(), range, id));
                        id += 1;
                    }
                    current = String::new();
                    start_offset = tok.offset;
                    current.push_str(&tok.source);
                    current.push(' ');
                }
                _ => {
                    if current.is_empty() {
                        start_offset = tok.offset;
                    }
                    current.push_str(&tok.source);
                    current.push(' ');
                }
            }
        }

        commands
    }

    /// Find the last command that is unchanged between old and new.
    fn find_fork_point(old: &[Command], new: &[Command]) -> usize {
        let mut i = 0;
        while i < old.len() && i < new.len() && old[i].source == new[i].source {
            i += 1;
        }
        if i > 0 {
            i - 1 // fork point is the *last unchanged* command
        } else {
            0 // everything changed (or first command)
        }
    }
}

/// Result of updating a node's content.
#[derive(Debug)]
pub struct UpdateResult {
    /// The last unchanged command index.
    pub fork_point: usize,
    /// Total number of commands after update.
    pub total_commands: usize,
    /// How many snapshots were kept.
    pub snapshots_kept: usize,
}

// =========================================================================
// Document — the workspace
// =========================================================================

/// The document workspace manages all open theory files.
///
/// This is similar to Lean 4's `Watchdog` process and
/// Isabelle PIDE's `Document` model.
#[derive(Debug)]
pub struct Document {
    /// Open files, keyed by URI.
    nodes: HashMap<DocumentUri, Node>,
    /// Global version counter.
    global_version: i32,
}

impl Document {
    /// Create an empty document workspace.
    pub fn new() -> Self {
        Document {
            nodes: HashMap::new(),
            global_version: 0,
        }
    }

    /// Open a new file.
    pub fn open_file(&mut self, uri: DocumentUri, content: String) -> &Node {
        self.global_version += 1;
        let mut node = Node::new(uri.clone());
        node.update_content(content, self.global_version);
        self.nodes.insert(uri.clone(), node);
        self.nodes.get(&uri).unwrap()
    }

    /// Update a file's content.
    pub fn update_file(&mut self, uri: &str, content: String) -> Option<UpdateResult> {
        self.global_version += 1;
        if let Some(node) = self.nodes.get_mut(uri) {
            Some(node.update_content(content, self.global_version))
        } else {
            None
        }
    }

    /// Close a file.
    pub fn close_file(&mut self, uri: &str) {
        self.nodes.remove(uri);
    }

    /// Get a node by URI.
    pub fn get_node(&self, uri: &str) -> Option<&Node> {
        self.nodes.get(uri)
    }

    /// Get a mutable node by URI.
    pub fn get_node_mut(&mut self, uri: &str) -> Option<&mut Node> {
        self.nodes.get_mut(uri)
    }

    /// Get all open files.
    pub fn nodes(&self) -> impl Iterator<Item = &Node> {
        self.nodes.values()
    }

    /// Get the current global version.
    pub fn version(&self) -> i32 {
        self.global_version
    }

    /// Get the diagnostics for a file.
    pub fn diagnostics(&self, uri: &str) -> Vec<Diagnostic> {
        let mut diags = Vec::new();
        if let Some(node) = self.nodes.get(uri) {
            for snap in &node.snapshots {
                diags.extend(snap.diagnostics.clone());
            }
        }
        diags
    }
}

impl Default for Document {
    fn default() -> Self {
        Self::new()
    }
}

// =========================================================================
// Helpers
// =========================================================================

fn offset_to_line(content: &str, offset: usize) -> u32 {
    let slice = &content[..offset.min(content.len())];
    slice.chars().filter(|c| *c == '\n').count() as u32
}

fn line_start_offset(content: &str, offset: usize) -> u32 {
    let slice = &content[..offset.min(content.len())];
    if let Some(pos) = slice.rfind('\n') {
        (pos + 1) as u32
    } else {
        0
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_command_classify() {
        assert_eq!(CommandKind::classify("lemma foo: \"x = x\""), CommandKind::Lemma);
        assert_eq!(CommandKind::classify("theorem bar: \"P\""), CommandKind::Theorem);
        assert_eq!(CommandKind::classify("proof"), CommandKind::Proof);
        assert_eq!(CommandKind::classify("by auto"), CommandKind::By);
        assert_eq!(CommandKind::classify("apply simp"), CommandKind::Apply);
        assert_eq!(CommandKind::classify("definition x where \"x = 0\""), CommandKind::Definition);
        assert_eq!(CommandKind::classify("fun f :: \"nat => nat\""), CommandKind::Function);
        assert_eq!(CommandKind::classify("theory Foo imports Bar begin"), CommandKind::TheoryHeader);
    }

    #[test]
    fn test_document_open_update() {
        let mut doc = Document::new();
        let uri = "file:///test.thy".to_string();

        doc.open_file(uri.clone(), "lemma A: True\n  by auto".into());
        let node = doc.get_node(&uri).unwrap();
        assert!(node.commands.len() >= 1);
        assert!(node.version > 0);

        // Update: same content, should keep snapshots
        let result = doc.update_file(&uri, "lemma A: True\n  by auto".into()).unwrap();
        assert!(result.fork_point <= 1);
    }

    #[test]
    fn test_fork_point() {
        let old = vec![
            Command::new("lemma A".into(), dummy_range(0), 0),
            Command::new("proof".into(), dummy_range(1), 1),
            Command::new("qed".into(), dummy_range(2), 2),
        ];
        let new = vec![
            Command::new("lemma A".into(), dummy_range(0), 0),
            Command::new("proof".into(), dummy_range(1), 1),
            Command::new("by auto".into(), dummy_range(2), 2), // changed
        ];
        assert_eq!(Node::find_fork_point(&old, &new), 1);
    }

    fn dummy_range(id: u32) -> Range {
        Range {
            start: Position { line: id, character: 0 },
            end: Position { line: id, character: 10 },
        }
    }
}
