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

use std::{
    collections::HashMap,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

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
        Command { source, kind, range, id }
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
    pub proof_state: Option<Arc<ProofState>>,
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
    /// Monotonic generation within this open lifetime.
    pub(crate) generation: u64,
    /// Unique identity retained by outstanding checks across close/reopen.
    pub(crate) lifetime: Arc<()>,
    /// Per-revision cancellation shared with a checking job.
    pub(crate) is_cancelled: Arc<AtomicBool>,
    /// The full text content.
    pub content: String,
    /// The parsed commands (toplevel structure).
    pub commands: Arc<Vec<Command>>,
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
            generation: 0,
            lifetime: Arc::new(()),
            is_cancelled: Arc::new(AtomicBool::new(false)),
            content: String::new(),
            commands: Arc::new(Vec::new()),
            snapshots: Vec::new(),
            processing: false,
            pending_diagnostics: Vec::new(),
        }
    }

    /// Update the content and increment the version.
    /// Returns the set of commands that changed.
    pub fn update_content(&mut self, new_content: String, new_version: i32) -> UpdateResult {
        let commands = Arc::new(Self::parse_commands(&new_content));
        self.update_parsed_content(new_content, commands, new_version)
    }

    /// Install commands tokenized before acquiring the document lock.
    pub(crate) fn update_parsed_content(
        &mut self,
        new_content: String,
        new_commands: Arc<Vec<Command>>,
        new_version: i32,
    ) -> UpdateResult {
        // Exhausting this counter requires more than u64 edits of a single open file.
        if self.generation != 0 {
            self.revoke_checks();
            self.is_cancelled = Arc::new(AtomicBool::new(false));
        }
        self.generation = self.generation.checked_add(1).expect("Document generation exhausted");
        self.version = new_version;
        let _old_content = std::mem::replace(&mut self.content, new_content);
        let old_commands = std::mem::take(&mut self.commands);
        let old_snapshots = std::mem::take(&mut self.snapshots);

        // Preserve only the exact unchanged prefix. Zero matching commands must not
        // retain command zero's old proof state or diagnostics.
        let fork_point = Self::find_fork_point(&old_commands, &new_commands);
        let retained_count = fork_point.map_or(0, |index| index + 1);
        let new_snapshots = old_snapshots.into_iter().take(retained_count).collect();

        self.commands = new_commands;
        self.snapshots = new_snapshots;
        self.pending_diagnostics.clear();

        UpdateResult {
            fork_point: fork_point.unwrap_or(0),
            total_commands: self.commands.len(),
            snapshots_kept: self.snapshots.len(),
        }
    }

    pub(crate) fn revoke_checks(&self) {
        self.is_cancelled.store(true, Ordering::Release);
    }

    /// Parse the document into commands using the Isabelle tokenizer.
    /// Commands are separated by semicolons or toplevel keyword boundaries.
    pub(crate) fn parse_commands(content: &str) -> Vec<Command> {
        Self::parse_commands_impl(content, usize::MAX).0
    }

    pub(crate) fn parse_commands_bounded(content: &str, max: usize) -> Option<Vec<Command>> {
        let (commands, is_over_limit) = Self::parse_commands_impl(content, max);
        (!is_over_limit).then_some(commands)
    }

    fn parse_commands_impl(content: &str, max: usize) -> (Vec<Command>, bool) {
        use crate::isar::{
            keyword::Keywords,
            token::{Lexer, TokenKind},
        };

        let mut lexer = Lexer::new(content);
        let keywords = Keywords::standard();
        let line_starts: Vec<_> = std::iter::once(0)
            .chain(
                content
                    .bytes()
                    .enumerate()
                    .filter_map(|(index, byte)| (byte == b'\n').then_some(index + 1)),
            )
            .collect();
        let mut commands = Vec::new();
        let mut current = String::new();
        let mut start_offset = 0;

        loop {
            let tok = lexer.next_token();
            let done = tok.kind == TokenKind::EOF;
            if commands.len() >= max && (!current.trim().is_empty() || !done) {
                return (Vec::new(), true);
            }
            match &tok.kind {
                TokenKind::EOF if !current.trim().is_empty() => {
                    Self::append_command(
                        &mut commands,
                        &current,
                        start_offset,
                        tok.offset,
                        &line_starts,
                    );
                },
                TokenKind::Semicolon if !current.trim().is_empty() => {
                    Self::append_command(
                        &mut commands,
                        &current,
                        start_offset,
                        tok.offset + 1,
                        &line_starts,
                    );
                    current.clear();
                    start_offset = tok.offset + 1;
                },
                TokenKind::Keyword(_) | TokenKind::Ident | TokenKind::LongIdent
                    if keywords.is_command(&tok.source) && !current.trim().is_empty() =>
                {
                    Self::append_command(
                        &mut commands,
                        &current,
                        start_offset,
                        tok.offset,
                        &line_starts,
                    );
                    current.clear();
                    start_offset = tok.offset;
                    current.push_str(&tok.source);
                    current.push(' ');
                },
                TokenKind::EOF => {},
                _ => {
                    if current.is_empty() {
                        start_offset = tok.offset;
                    }
                    current.push_str(&tok.source);
                    current.push(' ');
                },
            }
            if done {
                break;
            }
        }

        (commands, false)
    }

    fn append_command(
        commands: &mut Vec<Command>,
        source: &str,
        start_offset: usize,
        end_offset: usize,
        line_starts: &[usize],
    ) {
        let range = Range {
            start: Position { line: offset_to_line(line_starts, start_offset), character: 0 },
            end: Position { line: offset_to_line(line_starts, end_offset), character: 0 },
        };
        commands.push(Command::new(source.trim().to_owned(), range, commands.len()));
    }

    /// Find the last command that is unchanged between old and new, if any.
    fn find_fork_point(old: &[Command], new: &[Command]) -> Option<usize> {
        old.iter()
            .zip(new)
            .take_while(|(before, after)| {
                before.source == after.source && before.range == after.range
            })
            .count()
            .checked_sub(1)
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
        Document { nodes: HashMap::new(), global_version: 0 }
    }

    /// Open a new file.
    pub fn open_file(&mut self, uri: DocumentUri, content: String) -> &Node {
        let commands = Arc::new(Node::parse_commands(&content));
        self.open_parsed_file(uri, content, commands)
    }

    /// Install an already tokenized file under the workspace lock.
    pub(crate) fn open_parsed_file(
        &mut self,
        uri: DocumentUri,
        content: String,
        commands: Arc<Vec<Command>>,
    ) -> &Node {
        self.global_version += 1;
        let mut node = Node::new(uri.clone());
        node.update_parsed_content(content, commands, self.global_version);
        if let Some(previous) = self.nodes.insert(uri.clone(), node) {
            previous.revoke_checks();
        }
        self.nodes.get(&uri).expect("just inserted")
    }

    /// Update a file's content.
    pub fn update_file(&mut self, uri: &str, content: String) -> Option<UpdateResult> {
        let commands = Arc::new(Node::parse_commands(&content));
        self.update_parsed_file(uri, content, commands)
    }

    /// Apply an already tokenized edit under the workspace lock.
    pub(crate) fn update_parsed_file(
        &mut self,
        uri: &str,
        content: String,
        commands: Arc<Vec<Command>>,
    ) -> Option<UpdateResult> {
        self.global_version += 1;
        if let Some(node) = self.nodes.get_mut(uri) {
            Some(node.update_parsed_content(content, commands, self.global_version))
        } else {
            None
        }
    }

    /// Close a file.
    pub fn close_file(&mut self, uri: &str) {
        if let Some(node) = self.nodes.remove(uri) {
            node.revoke_checks();
        }
    }

    /// Get a node by URI.
    pub fn get_node(&self, uri: &str) -> Option<&Node> {
        self.nodes.get(uri)
    }

    /// Get a mutable node by URI.
    pub fn get_node_mut(&mut self, uri: &str) -> Option<&mut Node> {
        self.nodes.get_mut(uri)
    }

    /// Get the full text of a document by URI.
    pub fn get_text(&self, uri: &str) -> Option<String> {
        self.get_node(uri).map(|n| n.content.clone())
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
            diags.extend(node.pending_diagnostics.iter().cloned());
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

fn offset_to_line(line_starts: &[usize], offset: usize) -> u32 {
    line_starts.partition_point(|start| *start <= offset).saturating_sub(1) as u32
}

#[allow(dead_code)]
fn line_start_offset(content: &str, offset: usize) -> u32 {
    let slice = &content[..offset.min(content.len())];
    if let Some(pos) = slice.rfind('\n') { (pos + 1) as u32 } else { 0 }
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
        assert_eq!(
            CommandKind::classify("theory Foo imports Bar begin"),
            CommandKind::TheoryHeader
        );
    }

    #[test]
    fn test_document_open_update() {
        let mut doc = Document::new();
        let uri = "file:///test.thy".to_string();

        doc.open_file(uri.clone(), "lemma A: True\n  by auto".into());
        let node = doc.get_node(&uri).expect("node should exist after open_file");
        assert!(!node.commands.is_empty());
        assert!(node.version > 0);

        // Update: same content, should keep snapshots
        let result = doc
            .update_file(&uri, "lemma A: True\n  by auto".into())
            .expect("update_file should succeed");
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
        assert_eq!(Node::find_fork_point(&old, &new), Some(1));
    }

    #[test]
    fn node_first_command_changed_drops_old_snapshot() {
        let mut node = Node::new("file:///first.thy".into());
        node.update_content("lemma A: True".into(), 1);
        node.snapshots.push(Snapshot::new(0, 1));

        let result = node.update_content("lemma B: True".into(), 2);

        assert_eq!(result.snapshots_kept, 0);
        assert!(node.snapshots.is_empty());
    }

    fn dummy_range(id: u32) -> Range {
        Range {
            start: Position { line: id, character: 0 },
            end: Position { line: id, character: 10 },
        }
    }

    #[test]
    fn document_splits_registered_outer_commands() {
        let commands = Node::parse_commands(
            "theory Test\nimports HOL\nbegin\nlemma foo: \"A\"\nproof\napply rule\ndone\nend",
        );

        assert!(commands.iter().any(|command| command.kind == CommandKind::Lemma));
        assert!(commands.iter().any(|command| command.kind == CommandKind::Proof));
        assert!(commands.iter().any(|command| command.kind == CommandKind::Apply));
        assert!(commands.iter().any(|command| command.kind == CommandKind::By));
    }
    #[test]
    fn document_multiline_commands_preserve_line_ranges() {
        let commands =
            Node::parse_commands("theory Test\nbegin\nlemma foo: \"β\";\nlemma bar: \"γ\"\nend");
        let lemmas: Vec<_> =
            commands.iter().filter(|command| command.kind == CommandKind::Lemma).collect();
        assert_eq!(lemmas.len(), 2);
        assert_eq!((lemmas[0].range.start.line, lemmas[0].range.end.line), (2, 2));
        assert_eq!(lemmas[1].range.start.line, 3);
        assert_eq!(commands.last().unwrap().range.end.line, 4);
    }
    #[test]
    fn document_bounded_parse_accepts_exact_limit_and_rejects_next_command() {
        let source = "theory A; theory B;";
        assert_eq!(Node::parse_commands_bounded(source, 2).unwrap().len(), 2);
        assert!(Node::parse_commands_bounded(source, 1).is_none());
        assert_eq!(Node::parse_commands_bounded("", 0).unwrap().len(), 0);
    }
}
