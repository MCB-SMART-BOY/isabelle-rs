//! Outer syntax — command parsing and classification for Isar.
//!
//! Corresponds to `src/Pure/Isar/outer_syntax.ML`.
//!
//! The outer syntax is the entry point for all Isar commands.
//! It classifies command tokens, dispatches them to the appropriate
//! handler, and manages the transition between theory and proof mode.
//!
//! ## Architecture
//!
//! ```text
//! text → tokenize → classify → parse → execute → state transition
//! ```
//!
//! ## State transitions
//!
//! | Current State | Command Kind | Next State |
//! |:--------------|:-------------|:-----------|
//! | Theory | `thy_goal` (lemma, theorem) | Proof |
//! | Theory | `thy_decl`, `thy_defn`, `thy_stmt` | Theory |
//! | Proof | `qed`, `qed_script`, `qed_block` | Theory |
//! | Proof | `prf_goal` (have, show) | Proof (subgoal) |
//! | Proof | `prf_asm` (fix, assume) | Proof |

use crate::isar::{
    keyword::Keywords,
    token::{Lexer, Token, TokenKind},
};

// =========================================================================
// Command Span
// =========================================================================

/// A parsed command: a sequence of tokens forming one command.
#[derive(Debug, Clone)]
pub struct CommandSpan {
    /// The command name.
    pub name: String,
    /// The kind of command (thy_goal, prf_script, etc.).
    pub kind: String,
    /// All tokens in this command (including the command name).
    pub tokens: Vec<Token>,
    /// The content after the command name.
    pub body: String,
}

impl CommandSpan {
    pub fn new(name: String, kind: String, tokens: Vec<Token>, body: String) -> Self {
        CommandSpan { name, kind, tokens, body }
    }

    /// Compute the line number (1-based) given the original source text.
    pub fn line_number(&self, source: &str) -> usize {
        let offset = self.tokens.first().map(|t| t.offset).unwrap_or(0);
        source[..offset.min(source.len())].lines().count()
    }
}

// =========================================================================
// Outer Syntax parser
// =========================================================================

/// The outer syntax parser takes a token stream and produces
/// classified command spans, managing the state transition.
#[derive(Clone)]
pub struct OuterSyntax {
    keywords: Keywords,
}

impl OuterSyntax {
    /// Create an outer syntax parser with the given keyword table.
    pub fn new(keywords: Keywords) -> Self {
        OuterSyntax { keywords }
    }

    /// Create an outer syntax parser with standard keywords.
    pub fn standard() -> Self {
        Self::new(Keywords::standard())
    }

    /// Get the keyword table.
    pub fn keywords(&self) -> &Keywords {
        &self.keywords
    }

    // ── Parsing ──

    /// Parse a source text into a sequence of command spans.
    pub fn parse_spans(&self, source: &str) -> Vec<CommandSpan> {
        let tokens = Lexer::new(source).tokenize();
        self.tokenize_to_spans(&tokens)
    }

    /// Convert a flat list of tokens into command spans.
    /// A command span starts with a command keyword and continues
    /// until the next command keyword or EOF.
    pub fn tokenize_to_spans(&self, tokens: &[Token]) -> Vec<CommandSpan> {
        let mut spans = Vec::new();
        let mut current_tokens: Vec<Token> = Vec::new();
        let mut current_name: Option<String> = None;

        for tok in tokens {
            match &tok.kind {
                TokenKind::Keyword(_) | TokenKind::Ident | TokenKind::LongIdent => {
                    let s = &tok.source;
                    if self.keywords.is_command(s) {
                        // Flush the previous command
                        if let Some(name) = current_name.take() {
                            let kind = self.keywords.command_kind(&name).unwrap_or("").to_string();
                            let body = current_tokens
                                .iter()
                                .skip(1) // skip the command name itself
                                .map(|t| t.source.as_str())
                                .collect::<Vec<_>>()
                                .join("");
                            spans.push(CommandSpan::new(
                                name,
                                kind,
                                std::mem::take(&mut current_tokens),
                                body,
                            ));
                        }
                        // Start a new command
                        current_name = Some(s.clone());
                    }
                    current_tokens.push(tok.clone());
                },
                TokenKind::Semicolon => {
                    // Semicolon ends the current command
                    if let Some(name) = current_name.take() {
                        let kind = self.keywords.command_kind(&name).unwrap_or("").to_string();
                        let body = current_tokens
                            .iter()
                            .skip(1)
                            .map(|t| t.source.as_str())
                            .collect::<Vec<_>>()
                            .join("");
                        spans.push(CommandSpan::new(
                            name,
                            kind,
                            std::mem::take(&mut current_tokens),
                            body,
                        ));
                    }
                },
                TokenKind::EOF => {
                    // Flush the last command
                    if let Some(name) = current_name.take() {
                        let kind = self.keywords.command_kind(&name).unwrap_or("").to_string();
                        let body = current_tokens
                            .iter()
                            .skip(1)
                            .map(|t| t.source.as_str())
                            .collect::<Vec<_>>()
                            .join("");
                        spans.push(CommandSpan::new(
                            name,
                            kind,
                            std::mem::take(&mut current_tokens),
                            body,
                        ));
                    }
                },
                _ => {
                    current_tokens.push(tok.clone());
                },
            }
        }

        spans
    }

    // ── Classification ──

    /// Classify a command: returns the category it belongs to.
    pub fn classify(&self, name: &str) -> CommandCategory {
        // Check most specific categories first
        if self.keywords.is_theory_begin(name) {
            CommandCategory::TheoryBegin
        } else if self.keywords.is_theory_end(name) {
            CommandCategory::TheoryEnd
        } else if self.keywords.is_theory_goal(name) {
            CommandCategory::TheoryGoal
        } else if self.keywords.is_qed(name) {
            CommandCategory::Qed
        } else if self.keywords.is_qed_global(name) {
            CommandCategory::QedGlobal
        } else if self.keywords.is_proof_goal(name) {
            CommandCategory::ProofGoal
        } else if self.keywords.is_proof_asm(name) {
            CommandCategory::ProofAsm
        } else if self.keywords.is_proof_script(name) {
            CommandCategory::ProofScript
        } else if self.keywords.is_kind(name, crate::isar::keyword::PRF_CHAIN) {
            CommandCategory::ProofChain
        } else if self.keywords.is_kind(name, crate::isar::keyword::NEXT_BLOCK) {
            CommandCategory::ProofChain
        } else if self.keywords.is_kind(name, crate::isar::keyword::PRF_DECL) {
            CommandCategory::ProofDecl
        } else if self.keywords.is_proof_open(name) {
            CommandCategory::ProofOpen
        } else if self.keywords.is_proof_close(name) {
            CommandCategory::ProofClose
        } else if self.keywords.is_theory_body(name) {
            CommandCategory::TheoryBody
        } else if self.keywords.is_vacuous(name) {
            CommandCategory::Vacuous
        } else {
            CommandCategory::Unknown
        }
    }

    // ── State machine ──

    /// Check if a command can legally appear in the given mode.
    pub fn is_legal_in_mode(&self, name: &str, mode: &IsarMode) -> bool {
        match mode {
            IsarMode::Theory => {
                self.keywords.is_theory(name)
                    && !self.keywords.is_qed(name)
                    && !self.keywords.is_qed_global(name)
            },
            IsarMode::Proof => {
                self.keywords.is_proof(name)
                    || self.keywords.is_qed(name)
                    || self.keywords.is_qed_global(name)
            },
            IsarMode::SkipProof => self.keywords.is_proof(name) || self.keywords.is_qed(name),
            IsarMode::Closed => false,
        }
    }

    /// Transition: given a command and current mode, return the new mode.
    pub fn transition(&self, name: &str, current_mode: &IsarMode) -> IsarMode {
        match current_mode {
            IsarMode::Theory => {
                if self.keywords.is_theory_goal(name) {
                    IsarMode::Proof
                } else if self.keywords.is_theory_end(name) {
                    IsarMode::Closed
                } else {
                    IsarMode::Theory
                }
            },
            IsarMode::Proof => {
                if self.keywords.is_qed(name) || self.keywords.is_qed_global(name) {
                    IsarMode::Theory
                } else {
                    IsarMode::Proof
                }
            },
            IsarMode::SkipProof => {
                if self.keywords.is_qed(name) || self.keywords.is_qed_global(name) {
                    IsarMode::Theory
                } else {
                    IsarMode::SkipProof
                }
            },
            IsarMode::Closed => IsarMode::Closed,
        }
    }
}

// =========================================================================
// Command category
// =========================================================================

/// Classification of a command by its role in the state machine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommandCategory {
    /// `theory`, `begin` — start a new theory
    TheoryBegin,
    /// `end` — finish the current theory
    TheoryEnd,
    /// `lemma`, `theorem`, `corollary` — enter proof mode
    TheoryGoal,
    /// `definition`, `fun`, `datatype`, `lemmas`, etc.
    TheoryBody,
    /// `proof`, `{` — open a proof block
    ProofOpen,
    /// `qed`, `}` — close a proof block
    ProofClose,
    /// `done`, `by`, `sorry` — finish a proof
    Qed,
    /// `done`, `by` at global level
    QedGlobal,
    /// `have`, `show`, `hence`, `thus` — intermediate goal
    ProofGoal,
    /// `fix`, `assume`, `presume`, `def` — context elements
    ProofAsm,
    /// `apply`, `apply_end`, `defer`, `prefer` — tactic scripts
    ProofScript,
    /// `also`, `finally`, `then`, `from`, `with` — chaining
    ProofChain,
    /// `let`, `note`, `using`, `unfolding` — declarations
    ProofDecl,
    /// `section`, `text`, `print_*` — document/diagnostic
    Vacuous,
    /// Unrecognized command
    Unknown,
}

// =========================================================================
// Isar mode
// =========================================================================

/// The mode of the Isar state machine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IsarMode {
    /// Processing theory-level commands.
    Theory,
    /// Inside a proof.
    Proof,
    /// Inside a proof that will be skipped (e.g., after `sorry` within a block).
    SkipProof,
    /// Theory is closed (after `end`).
    Closed,
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_spans_simple() {
        let syn = OuterSyntax::standard();
        let source = "theory Foo\nbegin\nlemma test: \"A\"\nproof\napply rule\ndone\nend";
        let spans = syn.parse_spans(source);

        let names: Vec<&str> = spans.iter().map(|s| s.name.as_str()).collect();
        assert_eq!(names, vec!["theory", "begin", "lemma", "proof", "apply", "done", "end"]);
    }

    #[test]
    fn test_classify() {
        let syn = OuterSyntax::standard();

        assert_eq!(syn.classify("theory"), CommandCategory::TheoryBegin);
        assert_eq!(syn.classify("lemma"), CommandCategory::TheoryGoal);
        assert_eq!(syn.classify("definition"), CommandCategory::TheoryBody);
        assert_eq!(syn.classify("have"), CommandCategory::ProofGoal);
        assert_eq!(syn.classify("show"), CommandCategory::ProofGoal);
        assert_eq!(syn.classify("fix"), CommandCategory::ProofAsm);
        assert_eq!(syn.classify("apply"), CommandCategory::ProofScript);
        assert_eq!(syn.classify("done"), CommandCategory::Qed);
        assert_eq!(syn.classify("by"), CommandCategory::Qed);
        assert_eq!(syn.classify("section"), CommandCategory::Vacuous);
        assert_eq!(syn.classify("xyz"), CommandCategory::Unknown);
    }

    #[test]
    fn test_transition() {
        let syn = OuterSyntax::standard();

        // Theory → lemma → Proof
        assert_eq!(syn.transition("lemma", &IsarMode::Theory), IsarMode::Proof);

        // Theory → definition → Theory
        assert_eq!(syn.transition("definition", &IsarMode::Theory), IsarMode::Theory);

        // Proof → done → Theory
        assert_eq!(syn.transition("done", &IsarMode::Proof), IsarMode::Theory);

        // Theory → end → Closed
        assert_eq!(syn.transition("end", &IsarMode::Theory), IsarMode::Closed);
    }

    #[test]
    fn test_is_legal_in_mode() {
        let syn = OuterSyntax::standard();

        // In theory mode, lemma is legal
        assert!(syn.is_legal_in_mode("lemma", &IsarMode::Theory));
        // In theory mode, definition is legal
        assert!(syn.is_legal_in_mode("definition", &IsarMode::Theory));
        // In theory mode, done is NOT legal
        assert!(!syn.is_legal_in_mode("done", &IsarMode::Theory));

        // In proof mode, have is legal
        assert!(syn.is_legal_in_mode("have", &IsarMode::Proof));
        // In proof mode, definition is NOT legal
        assert!(!syn.is_legal_in_mode("definition", &IsarMode::Proof));
    }

    #[test]
    fn test_parse_multiple_commands() {
        let syn = OuterSyntax::standard();
        let source = "lemma foo: \"A\" proof auto qed lemma bar: \"B\" by simp";
        let spans = syn.parse_spans(source);

        let names: Vec<&str> = spans.iter().map(|s| s.name.as_str()).collect();
        // "auto" is a method argument to "proof", not a separate command
        assert_eq!(names, vec!["lemma", "proof", "qed", "lemma", "by"]);
    }
}
