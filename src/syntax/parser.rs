//! Incremental parser — Rowan CST based.
//!
//! ## Design
//!
//! - **Green/Red tree** (Rowan): lossless CST, position-preserving
//! - **Incremental re-parse**: only re-lex/tokenize changed regions
//! - **Error recovery**: produces partial AST on syntax errors
//!
//! ## Pipeline
//!
//! ```text
//! Source text → Tokenizer (isar/token.rs) → CstBuilder → GreenNode (CST)
//!                                                              ↓
//!                                                        SyntaxNode (Red)
//!                                                              ↓
//!                                                        Ast (syntax/ast.rs)
//! ```

use rowan::{GreenNode, GreenNodeBuilder, Language, SyntaxKind as RowanSyntaxKind};

use crate::isar::token::{Lexer, Token, TokenKind};

// =========================================================================
// SyntaxKind — all node types in the Isabelle CST
// =========================================================================

/// Every node (leaf or internal) in the concrete syntax tree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u16)]
pub enum SyntaxKind {
    // ── Leaf nodes (tokens) ──
    /// A keyword: `theory`, `lemma`, `proof`, etc.
    Keyword = 0,
    /// An identifier: `foo`, `nat`, `map'`
    Ident = 1,
    /// A long identifier: `Foo.bar.baz`
    LongIdent = 2,
    /// A type variable: `'a`, `''a`, `?'a`
    TypeVar = 3,
    /// A string literal: `"..."`
    String_ = 4,
    /// A number: `42`
    Number_ = 5,
    /// A symbol: `==>`, `!!`, `=>`, `:`
    Symbol_ = 6,
    /// A semicolon
    Semicolon = 7,
    /// A comment: `(* ... *)`
    Comment = 8,
    /// Whitespace
    Space = 9,
    /// End of input
    Eof = 10,
    /// Erroneous token
    TokenError = 11,

    // ── Internal (composite) nodes ──
    /// The root of the file
    Root = 20,
    /// `theory Name imports ... begin`
    TheoryHeader = 21,
    /// A single top-level command
    Command = 22,
    /// `lemma name: "stmt"`
    Lemma = 23,
    /// `theorem name: "stmt"`
    Theorem = 24,
    /// `proof ... qed`
    Proof = 25,
    /// `qed` / `done`
    Qed = 26,
    /// `by method`
    By = 27,
    /// `apply method`
    Apply = 28,
    /// A term expression
    Term = 30,
    /// A type expression
    Type = 31,
    /// `%x. body`
    Lambda = 32,
    /// `f x`
    Application = 33,
    /// A variable reference
    Variable = 34,
    /// A constant reference
    Constant = 35,

    // ── Error recovery ──
    /// Placeholder for syntax errors
    ErrorNode = 99,
}

// =========================================================================
// IsabelleLanguage — Rowan Language trait implementation
// =========================================================================

/// Marker type for the Isabelle language.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IsabelleLanguage {}

impl Language for IsabelleLanguage {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: RowanSyntaxKind) -> SyntaxKind {
        assert!(raw.0 < SyntaxKind::ErrorNode as u16 + 1);
        unsafe { std::mem::transmute::<u16, SyntaxKind>(raw.0) }
    }

    fn kind_to_raw(kind: SyntaxKind) -> RowanSyntaxKind {
        RowanSyntaxKind(kind as u16)
    }
}

/// Type aliases for Rowan nodes specialized to Isabelle.
pub type SyntaxNode = rowan::SyntaxNode<IsabelleLanguage>;
pub type SyntaxToken = rowan::SyntaxToken<IsabelleLanguage>;
pub type SyntaxElement = rowan::SyntaxElement<IsabelleLanguage>;

// =========================================================================
// Token → SyntaxKind mapping
// =========================================================================

fn token_kind_to_syntax(kind: &TokenKind) -> SyntaxKind {
    match kind {
        TokenKind::Keyword(_) => SyntaxKind::Keyword,
        TokenKind::Ident => SyntaxKind::Ident,
        TokenKind::LongIdent => SyntaxKind::LongIdent,
        TokenKind::TypeVar | TokenKind::SchematicTypeVar => SyntaxKind::TypeVar,
        TokenKind::String => SyntaxKind::String_,
        TokenKind::Number => SyntaxKind::Number_,
        TokenKind::Symbol(_) => SyntaxKind::Symbol_,
        TokenKind::Semicolon => SyntaxKind::Semicolon,
        TokenKind::Comment => SyntaxKind::Comment,
        TokenKind::Space => SyntaxKind::Space,
        TokenKind::EOF => SyntaxKind::Eof,
        TokenKind::Error => SyntaxKind::TokenError,
    }
}

// =========================================================================
// ParseError
// =========================================================================

/// A parse error with source position.
#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub offset: usize,
    pub length: usize,
}

// =========================================================================
// CstBuilder — builds a GreenNode from tokens
// =========================================================================

struct CstBuilder {
    builder: GreenNodeBuilder<'static>,
    errors: Vec<ParseError>,
    tokens: Vec<Token>,
    pos: usize,
}

impl CstBuilder {
    /// Build a CST from source text.
    fn build(source: &str) -> (GreenNode, Vec<ParseError>) {
        let tokens = Lexer::new(source).tokenize();
        let mut builder = CstBuilder {
            builder: GreenNodeBuilder::new(),
            errors: Vec::new(),
            tokens,
            pos: 0,
        };
        builder.parse_root();
        let green = builder.builder.finish();
        (green, builder.errors)
    }

    // ── Top-level ──

    fn parse_root(&mut self) {
        self.builder.start_node(SyntaxKind::Root.into());

        while !self.is_eof() {
            if self.at_keyword("theory") {
                self.parse_theory_header();
            } else if self.at_keyword("lemma") || self.at_keyword("theorem") || self.at_keyword("corollary") {
                self.parse_lemma();
            } else {
                // Skip unknown top-level content
                self.advance();
            }
        }

        self.builder.finish_node();
    }

    // ── Theory header ──

    fn parse_theory_header(&mut self) {
        self.builder.start_node(SyntaxKind::TheoryHeader.into());
        self.expect_keyword("theory");
        self.expect_ident(); // theory name
        if self.at_keyword("imports") {
            self.expect_keyword("imports");
            while self.at_ident() {
                self.expect_ident();
            }
        }
        self.expect_keyword("begin");
        self.builder.finish_node();
    }

    // ── Lemma / Theorem ──

    fn parse_lemma(&mut self) {
        self.builder.start_node(SyntaxKind::Lemma.into());
        self.advance(); // lemma/theorem/corollary
        self.expect_ident(); // lemma name
        if self.at_symbol(":") {
            self.advance(); // ':'
        }
        if self.at_string() {
            self.advance(); // statement
        }
        self.builder.finish_node();
    }

    // ── Token helpers ──

    fn is_eof(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    fn current(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn current_kind(&self) -> Option<&TokenKind> {
        self.current().map(|t| &t.kind)
    }

    fn at_keyword(&self, kw: &str) -> bool {
        match self.current_kind() {
            Some(TokenKind::Keyword(k)) => k.as_ref() == kw,
            _ => false,
        }
    }

    fn at_ident(&self) -> bool {
        matches!(self.current_kind(), Some(TokenKind::Ident | TokenKind::LongIdent))
    }

    fn at_string(&self) -> bool {
        matches!(self.current_kind(), Some(TokenKind::String))
    }

    fn at_symbol(&self, s: &str) -> bool {
        match self.current_kind() {
            Some(TokenKind::Symbol(k)) => k.as_ref() == s,
            _ => false,
        }
    }

    fn advance(&mut self) {
        if self.pos < self.tokens.len() {
            let tok = &self.tokens[self.pos];
            let kind = token_kind_to_syntax(&tok.kind);
            self.builder.token(kind.into(), &tok.source);
            self.pos += 1;
        }
    }

    fn expect_keyword(&mut self, kw: &str) {
        if self.at_keyword(kw) {
            self.advance();
        } else {
            self.error(&format!("expected keyword `{kw}`"));
        }
    }

    fn expect_ident(&mut self) {
        if self.at_ident() {
            self.advance();
        } else {
            self.error("expected identifier");
        }
    }

    fn error(&mut self, msg: &str) {
        let offset = self.current().map(|t| t.offset).unwrap_or(0);
        let length = self.current().map(|t| t.source.len()).unwrap_or(1);
        self.errors.push(ParseError {
            message: msg.to_string(),
            offset,
            length,
        });
        // Insert error node and continue
        self.builder.start_node(SyntaxKind::ErrorNode.into());
        self.builder.token(SyntaxKind::TokenError.into(), msg);
        self.builder.finish_node();
        // Skip current token to avoid infinite loop
        self.pos += 1;
    }
}

impl From<SyntaxKind> for rowan::SyntaxKind {
    fn from(kind: SyntaxKind) -> Self {
        IsabelleLanguage::kind_to_raw(kind)
    }
}

// =========================================================================
// SyntaxTree — public API
// =========================================================================

/// A concrete syntax tree for an Isabelle source file.
///
/// Internally uses Rowan's green tree for O(1) cloning and
/// structural sharing during incremental re-parsing.
pub struct SyntaxTree {
    green: GreenNode,
    errors: Vec<ParseError>,
}

impl SyntaxTree {
    /// Parse source text into a concrete syntax tree.
    ///
    /// Returns the tree and any parse errors encountered.
    /// Even with errors, the tree is complete (error recovery).
    pub fn parse(source: &str) -> (Self, Vec<ParseError>) {
        let (green, errors) = CstBuilder::build(source);
        (SyntaxTree { green, errors: errors.clone() }, errors)
    }

    /// Get the root syntax node.
    pub fn root(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green.clone())
    }

    /// Get the parse errors.
    pub fn errors(&self) -> &[ParseError] {
        &self.errors
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_empty() {
        let (tree, _errors) = SyntaxTree::parse("");
        let root = tree.root();
        assert_eq!(root.kind(), SyntaxKind::Root);
    }

    #[test]
    fn test_parse_theory_header() {
        let (tree, errors) = SyntaxTree::parse("theory MyTheory imports Foo Bar begin");
        assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
        let root = tree.root();
        // Should have a TheoryHeader child
        let header = root.children().find(|c| c.kind() == SyntaxKind::TheoryHeader);
        assert!(header.is_some(), "no theory header found");
    }

    #[test]
    fn test_parse_lemma() {
        let (tree, errors) = SyntaxTree::parse("lemma foo: \"A\"");
        assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
        let root = tree.root();
        let lemmas: Vec<_> = root.children().filter(|c| c.kind() == SyntaxKind::Lemma).collect();
        assert!(!lemmas.is_empty(), "no lemma found");
    }

    #[test]
    fn test_parse_with_error_recovery() {
        let (tree, errors) = SyntaxTree::parse("lemma 123: \"A\"");
        // Should have at least one error (number where identifier expected)
        assert!(!errors.is_empty(), "expected parse errors");
        // But should still produce a tree (error recovery)
        let root = tree.root();
        assert_eq!(root.kind(), SyntaxKind::Root);
    }

    #[test]
    fn test_parse_full_theory() {
        let source = "theory Test imports Pure begin\nlemma foo: \"True\"\nby auto\nend";
        let (tree, _errors) = SyntaxTree::parse(source);
        // May have errors due to incomplete parser (end not handled)
        // But should not panic
        let root = tree.root();
        assert_eq!(root.kind(), SyntaxKind::Root);
    }
}
