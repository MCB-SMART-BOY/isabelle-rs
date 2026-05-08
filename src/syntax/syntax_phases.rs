//! Syntax phase pipeline — from source text to kernel Terms.
//!
//! ## Phases
//!
//! ```text
//! Source text
//!   → Tokenizer (isar/token.rs)
//!   → CST Parser (syntax/parser.rs)
//!   → AST Builder (syntax/ast.rs)
//!   → Type annotation / elaboration
//!   → Kernel Term (kernel/term.rs)
//! ```

use crate::syntax::ast::Ast;
use crate::syntax::parser::{ParseError, SyntaxTree};

// =========================================================================
// SyntaxPhases
// =========================================================================

/// The syntax phase pipeline: source → CST → AST → Term.
pub struct SyntaxPhases;

impl SyntaxPhases {
    pub fn new() -> Self {
        SyntaxPhases
    }

    /// Parse source text and return the AST.
    ///
    /// Returns the AST and any parse errors. Even with errors,
    /// a partial AST is returned (error recovery).
    pub fn parse_ast(&self, source: &str) -> (Option<Ast>, Vec<ParseError>) {
        let (tree, errors) = SyntaxTree::parse(source);
        let ast = tree.root();
        let ast = Ast::from_syntax(&ast);
        (ast, errors)
    }

    /// Parse source text into a CST (SyntaxTree).
    pub fn parse_cst(&self, source: &str) -> (SyntaxTree, Vec<ParseError>) {
        SyntaxTree::parse(source)
    }
}

impl Default for SyntaxPhases {
    fn default() -> Self {
        Self::new()
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_ast_theory() {
        let phases = SyntaxPhases::new();
        let (ast, errors) = phases.parse_ast("theory Test imports Pure begin");
        assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
        assert!(ast.is_some());
    }

    #[test]
    fn test_parse_ast_lemma() {
        let phases = SyntaxPhases::new();
        let (ast, errors) = phases.parse_ast("lemma foo: \"A\"");
        assert!(errors.is_empty(), "unexpected errors: {:?}", errors);
        assert!(ast.is_some());
    }

    #[test]
    fn test_parse_cst() {
        let phases = SyntaxPhases::new();
        let (tree, _) = phases.parse_cst("lemma foo: \"A\"");
        let root = tree.root();
        assert_eq!(root.kind(), crate::syntax::parser::SyntaxKind::Root);
    }
}
