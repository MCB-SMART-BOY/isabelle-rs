//! Abstract syntax tree types.
//!
//! The AST sits between the CST (concrete syntax) and the kernel Term.
//! It resolves mixfix operators, precedence, and notation macros.
//!
//! ## CST → AST bridge
//!
//! The `Ast::from_syntax()` method converts a Rowan CST node to an AST node.
//! This is where syntactic sugar is desugared and names are resolved.

use crate::syntax::parser::{SyntaxKind, SyntaxNode};

// =========================================================================
// Ast — abstract syntax tree
// =========================================================================

/// An AST node representing a parsed Isabelle expression.
#[derive(Debug, Clone)]
pub enum Ast {
    /// A constant reference: `True`, `Pure.all`, `HOL.eq`
    Constant(String),
    /// A (free) variable reference: `x`, `f`, `P`
    Variable(String),
    /// Function application: `f x`
    Application(Box<Ast>, Box<Ast>),
    /// Lambda abstraction: `%x. body` or `λx. body`
    Abstraction(String, Option<Box<Ast>>, Box<Ast>),
    /// Mixfix operator application: `a + b`, `if P then Q else R`
    Mixfix(String, Vec<Ast>),
    /// A string literal
    String(String),
    /// A number literal
    Number(String),
    /// A type annotation: `t :: τ`
    TypeAnnotation(Box<Ast>, Box<Ast>),
}

// =========================================================================
// CST → AST conversion
// =========================================================================

impl Ast {
    /// Build an AST from a Rowan syntax node.
    ///
    /// Returns `None` if the node doesn't represent a valid AST construct.
    pub fn from_syntax(node: &SyntaxNode) -> Option<Self> {
        match node.kind() {
            SyntaxKind::Root => {
                // A root is a sequence of commands; collect them
                let children: Vec<Ast> = node.children()
                    .filter_map(|c| Ast::from_syntax(&c))
                    .collect();
                if children.is_empty() {
                    None
                } else {
                    Some(Ast::Mixfix("root".into(), children))
                }
            }
            SyntaxKind::Lemma | SyntaxKind::Theorem => {
                // Extract name and statement from lemma children
                let mut name = String::new();
                let mut stmt = String::new();
                for child in node.children_with_tokens() {
                    match child.kind() {
                        SyntaxKind::Ident => {
                            let text = child.as_token()?.text().to_string();
                            if name.is_empty() {
                                name = text;
                            }
                        }
                        SyntaxKind::String_ => {
                            stmt = child.as_token()?.text().to_string();
                        }
                        _ => {}
                    }
                }
                if name.is_empty() {
                    None
                } else {
                    Some(Ast::Mixfix("lemma".into(), vec![
                        Ast::Variable(name),
                        Ast::String(stmt),
                    ]))
                }
            }
            SyntaxKind::TheoryHeader => {
                // Extract theory name from header
                let ident = node.children_with_tokens()
                    .find(|c| c.kind() == SyntaxKind::Ident)?
                    .as_token()?
                    .text()
                    .to_string();
                Some(Ast::Mixfix("theory".into(), vec![
                    Ast::Variable(ident),
                ]))
            }
            SyntaxKind::Ident | SyntaxKind::LongIdent => {
                let text = node.first_token()?.text().to_string();
                Some(Ast::Variable(text))
            }
            SyntaxKind::Keyword => {
                let text = node.first_token()?.text().to_string();
                Some(Ast::Constant(text))
            }
            SyntaxKind::String_ => {
                let text = node.first_token()?.text().to_string();
                Some(Ast::String(text))
            }
            SyntaxKind::Number_ => {
                let text = node.first_token()?.text().to_string();
                Some(Ast::Number(text))
            }
            _ => None,
        }
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::parser::SyntaxTree;

    #[test]
    fn test_ast_from_theory_header() {
        let (tree, _) = SyntaxTree::parse("theory MyTheory imports Foo begin");
        let root = tree.root();
        let ast = Ast::from_syntax(&root);
        assert!(ast.is_some());
    }

    #[test]
    fn test_ast_from_lemma() {
        let (tree, _) = SyntaxTree::parse("lemma foo: \"A\"");
        let root = tree.root();
        let ast = Ast::from_syntax(&root);
        assert!(ast.is_some());
    }

    #[test]
    fn test_ast_from_lemma_inner() {
        // Test that Lemma → Ast conversion works end-to-end
        let (tree, _) = SyntaxTree::parse("lemma my_lemma: \"A ==> B\"");
        let root = tree.root();
        let lemma_node = root.children()
            .find(|c| c.kind() == SyntaxKind::Lemma);
        assert!(lemma_node.is_some(), "no Lemma node found");
        let ast = Ast::from_syntax(&lemma_node.unwrap());
        assert!(ast.is_some());
        // The lemma AST should be a Mixfix with name and statement
        match &ast.unwrap() {
            Ast::Mixfix(op, args) => {
                assert_eq!(op, "lemma");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("expected Mixfix"),
        }
    }
}
