//! Source-level proposition AST — pure syntax, no semantic resolution.
//!
//! This module provides a syntax-tree representation of Isabelle propositions
//! as they appear in source text. Every name is unresolved (no `Const`/`Free`
//! distinction), no `ContextStamp` or trusted-theory identity is carried, and
//! there is intentionally no conversion path to `CProp`, `ClosedThm`, or
//! `TrustedTheorem`. The only future route from a `SourceProposition` to a
//! checked kernel proposition is through an explicit elaborator (planned for
//! Change C2).
//!
//! Concretely, this module does NOT provide:
//!
//! - `impl From<SourceExpr> for core::Term`
//! - `impl From<SourceProposition> for kernel::CProp`
//! - `impl From<SourceProposition> for kernel::KernelThm`
//! - `impl From<SourceProposition> for kernel::ClosedThm`
//! - `impl From<SourceProposition> for kernel::TrustedTheorem`
//! - Any method named `assume_is_checked`, `into_trusted_term`, `certify`, or
//!   `trust`.
//!
//! Source spans and `SourceId` are caller-supplied diagnostic metadata. They
//! are deliberately forgeable and do not enter `TheoremId`, dependencies, or
//! any other kernel identity or authority check.

use std::sync::Arc;

/// Caller-supplied label for a source file or session input.
///
/// This is diagnostic metadata, not a content digest or trusted provenance
/// token. Equal labels need not identify equal bytes, and callers may construct
/// any label.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SourceId(Arc<str>);

impl SourceId {
    pub fn new(id: impl Into<Arc<str>>) -> Self {
        Self(id.into())
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// Half-open, 0-indexed byte range `[start, end)` in the labelled source.
///
/// The data-only AST does not validate ordering or source bounds. A parser or
/// elaborator consuming spans must validate them against the exact source
/// bytes before using them for diagnostics. Spans never confer trust.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SourceSpan {
    pub start: usize,
    pub end: usize,
}

/// Exact unresolved name spelling from source text.
///
/// A dot or theory-like prefix is retained as text, not preclassified as
/// qualification. Name resolution later decides whether the spelling denotes
/// a constant, free, schematic variable, bound occurrence, or syntax name.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SourceName {
    pub spelling: Arc<str>,
}

/// A source-level type annotation — unresolved, no arity/sort checking.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SourceType {
    Name { name: SourceName, span: SourceSpan },
    Application { constructor: Box<SourceType>, arguments: Vec<SourceType>, span: SourceSpan },
    Arrow { from: Box<SourceType>, to: Box<SourceType>, span: SourceSpan },
}

/// Exact unresolved syntax token and its source location.
///
/// Tokens such as `!!`, `ALL`, `EX`, and lambda syntax remain raw spellings.
/// Their Pure/HOL meaning is assigned only by a declaration-aware parser or
/// elaborator.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SourceSyntax {
    pub spelling: Arc<str>,
    pub span: SourceSpan,
}

/// One bound variable in a source binder.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SourceBinder {
    pub name: SourceName,
    pub typ: Option<SourceType>,
    pub span: SourceSpan,
}

/// A source-level expression — structure before elaboration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SourceExpr {
    Name {
        name: SourceName,
        span: SourceSpan,
    },
    Application {
        function: Box<SourceExpr>,
        argument: Box<SourceExpr>,
        span: SourceSpan,
    },
    Binder {
        syntax: SourceSyntax,
        binders: Vec<SourceBinder>,
        body: Box<SourceExpr>,
        span: SourceSpan,
    },
    SyntaxApplication {
        syntax: SourceSyntax,
        arguments: Vec<SourceExpr>,
        span: SourceSpan,
    },
    TypeAscription {
        expression: Box<SourceExpr>,
        typ: SourceType,
        span: SourceSpan,
    },
    /// A sub-proposition wrapped in parentheses — preserves source grouping.
    Group {
        inner: Box<SourceExpr>,
        span: SourceSpan,
    },
}

impl SourceExpr {
    /// Return the source span of this expression node.
    pub fn span(&self) -> SourceSpan {
        match self {
            SourceExpr::Name { span, .. } => *span,
            SourceExpr::Application { span, .. } => *span,
            SourceExpr::Binder { span, .. } => *span,
            SourceExpr::SyntaxApplication { span, .. } => *span,
            SourceExpr::TypeAscription { span, .. } => *span,
            SourceExpr::Group { span, .. } => *span,
        }
    }
}

/// A complete source-level proposition with origin tracking.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceProposition {
    pub source: SourceId,
    pub span: SourceSpan,
    pub expression: SourceExpr,
}

/// ```compile_fail
/// use isabelle_rs::isar::source_ast::{SourceExpr, SourceName, SourceSpan};
/// use isabelle_rs::core::term::Term;
/// // This conversion must not exist: source names are unresolved.
/// let _: Term = SourceExpr::Name {
///     name: SourceName { spelling: "x".into() },
///     span: SourceSpan { start: 0, end: 1 },
/// }.into();
/// ```
///
/// ```compile_fail
/// use isabelle_rs::isar::source_ast::{SourceId, SourceExpr, SourceName, SourceProposition, SourceSpan};
/// use isabelle_rs::kernel::CProp;
/// // Source AST must not convert to a certified proposition.
/// let _: CProp = SourceProposition {
///     source: SourceId::new("test.thy"),
///     span: SourceSpan { start: 0, end: 1 },
///     expression: SourceExpr::Name {
///         name: SourceName { spelling: "A".into() },
///         span: SourceSpan { start: 0, end: 1 },
///     },
/// }.into();
/// ```
///
/// ```compile_fail
/// use isabelle_rs::isar::source_ast::{SourceId, SourceExpr, SourceName, SourceProposition, SourceSpan};
/// use isabelle_rs::kernel::TrustedTheorem;
/// // Source AST must never become a sealed trusted theorem.
/// let _: TrustedTheorem = SourceProposition {
///     source: SourceId::new("test.thy"),
///     span: SourceSpan { start: 0, end: 1 },
///     expression: SourceExpr::Name {
///         name: SourceName { spelling: "A".into() },
///         span: SourceSpan { start: 0, end: 1 },
///     },
/// }.into();
/// ```
///
/// ```compile_fail
/// use isabelle_rs::isar::source_ast::{SourceId, SourceExpr, SourceName, SourceProposition, SourceSpan};
/// use isabelle_rs::kernel::ClosedThm;
/// // Source AST must not become a closed theorem.
/// let _: ClosedThm = SourceProposition {
///     source: SourceId::new("test.thy"),
///     span: SourceSpan { start: 0, end: 1 },
///     expression: SourceExpr::Name {
///         name: SourceName { spelling: "A".into() },
///         span: SourceSpan { start: 0, end: 1 },
///     },
/// }.into();
/// ```
///
/// ```compile_fail
/// use isabelle_rs::isar::source_ast::{SourceId, SourceExpr, SourceName, SourceProposition, SourceSpan};
/// use isabelle_rs::kernel::DependencySet;
/// // Parser metadata never enters dependency sets.
/// let _: DependencySet = SourceProposition {
///     source: SourceId::new("test.thy"),
///     span: SourceSpan { start: 0, end: 1 },
///     expression: SourceExpr::Name {
///         name: SourceName { spelling: "A".into() },
///         span: SourceSpan { start: 0, end: 1 },
///     },
/// }.into();
/// ```
///
/// ```compile_fail
/// use isabelle_rs::isar::source_ast::{
///     SourceExpr, SourceId, SourceName, SourceProposition, SourceSpan,
/// };
/// use isabelle_rs::kernel::ContextStamp;
/// // The source proposition has no field from which trusted context can leak.
/// let proposition = SourceProposition {
///     source: SourceId::new("test.thy"),
///     span: SourceSpan { start: 0, end: 1 },
///     expression: SourceExpr::Name {
///         name: SourceName { spelling: "A".into() },
///         span: SourceSpan { start: 0, end: 1 },
///     },
/// };
/// let SourceProposition { context, .. } = proposition;
/// let _: ContextStamp = context;
/// ```
#[allow(unused_imports)]
mod _compile_fail_guards {
    // These imports are referenced by the doc-tests above.
    // They are intentionally unused at the module level.
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(spelling: &str) -> SourceName {
        SourceName { spelling: spelling.into() }
    }

    fn span(start: usize, end: usize) -> SourceSpan {
        SourceSpan { start, end }
    }

    fn syntax(spelling: &str, start: usize, end: usize) -> SourceSyntax {
        SourceSyntax { spelling: spelling.into(), span: span(start, end) }
    }

    #[test]
    fn span_preservation_through_nested_application() {
        let function = SourceExpr::Name { name: name("f"), span: span(0, 1) };
        let argument = SourceExpr::Name { name: name("x"), span: span(2, 3) };
        let application = SourceExpr::Application {
            function: Box::new(function),
            argument: Box::new(argument),
            span: span(0, 3),
        };

        assert_eq!(application.span(), span(0, 3));
        match &application {
            SourceExpr::Application { function, argument, .. } => {
                assert_eq!(function.span(), span(0, 1));
                assert_eq!(argument.span(), span(2, 3));
            },
            _ => unreachable!(),
        }
    }

    #[test]
    fn source_spans_are_half_open_byte_ranges() {
        let source = "λx. x";
        let lambda_end = "λ".len();
        assert_eq!(lambda_end, 2);
        assert_eq!(&source[span(0, lambda_end).start..span(0, lambda_end).end], "λ");

        let binder = SourceExpr::Binder {
            syntax: syntax("λ", 0, lambda_end),
            binders: vec![SourceBinder {
                name: name("x"),
                typ: None,
                span: span(lambda_end, lambda_end + 1),
            }],
            body: Box::new(SourceExpr::Name {
                name: name("x"),
                span: span(source.len() - 1, source.len()),
            }),
            span: span(0, source.len()),
        };

        assert_eq!(binder.span(), span(0, source.len()));
        match binder {
            SourceExpr::Binder { syntax, binders, body, .. } => {
                assert_eq!(&source[syntax.span.start..syntax.span.end], "λ");
                assert_eq!(&source[binders[0].span.start..binders[0].span.end], "x");
                assert_eq!(&source[body.span().start..body.span().end], "x");
            },
            _ => unreachable!(),
        }
    }

    #[test]
    fn dotted_and_bare_names_remain_unclassified_spellings() {
        let dotted = name("HOL.True");
        let bare = name("True");

        assert_eq!(dotted.spelling.as_ref(), "HOL.True");
        assert_eq!(bare.spelling.as_ref(), "True");
    }

    #[test]
    fn binder_syntax_remains_unresolved_surface_text() {
        let pure = SourceExpr::Binder {
            syntax: syntax("!!", 0, 2),
            binders: vec![SourceBinder { name: name("x"), typ: None, span: span(3, 4) }],
            body: Box::new(SourceExpr::Name { name: name("P"), span: span(6, 7) }),
            span: span(0, 7),
        };
        let object = SourceExpr::Binder {
            syntax: syntax("ALL", 0, 3),
            binders: vec![SourceBinder { name: name("x"), typ: None, span: span(4, 5) }],
            body: Box::new(SourceExpr::Name { name: name("P"), span: span(7, 8) }),
            span: span(0, 8),
        };

        match (pure, object) {
            (
                SourceExpr::Binder { syntax: pure_syntax, .. },
                SourceExpr::Binder { syntax: object_syntax, .. },
            ) => {
                assert_eq!(pure_syntax.spelling.as_ref(), "!!");
                assert_eq!(object_syntax.spelling.as_ref(), "ALL");
            },
            _ => unreachable!(),
        }
    }

    #[test]
    fn binder_shadowing_preserves_distinct_source_nodes() {
        let inner = SourceExpr::Binder {
            syntax: syntax("ALL", 7, 10),
            binders: vec![SourceBinder { name: name("x"), typ: None, span: span(11, 12) }],
            body: Box::new(SourceExpr::Name { name: name("x"), span: span(14, 15) }),
            span: span(7, 15),
        };
        let outer = SourceExpr::Binder {
            syntax: syntax("ALL", 0, 3),
            binders: vec![SourceBinder { name: name("x"), typ: None, span: span(4, 5) }],
            body: Box::new(inner.clone()),
            span: span(0, 15),
        };

        assert_ne!(outer, inner);
        match &outer {
            SourceExpr::Binder { binders: outer_binders, body, .. } => {
                let SourceExpr::Binder { binders: inner_binders, .. } = body.as_ref() else {
                    unreachable!()
                };
                assert_eq!(outer_binders[0].name.spelling.as_ref(), "x");
                assert_eq!(inner_binders[0].name.spelling.as_ref(), "x");
                assert_ne!(outer_binders[0].span, inner_binders[0].span);
            },
            _ => unreachable!(),
        }
    }

    #[test]
    fn all_unresolved_names_share_one_source_variant() {
        for spelling in ["True", "f", "x", "HOL.True"] {
            let expression = SourceExpr::Name { name: name(spelling), span: span(0, 0) };
            assert!(matches!(expression, SourceExpr::Name { .. }));
        }
    }

    #[test]
    fn diagnostic_source_metadata_is_separate_from_expression_structure() {
        let expression = SourceExpr::Name { name: name("A"), span: span(0, 1) };
        let first = SourceProposition {
            source: SourceId::new("a.thy"),
            span: span(0, 1),
            expression: expression.clone(),
        };
        let second = SourceProposition {
            source: SourceId::new("forged-label"),
            span: span(10, 11),
            expression,
        };

        assert_ne!(first, second);
        assert_eq!(first.expression, second.expression);
        assert_eq!(second.source.as_str(), "forged-label");
    }

    #[test]
    fn source_ast_is_constructible_without_trusted_context() {
        let proposition = SourceProposition {
            source: SourceId::new("test.thy"),
            span: span(0, 1),
            expression: SourceExpr::Name { name: name("A"), span: span(0, 1) },
        };

        assert_eq!(proposition.source.as_str(), "test.thy");
    }

    #[test]
    fn source_group_preserves_inner_span() {
        let inner = SourceExpr::Name { name: name("P"), span: span(1, 2) };
        let group = SourceExpr::Group { inner: Box::new(inner), span: span(0, 3) };

        assert_eq!(group.span(), span(0, 3));
        match &group {
            SourceExpr::Group { inner, .. } => assert_eq!(inner.span(), span(1, 2)),
            _ => unreachable!(),
        }
    }

    #[test]
    fn syntax_application_preserves_raw_operator_and_arguments() {
        let arguments = vec![
            SourceExpr::Name { name: name("a"), span: span(0, 1) },
            SourceExpr::Name { name: name("b"), span: span(6, 7) },
        ];
        let application = SourceExpr::SyntaxApplication {
            syntax: syntax("⊗", 2, 5),
            arguments: arguments.clone(),
            span: span(0, 7),
        };

        match &application {
            SourceExpr::SyntaxApplication { syntax, arguments: actual, .. } => {
                assert_eq!(syntax.spelling.as_ref(), "⊗");
                assert_eq!(syntax.span, span(2, 5));
                assert_eq!(actual, &arguments);
            },
            _ => unreachable!(),
        }
    }
}
