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
//! Source spans and `SourceId` are for diagnostics and provenance reporting
//! only; they do not enter `TheoremId` or any other kernel identity digest.

use std::sync::Arc;

/// Identifies a source file or session input.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SourceId(Arc<str>);

impl SourceId {
    pub fn new(id: impl Into<Arc<str>>) -> Self {
        Self(id.into())
    }
}

/// 0-indexed byte range in the source text.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SourceSpan {
    pub start: usize,
    pub end: usize,
}

/// An unresolved name from source text — never `Const`, `Free`, or `Var` yet.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SourceName {
    pub spelling: Arc<str>,
    /// True if the source contained a qualified "Thy.name" form.
    pub qualified: bool,
}

/// A source-level type annotation — unresolved, no arity/sort checking.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SourceType {
    Name { name: SourceName, span: SourceSpan },
    Application { constructor: Box<SourceType>, arguments: Vec<SourceType>, span: SourceSpan },
    Arrow { from: Box<SourceType>, to: Box<SourceType>, span: SourceSpan },
}

/// Binder kind as it appears in the source.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinderKind {
    Forall,
    Exists,
    Lambda,
    Epsilon,
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
        kind: BinderKind,
        binders: Vec<SourceBinder>,
        body: Box<SourceExpr>,
        span: SourceSpan,
    },
    SyntaxApplication {
        syntax: SourceName,
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
///     name: SourceName { spelling: "x".into(), qualified: false },
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
///         name: SourceName { spelling: "A".into(), qualified: false },
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
///         name: SourceName { spelling: "A".into(), qualified: false },
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
///         name: SourceName { spelling: "A".into(), qualified: false },
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
///         name: SourceName { spelling: "A".into(), qualified: false },
///         span: SourceSpan { start: 0, end: 1 },
///     },
/// }.into();
/// ```
///
/// ```compile_fail
/// use isabelle_rs::isar::source_ast::{SourceExpr, SourceName, SourceSpan};
/// use isabelle_rs::kernel::ContextStamp;
/// // No ContextStamp appears in the source AST public API.
/// fn _leak(e: SourceExpr) -> ContextStamp {
///     match e {
///         SourceExpr::Name { .. } => ContextStamp::dummy_for_test(),
///         _ => ContextStamp::dummy_for_test(),
///     }
/// }
/// ```
#[allow(unused_imports)]
mod _compile_fail_guards {
    // These imports are referenced by the doc-tests above.
    // They are intentionally unused at the module level.
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(s: &str) -> SourceName {
        SourceName { spelling: s.into(), qualified: s.contains('.') }
    }

    fn span(start: usize, end: usize) -> SourceSpan {
        SourceSpan { start, end }
    }

    #[test]
    fn span_preservation_through_nested_application() {
        let inner = SourceExpr::Name { name: name("f"), span: span(0, 1) };
        let arg = SourceExpr::Name { name: name("x"), span: span(2, 3) };
        let app = SourceExpr::Application {
            function: Box::new(inner),
            argument: Box::new(arg),
            span: span(0, 3),
        };
        assert_eq!(app.span(), span(0, 3));
        match &app {
            SourceExpr::Application { function, argument, .. } => {
                assert_eq!(function.span(), span(0, 1));
                assert_eq!(argument.span(), span(2, 3));
            },
            _ => unreachable!(),
        }
    }

    #[test]
    fn qualified_name_round_trip() {
        let qname = name("HOL.True");
        assert!(qname.qualified);
        assert_eq!(qname.spelling.as_ref(), "HOL.True");

        let uname = name("True");
        assert!(!uname.qualified);
        assert_eq!(uname.spelling.as_ref(), "True");
    }

    #[test]
    fn binder_shadowing_preserves_distinct_nodes() {
        let inner = SourceExpr::Binder {
            kind: BinderKind::Forall,
            binders: vec![SourceBinder { name: name("x"), typ: None, span: span(5, 6) }],
            body: Box::new(SourceExpr::Name { name: name("x"), span: span(7, 8) }),
            span: span(0, 9),
        };
        let outer = SourceExpr::Binder {
            kind: BinderKind::Forall,
            binders: vec![SourceBinder { name: name("x"), typ: None, span: span(1, 2) }],
            body: Box::new(inner.clone()),
            span: span(0, 9),
        };
        // They are structurally distinct even with same binder name spelling.
        assert_ne!(outer, inner);
        match &outer {
            SourceExpr::Binder { body, .. } => match body.as_ref() {
                SourceExpr::Binder { binders, .. } => {
                    assert_eq!(binders[0].name.spelling.as_ref(), "x");
                },
                _ => unreachable!(),
            },
            _ => unreachable!(),
        }
    }

    #[test]
    fn no_const_free_distinction_all_names_are_sourceexpr_name() {
        // All of these are SourceExpr::Name — no Const/Free variant exists.
        for spelling in &["True", "f", "x", "HOL.True"] {
            let expr = SourceExpr::Name { name: name(spelling), span: span(0, 0) };
            assert!(matches!(expr, SourceExpr::Name { .. }));
        }
    }

    #[test]
    fn fake_span_does_not_affect_expression_equality() {
        let expr = SourceExpr::Name { name: name("A"), span: span(0, 1) };
        let prop_a = SourceProposition {
            source: SourceId::new("a.thy"),
            span: span(0, 1),
            expression: expr.clone(),
        };
        let prop_b = SourceProposition {
            source: SourceId::new("b.thy"),
            span: span(10, 11),
            expression: expr,
        };
        // Different source/span → not equal.
        assert_ne!(prop_a, prop_b);
        // But expressions are equal.
        assert_eq!(prop_a.expression, prop_b.expression);
    }

    #[test]
    fn source_ast_has_no_context_stamp_field() {
        // Verify structurally: no ContextStamp appears in the public types.
        // This test exists as a runtime check that the types are self-contained.
        let prop = SourceProposition {
            source: SourceId::new("test.thy"),
            span: span(0, 1),
            expression: SourceExpr::Name { name: name("A"), span: span(0, 1) },
        };
        // Construction succeeds without any ContextStamp, TheoryId, etc.
        assert_eq!(prop.source.0.as_ref(), "test.thy");
    }

    #[test]
    fn source_group_preserves_inner_span() {
        let inner = SourceExpr::Name { name: name("P"), span: span(1, 2) };
        let group = SourceExpr::Group { inner: Box::new(inner.clone()), span: span(0, 3) };
        assert_eq!(group.span(), span(0, 3));
        match &group {
            SourceExpr::Group { inner: box_inner, .. } => {
                assert_eq!(box_inner.span(), span(1, 2));
            },
            _ => unreachable!(),
        }
    }

    #[test]
    fn syntax_application_preserves_raw_arguments() {
        let args = vec![
            SourceExpr::Name { name: name("a"), span: span(0, 1) },
            SourceExpr::Name { name: name("b"), span: span(2, 3) },
        ];
        let syntax = SourceExpr::SyntaxApplication {
            syntax: name("{*}"),
            arguments: args.clone(),
            span: span(0, 5),
        };
        match &syntax {
            SourceExpr::SyntaxApplication { arguments, .. } => {
                assert_eq!(arguments.len(), 2);
                assert_eq!(arguments[0], args[0]);
                assert_eq!(arguments[1], args[1]);
            },
            _ => unreachable!(),
        }
    }
}
