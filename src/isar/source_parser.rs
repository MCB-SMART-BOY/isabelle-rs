//! Strict, syntax-only parser for the supported Pure proposition subset.
//! Tokens retain byte offsets; no legacy `Term` or type inference enters this path.

use std::sync::Arc;

use super::source_ast::{
    SourceBinder, SourceExpr, SourceId, SourceName, SourceProposition, SourceSpan, SourceSyntax,
    SourceType,
};

const MAX_SOURCE_NESTING: usize = 128;
const MAX_SOURCE_TOKENS: usize = 256;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Name,
    Prop,
    TypeName,
    Left,
    Right,
    LeftBracket,
    RightBracket,
    Comma,
    Dot,
    Ascribe,
    Imply,
    Equal,
    ObjectEqual,
    Forall,
    Lambda,
    Arrow,
}

#[derive(Clone, Copy)]
struct Lexeme<'a> {
    kind: Kind,
    text: &'a str,
    span: SourceSpan,
}

fn is_name_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

fn is_name_continue(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_' || ch == '\''
}

fn is_unsupported_keyword(name: &str) -> bool {
    matches!(
        name,
        "if" | "then"
            | "else"
            | "let"
            | "in"
            | "case"
            | "of"
            | "ALL"
            | "EX"
            | "and"
            | "or"
            | "not"
            | "theory"
            | "imports"
            | "begin"
            | "end"
            | "lemma"
            | "theorem"
            | "proof"
            | "qed"
            | "by"
            | "show"
            | "assume"
            | "fix"
            | "sorry"
    )
}

fn scan_name(input: &str, is_binder_name: bool) -> Option<(Kind, usize)> {
    let initial = input.chars().next()?;
    let is_type_name = initial == '\'';
    let mut end = initial.len_utf8();
    while end < input.len() {
        let next = input[end..].chars().next()?;
        if is_name_continue(next) {
            end += next.len_utf8();
        } else if next == '.'
            && !is_binder_name
            && input[end + 1..].chars().next().is_some_and(is_name_start)
        {
            end += 1;
        } else {
            break;
        }
    }
    if (is_type_name && end == 1) || is_unsupported_keyword(&input[..end]) {
        return None;
    }
    let kind = if is_type_name {
        Kind::TypeName
    } else if &input[..end] == "PROP" {
        Kind::Prop
    } else {
        Kind::Name
    };
    Some((kind, end))
}

fn lex(input: &str, base: usize) -> Option<Vec<Lexeme<'_>>> {
    let mut tokens = Vec::new();
    let mut offset = 0;
    let mut is_binder_header = false;
    let mut is_binder_type = false;
    while offset < input.len() {
        let remaining = &input[offset..];
        let ch = remaining.chars().next()?;
        if ch.is_whitespace() {
            offset += ch.len_utf8();
            continue;
        }
        let (kind, length) = if remaining.starts_with("==>") {
            (Kind::Imply, 3)
        } else if remaining.starts_with("==") {
            (Kind::Equal, 2)
        } else if remaining.starts_with("!!") {
            (Kind::Forall, 2)
        } else if remaining.starts_with("::") {
            (Kind::Ascribe, 2)
        } else if remaining.starts_with(r"\<Rightarrow>") {
            (Kind::Arrow, r"\<Rightarrow>".len())
        } else if remaining.starts_with("=>") {
            (Kind::Arrow, 2)
        } else if remaining.starts_with(r"\<And>") {
            (Kind::Forall, r"\<And>".len())
        } else if remaining.starts_with(r"\<Longrightarrow>") {
            (Kind::Imply, r"\<Longrightarrow>".len())
        } else if remaining.starts_with(r"\<equiv>") {
            (Kind::Equal, r"\<equiv>".len())
        } else if remaining.starts_with(r"\<lambda>") {
            (Kind::Lambda, r"\<lambda>".len())
        } else if matches!(ch, '⋀' | 'λ' | '%') {
            (if ch == '⋀' { Kind::Forall } else { Kind::Lambda }, ch.len_utf8())
        } else if matches!(ch, '⟹' | '≡') {
            (if ch == '⟹' { Kind::Imply } else { Kind::Equal }, ch.len_utf8())
        } else if ch == '⇒' {
            (Kind::Arrow, ch.len_utf8())
        } else if is_name_start(ch) || ch == '\'' {
            scan_name(remaining, is_binder_header && !is_binder_type)?
        } else {
            match ch {
                '(' => (Kind::Left, 1),
                ')' => (Kind::Right, 1),
                '[' => (Kind::LeftBracket, 1),
                ']' => (Kind::RightBracket, 1),
                ',' => (Kind::Comma, 1),
                '=' => (Kind::ObjectEqual, 1),
                '.' => (Kind::Dot, 1),
                _ => return None,
            }
        };
        let text = &remaining[..length];
        if tokens.len() >= MAX_SOURCE_TOKENS {
            return None;
        }
        tokens.push(Lexeme {
            kind,
            text,
            span: SourceSpan { start: base + offset, end: base + offset + length },
        });
        match kind {
            Kind::Forall | Kind::Lambda => is_binder_header = true,
            Kind::Ascribe if is_binder_header => is_binder_type = true,
            Kind::Dot => {
                is_binder_header = false;
                is_binder_type = false;
            },
            _ => {},
        }
        offset += length;
    }
    Some(tokens)
}

struct Parser<'a> {
    tokens: Vec<Lexeme<'a>>,
    position: usize,
    depth: usize,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<Lexeme<'a>> {
        self.tokens.get(self.position).copied()
    }

    fn take(&mut self, kind: Kind) -> Option<Lexeme<'a>> {
        let token = self.peek().filter(|token| token.kind == kind)?;
        self.position += 1;
        Some(token)
    }

    fn parse_expression(&mut self) -> Option<SourceExpr> {
        if self.depth >= MAX_SOURCE_NESTING {
            return None;
        }
        self.depth += 1;
        let result = self.parse_implication();
        self.depth -= 1;
        result
    }

    fn parse_implication(&mut self) -> Option<SourceExpr> {
        if matches!(self.peek()?.kind, Kind::Forall | Kind::Lambda) {
            return self.parse_binder();
        }
        let left = self.parse_equality()?;
        let Some(op) = self.take(Kind::Imply) else { return Some(left) };
        let right = self.parse_expression()?;
        let span = SourceSpan { start: left.span().start, end: right.span().end };
        Some(SourceExpr::SyntaxApplication {
            syntax: SourceSyntax { spelling: Arc::from(op.text), span: op.span },
            arguments: vec![left, right],
            span,
        })
    }

    fn parse_equality(&mut self) -> Option<SourceExpr> {
        let left = self.parse_ascription()?;
        let op = self.take(Kind::Equal).or_else(|| self.take(Kind::ObjectEqual));
        let Some(op) = op else { return Some(left) };
        let right = self.parse_ascription()?;
        let span = SourceSpan { start: left.span().start, end: right.span().end };
        Some(SourceExpr::SyntaxApplication {
            syntax: SourceSyntax { spelling: Arc::from(op.text), span: op.span },
            arguments: vec![left, right],
            span,
        })
    }

    fn parse_binder(&mut self) -> Option<SourceExpr> {
        let op = self.take(Kind::Forall).or_else(|| self.take(Kind::Lambda))?;
        let mut binders = Vec::new();
        while self.peek().is_some_and(|token| matches!(token.kind, Kind::Name | Kind::Left)) {
            if binders.len() >= MAX_SOURCE_NESTING {
                return None;
            }
            binders.push(self.parse_binder_variable()?);
        }
        if binders.is_empty() || self.take(Kind::Dot).is_none() {
            return None;
        }
        let body = self.parse_expression()?;
        let span = SourceSpan { start: op.span.start, end: body.span().end };
        Some(SourceExpr::Binder {
            syntax: SourceSyntax { spelling: Arc::from(op.text), span: op.span },
            binders,
            body: Box::new(body),
            span,
        })
    }

    fn parse_binder_variable(&mut self) -> Option<SourceBinder> {
        let opening = self.take(Kind::Left);
        let token = self.take(Kind::Name)?;
        let name = SourceName { spelling: Arc::from(token.text) };
        let typ = if self.take(Kind::Ascribe).is_some() { Some(self.parse_type()?) } else { None };
        let end = if opening.is_some() {
            self.take(Kind::Right)?.span.end
        } else {
            typ.as_ref().map_or(token.span.end, |(_, span)| span.end)
        };
        Some(SourceBinder {
            name,
            typ: typ.map(|(typ, _)| typ),
            span: SourceSpan { start: opening.map_or(token.span.start, |op| op.span.start), end },
        })
    }

    fn parse_ascription(&mut self) -> Option<SourceExpr> {
        let prop = self.take(Kind::Prop);
        let mut expression = self.parse_application()?;
        if self.take(Kind::Ascribe).is_some() {
            let (typ, type_span) = self.parse_type()?;
            let span = SourceSpan { start: expression.span().start, end: type_span.end };
            expression = SourceExpr::TypeAscription { expression: Box::new(expression), typ, span };
        }
        if let Some(token) = prop {
            expression = SourceExpr::SyntaxApplication {
                syntax: SourceSyntax { spelling: Arc::from(token.text), span: token.span },
                span: SourceSpan { start: token.span.start, end: expression.span().end },
                arguments: vec![expression],
            };
        }
        Some(expression)
    }

    fn parse_application(&mut self) -> Option<SourceExpr> {
        let mut expression = self.parse_atom()?;
        let mut applications = 0;
        while self.peek().is_some_and(|token| matches!(token.kind, Kind::Name | Kind::Left)) {
            if applications >= MAX_SOURCE_NESTING {
                return None;
            }
            let argument = self.parse_atom()?;
            let span = SourceSpan { start: expression.span().start, end: argument.span().end };
            expression = SourceExpr::Application {
                function: Box::new(expression),
                argument: Box::new(argument),
                span,
            };
            applications += 1;
        }
        Some(expression)
    }

    fn parse_atom(&mut self) -> Option<SourceExpr> {
        if let Some(token) = self.take(Kind::Name) {
            return Some(SourceExpr::Name {
                name: SourceName { spelling: Arc::from(token.text) },
                span: token.span,
            });
        }
        let opening = self.take(Kind::Left)?;
        let inner = self.parse_expression()?;
        let closing = self.take(Kind::Right)?;
        Some(SourceExpr::Group {
            inner: Box::new(inner),
            span: SourceSpan { start: opening.span.start, end: closing.span.end },
        })
    }

    fn parse_type(&mut self) -> Option<(SourceType, SourceSpan)> {
        if self.depth >= MAX_SOURCE_NESTING {
            return None;
        }
        self.depth += 1;
        let result = self.parse_type_inner();
        self.depth -= 1;
        result
    }

    fn parse_type_inner(&mut self) -> Option<(SourceType, SourceSpan)> {
        if self.peek()?.kind == Kind::LeftBracket {
            return self.parse_curried_type();
        }
        let (from, from_span) = self.parse_type_application()?;
        if self.take(Kind::Arrow).is_none() {
            return Some((from, from_span));
        }
        let (to, to_span) = self.parse_type()?;
        let span = SourceSpan { start: from_span.start, end: to_span.end };
        Some((SourceType::Arrow { from: Box::new(from), to: Box::new(to), span }, span))
    }

    fn parse_curried_type(&mut self) -> Option<(SourceType, SourceSpan)> {
        let opening = self.take(Kind::LeftBracket)?;
        let mut arguments = Vec::new();
        loop {
            if arguments.len() >= MAX_SOURCE_NESTING {
                return None;
            }
            arguments.push(self.parse_type()?);
            if self.take(Kind::Comma).is_none() {
                break;
            }
        }
        self.take(Kind::RightBracket)?;
        self.take(Kind::Arrow)?;
        let (mut result, result_span) = self.parse_type()?;
        for (argument, argument_span) in arguments.into_iter().rev() {
            result = SourceType::Arrow {
                from: Box::new(argument),
                to: Box::new(result),
                span: SourceSpan { start: argument_span.start, end: result_span.end },
            };
        }
        let span = SourceSpan { start: opening.span.start, end: result_span.end };
        if let SourceType::Arrow { span: arrow_span, .. } = &mut result {
            *arrow_span = span;
        }
        Some((result, span))
    }

    fn parse_type_application(&mut self) -> Option<(SourceType, SourceSpan)> {
        let (mut typ, mut span) = self.parse_type_atom()?;
        let mut applications = 0;
        while let Some(token) = self.take(Kind::Name) {
            if applications >= MAX_SOURCE_NESTING {
                return None;
            }
            span.end = token.span.end;
            let constructor = SourceType::Name {
                name: SourceName { spelling: Arc::from(token.text) },
                span: token.span,
            };
            typ = SourceType::Application {
                constructor: Box::new(constructor),
                arguments: vec![typ],
                span,
            };
            applications += 1;
        }
        Some((typ, span))
    }

    fn parse_type_atom(&mut self) -> Option<(SourceType, SourceSpan)> {
        if let Some(token) = self.take(Kind::Name).or_else(|| self.take(Kind::TypeName)) {
            return Some((
                SourceType::Name {
                    name: SourceName { spelling: Arc::from(token.text) },
                    span: token.span,
                },
                token.span,
            ));
        }
        let opening = self.take(Kind::Left)?;
        let (inner, _) = self.parse_type()?;
        let closing = self.take(Kind::Right)?;
        Some((inner, SourceSpan { start: opening.span.start, end: closing.span.end }))
    }
}

pub fn parse_source_proposition(input: &str, source: SourceId) -> Option<SourceProposition> {
    parse_source_proposition_at(input, source, 0)
}

pub fn parse_source_proposition_at(
    input: &str,
    source: SourceId,
    source_offset: usize,
) -> Option<SourceProposition> {
    source_offset.checked_add(input.len())?;
    let trimmed = input.trim();
    let trim_offset = input.len().checked_sub(input.trim_start().len())?;
    let start = source_offset.checked_add(trim_offset)?;
    let (text, base) = if trimmed.starts_with('"') {
        let content = trimmed.strip_prefix('"')?.strip_suffix('"')?;
        if content.contains('"') {
            return None;
        }
        (content, start.checked_add(1)?)
    } else {
        (trimmed, start)
    };
    let tokens = lex(text, base)?;
    let mut parser = Parser { tokens, position: 0, depth: 0 };
    let expression = parser.parse_expression()?;
    if parser.position != parser.tokens.len() {
        return None;
    }
    Some(SourceProposition { source, span: expression.span(), expression })
}

/// Parse a complete source type with absolute byte offsets; no type authority is granted.
pub fn parse_source_type_at(input: &str, source_offset: usize) -> Option<SourceType> {
    source_offset.checked_add(input.len())?;
    let trimmed = input.trim();
    let trim_offset = input.len().checked_sub(input.trim_start().len())?;
    let base = source_offset.checked_add(trim_offset)?;
    let tokens = lex(trimmed, base)?;
    let mut parser = Parser { tokens, position: 0, depth: 0 };
    let (typ, _) = parser.parse_type()?;
    (parser.position == parser.tokens.len()).then_some(typ)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(input: &str) -> Option<SourceProposition> {
        parse_source_proposition(input, SourceId::new("test"))
    }

    #[test]
    fn source_parser_complete_implication_and_equality_preserve_structure() {
        let source = "  A x == B ==> C  ";
        let parsed = parse(source).expect("complete proposition");
        assert_eq!(&source[parsed.span.start..parsed.span.end], "A x == B ==> C");
        let SourceExpr::SyntaxApplication { syntax, arguments, .. } = parsed.expression else {
            panic!("expected implication")
        };
        assert_eq!(syntax.spelling.as_ref(), "==>");
        assert_eq!(&source[syntax.span.start..syntax.span.end], "==>");
        let SourceExpr::SyntaxApplication { syntax, arguments: eq_args, .. } = &arguments[0] else {
            panic!("expected equality")
        };
        assert_eq!(syntax.spelling.as_ref(), "==");
        let SourceExpr::Application { function, argument, span } = &eq_args[0] else {
            panic!("expected application")
        };
        assert_eq!(&source[span.start..span.end], "A x");
        assert_eq!(&source[function.span().start..function.span().end], "A");
        assert_eq!(&source[argument.span().start..argument.span().end], "x");
    }

    #[test]
    fn source_parser_prop_wraps_only_its_operand_with_exact_spans() {
        let source = " \"!!Q::prop. PROP f (Q :: prop) ==> PROP Q\" ";
        let parsed = parse(source).expect("explicit Pure propositions");
        let SourceExpr::Binder { body, .. } = parsed.expression else {
            panic!("expected universal binder");
        };
        let SourceExpr::SyntaxApplication { syntax, arguments, .. } = *body else {
            panic!("expected implication");
        };
        assert_eq!(syntax.spelling.as_ref(), "==>");
        let SourceExpr::SyntaxApplication { syntax, arguments: operand, span } = &arguments[0]
        else {
            panic!("expected PROP operand");
        };
        assert_eq!(syntax.spelling.as_ref(), "PROP");
        assert_eq!(&source[syntax.span.start..syntax.span.end], "PROP");
        assert_eq!(&source[span.start..span.end], "PROP f (Q :: prop)");
        let SourceExpr::Application { argument, .. } = &operand[0] else {
            panic!("expected complete application");
        };
        assert!(matches!(argument.as_ref(), SourceExpr::Group { .. }));
        assert!(matches!(
            &arguments[1],
            SourceExpr::SyntaxApplication { syntax, arguments, .. }
                if syntax.spelling.as_ref() == "PROP"
                    && matches!(&arguments[0], SourceExpr::Name { name, .. } if name.spelling.as_ref() == "Q")
        ));
    }

    #[test]
    fn source_parser_prop_keeps_operand_ascription_inside_wrapper() {
        let source = "PROP f x :: prop == PROP y";
        let parsed = parse(source).expect("PROP with typed application");
        let SourceExpr::SyntaxApplication { arguments, .. } = parsed.expression else {
            panic!("expected equality");
        };
        let SourceExpr::SyntaxApplication { syntax, arguments: wrapped, span } = &arguments[0]
        else {
            panic!("expected PROP");
        };
        assert_eq!(&source[syntax.span.start..syntax.span.end], "PROP");
        assert_eq!(&source[span.start..span.end], "PROP f x :: prop");
        let SourceExpr::TypeAscription { expression, .. } = &wrapped[0] else {
            panic!("expected operand ascription");
        };
        assert!(matches!(expression.as_ref(), SourceExpr::Application { .. }));
    }

    #[test]
    fn source_parser_typed_binder_and_unicode_spans_are_exact() {
        let source = " \"!!(α::'a). (P α :: prop)\" ";
        let parsed = parse(source).expect("typed binder");
        assert_eq!(&source[parsed.span.start..parsed.span.end], "!!(α::'a). (P α :: prop)");
        let SourceExpr::Binder { syntax, binders, body, .. } = parsed.expression else {
            panic!("expected binder")
        };
        assert_eq!(&source[syntax.span.start..syntax.span.end], "!!");
        assert_eq!(&source[binders[0].span.start..binders[0].span.end], "(α::'a)");
        let SourceType::Name { span, .. } = binders[0].typ.as_ref().expect("typed") else {
            panic!("expected name type")
        };
        assert_eq!(&source[span.start..span.end], "'a");
        assert_eq!(&source[body.span().start..body.span().end], "(P α :: prop)");
    }

    #[test]
    fn source_parser_pure_operator_spellings_preserve_byte_spans() {
        for (text, binder, imply, equal) in [
            ("⋀(x::prop). x ≡ x ⟹ x", "⋀", "⟹", "≡"),
            (
                r"\<And>(x::prop). x \<equiv> x \<Longrightarrow> x",
                r"\<And>",
                r"\<Longrightarrow>",
                r"\<equiv>",
            ),
        ] {
            let input = format!(" \"{text}\" ");
            let parsed = parse(&input).expect("complete Pure proposition");
            let SourceExpr::Binder { syntax, binders, body, .. } = parsed.expression else {
                panic!("expected binder");
            };
            assert_eq!(syntax.spelling.as_ref(), binder);
            assert_eq!(&input[syntax.span.start..syntax.span.end], binder);
            assert_eq!(&input[binders[0].span.start..binders[0].span.end], "(x::prop)");
            let SourceExpr::SyntaxApplication { syntax, arguments, .. } = *body else {
                panic!("expected implication");
            };
            assert_eq!(syntax.spelling.as_ref(), imply);
            assert_eq!(&input[syntax.span.start..syntax.span.end], imply);
            let SourceExpr::SyntaxApplication { syntax, .. } = &arguments[0] else {
                panic!("expected equality");
            };
            assert_eq!(syntax.spelling.as_ref(), equal);
            assert_eq!(&input[syntax.span.start..syntax.span.end], equal);
        }
    }

    #[test]
    fn source_parser_typed_lambda_spellings_preserve_byte_spans() {
        for spelling in ["λ", r"\<lambda>", "%"] {
            let input = format!("({spelling}(x::prop). x) A ≡ A");
            let parsed = parse(&input).expect("typed lambda proposition");
            let SourceExpr::SyntaxApplication { arguments, .. } = parsed.expression else {
                panic!("expected equality");
            };
            let SourceExpr::Application { function, .. } = &arguments[0] else {
                panic!("expected lambda application");
            };
            let SourceExpr::Group { inner, .. } = function.as_ref() else {
                panic!("expected grouped lambda");
            };
            let SourceExpr::Binder { syntax, binders, .. } = inner.as_ref() else {
                panic!("expected lambda binder");
            };
            assert_eq!(syntax.spelling.as_ref(), spelling);
            assert_eq!(&input[syntax.span.start..syntax.span.end], spelling);
            assert_eq!(&input[binders[0].span.start..binders[0].span.end], "(x::prop)");
        }
    }

    #[test]
    fn source_parser_alias_and_right_associativity_are_preserved() {
        let parsed = parse("True ==> A ==> B").expect("implication");
        let SourceExpr::SyntaxApplication { arguments, .. } = parsed.expression else {
            panic!("expected implication")
        };
        assert!(
            matches!(&arguments[0], SourceExpr::Name { name, .. } if name.spelling.as_ref() == "True")
        );
        assert!(
            matches!(&arguments[1], SourceExpr::SyntaxApplication { syntax, .. } if syntax.spelling.as_ref() == "==>")
        );
    }

    #[test]
    fn source_parser_adjacent_binder_period_is_not_a_qualified_name() {
        let source = "!!x.P x";
        let parsed = parse(source).expect("adjacent binder separator");
        let SourceExpr::Binder { binders, body, .. } = parsed.expression else {
            panic!("expected binder")
        };
        assert_eq!(&source[binders[0].span.start..binders[0].span.end], "x");
        assert_eq!(&source[body.span().start..body.span().end], "P x");
    }

    #[test]
    fn source_parser_grouped_type_preserves_name_and_outer_spans() {
        let source = "(f :: ('a => 'b) list) x";
        let parsed = parse(source).expect("ascribed function application");
        let SourceExpr::Application { function, .. } = parsed.expression else {
            panic!("expected application")
        };
        let SourceExpr::Group { inner, span } = *function else {
            panic!("expected grouped ascription")
        };
        assert_eq!(&source[span.start..span.end], "(f :: ('a => 'b) list)");
        let SourceExpr::TypeAscription {
            typ: SourceType::Application { arguments, span, .. }, ..
        } = *inner
        else {
            panic!("expected type application")
        };
        assert_eq!(&source[span.start..span.end], "('a => 'b) list");
        let SourceType::Arrow { from, to, .. } = &arguments[0] else {
            panic!("expected arrow type")
        };
        for (typ, expected) in [(from.as_ref(), "'a"), (to.as_ref(), "'b")] {
            let SourceType::Name { span, .. } = typ else { panic!("expected type variable") };
            assert_eq!(&source[span.start..span.end], expected);
        }
    }

    #[test]
    fn source_parser_incomplete_or_unknown_input_is_rejected() {
        for input in [
            "",
            "  ",
            "A ==>",
            "A ==",
            "!!x.",
            "!!.",
            "!!x P",
            "A)",
            "(A",
            "A B ::",
            "A :: 'a =>",
            "A :: (nat",
            "A == B == C",
            "True : {False}",
            "A + B",
            "A ; B",
            "A (* comment *)",
            "\"A",
            "A\"",
            "\"A\" B",
            "\"A\\\"B\"",
            "λx x",
            "if P then Q else R",
            r"!!x. x \<And",
            r"A \<equiv",
            r"A \<equiv>> A",
            r"A \<Longrightarrow",
            r"A \<Longrightarrow> ",
            r"\<And>(x::prop). x \<forall> x",
            r"\<lambda>(x::prop) x",
            r"A \<unknown> A",
            r#""A \q A""#,
            "A ≡",
            "A ⟹",
            "⋀(x::prop).",
            "ALL x. P x",
            "lemma A",
            "A and B",
        ] {
            assert!(parse(input).is_none(), "unexpected acceptance: {input:?}");
        }
    }

    #[test]
    fn source_parser_prop_missing_operand_or_reserved_binder_is_rejected() {
        for input in [
            "PROP",
            "PROP ==> P",
            "PROP == P",
            "PROP :: prop",
            "PROP (P",
            "PROP P )",
            "PROP PROP P",
            "!!PROP::prop. PROP PROP ==> PROP PROP",
        ] {
            assert!(parse(input).is_none(), "unexpected acceptance: {input:?}");
        }
    }

    #[test]
    fn source_parser_offset_is_applied_to_nested_spans() {
        let source = "prefix (P α)";
        let fragment_offset = "prefix ".len();
        let parsed = parse_source_proposition_at(
            &source[fragment_offset..],
            SourceId::new("whole.thy"),
            fragment_offset,
        )
        .expect("offset proposition");
        assert_eq!(&source[parsed.span.start..parsed.span.end], "(P α)");
        let SourceExpr::Group { inner, .. } = parsed.expression else {
            panic!("expected group");
        };
        assert_eq!(&source[inner.span().start..inner.span().end], "P α");
    }

    #[test]
    fn source_parser_oversized_application_is_rejected() {
        let source =
            std::iter::repeat_n("True", MAX_SOURCE_TOKENS + 1).collect::<Vec<_>>().join(" ");
        assert!(parse(&source).is_none());
    }

    #[test]
    fn source_parser_overflowing_offset_is_rejected() {
        assert!(
            parse_source_proposition_at("True", SourceId::new("overflow.thy"), usize::MAX,)
                .is_none()
        );
    }
}
