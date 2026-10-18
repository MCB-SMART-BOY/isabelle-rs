//! Isabelle term and type parser + pretty printer.

use std::sync::Arc;

use crate::{
    core::{
        term::Term,
        types::{Sort, Typ},
    },
    hol::hologic,
    isar::token::{Lexer, Token, TokenKind},
};

// The binder stack is outermost first; the last matching name is Bound(0).
struct P {
    tokens: Vec<Token>,
    pos: usize,
    binders: Vec<(Arc<str>, Typ)>,
}
impl P {
    fn new(tokens: Vec<Token>) -> Self {
        P { tokens, pos: 0, binders: Vec::new() }
    }
    fn kind(&self) -> Option<TokenKind> {
        self.tokens.get(self.pos).map(|t| t.kind.clone())
    }
    fn src(&self) -> Option<&str> {
        self.tokens.get(self.pos).map(|token| token.source.as_str())
    }
    fn is_kw(&self, kw: &str) -> bool {
        self.tokens.get(self.pos).is_some_and(|t| t.is_keyword(kw))
    }
    fn is_id(&self) -> bool {
        self.tokens.get(self.pos).is_some_and(|t| t.is_ident())
    }
    fn is_sym(&self, sym: &str) -> bool {
        self.tokens
            .get(self.pos)
            .is_some_and(|t| matches!(&t.kind, TokenKind::Symbol(value) if value.as_ref() == sym))
    }
    fn adv(&mut self) {
        self.pos += 1;
    }
    fn take_sym(&mut self, sym: &str) -> Option<()> {
        if !self.is_sym(sym) {
            return None;
        }
        self.adv();
        Some(())
    }
    fn parse_binder(&mut self) -> Option<(Arc<str>, Typ)> {
        if !self.is_id() {
            return None;
        }
        let name = Arc::from(self.src()?);
        self.adv();
        let typ = if self.is_sym("::") {
            self.adv();
            parse_typ(self)?
        } else {
            Typ::dummy()
        };
        Some((name, typ))
    }
    fn parse_scoped(&mut self, vars: &[(Arc<str>, Typ)]) -> Option<Term> {
        let previous = self.binders.len();
        self.binders.extend_from_slice(vars);
        let result = parse_trm(self);
        self.binders.truncate(previous);
        result
    }
}

pub fn parse_type(input: &str) -> Option<Typ> {
    let mut s = P::new(Lexer::new(input).tokenize_checked().ok()?);
    let typ = parse_typ(&mut s)?;
    matches!(s.kind(), Some(TokenKind::EOF)).then_some(typ)
}

/// Extended parse with TypeEnv for arity checking.
pub fn parse_type_with_env(input: &str, env: &crate::core::types::TypeEnv) -> Option<Typ> {
    let mut s = P::new(Lexer::new(input).tokenize_checked().ok()?);
    let typ = parse_typ_env(&mut s, env)?;
    (matches!(s.kind(), Some(TokenKind::EOF)) && is_well_formed_type(&typ, env)).then_some(typ)
}

fn parse_typ(s: &mut P) -> Option<Typ> {
    let env = crate::core::types::TypeEnv::new();
    let typ = parse_typ_env(s, &env)?;
    is_well_formed_type(&typ, &env).then_some(typ)
}

fn is_well_formed_type(typ: &Typ, env: &crate::core::types::TypeEnv) -> bool {
    match typ {
        Typ::Type { name, args } => {
            env.type_arity(name).is_none_or(|arity| arity == args.len())
                && args.iter().all(|arg| is_well_formed_type(arg, env))
        },
        Typ::TFree { .. } | Typ::TVar { .. } => true,
    }
}

fn parse_typ_env(s: &mut P, env: &crate::core::types::TypeEnv) -> Option<Typ> {
    let mut typ = parse_typ_atom(s, env)?;
    while matches!(s.kind(), Some(TokenKind::Ident | TokenKind::LongIdent)) {
        if env.type_arity(s.src()?) != Some(1) {
            break;
        }
        let name: Arc<str> = Arc::from(s.src()?);
        s.adv();
        typ = Typ::apply(name, vec![typ]);
    }
    if s.is_sym("=>") {
        s.adv();
        typ = Typ::arrow(typ, parse_typ_env(s, env)?);
    }
    Some(typ)
}

fn parse_typ_atom(s: &mut P, env: &crate::core::types::TypeEnv) -> Option<Typ> {
    match s.kind()? {
        TokenKind::TypeVar | TokenKind::SchematicTypeVar => {
            let name: Arc<str> = Arc::from(s.src()?);
            s.adv();
            if name.starts_with('?') {
                Some(Typ::var(name, 0, Sort::singleton("type")))
            } else {
                Some(Typ::free(name, Sort::singleton("type")))
            }
        },
        TokenKind::Ident | TokenKind::LongIdent => {
            let name: Arc<str> = Arc::from(s.src()?);
            s.adv();
            Some(Typ::base(name))
        },
        TokenKind::Symbol(symbol) if symbol.as_ref() == "(" => {
            s.adv();
            let typ = parse_typ_env(s, env)?;
            s.take_sym(")")?;
            Some(typ)
        },
        _ => None,
    }
}

thread_local! {
    static PARSE_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
const MAX_PARSE_DEPTH: usize = 200;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TermParseStatus {
    FullyConsumed,
    Incomplete,
}

pub fn parse_term(input: &str) -> Option<Term> {
    match parse_term_with_status(input)? {
        (term, TermParseStatus::FullyConsumed) => Some(term),
        (_, TermParseStatus::Incomplete) => None,
    }
}

pub(crate) fn parse_term_with_status(input: &str) -> Option<(Term, TermParseStatus)> {
    PARSE_DEPTH.with(|d| d.set(0));
    let mut s = P::new(Lexer::new(input).tokenize_checked().ok()?);
    let term = parse_trm(&mut s)?;
    let status = if matches!(s.kind(), Some(TokenKind::EOF)) {
        TermParseStatus::FullyConsumed
    } else {
        TermParseStatus::Incomplete
    };
    Some((term, status))
}

fn parse_trm(s: &mut P) -> Option<Term> {
    parse_trm_bounded(s, false)
}

/// Parse a term that stops at implication (=, &, | bind tighter than ==>)
fn parse_trm_no_imp(s: &mut P) -> Option<Term> {
    parse_trm_bounded(s, true)
}

fn parse_trm_bounded(s: &mut P, stop_at_imp: bool) -> Option<Term> {
    let depth = PARSE_DEPTH.with(|cell| {
        let depth = cell.get() + 1;
        cell.set(depth);
        depth
    });
    let result = if depth <= MAX_PARSE_DEPTH { parse_trm_flag(s, stop_at_imp) } else { None };
    PARSE_DEPTH.with(|cell| cell.set(cell.get() - 1));
    result
}

fn parse_trm_flag(s: &mut P, stop_at_imp: bool) -> Option<Term> {
    let mut head = parse_prefix(s)?;
    let mut has_annotation = false;
    loop {
        if stop_at_imp && (s.is_sym("==>") || s.is_sym("-->") || s.is_sym("\u{27f6}")) {
            break;
        }
        if s.is_sym("::") {
            if has_annotation {
                return None;
            }
            s.adv();
            head = annotate_term(head, parse_typ(s)?, &s.binders)?;
            has_annotation = true;
            continue;
        }
        if let Some(operator) = parse_operator(s) {
            let rhs = if operator == "=" { parse_trm_no_imp(s)? } else { parse_trm(s)? };
            head = apply_operator(operator, head, rhs);
            if operator != "=" {
                return Some(head);
            }
            has_annotation = false;
            continue;
        }
        if s.is_sym("(")
            || s.is_sym("[")
            || s.is_sym("{")
            || s.is_id()
            || matches!(s.kind(), Some(TokenKind::Number))
        {
            head = Term::app(head, parse_atom(s)?);
            continue;
        }
        break;
    }
    Some(head)
}

fn parse_prefix(s: &mut P) -> Option<Term> {
    let quant = parse_quantifier_name(s);
    if let Some(name) = quant {
        s.adv();
        return parse_quant(s, name);
    }
    if s.is_sym("%") || s.is_sym("λ") {
        s.adv();
        let mut vars = vec![s.parse_binder()?];
        while s.is_id() {
            vars.push(s.parse_binder()?);
        }
        s.take_sym(".")?;
        let body = s.parse_scoped(&vars)?;
        return Some(vars.into_iter().rfold(body, |body, (name, typ)| Term::abs(name, typ, body)));
    }
    if s.is_sym("[|") {
        s.adv();
        let mut premises = vec![parse_trm(s)?];
        while matches!(s.kind(), Some(TokenKind::Semicolon)) {
            s.adv();
            premises.push(parse_trm(s)?);
        }
        s.take_sym("|]")?;
        if !(s.is_sym("==>") || s.is_sym("-->")) {
            return None;
        }
        s.adv();
        let conclusion = parse_trm(s)?;
        return Some(
            premises
                .into_iter()
                .rfold(conclusion, |body, premise| make_binary("Pure.imp", premise, body)),
        );
    }
    let prefix = if s.is_sym("~") || s.is_sym("\\<not>") || s.is_sym("¬") {
        Some(hologic::not_const())
    } else if s.is_sym("-") {
        Some(hologic::uminus_const(Typ::dummy()))
    } else if s.is_sym("\\<Sqinter>") {
        Some(hologic::Inf_const(Typ::dummy()))
    } else if s.is_sym("\\<Squnion>") {
        Some(hologic::Sup_const(Typ::dummy()))
    } else {
        None
    };
    if let Some(func) = prefix {
        s.adv();
        return Some(Term::app(func, parse_trm(s)?));
    }
    parse_atom(s)
}

fn parse_quantifier_name(s: &P) -> Option<&'static str> {
    if s.is_kw("ALL") || s.is_sym("!") {
        Some("HOL.All")
    } else if s.is_kw("EX") || s.is_sym("?") {
        Some("HOL.Ex")
    } else if s.is_sym("!!") {
        Some("Pure.all")
    } else if s.is_id() && s.src()? == "EX1" {
        Some("HOL.Ex1")
    } else if s.is_id() && s.src()? == "THE" {
        Some("HOL.The")
    } else if s.is_id() && s.src()? == "SOME" {
        Some("HOL.Eps")
    } else {
        None
    }
}

fn annotate_term(mut term: Term, typ: Typ, binders: &[(Arc<str>, Typ)]) -> Option<Term> {
    match &mut term {
        Term::Const { typ: current, .. }
        | Term::Free { typ: current, .. }
        | Term::Var { typ: current, .. } => {
            if !current.is_dummy() && *current != typ {
                return None;
            }
            *current = typ;
        },
        Term::Bound(index)
            if binders.iter().rev().nth(*index).is_some_and(|(_, bound_typ)| bound_typ == &typ) => {
        },
        _ => return None,
    }
    Some(term)
}

fn parse_operator(s: &mut P) -> Option<&'static str> {
    let op = match s.src()? {
        "==>" | "-->" | "⟶" => "Pure.imp",
        "&&&" | "&" | "∧" => "conj",
        "|||" | "|" | "∨" => "disj",
        "~=" => "neq",
        "=" => "=",
        "@" | "APPEND" => "HOL.append",
        "<" => "HOL.less",
        "`" => "HOL.image",
        "#" => "HOL.Cons",
        "\\<in>" => "HOL.member",
        "\\<notin>" => "HOL.NotMember",
        "\\<le>" => "HOL.ordLessEq",
        "\\<ge>" => "HOL.ordGreaterEq",
        "\\<subseteq>" => "HOL.subsetEq",
        "\\<inter>" => "HOL.inter",
        "\\<union>" => "HOL.union",
        "+" => "HOL.plus",
        "-" => "HOL.minus",
        "IFF" => "iff",
        _ => return None,
    };
    s.adv();
    Some(op)
}

fn apply_operator(operator: &str, lhs: Term, rhs: Term) -> Term {
    match operator {
        "=" | "iff" => hologic::mk_eq(lhs, rhs),
        "neq" => Term::app(hologic::not_const(), hologic::mk_eq(lhs, rhs)),
        "conj" => hologic::mk_conj(lhs, rhs),
        "disj" => hologic::mk_disj(lhs, rhs),
        name => make_binary(name, lhs, rhs),
    }
}

fn parse_quant(s: &mut P, qname: &str) -> Option<Term> {
    let mut vars = vec![s.parse_binder()?];
    while s.is_id() {
        vars.push(s.parse_binder()?);
    }
    // Bounded quantifiers need a separate representation of their domain.
    s.take_sym(".")?;
    let body = s.parse_scoped(&vars)?;
    Some(vars.into_iter().rfold(body, |body, (name, typ)| {
        let predicate_result = Typ::base(if qname == "Pure.all" { "prop" } else { "bool" });
        let result = if matches!(qname, "HOL.The" | "HOL.Eps") {
            typ.clone()
        } else {
            predicate_result.clone()
        };
        let qt = Typ::arrow(Typ::arrow(typ.clone(), predicate_result), result);
        Term::app(Term::const_(qname, qt), Term::abs(name, typ, body))
    }))
}

fn make_binary(conn: &str, a: Term, b: Term) -> Term {
    let p = Typ::base("prop");
    let ct = Typ::arrow(p.clone(), Typ::arrow(p.clone(), p));
    Term::app(Term::app(Term::const_(conn, ct), a), b)
}

fn parse_atom(s: &mut P) -> Option<Term> {
    if s.is_kw("if") {
        return parse_if(s);
    }
    if s.is_sym("[") {
        return parse_list(s);
    }
    if s.is_sym("{") {
        return parse_set(s);
    }
    if s.is_sym("(") {
        return parse_parenthesized(s);
    }
    match s.kind()? {
        TokenKind::Ident | TokenKind::LongIdent => {
            let src = s.src()?;
            let term = if let Some(index) =
                s.binders.iter().rev().position(|(name, _)| name.as_ref() == src)
            {
                Term::bound(index)
            } else if src == "True" || src == "HOL.True" {
                hologic::true_const()
            } else {
                Term::free(src, Typ::dummy())
            };
            s.adv();
            Some(term)
        },
        TokenKind::Number => {
            let term = Term::const_(s.src()?, Typ::base("nat"));
            s.adv();
            Some(term)
        },
        TokenKind::Symbol(symbol) => {
            let term = match symbol.as_ref() {
                "\\<nat>" => hologic::nat_set_const(),
                "\\<top>" => hologic::top_const(Typ::dummy()),
                "\\<bottom>" => hologic::bot_const(Typ::dummy()),
                _ => return None,
            };
            s.adv();
            Some(term)
        },
        // Command-level syntax strips a complete quote before invoking this parser.
        TokenKind::String => None,
        _ => None,
    }
}

fn parse_if(s: &mut P) -> Option<Term> {
    s.adv();
    let cond = parse_trm(s)?;
    if !s.is_kw("then") {
        return None;
    }
    s.adv();
    let then_branch = parse_trm(s)?;
    if !s.is_kw("else") {
        return None;
    }
    s.adv();
    let else_branch = parse_trm(s)?;
    Some(Term::apps(hologic::if_const(Typ::dummy()), [cond, then_branch, else_branch]))
}

fn parse_parenthesized(s: &mut P) -> Option<Term> {
    s.take_sym("(")?;
    let is_section = matches!(s.kind(), Some(TokenKind::Symbol(_)))
        && matches!(
            s.src()?,
            "=" | "~="
                | "<"
                | ">"
                | "#"
                | "@"
                | "&"
                | "|"
                | "+"
                | "\\<in>"
                | "\\<notin>"
                | "\\<le>"
                | "\\<ge>"
                | "\\<subseteq>"
                | "\\<inter>"
                | "\\<union>"
        );
    let term = if is_section {
        let op = Term::free(s.src()?, Typ::dummy());
        s.adv();
        if s.is_sym(")") { op } else { Term::app(op, parse_trm(s)?) }
    } else {
        parse_trm(s)?
    };
    s.take_sym(")")?;
    Some(term)
}

fn parse_list(s: &mut P) -> Option<Term> {
    s.take_sym("[")?;
    let mut elems = Vec::new();
    if !s.is_sym("]") {
        elems.push(parse_trm(s)?);
        while s.is_sym(",") {
            s.adv();
            elems.push(parse_trm(s)?);
        }
    }
    s.take_sym("]")?;
    let cons = hologic::cons_const(Typ::dummy());
    Some(elems.into_iter().rfold(hologic::nil_const(Typ::dummy()), |rest, elem| {
        Term::apps(cons.clone(), [elem, rest])
    }))
}

fn parse_set(s: &mut P) -> Option<Term> {
    s.take_sym("{")?;
    if s.is_sym("}") {
        s.adv();
        return Some(hologic::empty_set_const(Typ::dummy()));
    }
    if s.is_sym(".") {
        parse_range_mark(s)?;
        let upper = if s.is_sym("}") { None } else { Some(parse_trm(s)?) };
        s.take_sym("}")?;
        return Some(upper.map_or_else(hologic::set_range_const, |term| {
            Term::app(hologic::set_range_const(), term)
        }));
    }
    if s.is_id() {
        let start = s.pos;
        let binder = s.parse_binder()?;
        let is_comprehension = s.is_sym("|")
            || (s.is_sym(".") && !s.tokens.get(s.pos + 1)
                .is_some_and(|token| matches!(&token.kind, TokenKind::Symbol(symbol) if symbol.as_ref() == ".")));
        if is_comprehension {
            s.adv();
            let body = s.parse_scoped(std::slice::from_ref(&binder))?;
            s.take_sym("}")?;
            return Some(Term::app(
                hologic::collect_const(binder.1.clone()),
                Term::abs(binder.0, binder.1, body),
            ));
        }
        s.pos = start;
    }
    let first = parse_trm(s)?;
    if s.is_sym(".") {
        parse_range_mark(s)?;
        let upper = if s.is_sym("}") { None } else { Some(parse_trm(s)?) };
        s.take_sym("}")?;
        let range = Term::app(hologic::set_range_const(), first);
        return Some(match upper {
            Some(term) => Term::app(range, term),
            None => range,
        });
    }
    let mut elems = vec![first];
    while s.is_sym(",") {
        s.adv();
        elems.push(parse_trm(s)?);
    }
    s.take_sym("}")?;
    let insert = hologic::insert_const(Typ::dummy());
    Some(elems.into_iter().rfold(hologic::empty_set_const(Typ::dummy()), |rest, elem| {
        Term::apps(insert.clone(), [elem, rest])
    }))
}

fn parse_range_mark(s: &mut P) -> Option<()> {
    s.take_sym(".")?;
    s.take_sym(".")?;
    if s.is_sym("<") {
        s.adv();
    }
    Some(())
}

// Pretty printer
pub fn print_type(typ: &Typ) -> String {
    match typ {
        Typ::Type { name, args } if args.is_empty() => name.to_string(),
        Typ::Type { name, args } if name.as_ref() == "fun" && args.len() == 2 => {
            format!("{} => {}", print_type(&args[0]), print_type(&args[1]))
        },
        Typ::Type { name, .. } => name.to_string(),
        Typ::TFree { name, .. } => format!("'{name}"),
        Typ::TVar { name, index, .. } => format!("?'{name}.{index}"),
    }
}

pub fn print_term(term: &Term) -> String {
    match term {
        Term::Const { name, .. } | Term::Free { name, .. } => name.to_string(),
        Term::Var { name, index, .. } => format!("?{name}.{index}"),
        Term::Bound(i) => format!("B_{i}"),
        Term::Abs { name, typ, body } => {
            if typ.is_dummy() {
                format!("%{name}. {}", print_term(body))
            } else {
                format!("%{name}::{} . {}", print_type(typ), print_term(body))
            }
        },
        Term::App { func, arg } => format!("({} {})", print_term(func), print_term(arg)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_type_simple() {
        assert_eq!(parse_type("nat"), Some(Typ::base("nat")));
    }

    #[test]
    fn test_parse_type_fun() {
        let t = parse_type("nat => bool").unwrap();
        assert_eq!(t, Typ::arrow(Typ::base("nat"), Typ::base("bool")));
    }

    #[test]
    fn parse_term_juxtaposition_builds_application() {
        assert_eq!(
            parse_term("f x"),
            Some(Term::app(Term::free("f", Typ::dummy()), Term::free("x", Typ::dummy())))
        );
    }

    #[test]
    fn parse_term_lambda_binds_nearest_variable() {
        assert_eq!(parse_term("%x. x"), Some(Term::abs("x", Typ::dummy(), Term::bound(0))));
        assert_eq!(
            parse_term("%x. %x. x"),
            Some(Term::abs("x", Typ::dummy(), Term::abs("x", Typ::dummy(), Term::bound(0))))
        );
        assert_eq!(
            parse_term("%x. %y. x"),
            Some(Term::abs("x", Typ::dummy(), Term::abs("y", Typ::dummy(), Term::bound(1))))
        );
        assert_eq!(
            parse_term("%x. y"),
            Some(Term::abs("x", Typ::dummy(), Term::free("y", Typ::dummy())))
        );
    }

    #[test]
    fn parse_term_parenthesized_application_preserves_following_tokens() {
        let function = Term::free("f", Typ::dummy());
        let argument = Term::free("x", Typ::dummy());
        let application = Term::app(function, argument);
        assert_eq!(
            parse_term("f (x) = y"),
            Some(hologic::mk_eq(application.clone(), Term::free("y", Typ::dummy())))
        );
        assert_eq!(
            parse_term("f (x) y"),
            Some(Term::app(application, Term::free("y", Typ::dummy())))
        );
    }

    #[test]
    fn parse_term_quantifier_and_comprehension_bind_and_preserve_types() {
        let quantified = parse_term("ALL x. P x").expect("quantifier must parse");
        assert!(matches!(&quantified,
            Term::App { func, arg }
                if matches!(func.as_ref(), Term::Const { name, .. } if name.as_ref() == "HOL.All")
                    && matches!(arg.as_ref(), Term::Abs { name, body, .. }
                        if name.as_ref() == "x" && matches!(body.as_ref(),
                            Term::App { func, arg }
                                if matches!(func.as_ref(), Term::Free { name, .. } if name.as_ref() == "P")
                                    && matches!(arg.as_ref(), Term::Bound(0))))
        ));
        assert_eq!(
            parse_term("%x::nat. x"),
            Some(Term::abs("x", Typ::base("nat"), Term::bound(0)))
        );
        assert_eq!(
            parse_term("%x::prop. x"),
            Some(Term::abs("x", Typ::base("prop"), Term::bound(0)))
        );
        assert_eq!(
            parse_term("%x::nat. x::nat"),
            Some(Term::abs("x", Typ::base("nat"), Term::bound(0)))
        );
        assert!(matches!(parse_term("{x::nat. P x}"),
            Some(Term::App { func, arg })
                if matches!(func.as_ref(), Term::Const { name, .. } if name.as_ref() == "Set.Collect")
                    && matches!(arg.as_ref(), Term::Abs { name, typ, body }
                        if name.as_ref() == "x" && typ == &Typ::base("nat")
                            && matches!(body.as_ref(), Term::App { arg, .. }
                                if matches!(arg.as_ref(), Term::Bound(0))))
        ));
    }

    #[test]
    fn parse_term_malformed_operands_and_delimiters_are_rejected() {
        for source in [
            "f (x",
            "(x",
            "f (x = )",
            "f (x) =",
            "True ==>",
            "~",
            "-",
            "[x",
            "[x,]",
            "f [x",
            "{x. P x",
            "{x y. P x}",
            "{x,}",
            "{x..y",
            "{x.}",
            "%x x",
            "% . x",
            "ALL x P x",
            "x ::",
            "(x :: nat",
            "x :: (nat",
            "x :: nat garbage :",
            "x :: nat :: bool",
            "%x::nat. x::bool",
            "(+ x",
            "\"malformed ==\"",
            "x ; y",
            "x : {y}",
            "x (* unfinished",
        ] {
            assert!(parse_term(source).is_none(), "accepted malformed input: {source}");
        }
    }

    #[test]
    fn parse_term_nested_comments_do_not_discard_valid_source() {
        assert_eq!(
            parse_term("x (* outer (* inner *) outer *)"),
            Some(Term::free("x", Typ::dummy()))
        );
    }

    #[test]
    fn parse_type_incomplete_annotation_and_suffix_are_rejected() {
        let mut env = crate::core::types::TypeEnv::new();
        env.declare_type("list", 1);
        for source in
            ["(nat", "(nat => bool", "nat =>", "nat extra", "nat : bool", "\"nat\"", "fun"]
        {
            assert!(parse_type(source).is_none(), "accepted malformed type: {source}");
            assert!(parse_type_with_env(source, &env).is_none(), "accepted env type: {source}");
        }
        assert!(parse_type_with_env("list", &env).is_none());
        assert_eq!(
            parse_type("(nat => bool)"),
            Some(Typ::arrow(Typ::base("nat"), Typ::base("bool")))
        );
        assert_eq!(
            parse_type_with_env("'a list", &env),
            Some(Typ::apply("list", vec![Typ::free("'a", Sort::singleton("type"))]))
        );
    }

    #[test]
    fn test_parse_true_aliases_as_typed_hol_constant() {
        for alias in ["True", "HOL.True"] {
            assert_eq!(parse_term(alias), Some(hologic::true_const()));
            assert_eq!(parse_term(&format!("{alias} :: bool")), Some(hologic::true_const()));
        }
    }

    #[test]
    fn parse_term_conflicting_constant_annotation_is_rejected() {
        for (alias, explicit_type) in [("True", "nat"), ("HOL.True", "prop")] {
            assert!(parse_term(&format!("{alias} :: {explicit_type}")).is_none());
        }
    }

    #[test]
    fn test_parse_true_annotation_does_not_swallow_following_equality() {
        let parsed = parse_term("True :: bool = False").expect("annotated equality should parse");

        assert_ne!(parsed, hologic::true_const());
        assert!(hologic::dest_hol_equals(&parsed).is_some());
    }

    #[test]
    fn test_parse_term_reports_unconsumed_true_suffix() {
        for source in ["True", "HOL.True :: bool"] {
            let (parsed, status) =
                parse_term_with_status(source).expect("complete True source should parse");
            assert_eq!(parsed, hologic::true_const());
            assert_eq!(status, TermParseStatus::FullyConsumed);
        }

        let (parsed, status) = parse_term_with_status("True : {False}")
            .expect("legacy parser should retain its prefix parse");
        assert_eq!(parsed, hologic::true_const());
        assert_eq!(status, TermParseStatus::Incomplete);
        assert_eq!(parse_term("True : {False}"), None);
    }

    #[test]
    fn test_pretty_print() {
        let t = Term::abs("x", Typ::dummy(), Term::bound(0));
        assert_eq!(print_term(&t), "%x. B_0");
    }
}
