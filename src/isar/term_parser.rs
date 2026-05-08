//! Isabelle term and type parser + pretty printer.

use crate::core::term::Term;
use crate::core::types::{Sort, Typ};
use crate::isar::token::{Token, TokenKind, Lexer};
use std::sync::Arc;

// Parser state with clone-based peek to avoid borrow issues
struct P {
    tokens: Vec<Token>,
    pos: usize,
}
impl P {
    fn new(t: Vec<Token>) -> Self { P { tokens: t, pos: 0 } }
    fn kind(&self) -> Option<TokenKind> { self.tokens.get(self.pos).map(|t| t.kind.clone()) }
    fn src(&self) -> Option<String> { self.tokens.get(self.pos).map(|t| t.source.clone()) }
    fn is_kw(&self, kw: &str) -> bool { self.tokens.get(self.pos).map_or(false, |t| t.is_keyword(kw)) }
    fn is_id(&self) -> bool { self.tokens.get(self.pos).map_or(false, |t| t.is_ident()) }
    fn is_sym(&self, s: &str) -> bool { self.tokens.get(self.pos).map_or(false, |t| matches!(&t.kind, TokenKind::Symbol(x) if x.as_ref() == s)) }
    fn adv(&mut self) { self.pos += 1; }
}

pub fn parse_type(input: &str) -> Option<Typ> {
    let mut s = P::new(Lexer::new(input).tokenize());
    parse_typ(&mut s)
}

fn parse_typ(s: &mut P) -> Option<Typ> {
    let t1 = parse_typ_atom(s)?;
    if s.is_sym("=>") { s.adv(); let t2 = parse_typ(s)?; return Some(Typ::arrow(t1, t2)); }
    Some(t1)
}

fn parse_typ_atom(s: &mut P) -> Option<Typ> {
    match &s.kind()? {
        TokenKind::TypeVar | TokenKind::SchematicTypeVar => {
            let name = Arc::from(s.src()?.as_str()); s.adv();
            Some(Typ::free(name, Sort::singleton("type")))
        }
        TokenKind::Ident | TokenKind::LongIdent => {
            let name = Arc::from(s.src()?.as_str()); s.adv();
            Some(Typ::Type { name, args: vec![] })
        }
        TokenKind::Symbol(x) if x.as_ref() == "(" => {
            s.adv(); let t = parse_typ(s)?; s.is_sym(")"); s.adv(); Some(t)
        }
        _ => None,
    }
}

pub fn parse_term(input: &str) -> Option<Term> {
    let mut s = P::new(Lexer::new(input).tokenize());
    parse_trm(&mut s)
}

fn parse_trm(s: &mut P) -> Option<Term> {
    // Quantifiers: ALL x. P / EX x. P
    if s.is_kw("ALL") || s.is_sym("!") { s.adv(); return parse_quant(s, "HOL.All"); }
    if s.is_kw("EX") || s.is_sym("?") { s.adv(); return parse_quant(s, "HOL.Ex"); }
    // Lambda: %x. body
    if s.is_sym("%") || s.is_sym("λ") { s.adv();
        let mut vars = vec![];
        while s.is_id() {
            let name = Arc::from(s.src()?.as_str()); s.adv();
            let typ = Typ::dummy();
            vars.push((name, typ));
        }
        if s.is_sym(".") { s.adv(); }
        let body = parse_trm(s)?;
        return Some(vars.into_iter().rfold(body, |b, (n, t)| Term::abs(n, t, b)));
    }
    // Application: head arg1 arg2 ...
    // [| A; B |] ==> C  — bracketed premises
    if s.is_sym("[|") {
        s.adv();
        let mut prems = vec![];
        loop {
            let p = parse_trm(s)?;
            prems.push(p);
            if s.is_sym("|]") { s.adv(); break; }
            if matches!(s.kind(), Some(TokenKind::Semicolon)) { s.adv(); continue; }
            break;
        }
        if s.is_sym("==>") || s.is_sym("-->") {
            s.adv();
            let concl = parse_trm(s)?;
            let mut result = concl;
            for p in prems.into_iter().rev() {
                result = make_binary("Pure.imp", p, result);
            }
            return Some(result);
        }
        return None;
    }
    let mut head = parse_atom(s)?;
    loop {
        if s.is_sym("(") { s.adv(); let a = parse_trm(s)?; s.is_sym(")"); s.adv(); head = Term::app(head, a); continue; }
        if s.is_sym("==>") || s.is_sym("-->") || s.is_sym("⟶") {
            s.adv(); let rhs = parse_trm(s)?;
            head = make_binary("Pure.imp", head, rhs);
            return Some(head);
        }
        if s.is_sym("&&&") || s.is_sym("&") || s.is_sym("∧") {
            s.adv(); let rhs = parse_trm(s)?;
            head = make_binary("HOL.conj", head, rhs);
            return Some(head);
        }
        if s.is_sym("|||") || s.is_sym("|") || s.is_sym("∨") {
            s.adv(); let rhs = parse_trm(s)?;
            head = make_binary("HOL.disj", head, rhs);
            return Some(head);
        }
        if s.is_sym("~") || s.is_sym("¬") {
            let not_const = Term::const_("HOL.Not", Typ::arrow(Typ::base("prop"), Typ::base("prop")));
            head = Term::app(not_const, head);
            break;
        }
        if s.is_sym("~=") {
        if s.is_sym("=") {
            s.adv(); let rhs = parse_trm(s)?;
            head = make_binary("HOL.eq", head, rhs);
            return Some(head);
        }
            s.adv(); let rhs = parse_trm(s)?;
            head = make_binary("HOL.eq", head, rhs);
            let not_const = Term::const_("HOL.Not", Typ::arrow(Typ::base("prop"), Typ::base("prop")));
            head = Term::app(not_const, head);
            return Some(head);
        }
        if s.is_id() || matches!(s.kind(), Some(TokenKind::String | TokenKind::Number)) {
            if let Some(a) = parse_atom(s) { head = Term::app(head, a); continue; }
        }
        break;
    }
    Some(head)
}

fn parse_quant(s: &mut P, qname: &str) -> Option<Term> {
    let mut vars = vec![];
    while s.is_id() { let n = Arc::from(s.src()?.as_str()); s.adv(); vars.push((n, Typ::dummy())); }
    if s.is_sym(".") { s.adv(); }
    let body = parse_trm(s)?;
    let inner = vars.into_iter().rfold(body, |b,(n,t)| Term::abs(n,t,b));
    let prop = Typ::base("prop");
    let qt = Typ::arrow(Typ::arrow(Typ::dummy(), prop.clone()), prop);
    Some(Term::app(Term::const_(qname, qt), inner))
}

fn make_binary(conn: &str, a: Term, b: Term) -> Term {
    let p = Typ::base("prop");
    let ct = Typ::arrow(p.clone(), Typ::arrow(p.clone(), p));
    Term::app(Term::app(Term::const_(conn, ct), a), b)
}

fn parse_atom(s: &mut P) -> Option<Term> {
    let kind = s.kind()?;
    let src = s.src()?;
    match &kind {
        TokenKind::Ident | TokenKind::LongIdent => { s.adv(); Some(Term::free(Arc::from(src.as_str()), Typ::dummy())) }
        TokenKind::String => { s.adv(); Some(Term::const_(&src[1..src.len()-1], Typ::base("prop"))) }
        TokenKind::Number => { s.adv(); Some(Term::const_(src, Typ::base("nat"))) }
        TokenKind::Symbol(x) if x.as_ref() == "(" => { s.adv(); let t = parse_trm(s)?; s.is_sym(")"); s.adv(); Some(t) }
        _ => None,
    }
}

// Pretty printer
pub fn print_type(typ: &Typ) -> String {
    match typ {
        Typ::Type { name, args } if args.is_empty() => name.to_string(),
        Typ::Type { name, args } if name.as_ref() == "fun" && args.len() == 2 =>
            format!("{} => {}", print_type(&args[0]), print_type(&args[1])),
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
            if typ.is_dummy() { format!("%{name}. {}", print_term(body)) }
            else { format!("%{name}::{} . {}", print_type(typ), print_term(body)) }
        }
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
    fn test_parse_term_app() {
        let t = parse_term("f x").unwrap();
        assert!(matches!(t, Term::App { .. }));
    }

    #[test]
    fn test_parse_term_lambda() {
        let t = parse_term("%x. x").unwrap();
        assert!(matches!(t, Term::Abs { .. }));
    }

    #[test]
    fn test_pretty_print() {
        let t = Term::abs("x", Typ::dummy(), Term::bound(0));
        assert_eq!(print_term(&t), "%x. B_0");
    }
}

    #[test]
    fn test_parse_bracket() {
        let t = parse_term("[| A; B |] ==> C").unwrap();
        assert!(matches!(t, Term::App { .. }));
    }

    #[test]
    fn test_parse_inequality() {
        let t = parse_term("A ~= B").unwrap();
        assert!(matches!(t, Term::App { .. }));
    }
