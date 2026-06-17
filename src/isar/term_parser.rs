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

// Parser state with clone-based peek to avoid borrow issues
struct P {
    tokens: Vec<Token>,
    pos: usize,
}
impl P {
    fn new(t: Vec<Token>) -> Self {
        P { tokens: t, pos: 0 }
    }
    fn kind(&self) -> Option<TokenKind> {
        self.tokens.get(self.pos).map(|t| t.kind.clone())
    }
    fn src(&self) -> Option<String> {
        self.tokens.get(self.pos).map(|t| t.source.clone())
    }
    fn is_kw(&self, kw: &str) -> bool {
        self.tokens.get(self.pos).is_some_and(|t| t.is_keyword(kw))
    }
    fn is_id(&self) -> bool {
        self.tokens.get(self.pos).is_some_and(|t| t.is_ident())
    }
    fn is_sym(&self, s: &str) -> bool {
        self.tokens
            .get(self.pos)
            .is_some_and(|t| matches!(&t.kind, TokenKind::Symbol(x) if x.as_ref() == s))
    }
    fn adv(&mut self) {
        self.pos += 1;
    }
}

pub fn parse_type(input: &str) -> Option<Typ> {
    let mut s = P::new(Lexer::new(input).tokenize());
    parse_typ(&mut s)
}

/// Extended parse with TypeEnv for arity checking.
pub fn parse_type_with_env(input: &str, env: &crate::core::types::TypeEnv) -> Option<Typ> {
    let mut s = P::new(Lexer::new(input).tokenize());
    parse_typ_env(&mut s, env)
}

fn parse_typ(s: &mut P) -> Option<Typ> {
    parse_typ_env(s, &crate::core::types::TypeEnv::new())
}

fn parse_typ_env(s: &mut P, env: &crate::core::types::TypeEnv) -> Option<Typ> {
    let mut t = parse_typ_atom(s)?;
    // Postfix type application: 'a list  →  Type("list", ['a])
    // Keep applying while the next token is a type identifier
    loop {
        match s.kind() {
            Some(TokenKind::Ident) | Some(TokenKind::LongIdent) => {
                let name: Arc<str> = Arc::from(s.src()?.as_str());
                // Check if this is a known type constructor (has arity > 0)
                let arity = env.type_arity(&name).unwrap_or(0);
                if arity > 0 {
                    s.adv();
                    // Collect the required number of arguments (already parsed as 't')
                    // For postfix: 'a list → list('a), so t is the arg
                    let args = vec![t];
                    // If arity > 1, collect more args from the left side
                    // (e.g., ('a, 'b) map → map('a, 'b) — not standard but possible)
                    t = Typ::Type { name, args };
                } else if arity == 0 {
                    // Not a type constructor — stop
                    break;
                } else {
                    // Unknown arity — assume 0 and skip
                    break;
                }
            },
            Some(TokenKind::Symbol(ref x)) if x.as_ref() == "=>" => {
                s.adv();
                let t2 = parse_typ_env(s, env)?;
                return Some(Typ::arrow(t, t2));
            },
            _ => break,
        }
    }
    Some(t)
}

fn parse_typ_atom(s: &mut P) -> Option<Typ> {
    match &s.kind()? {
        TokenKind::TypeVar => {
            let name: Arc<str> = Arc::from(s.src()?.as_str());
            s.adv();
            // 'a → TFree, ?'a → TVar
            if name.starts_with('?') {
                Some(Typ::var(name, 0, Sort::singleton("type")))
            } else {
                Some(Typ::free(name, Sort::singleton("type")))
            }
        },
        TokenKind::SchematicTypeVar => {
            let name: Arc<str> = Arc::from(s.src()?.as_str());
            s.adv();
            Some(Typ::var(name, 0, Sort::singleton("type")))
        },
        TokenKind::Ident | TokenKind::LongIdent => {
            let name: Arc<str> = Arc::from(s.src()?.as_str());
            s.adv();
            Some(Typ::Type { name, args: vec![] })
        },
        TokenKind::Symbol(x) if x.as_ref() == "(" => {
            s.adv();
            let t = parse_typ(s)?;
            s.is_sym(")");
            s.adv();
            Some(t)
        },
        _ => None,
    }
}

thread_local! {
    static PARSE_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
const MAX_PARSE_DEPTH: usize = 200;

pub fn parse_term(input: &str) -> Option<Term> {
    PARSE_DEPTH.with(|d| d.set(0));
    let mut s = P::new(Lexer::new(input).tokenize());
    parse_trm(&mut s)
}

fn parse_trm(s: &mut P) -> Option<Term> {
    let depth = PARSE_DEPTH.with(|d| {
        let v = d.get() + 1;
        d.set(v);
        v
    });
    if depth > MAX_PARSE_DEPTH {
        return None;
    }
    let result = parse_trm_flag(s, false);
    PARSE_DEPTH.with(|d| d.set(d.get() - 1));
    result
}

/// Parse a term that stops at implication (=, &, | bind tighter than ==>)
fn parse_trm_no_imp(s: &mut P) -> Option<Term> {
    parse_trm_flag(s, true)
}

fn parse_trm_flag(s: &mut P, stop_at_imp: bool) -> Option<Term> {
    // Quantifiers: ALL x. P / EX x. P / !!x. P (Pure.all)
    if s.is_kw("ALL") || s.is_sym("!") {
        s.adv();
        return parse_quant(s, "HOL.All");
    }
    if s.is_kw("EX") || s.is_sym("?") {
        s.adv();
        return parse_quant(s, "HOL.Ex");
    }
    if s.is_sym("!!") {
        s.adv();
        return parse_quant(s, "Pure.all");
    }
    if s.is_kw("EX1") {
        s.adv();
        return parse_quant(s, "HOL.Ex1");
    }
    if s.is_kw("THE") {
        s.adv();
        return parse_quant(s, "HOL.The");
    }
    if s.is_kw("SOME") {
        s.adv();
        return parse_quant(s, "HOL.Eps");
    }
    // Lambda: %x. body
    if s.is_sym("%") || s.is_sym("λ") {
        s.adv();
        let mut vars = vec![];
        while s.is_id() {
            let name = Arc::from(s.src()?.as_str());
            s.adv();
            let typ = Typ::dummy();
            vars.push((name, typ));
        }
        if s.is_sym(".") {
            s.adv();
        }
        let body = parse_trm(s)?;
        return Some(vars.into_iter().rfold(body, |b, (n, t)| Term::abs(n, t, b)));
    }
    // Set comprehension: {x. P x} or {x | P x}
    if s.is_sym("{") {
        s.adv();
        // Collect bound variables before . or |
        let mut vars = vec![];
        while s.is_id() {
            let name = Arc::from(s.src()?.as_str());
            s.adv();
            vars.push(name);
            // Check for type annotation: x :: 'a
            if s.is_sym("::") {
                s.adv();
                let _typ = parse_typ(s).unwrap_or(Typ::dummy());
            }
        }
        // Separator: . or |
        if s.is_sym(".") || s.is_sym("|") {
            s.adv();
        }
        // Parse the body predicate
        let body = parse_trm(s)?;
        // Expect closing }
        if s.is_sym("}") {
            s.adv();
        }
        // Build: Collect(P) where P = λvars. body
        let set_const = Term::const_(
            "HOL.Collect",
            Typ::arrow(Typ::arrow(Typ::dummy(), Typ::base("bool")), Typ::base("set")),
        );
        let abs_body = vars.into_iter().rfold(body, |b, n| Term::abs(n, Typ::dummy(), b));
        return Some(Term::app(set_const, abs_body));
    }
    // Application: head arg1 arg2 ...
    // [| A; B |] ==> C  — bracketed premises
    if s.is_sym("[|") {
        s.adv();
        let mut prems = vec![];
        loop {
            if let Some(p) = parse_trm(s) {
                prems.push(p);
            }
            if s.is_sym("|]") {
                s.adv();
                break;
            }
            if matches!(s.kind(), Some(TokenKind::Semicolon)) {
                s.adv();
                continue;
            }
            break;
        }
        if s.is_sym("==>") || s.is_sym("-->") {
            s.adv();
            let concl = if let Some(c) = parse_trm(s) {
                c
            } else {
                Term::const_("dummy", Typ::base("prop"))
            };
            let mut result = concl;
            for p in prems.into_iter().rev() {
                result = make_binary("Pure.imp", p, result);
            }
            return Some(result);
        }
        // No ==> — return conjunction of premises
        if prems.is_empty() {
            return Some(Term::const_("True", Typ::base("prop")));
        }
        let mut result = prems.remove(0);
        for p in prems {
            result = hologic::mk_conj(result, p);
        }
        return Some(result);
    }
    // Negation prefix: ~ P  or  \<not> P  or  ¬ P
    if s.is_sym("~") || s.is_sym("\\<not>") || s.is_sym("\u{00ac}") {
        s.adv();
        let body =
            if let Some(b) = parse_trm(s) { b } else { Term::const_("True", Typ::base("prop")) };
        return Some(Term::app(hologic::not_const(), body));
    }
    // Unary minus (set complement, arithmetic negation)
    if s.is_sym("-") {
        s.adv();
        let body =
            if let Some(b) = parse_trm(s) { b } else { Term::const_("True", Typ::base("prop")) };
        return Some(Term::app(hologic::uminus_const(Typ::dummy()), body));
    }
    // Infimum / supremum prefix
    if s.is_sym("\\<Sqinter>") {
        s.adv();
        if let Some(body) = parse_trm(s) {
            return Some(Term::app(hologic::Inf_const(Typ::dummy()), body));
        }
        return Some(hologic::Inf_const(Typ::dummy()));
    }
    if s.is_sym("\\<Squnion>") {
        s.adv();
        if let Some(body) = parse_trm(s) {
            return Some(Term::app(hologic::Sup_const(Typ::dummy()), body));
        }
        return Some(hologic::Sup_const(Typ::dummy()));
    }
    let mut head = parse_atom(s)?;
    loop {
        // Stop at implication if requested (for RHS of =, &, |)
        if stop_at_imp && (s.is_sym("==>") || s.is_sym("-->") || s.is_sym("\u{27f6}")) {
            break;
        }
        // Function application: f (x)
        if s.is_sym("(") {
            s.adv();
            // Check for operator section: (<op>) or ((<op>) arg)
            let next_is_op = match s.kind() {
                Some(TokenKind::Symbol(sym)) => {
                    let s = sym.as_ref();
                    s == "="
                        || s == "~="
                        || s == "<"
                        || s == ">"
                        || s == "#"
                        || s == "@"
                        || s == "&"
                        || s == "|"
                        || s == "+"
                        || s == "\\<in>"
                        || s == "\\<notin>"
                        || s == "\\<le>"
                        || s == "\\<ge>"
                        || s == "\\<subseteq>"
                        || s == "\\<inter>"
                        || s == "\\<union>"
                },
                _ => false,
            };
            if next_is_op {
                // Operator section: (<op>) or ((<op>) arg)
                let op_src = s.src()?;
                s.adv(); // skip operator
                let op_term = Term::free(Arc::from(op_src.as_str()), Typ::dummy());
                if s.is_sym(")") {
                    // Bare operator section: (<op>)
                    s.adv();
                    head = Term::app(head, op_term);
                } else {
                    // ((<op>) arg) or (<op> arg) — parse the argument
                    let arg = parse_trm(s).unwrap_or_else(|| Term::const_("dummy", Typ::dummy()));
                    if s.is_sym(")") {
                        s.adv();
                    }
                    head = Term::app(head, Term::app(op_term, arg));
                }
            } else {
                // Regular parenthesized expression or function argument
                if let Some(a) = parse_trm(s) {
                    if s.is_sym(")") {
                        s.adv();
                    }
                    head = Term::app(head, a);
                }
                // If inner parse fails, just skip to )
                while !s.is_sym(")") && s.kind().is_some() {
                    s.adv();
                }
                if s.is_sym(")") {
                    s.adv();
                }
            }
            continue;
        }
        // List literal: f [x, y, z]  or  P []
        if s.is_sym("[") {
            s.adv();
            // Empty list
            if s.is_sym("]") {
                s.adv();
                head = Term::app(head, hologic::nil_const(Typ::dummy()));
                continue;
            }
            let first = parse_trm(s)?;
            let mut elems = vec![first];
            while s.is_sym(",") {
                s.adv();
                elems.push(parse_trm(s)?);
            }
            if s.is_sym("]") {
                s.adv();
            }
            // Build list: x # y # z # []
            let nil = hologic::nil_const(Typ::dummy());
            let cons = hologic::cons_const(Typ::dummy());
            let mut result = nil;
            for e in elems.into_iter().rev() {
                result = Term::app(Term::app(cons.clone(), e), result);
            }
            head = Term::app(head, result);
            continue;
        }

        // Set comprehension, enumeration, or range: {x. P x}, {a,b,c}, {..n}, {a..b}
        if s.is_sym("{") {
            s.adv();
            if s.is_sym("}") {
                s.adv();
                head = Term::app(head, hologic::empty_set_const(Typ::dummy()));
                continue;
            }

            // Check for set range starting with .. or ..<: {..n}, {..<n}
            if s.is_sym(".") {
                let next_is_dot_or_lt = s.tokens.get(s.pos + 1).is_some_and(|t| {
                    matches!(&t.kind, TokenKind::Symbol(s) if s.as_ref() == "." || s.as_ref() == "<")
                });
                if next_is_dot_or_lt {
                    s.adv(); // first dot
                    if s.is_sym(".") {
                        s.adv(); // second dot
                        if s.is_sym("<") {
                            s.adv();
                        } // ..< (three chars)
                    } else if s.is_sym("<") {
                        s.adv();
                    } // .< (unusual but handle)
                    let upper = if !s.is_sym("}") { Some(parse_trm(s)?) } else { None };
                    if s.is_sym("}") {
                        s.adv();
                    }
                    let range_const = hologic::set_range_const();
                    let result = match upper {
                        Some(up) => Term::app(range_const, up),
                        None => range_const,
                    };
                    head = Term::app(head, result);
                    continue;
                }
            }

            let first = parse_trm(s)?;

            // Check for set range with lower bound: {a..b}, {a..}, {a..<b}
            if s.is_sym(".") {
                let next_is_dot_or_lt = s.tokens.get(s.pos + 1).is_some_and(|t| {
                    matches!(&t.kind, TokenKind::Symbol(s) if s.as_ref() == "." || s.as_ref() == "<")
                });
                if next_is_dot_or_lt {
                    s.adv(); // first dot
                    if s.is_sym(".") {
                        s.adv(); // second dot
                        if s.is_sym("<") {
                            s.adv();
                        } // ..< (three chars)
                    } else if s.is_sym("<") {
                        s.adv();
                    } // .< (unusual but handle)
                    let upper = if !s.is_sym("}") { Some(parse_trm(s)?) } else { None };
                    if s.is_sym("}") {
                        s.adv();
                    }
                    let range_const = hologic::set_range_const();
                    let result = match upper {
                        Some(up) => Term::app(Term::app(range_const, first), up),
                        None => Term::app(range_const, first),
                    };
                    head = Term::app(head, result);
                    continue;
                }
            }

            // Set comprehension: {x. P x} or {x | P x}
            if s.is_sym(".") || s.is_sym("|") {
                s.adv();
                let body = parse_trm(s)?;
                if s.is_sym("}") {
                    s.adv();
                }
                let collect = hologic::collect_const(Typ::dummy());
                let abs = Term::abs("_", Typ::dummy(), body);
                head = Term::app(head, Term::app(collect, abs));
                continue;
            }

            // Set enumeration: {a, b, c}
            let mut elems = vec![first];
            while s.is_sym(",") {
                s.adv();
                elems.push(parse_trm(s)?);
            }
            if s.is_sym("}") {
                s.adv();
            }
            let empty = hologic::empty_set_const(Typ::dummy());
            let insert = hologic::insert_const(Typ::dummy());
            let mut result = empty;
            for e in elems.into_iter().rev() {
                result = Term::app(Term::app(insert.clone(), e), result);
            }
            head = Term::app(head, result);
            continue;
        }

        // Type annotation: term :: type  — skip the type
        if s.is_sym("::") {
            s.adv();
            // Skip type tokens until a delimiter
            while s.kind().is_some() {
                if s.is_sym(")")
                    || s.is_sym("]")
                    || s.is_sym("|]")
                    || s.is_sym(";")
                    || s.is_sym(",")
                    || s.is_sym(".")
                    || s.is_sym("==")
                    || s.is_sym("==>")
                    || s.is_sym("-->")
                    || s.is_sym("&")
                    || s.is_sym("|")
                {
                    break;
                }
                s.adv();
            }
            continue;
        }

        // --- Lowest precedence: implication ---
        if s.is_sym("==>") || s.is_sym("-->") || s.is_sym("\u{27f6}") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = make_binary("Pure.imp", head.clone(), rhs);
            }
            return Some(head);
        }
        // Conjunction
        if s.is_sym("&&&") || s.is_sym("&") || s.is_sym("\u{2227}") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = hologic::mk_conj(head.clone(), rhs);
            }
            return Some(head);
        }
        // Disjunction
        if s.is_sym("|||") || s.is_sym("|") || s.is_sym("\u{2228}") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = hologic::mk_disj(head.clone(), rhs);
            }
            return Some(head);
        }

        // --- Prefix negation (tightest binding) ---
        if s.is_sym("~") || s.is_sym("\u{00ac}") {
            head = Term::app(hologic::not_const(), head);
            break;
        }

        // Inequality (check before =)
        if s.is_sym("~=") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = hologic::mk_eq(head.clone(), rhs);
                head = Term::app(hologic::not_const(), head);
            }
            return Some(head);
        }
        // Equality (with graceful degradation)
        if s.is_sym("=") {
            s.adv();
            // Parse RHS without implication
            if let Some(rhs) = parse_trm_no_imp(s) {
                head = hologic::mk_eq(head.clone(), rhs);
            }
            continue;
        }
        // Append
        if s.is_sym("@") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = make_binary("HOL.append", head.clone(), rhs);
            }
            return Some(head);
        }
        // Less-than
        if s.is_sym("<") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = make_binary("HOL.less", head.clone(), rhs);
            }
            return Some(head);
        }
        // Image
        if s.is_sym("`") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = make_binary("HOL.image", head.clone(), rhs);
            }
            return Some(head);
        }
        // Cons
        if s.is_sym("#") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = make_binary("HOL.Cons", head.clone(), rhs);
            }
            return Some(head);
        }
        // Isabelle native symbols
        if s.is_sym("\\<in>") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = make_binary("HOL.member", head.clone(), rhs);
            }
            return Some(head);
        }
        if s.is_sym("\\<notin>") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = make_binary("HOL.NotMember", head.clone(), rhs);
            }
            return Some(head);
        }
        if s.is_sym("\\<le>") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = make_binary("HOL.ordLessEq", head.clone(), rhs);
            }
            return Some(head);
        }
        if s.is_sym("\\<ge>") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = make_binary("HOL.ordGreaterEq", head.clone(), rhs);
            }
            return Some(head);
        }
        if s.is_sym("\\<subseteq>") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = make_binary("HOL.subsetEq", head.clone(), rhs);
            }
            return Some(head);
        }
        if s.is_sym("\\<inter>") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = make_binary("HOL.inter", head.clone(), rhs);
            }
            return Some(head);
        }
        if s.is_sym("\\<union>") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = make_binary("HOL.union", head.clone(), rhs);
            }
            return Some(head);
        }
        // Addition
        if s.is_sym("+") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = make_binary("HOL.plus", head.clone(), rhs);
            }
            return Some(head);
        }
        // Set difference
        if s.is_sym("-") {
            s.adv();
            if let Some(rhs) = parse_trm(s) {
                head = make_binary("HOL.minus", head.clone(), rhs);
            }
            return Some(head);
        }

        // --- Ident-based operators ---
        if s.is_id() {
            let src = s.src()?;
            match src.as_str() {
                "APPEND" => {
                    s.adv();
                    let rhs = parse_trm(s)?;
                    return Some(make_binary("HOL.append", head, rhs));
                },
                "IFF" => {
                    s.adv();
                    let rhs = parse_trm(s)?;
                    return Some(hologic::mk_eq(head, rhs));
                },
                _ => {},
            }
        }

        // Application by juxtaposition
        if (s.is_id() || matches!(s.kind(), Some(TokenKind::String | TokenKind::Number)))
            && let Some(a) = parse_atom(s)
        {
            head = Term::app(head, a);
            continue;
        }
        break;
    }
    Some(head)
}

fn parse_quant(s: &mut P, qname: &str) -> Option<Term> {
    let mut vars = vec![];
    while s.is_id() {
        let n = Arc::from(s.src()?.as_str());
        s.adv();
        vars.push((n, Typ::dummy()));
        // Skip optional type annotation: ::type
        if s.is_sym("::") {
            s.adv();
            while s.kind().is_some() {
                if s.is_sym(")")
                    || s.is_sym("]")
                    || s.is_sym("|]")
                    || s.is_sym(";")
                    || s.is_sym(",")
                    || s.is_sym(".")
                    || s.is_sym("==")
                    || s.is_sym("==>")
                    || s.is_sym("-->")
                    || s.is_sym("&")
                    || s.is_sym("|")
                {
                    break;
                }
                s.adv();
            }
        }
    }
    // Check for bounded quantifier: ALL x : A . P  or  EX x : A . P
    let _set_opt = if s.is_sym(":") || s.is_sym("\\<in>") {
        s.adv();
        parse_trm(s)
    } else {
        None
    };
    if s.is_sym(".") {
        s.adv();
    }
    let body = parse_trm(s)?;
    let inner = vars.into_iter().rfold(body, |b, (n, t)| Term::abs(n, t, b));
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
    // if-then-else: if C then A else B
    if s.is_kw("if") {
        s.adv();
        let cond = parse_trm(s)?;
        // Expect "then"
        if s.is_kw("then") {
            s.adv();
        } else {
            return None;
        }
        let then_branch = parse_trm(s)?;
        // Expect "else"
        if s.is_kw("else") {
            s.adv();
        } else {
            return None;
        }
        let else_branch = parse_trm(s)?;
        // Build: HOL.If(cond, then, else)
        return Some(Term::app(
            Term::app(Term::app(hologic::if_const(Typ::dummy()), cond), then_branch),
            else_branch,
        ));
    }
    // let expression: let x = e1 in e2
    if s.is_kw("let") {
        s.adv();
        // Parse just the variable name (not a full term, which would consume =)
        if s.is_id() {
            s.adv();
        } else {
            return None;
        }
        if s.is_sym("=") {
            s.adv();
        }
        let _def = parse_trm(s)?; // skip definition
        if s.is_kw("in") {
            s.adv();
        }
        let body = parse_trm(s)?;
        return Some(body); // just return the body, skip the binding
    }
    // case expression: case E of P1 => R1 | P2 => R2 | ...
    if s.is_kw("case") {
        s.adv();
        let scrutinee = parse_trm(s)?;
        // Expect "of"
        if s.is_kw("of") {
            s.adv();
        } else {
            return None;
        }
        // Parse arms: P1 => R1 | P2 => R2 | ...
        // For simplicity, treat the entire case as a special term
        // Build: HOL.Case(scrutinee, arm1, arm2, ...)
        let case_const = hologic::case_const();
        let mut result = Term::app(case_const, scrutinee);
        loop {
            let _pat = parse_trm(s)?;
            // Expect =>
            if s.is_sym("=>") {
                s.adv();
            } else {
                break;
            }
            let body = parse_trm(s)?;
            result = Term::app(result, Term::abs("_", Typ::dummy(), body));
            // Check for |
            if s.is_sym("|") {
                s.adv();
                continue;
            }
            break;
        }
        return Some(result);
    }
    // List literal: [x, y, z] or []
    if s.is_sym("[") {
        s.adv();
        if s.is_sym("]") {
            s.adv();
            return Some(hologic::nil_const(Typ::dummy()));
        }
        let first = parse_trm(s)?;
        let mut elems = vec![first];
        while s.is_sym(",") {
            s.adv();
            elems.push(parse_trm(s)?);
        }
        if s.is_sym("]") {
            s.adv();
        }
        // Build: x # y # z # []
        let nil = hologic::nil_const(Typ::dummy());
        let cons = hologic::cons_const(Typ::dummy());
        let mut result = nil;
        for e in elems.into_iter().rev() {
            result = Term::app(Term::app(cons.clone(), e), result);
        }
        return Some(result);
    }
    // Set comprehension or enumeration: {x. P x} or {a, b, c}
    if let Some(TokenKind::Symbol(x)) = s.kind()
        && x.as_ref() == "{"
    {
        s.adv();
        if s.is_sym("}") {
            s.adv();
            return Some(hologic::empty_set_const(Typ::dummy()));
        }
        // Check for range starting with ..: {..n}
        if s.is_sym(".") {
            s.adv(); // first dot
            if s.is_sym(".") {
                s.adv(); // second dot
                if s.is_sym("<") {
                    s.adv();
                } // ..< (three chars)
            } else if s.is_sym("<") {
                s.adv();
            } // .< (unusual but handle)
            let upper = if !s.is_sym("}") { Some(parse_trm(s)?) } else { None };
            if s.is_sym("}") {
                s.adv();
            }
            let range_const = hologic::set_range_const();
            let result = match upper {
                Some(u) => Term::app(range_const, u),
                None => range_const,
            };
            return Some(result);
        }
        let first = parse_trm(s)?;
        // Check for set range: {a..}, {a..b}
        if s.is_sym(".") {
            s.adv(); // first dot
            if s.is_sym(".") {
                s.adv(); // second dot
                if s.is_sym("<") {
                    s.adv();
                } // ..< (three chars)
            } else if s.is_sym("<") {
                s.adv();
            } // .< (unusual but handle)
            // Parse the upper bound (optional)
            let upper = if !s.is_sym("}") { Some(parse_trm(s)?) } else { None };
            if s.is_sym("}") {
                s.adv();
            }
            // Build: setRange(lower, upper)
            let range_const = hologic::set_range_const();
            let result = match upper {
                Some(u) => Term::app(Term::app(range_const, first), u),
                None => Term::app(range_const, first),
            };
            return Some(result);
        }
        if s.is_sym(".") || s.is_sym("|") {
            // Set comprehension: {x. P x} or {x | P x}
            s.adv();
            let body = parse_trm(s)?;
            if s.is_sym("}") {
                s.adv();
            }
            let collect = hologic::collect_const(Typ::dummy());
            let abs = Term::abs("_", Typ::dummy(), body);
            return Some(Term::app(collect, abs));
        }
        // Set enumeration: {a, b, c} — parse as insert chain
        let mut elems = vec![first];
        while s.is_sym(",") {
            s.adv();
            elems.push(parse_trm(s)?);
        }
        if s.is_sym("}") {
            s.adv();
        }
        let empty = hologic::empty_set_const(Typ::dummy());
        let insert = hologic::insert_const(Typ::dummy());
        let mut result = empty;
        for e in elems.into_iter().rev() {
            result = Term::app(Term::app(insert.clone(), e), result);
        }
        return Some(result);
    }
    let kind = s.kind()?;
    let src = s.src()?;
    match &kind {
        TokenKind::Ident | TokenKind::LongIdent => {
            s.adv();
            Some(Term::free(Arc::from(src.as_str()), Typ::dummy()))
        },
        TokenKind::String => {
            s.adv();
            if src.len() >= 2 {
                Some(Term::const_(&src[1..src.len() - 1], Typ::base("prop")))
            } else {
                Some(Term::const_(src, Typ::base("prop")))
            }
        },
        TokenKind::Number => {
            s.adv();
            Some(Term::const_(src, Typ::base("nat")))
        },
        TokenKind::Symbol(x) if x.as_ref() == "(" => {
            s.adv();
            // Check if next token is a known infix operator (operator section)
            let next_is_op = match s.kind() {
                Some(TokenKind::Symbol(sym)) => {
                    let s = sym.as_ref();
                    s == "="
                        || s == "~="
                        || s == "<"
                        || s == ">"
                        || s == "#"
                        || s == "@"
                        || s == "&"
                        || s == "|"
                        || s == "+"
                        || s == "\\<in>"
                        || s == "\\<notin>"
                        || s == "\\<le>"
                        || s == "\\<ge>"
                        || s == "\\<subseteq>"
                        || s == "\\<inter>"
                        || s == "\\<union>"
                },
                _ => false,
            };
            if next_is_op {
                // Operator section: (<op>) or ((<op>) arg)
                let op_src = s.src()?;
                s.adv();
                let op_term = Term::free(Arc::from(op_src.as_str()), Typ::dummy());
                // Check for argument: ((<op>) arg)
                if !s.is_sym(")") {
                    let arg = parse_trm(s)?;
                    if s.is_sym(")") {
                        s.adv();
                    }
                    return Some(Term::app(op_term, arg));
                } else {
                    // Bare operator: (<op>)
                    if s.is_sym(")") {
                        s.adv();
                    }
                    return Some(op_term);
                }
            }
            // Not an operator — parse as parenthesized expression
            let t = parse_trm(s)?;
            s.is_sym(")");
            s.adv();
            Some(t)
        },
        // Isabelle constant symbols (not operators)
        TokenKind::Symbol(x) if x.as_ref() == "\\<nat>" => {
            s.adv();
            Some(hologic::nat_set_const())
        },
        TokenKind::Symbol(x) if x.as_ref() == "\\<top>" => {
            s.adv();
            Some(hologic::top_const(Typ::dummy()))
        },
        TokenKind::Symbol(x) if x.as_ref() == "\\<bottom>" => {
            s.adv();
            Some(hologic::bot_const(Typ::dummy()))
        },
        TokenKind::Symbol(x) if x.as_ref() == "\\<not>" => {
            s.adv();
            Some(hologic::not_const())
        },
        _ => None,
    }
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
