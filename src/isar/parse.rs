//! Isabelle parser combinators.
//!
//! Corresponds to `src/Pure/Isar/parse.ML`.
//!
//! Isabelle uses a combinator-based parser, similar to Haskell's Parsec.
//! Parsers consume tokens and either succeed (returning a value + remaining tokens)
//! or fail (returning None).

use super::token::{Token, TokenKind};

/// A parser that consumes tokens and produces a value of type `T`.
pub type Parser<T> = Box<dyn Fn(&[Token]) -> Option<(T, Vec<Token>)> + Send + Sync>;

/// Match a specific keyword.
pub fn keyword(kw: &str) -> Parser<String> {
    let kw = kw.to_string();
    Box::new(move |tokens: &[Token]| match tokens.first() {
        Some(tok) if tok.is_keyword(&kw) => Some((tok.source.clone(), tokens[1..].to_vec())),
        _ => None,
    })
}

/// Match an identifier.
pub fn ident() -> Parser<String> {
    Box::new(|tokens: &[Token]| match tokens.first() {
        Some(tok) if tok.is_ident() => Some((tok.source.clone(), tokens[1..].to_vec())),
        _ => None,
    })
}

/// Match a string literal (strips quotes).
pub fn string() -> Parser<String> {
    Box::new(|tokens: &[Token]| match tokens.first() {
        Some(Token { kind: TokenKind::String, source, .. }) => {
            let inner = if source.len() >= 2 { &source[1..source.len() - 1] } else { "" };
            Some((inner.to_string(), tokens[1..].to_vec()))
        },
        _ => None,
    })
}

/// Match a specific symbol.
pub fn symbol(sym: &str) -> Parser<String> {
    let sym = sym.to_string();
    Box::new(move |tokens: &[Token]| match tokens.first() {
        Some(Token { kind: TokenKind::Symbol(s), source, .. }) if s.as_ref() == sym => {
            Some((source.clone(), tokens[1..].to_vec()))
        },
        _ => None,
    })
}

/// Sequence: run p1 then p2, return both.
pub fn pair<T1: 'static, T2: 'static>(p1: Parser<T1>, p2: Parser<T2>) -> Parser<(T1, T2)> {
    Box::new(move |tokens: &[Token]| {
        p1(tokens).and_then(|(v1, rest)| p2(&rest).map(|(v2, r)| ((v1, v2), r)))
    })
}

/// Alternative: try p1, then p2.
pub fn alt<T: 'static>(p1: Parser<T>, p2: Parser<T>) -> Parser<T> {
    Box::new(move |tokens: &[Token]| p1(tokens).or_else(|| p2(tokens)))
}

/// Zero or more.
pub fn repeat<T: 'static>(p: Parser<T>) -> Parser<Vec<T>> {
    Box::new(move |tokens: &[Token]| {
        let mut results = Vec::new();
        let mut rest = tokens.to_vec();
        while let Some((v, r)) = p(&rest) {
            results.push(v);
            rest = r;
        }
        Some((results, rest))
    })
}

/// One or more.
pub fn repeat1<T: 'static>(p: Parser<T>) -> Parser<Vec<T>> {
    Box::new(move |tokens: &[Token]| {
        let (first, mut rest) = p(tokens)?;
        let mut results = vec![first];
        while let Some((v, r)) = p(&rest) {
            results.push(v);
            rest = r;
        }
        Some((results, rest))
    })
}

// =========================================================================
// Isabelle-specific parsers
// =========================================================================

/// A parsed theory header.
#[derive(Debug, Clone)]
pub struct TheoryHeader {
    pub name: String,
    pub imports: Vec<String>,
}

pub fn theory_header() -> Parser<TheoryHeader> {
    Box::new(|tokens: &[Token]| {
        let (_, rest) = keyword("theory")(tokens)?;
        let (name, rest) = ident()(&rest)?;
        let (_, rest) = keyword("imports")(&rest)?;
        let (imports, rest) = repeat(ident())(&rest)?;
        let (_, rest) = keyword("begin")(&rest)?;
        Some((TheoryHeader { name, imports }, rest))
    })
}

/// A parsed lemma statement.
#[derive(Debug, Clone)]
pub struct LemmaStmt {
    pub name: String,
    pub statement: String,
}

pub fn lemma_stmt() -> Parser<LemmaStmt> {
    Box::new(|tokens: &[Token]| {
        let (_, rest) = keyword("lemma")(tokens)?;
        let (name, rest) = ident()(&rest)?;
        let (_, rest) = symbol(":")(&rest)?;
        let (stmt, rest) = string()(&rest)?;
        Some((LemmaStmt { name, statement: stmt }, rest))
    })
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::{super::token::Lexer, *};

    fn tok(s: &str) -> Vec<Token> {
        Lexer::new(s).tokenize()
    }

    #[test]
    fn test_keyword_parser() {
        let tokens = tok("theory Foo");
        let (kw, rest) = keyword("theory")(&tokens).unwrap();
        assert_eq!(kw, "theory");
        assert_eq!(rest[0].source, "Foo");
    }

    #[test]
    fn test_pair() {
        let tokens = tok("lemma foo");
        let ((kw, id), _) = pair(keyword("lemma"), ident())(&tokens).unwrap();
        assert_eq!(kw, "lemma");
        assert_eq!(id, "foo");
    }

    #[test]
    fn test_alt() {
        let tokens = tok("foo");
        let (r, _) = alt(keyword("lemma"), ident())(&tokens).unwrap();
        assert_eq!(r, "foo");
    }

    #[test]
    fn test_repeat() {
        let tokens = tok("a b c");
        let (r, _) = repeat(ident())(&tokens).unwrap();
        assert_eq!(r, vec!["a", "b", "c"]);
    }

    #[test]
    fn test_theory_header() {
        let tokens = tok("theory MyTheory imports Foo Bar begin");
        let (h, _) = theory_header()(&tokens).unwrap();
        assert_eq!(h.name, "MyTheory");
        assert_eq!(h.imports, vec!["Foo", "Bar"]);
    }

    #[test]
    fn test_lemma_stmt() {
        let tokens = tok("lemma my_lemma: \"x = x\"");
        let (s, _) = lemma_stmt()(&tokens).unwrap();
        assert_eq!(s.name, "my_lemma");
        assert_eq!(s.statement, "x = x");
    }
}
