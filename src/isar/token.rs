// Isabelle tokenizer — lexical analysis of Isabelle theory files.
//
// Corresponds to `src/Pure/Isar/token.ML`.
//
// Isabelle's token language is sophisticated, supporting:
// - **Identifiers**: `foo`, `nat`, `map'`, `''a` (type variables)
// - **Long identifiers**: `Foo.bar.baz`
// - **Keywords**: `theory`, `lemma`, `proof`, `qed`, `if`, `then`, `else`, etc.
// - **Symbols**: `==>`, `!!`, `==`, `=>`, `-->`, `<->`, `<=>`, `!!`, `&&`, `||`, `~`, `ALL`, `EX`
// - **Strings**: `"hello world"`
// - **Numbers**: `42`, `0xFF`
// - **Comments**: `(* nested (* comments *) *)`
// - **Verbatim**: `{* ... *}`
// - **Cartouches**: `‹...›`
// - **Spaces, newlines, tabs**
use std::fmt;

use crate::core::types::{Symbol, intern};

// =========================================================================
// Token kinds
// =========================================================================

/// The kind of a token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    /// A keyword: `theory`, `lemma`, `proof`, `qed`, `if`, `then`, `else`, etc.
    Keyword(Symbol),
    /// An identifier: `foo`, `nat`, `map'`, `''a`
    Ident,
    /// A long identifier: `Foo.bar.baz`
    LongIdent,
    /// A type variable: `'a`, `?'a`, `''a`
    TypeVar,
    /// A schematic type variable: `?'a`
    SchematicTypeVar,
    /// A string literal: `"hello"`
    String,
    /// A number: `42`
    Number,
    /// A symbol: `==>`, `!!`, `==`, `=>`
    Symbol(Symbol),
    /// A command separator: `;`
    Semicolon,
    /// A comment: `(* ... *)`
    Comment,
    /// Whitespace
    Space,
    /// End of input
    EOF,
    /// Unknown / error token
    Error,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Keyword(k) => write!(f, "keyword `{k}`"),
            TokenKind::Ident => write!(f, "identifier"),
            TokenKind::LongIdent => write!(f, "long identifier"),
            TokenKind::TypeVar => write!(f, "type variable"),
            TokenKind::SchematicTypeVar => write!(f, "schematic type variable"),
            TokenKind::String => write!(f, "string"),
            TokenKind::Number => write!(f, "number"),
            TokenKind::Symbol(s) => write!(f, "symbol `{s}`"),
            TokenKind::Semicolon => write!(f, "`;`"),
            TokenKind::Comment => write!(f, "comment"),
            TokenKind::Space => write!(f, "space"),
            TokenKind::EOF => write!(f, "EOF"),
            TokenKind::Error => write!(f, "error"),
        }
    }
}

// =========================================================================
// Token
// =========================================================================

/// A lexical token with position information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    /// The kind of the token.
    pub kind: TokenKind,
    /// The source text of the token.
    pub source: String,
    /// Byte offset in the input.
    pub offset: usize,
}

impl Token {
    pub fn new(kind: TokenKind, source: String, offset: usize) -> Self {
        Token { kind, source, offset }
    }

    pub fn is_keyword(&self, kw: &str) -> bool {
        matches!(&self.kind, TokenKind::Keyword(k) if k.as_ref() == kw)
    }

    pub fn is_ident(&self) -> bool {
        matches!(self.kind, TokenKind::Ident)
    }

    pub fn is_command(&self) -> bool {
        matches!(&self.kind, TokenKind::Keyword(_))
    }
}

// =========================================================================
// Keywords
// =========================================================================

/// Isabelle keywords that start commands.
pub const COMMAND_KEYWORDS: &[&str] = &[
    "theory",
    "imports",
    "begin",
    "end",
    "lemma",
    "theorem",
    "corollary",
    "proposition",
    "definition",
    "abbreviation",
    "notation",
    "fun",
    "function",
    "primrec",
    "datatype",
    "record",
    "inductive",
    "coinductive",
    "class",
    "subclass",
    "instance",
    "instantiation",
    "locale",
    "sublocale",
    "interpretation",
    "interpret",
    "proof",
    "qed",
    "done",
    "by",
    "apply",
    "have",
    "show",
    "hence",
    "thus",
    "fix",
    "assume",
    "presume",
    "define",
    "obtain",
    "let",
    "from",
    "with",
    "using",
    "unfolding",
    "note",
    "also",
    "finally",
    "moreover",
    "ultimately",
    "case",
    "next",
    "if",
    "then",
    "else",
    "for",
    "and",
    "in",
    "is",
    "where",
    "when",
    "of",
    "ML",
    "ML_prf",
    "ML_val",
    "ML_command",
    "declare",
    "lemmas",
    "named_theorems",
    "hide_class",
    "hide_type",
    "hide_const",
    "hide_fact",
    "schematic_goal",
    "text",
    "txt",
    "chapter",
    "section",
    "subsection",
    "subsubsection",
    "ALL",
    "EX",
];

/// Is a string an Isabelle keyword?
pub fn is_keyword(s: &str) -> bool {
    COMMAND_KEYWORDS.contains(&s)
}

/// A malformed lexical unit, located at its starting byte in the original input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexError {
    pub offset: usize,
    pub detail: String,
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "byte {}: {}", self.offset, self.detail)
    }
}

impl std::error::Error for LexError {}

// =========================================================================
// Lexer
// =========================================================================

/// The Isabelle lexer.
pub struct Lexer {
    input: Vec<char>,
    pos: usize,
    offset: usize,
    first_error: Option<LexError>,
}

impl Lexer {
    /// Create a new lexer for the given input.
    pub fn new(input: &str) -> Self {
        Lexer { input: input.chars().collect(), pos: 0, offset: 0, first_error: None }
    }

    /// Tokenize the entire input.
    pub fn tokenize(&mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        loop {
            let tok = self.next_token();
            let done = tok.kind == TokenKind::EOF;
            tokens.push(tok);
            if done {
                break;
            }
        }
        tokens
    }

    /// Tokenize without accepting malformed units. Offsets refer to UTF-8 bytes.
    pub fn tokenize_checked(&mut self) -> Result<Vec<Token>, LexError> {
        let tokens = self.tokenize();
        if let Some(error) = self.first_error.take() {
            return Err(error);
        }
        if let Some(token) = tokens.iter().find(|token| token.kind == TokenKind::Error) {
            return Err(LexError {
                offset: token.offset,
                detail: format!("unexpected token `{}`", token.source),
            });
        }
        Ok(tokens)
    }

    pub(crate) fn next_token(&mut self) -> Token {
        loop {
            while self.pos < self.input.len() && self.peek().is_whitespace() {
                self.advance();
            }
            if self.pos >= self.input.len() {
                return Token::new(TokenKind::EOF, String::new(), self.offset);
            }
            if self.peek() == '(' && self.peek_n(1) == Some('*') {
                if let Some(error) = self.skip_comment() {
                    return error;
                }
                continue;
            }
            break;
        }

        let start_offset = self.offset;
        let ch = self.peek();

        match ch {
            '"' => self.lex_string(),
            '‹' => self.lex_cartouche(false),
            '{' if self.peek_n(1) == Some('*') => self.lex_verbatim(),
            '\\' if self.starts_with(r"\<open>") => self.lex_cartouche(true),
            // Semicolons
            ';' => {
                self.advance();
                Token::new(TokenKind::Semicolon, ";".into(), start_offset)
            },

            // Isabelle named symbols are indivisible; incomplete escapes are errors.
            '\\' if self.peek_n(1) == Some('<') => {
                let start = self.pos;
                if !self.scan_symbol_escape() {
                    return self.error_token(start, start_offset, "malformed symbol escape");
                }
                let text: String = self.input[start..self.pos].iter().collect();
                Token::new(TokenKind::Symbol(intern(&text)), text, start_offset)
            },

            // Symbols: try longest match first (==> before ==, =>)
            '=' if self.peek_n(1) == Some('=') && self.peek_n(2) == Some('>') => {
                self.advance_by(3);
                Token::new(TokenKind::Symbol(intern("==>")), "==>".into(), start_offset)
            },
            '=' if self.peek_n(1) == Some('>') => {
                self.advance_by(2);
                Token::new(TokenKind::Symbol(intern("=>")), "=>".into(), start_offset)
            },
            '=' if self.peek_n(1) == Some('=') => {
                self.advance_by(2);
                Token::new(TokenKind::Symbol(intern("==")), "==".into(), start_offset)
            },
            '!' if self.peek_n(1) == Some('!') => {
                self.advance_by(2);
                Token::new(TokenKind::Symbol(intern("!!")), "!!".into(), start_offset)
            },
            '-' if self.peek_n(1) == Some('-') && self.peek_n(2) == Some('>') => {
                self.advance_by(3);
                Token::new(TokenKind::Symbol(intern("-->")), "-->".into(), start_offset)
            },
            '-' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern("-")), '-'.into(), start_offset)
            },
            '+' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern("+")), '+'.into(), start_offset)
            },
            '<' if self.peek_n(1) == Some('=') && self.peek_n(2) == Some('>') => {
                self.advance_by(3);
                Token::new(TokenKind::Symbol(intern("<=>")), "<=>".into(), start_offset)
            },
            '<' if self.peek_n(1) == Some('-') && self.peek_n(2) == Some('>') => {
                self.advance_by(3);
                Token::new(TokenKind::Symbol(intern("<->")), "<->".into(), start_offset)
            },
            '<' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern("<")), '<'.into(), start_offset)
            },

            // Bracketed assumptions: [| ... |]
            '[' if self.peek_n(1) == Some('|') => {
                self.advance_by(2);
                Token::new(TokenKind::Symbol(intern("[|")), "[|".into(), start_offset)
            },
            '|' if self.peek_n(1) == Some(']') => {
                self.advance_by(2);
                Token::new(TokenKind::Symbol(intern("|]")), "|]".into(), start_offset)
            },
            // Inequality: ~=
            '~' if self.peek_n(1) == Some('=') => {
                self.advance_by(2);
                Token::new(TokenKind::Symbol(intern("~=")), "~=".into(), start_offset)
            },

            // Identifiers: start with letter, _, or type variable quote
            c if c.is_alphabetic() || c == '_' => self.lex_ident(),
            '\'' => self.lex_type_var(),

            // Numbers
            c if c.is_ascii_digit() => self.lex_number(),

            '.' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern(".")), '.'.into(), start_offset)
            },
            '%' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern("%")), '%'.into(), start_offset)
            },
            ':' if self.peek_n(1) == Some(':') => {
                self.advance_by(2);
                Token::new(TokenKind::Symbol(intern("::")), "::".into(), start_offset)
            },
            // Single-character symbols
            ':' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern(":")), ":".into(), start_offset)
            },
            '&' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern("&")), '&'.into(), start_offset)
            },
            '|' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern("|")), '|'.into(), start_offset)
            },
            '~' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern("~")), '~'.into(), start_offset)
            },
            '(' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern("(")), '('.into(), start_offset)
            },
            ')' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern(")")), ')'.into(), start_offset)
            },
            '[' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern("[")), '['.into(), start_offset)
            },
            ']' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern("]")), ']'.into(), start_offset)
            },
            '{' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern("{")), '{'.into(), start_offset)
            },
            '}' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern("}")), '}'.into(), start_offset)
            },
            '=' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern("=")), '='.into(), start_offset)
            },
            '#' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern("#")), '#'.into(), start_offset)
            },
            '>' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern(">")), '>'.into(), start_offset)
            },
            '@' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern("@")), '@'.into(), start_offset)
            },
            '`' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern("`")), '`'.into(), start_offset)
            },
            ',' | '!' | '*' | '?' => {
                self.advance();
                let symbol = ch.to_string();
                Token::new(TokenKind::Symbol(intern(&symbol)), symbol, start_offset)
            },
            // Error
            _ => {
                let start = self.pos;
                self.advance();
                self.error_token(start, start_offset, "unrecognized character")
            },
        }
    }

    fn lex_ident(&mut self) -> Token {
        let start = self.pos;
        let start_offset = self.offset;
        while self.pos < self.input.len() {
            let ch = self.peek();
            if ch.is_alphanumeric() || ch == '_' || ch == '\'' || ch == '.' {
                if ch == '.' {
                    // Only include dot if it's part of a qualified name (next char is ident char,
                    // not another dot)
                    match self.peek_n(1) {
                        Some('.') => break, // don't eat ..
                        Some(c) if !c.is_alphanumeric() && c != '_' && c != '\'' => break,
                        None => break,
                        _ => {}, // dot followed by ident char => include it (qualified name)
                    }
                }
                self.advance();
            } else {
                break;
            }
        }
        let text: String = self.input[start..self.pos].iter().collect();
        if text.contains('.') && text.len() > 1 {
            Token::new(TokenKind::LongIdent, text, start_offset)
        } else if is_keyword(&text) {
            Token::new(TokenKind::Keyword(intern(&text)), text, start_offset)
        } else {
            Token::new(TokenKind::Ident, text, start_offset)
        }
    }

    fn lex_type_var(&mut self) -> Token {
        let start = self.pos;
        let start_offset = self.offset;
        // Eat the leading quote(s)
        self.advance(); // first '
        if self.peek() == '\'' {
            self.advance(); // second ' for ''a style
        }

        if self.pos == self.input.len() || !self.peek().is_alphabetic() {
            return self.error_token(start, start_offset, "type variable requires a name");
        }
        while self.pos < self.input.len() && (self.peek().is_alphanumeric() || self.peek() == '_') {
            self.advance();
        }

        let text: String = self.input[start..self.pos].iter().collect();
        let kind =
            if text.starts_with("?'") { TokenKind::SchematicTypeVar } else { TokenKind::TypeVar };
        Token::new(kind, text, start_offset)
    }

    fn lex_string(&mut self) -> Token {
        let start = self.pos;
        let start_offset = self.offset;
        self.advance();
        while self.pos < self.input.len() {
            if self.peek() == '"' {
                self.advance();
                return self.text_token(TokenKind::String, start, start_offset);
            }
            if self.peek() == '\\' {
                if self.peek_n(1) == Some('<') {
                    let escape_offset = self.offset;
                    if !self.scan_symbol_escape() {
                        self.record_error(escape_offset, "malformed symbol escape in string");
                        return self.text_token(TokenKind::Error, start, start_offset);
                    }
                    continue;
                }
                self.advance();
                if self.pos >= self.input.len() {
                    break;
                }
            }
            self.advance();
        }
        self.error_token(start, start_offset, "unterminated string")
    }

    fn lex_cartouche(&mut self, escaped: bool) -> Token {
        let start = self.pos;
        let start_offset = self.offset;
        self.advance_by(if escaped { r"\<open>".len() } else { 1 });
        let mut depth = 1;
        while self.pos < self.input.len() {
            if self.starts_with(r"\<open>") {
                self.advance_by(r"\<open>".len());
                depth += 1;
            } else if self.starts_with(r"\<close>") {
                self.advance_by(r"\<close>".len());
                depth -= 1;
            } else if self.peek() == '‹' {
                self.advance();
                depth += 1;
            } else if self.peek() == '›' {
                self.advance();
                depth -= 1;
            } else if self.peek() == '\\' && self.peek_n(1) == Some('<') {
                let escape_offset = self.offset;
                if !self.scan_symbol_escape() {
                    self.record_error(escape_offset, "malformed symbol escape in cartouche");
                    return self.text_token(TokenKind::Error, start, start_offset);
                }
            } else {
                self.advance();
            }
            if depth == 0 {
                return self.text_token(TokenKind::String, start, start_offset);
            }
        }
        self.error_token(start, start_offset, "unterminated cartouche")
    }

    fn lex_verbatim(&mut self) -> Token {
        let start = self.pos;
        let start_offset = self.offset;
        self.advance_by(2);
        while self.pos < self.input.len() {
            if self.peek() == '*' && self.peek_n(1) == Some('}') {
                self.advance_by(2);
                return self.text_token(TokenKind::String, start, start_offset);
            }
            if self.peek() == '\\' && self.peek_n(1) == Some('<') {
                let escape_offset = self.offset;
                if !self.scan_symbol_escape() {
                    self.record_error(escape_offset, "malformed symbol escape in verbatim");
                    return self.text_token(TokenKind::Error, start, start_offset);
                }
            } else {
                self.advance();
            }
        }
        self.error_token(start, start_offset, "unterminated verbatim")
    }

    fn text_token(&self, kind: TokenKind, start: usize, offset: usize) -> Token {
        Token::new(kind, self.input[start..self.pos].iter().collect(), offset)
    }

    fn error_token(&mut self, start: usize, offset: usize, detail: &str) -> Token {
        self.record_error(offset, detail);
        self.text_token(TokenKind::Error, start, offset)
    }

    fn record_error(&mut self, offset: usize, detail: &str) {
        if self.first_error.is_none() {
            self.first_error = Some(LexError { offset, detail: detail.to_string() });
        }
    }

    fn starts_with(&self, text: &str) -> bool {
        text.chars().zip(self.input[self.pos..].iter().copied()).all(|(left, right)| left == right)
            && self.input.len() - self.pos >= text.chars().count()
    }

    fn scan_symbol_escape(&mut self) -> bool {
        self.advance_by(2);
        let start = self.pos;
        while matches!(self.peek(), c if c.is_alphanumeric() || c == '_' || c == '^')
            && self.pos < self.input.len()
        {
            self.advance();
        }
        if self.pos == start || self.peek() != '>' {
            return false;
        }
        self.advance();
        true
    }

    fn lex_number(&mut self) -> Token {
        let start = self.pos;
        let start_offset = self.offset;
        // Hex prefix
        if self.peek() == '0' && self.peek_n(1) == Some('x') {
            self.advance_by(2);
        }
        while self.pos < self.input.len() && self.peek().is_ascii_hexdigit() {
            self.advance();
        }
        let text: String = self.input[start..self.pos].iter().collect();
        Token::new(TokenKind::Number, text, start_offset)
    }

    fn skip_comment(&mut self) -> Option<Token> {
        let start = self.pos;
        let start_offset = self.offset;
        self.advance_by(2);
        let mut depth = 1;
        while self.pos < self.input.len() {
            match self.peek() {
                '(' if self.peek_n(1) == Some('*') => {
                    self.advance_by(2);
                    depth += 1;
                },
                '*' if self.peek_n(1) == Some(')') => {
                    self.advance_by(2);
                    depth -= 1;
                    if depth == 0 {
                        return None;
                    }
                },
                '\\' if self.peek_n(1) == Some('<') => {
                    let escape_offset = self.offset;
                    if !self.scan_symbol_escape() {
                        self.record_error(escape_offset, "malformed symbol escape in comment");
                        return Some(self.text_token(TokenKind::Error, start, start_offset));
                    }
                },
                _ => self.advance(),
            }
        }
        Some(self.error_token(start, start_offset, "unterminated comment"))
    }

    fn peek(&self) -> char {
        self.input.get(self.pos).copied().unwrap_or('\0')
    }

    fn peek_n(&self, n: usize) -> Option<char> {
        self.input.get(self.pos + n).copied()
    }

    fn advance(&mut self) {
        if self.pos < self.input.len() {
            self.offset += self.input[self.pos].len_utf8();
            self.pos += 1;
        }
    }

    fn advance_by(&mut self, n: usize) {
        for _ in 0..n {
            self.advance();
        }
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn tokenize(s: &str) -> Vec<Token> {
        Lexer::new(s).tokenize()
    }

    fn filter_tokens(tokens: &[Token]) -> Vec<&Token> {
        tokens.iter().filter(|t| !matches!(t.kind, TokenKind::EOF)).collect()
    }

    #[test]
    fn test_keywords() {
        let toks = tokenize("theory lemma proof qed");
        let tokens = filter_tokens(&toks);
        assert_eq!(tokens.len(), 4);
        assert!(tokens[0].is_keyword("theory"));
        assert!(tokens[1].is_keyword("lemma"));
        assert!(tokens[2].is_keyword("proof"));
        assert!(tokens[3].is_keyword("qed"));
    }

    #[test]
    fn test_identifiers() {
        let toks = tokenize("foo bar nat'");
        let tokens = filter_tokens(&toks);
        assert!(tokens.len() >= 3, "got {}", tokens.len());
        assert!(tokens[0].is_ident());
        assert!(tokens[1].is_ident());
    }

    #[test]
    fn test_symbols() {
        let toks = tokenize("==> !! == =>");
        let tokens = filter_tokens(&toks);
        assert_eq!(tokens.len(), 4);
        match &tokens[0].kind {
            TokenKind::Symbol(s) => assert_eq!(s.as_ref(), "==>"),
            _ => panic!(),
        }
        match &tokens[1].kind {
            TokenKind::Symbol(s) => assert_eq!(s.as_ref(), "!!"),
            _ => panic!(),
        }
        match &tokens[2].kind {
            TokenKind::Symbol(s) => assert_eq!(s.as_ref(), "=="),
            _ => panic!(),
        }
        match &tokens[3].kind {
            TokenKind::Symbol(s) => assert_eq!(s.as_ref(), "=>"),
            _ => panic!(),
        }
    }

    #[test]
    fn test_type_vars() {
        let toks = tokenize("'a ''a ?'b");
        let tokens = filter_tokens(&toks);
        assert!(tokens.len() >= 3, "got {}", tokens.len());
    }

    #[test]
    fn test_comments_are_skipped() {
        let toks = tokenize("lemma (* comment *) foo");
        let tokens = filter_tokens(&toks);
        assert_eq!(tokens.len(), 2);
        assert!(tokens[0].is_keyword("lemma"));
        assert!(tokens[1].is_ident());
    }

    #[test]
    fn test_nested_comments() {
        let toks = tokenize("x (* outer (* inner *) *) y");
        let tokens = filter_tokens(&toks);
        assert_eq!(tokens.len(), 2);
        assert_eq!(&tokens[0].source, "x");
        assert_eq!(&tokens[1].source, "y");
    }

    #[test]
    fn tokenize_unicode_prefix_reports_byte_offsets() {
        let tokens = tokenize(" lemma");
        assert_eq!(tokens[0].offset, " ".len());
        assert!(tokens[0].is_keyword("lemma"));
    }

    #[test]
    fn tokenize_checked_method_punctuation_preserves_symbols() {
        let tokens = Lexer::new(",!*?").tokenize_checked().unwrap();
        for (token, symbol) in tokens.iter().zip([",", "!", "*", "?"]) {
            assert!(matches!(&token.kind, TokenKind::Symbol(value) if value.as_ref() == symbol));
            assert_eq!(token.source, symbol);
        }
        assert_eq!(tokens.last().unwrap().kind, TokenKind::EOF);
    }

    #[test]
    fn tokenize_checked_malformed_suffix_reports_byte_offset_and_diagnostic_token() {
        for (suffix, detail) in [
            ("\"unfinished", "unterminated string"),
            ("(* outer (* inner *)", "unterminated comment"),
            ("‹unfinished", "unterminated cartouche"),
            (r"\<open>unfinished", "unterminated cartouche"),
            ("{*unfinished", "unterminated verbatim"),
            (r"\<unfinished", "malformed symbol escape"),
            ("\0", "unrecognized character"),
        ] {
            let source = format!(" end {suffix}");
            let error = Lexer::new(&source).tokenize_checked().unwrap_err();
            assert_eq!(error.offset, " end ".len(), "{suffix}");
            assert!(error.detail.contains(detail), "{suffix}: {error}");
            let diagnostic = Lexer::new(&source).tokenize();
            assert_eq!(diagnostic[1].kind, TokenKind::Error, "{suffix}");
        }
    }

    #[test]
    fn tokenize_checked_malformed_escape_inside_string_reports_escape_offset() {
        let source = "lemma x: \"P \\<bad!\"";
        let error = Lexer::new(source).tokenize_checked().unwrap_err();
        assert_eq!(error.offset, source.find(r"\<bad").unwrap());
        assert!(error.detail.contains("symbol escape"));
    }

    #[test]
    fn tokenize_checked_nested_quotations_hide_keywords_and_preserve_positions() {
        let source = "lemma ‹by ‹end› by› (* by (* end *) *) \"end\" {* by *} end";
        let tokens = Lexer::new(source).tokenize_checked().unwrap();
        let sources = tokens.iter().map(|token| token.source.as_str()).collect::<Vec<_>>();
        assert_eq!(sources, ["lemma", "‹by ‹end› by›", "\"end\"", "{* by *}", "end", ""]);
        for token in &tokens[..tokens.len() - 1] {
            assert_eq!(&source[token.offset..token.offset + token.source.len()], token.source);
        }
    }

    #[test]
    fn tokenize_checked_escaped_cartouche_does_not_create_inner_commands() {
        let source = r"lemma \<open>by \<open>end\<close> by\<close> end";
        let tokens = Lexer::new(source).tokenize_checked().unwrap();
        assert_eq!(tokens[1].kind, TokenKind::String);
        assert_eq!(tokens[1].source, r"\<open>by \<open>end\<close> by\<close>");
        assert!(tokens[2].is_keyword("end"));
    }

    #[test]
    fn tokenize_checked_comment_escape_error_reports_its_own_byte_offset() {
        let source = "lemma x (* nested (* \\<bad! *) *) end";
        let error = Lexer::new(source).tokenize_checked().unwrap_err();
        assert_eq!(error.offset, source.find(r"\<bad").unwrap());
        assert!(error.detail.contains("comment"));
    }
}
