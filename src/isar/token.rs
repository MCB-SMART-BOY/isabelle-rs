use crate::core::types::Symbol;
use crate::core::types::intern;
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
    "theory", "imports", "begin", "end",
    "lemma", "theorem", "corollary", "proposition",
    "definition", "abbreviation", "notation",
    "fun", "function", "primrec", "datatype", "record",
    "inductive", "coinductive",
    "class", "subclass", "instance", "instantiation",
    "locale", "sublocale", "interpretation", "interpret",
    "proof", "qed", "done", "by", "apply",
    "have", "show", "hence", "thus",
    "fix", "assume", "presume", "define", "obtain",
    "let", "from", "with", "using", "unfolding",
    "note", "also", "finally", "moreover", "ultimately",
    "case", "next",
    "if", "then", "else", "for",
    "and", "in", "is", "where", "when", "of",
    "ML", "ML_prf", "ML_val", "ML_command",
    "declare", "lemmas", "named_theorems",
    "hide_class", "hide_type", "hide_const", "hide_fact",
    "schematic_goal",
    "text", "txt", "chapter", "section", "subsection", "subsubsection",
    "ALL", "EX",
];

/// Is a string an Isabelle keyword?
pub fn is_keyword(s: &str) -> bool {
    COMMAND_KEYWORDS.contains(&s)
}

// =========================================================================
// Lexer
// =========================================================================

/// The Isabelle lexer.
pub struct Lexer {
    input: Vec<char>,
    pos: usize,
    offset: usize,
}

impl Lexer {
    /// Create a new lexer for the given input.
    pub fn new(input: &str) -> Self {
        Lexer {
            input: input.chars().collect(),
            pos: 0,
            offset: 0,
        }
    }

    /// Tokenize the entire input.
    pub fn tokenize(&mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        loop {
            let tok = self.next_token();
            let done = tok.kind == TokenKind::EOF;
            tokens.push(tok);
            if done { break; }
        }
        tokens
    }

    fn next_token(&mut self) -> Token {
        self.skip_whitespace_and_comments();

        if self.pos >= self.input.len() {
            return Token::new(TokenKind::EOF, String::new(), self.offset);
        }

        let _start = self.pos;
        let start_offset = self.offset;
        let ch = self.peek();

        match ch {
            // Strings
            '"' => self.lex_string(),

            // Comments: (* ... *)
            '(' if self.peek_n(1) == Some('*') => {
                self.skip_comment();
                self.next_token()
            }

            // Semicolons
            ';' => {
                self.advance();
                Token::new(TokenKind::Semicolon, ";".into(), start_offset)
            }

            // Isabelle symbol escapes: \<name> (e.g., \<in>, \<forall>, \<Longrightarrow>)
            '\\' if self.peek_n(1) == Some('<') => {
                self.advance_by(2); // skip \<
                let inner_start = self.pos;
                while self.pos < self.input.len() {
                    let c = self.peek();
                    if c == '>' { break; }
                    if c == '\n' { break; } // safety: don't cross lines
                    if !c.is_alphanumeric() && c != '_' && c != '^' { break; }
                    self.advance();
                }
                let inner: String = self.input[inner_start..self.pos].iter().collect();
                if self.pos < self.input.len() && self.peek() == '>' {
                    self.advance(); // skip >
                }
                let text = format!("\\<{}>", inner);
                Token::new(TokenKind::Symbol(intern(&text)), text, start_offset)
            }

            // Symbols: try longest match first (==> before ==, =>)
            '=' if self.peek_n(1) == Some('=') && self.peek_n(2) == Some('>') => {
                self.advance_by(3);
                Token::new(TokenKind::Symbol(intern("==>")), "==>".into(), start_offset)
            }
            '=' if self.peek_n(1) == Some('>') => {
                self.advance_by(2);
                Token::new(TokenKind::Symbol(intern("=>")), "=>".into(), start_offset)
            }
            '=' if self.peek_n(1) == Some('=') => {
                self.advance_by(2);
                Token::new(TokenKind::Symbol(intern("==")), "==".into(), start_offset)
            }
            '!' if self.peek_n(1) == Some('!') => {
                self.advance_by(2);
                Token::new(TokenKind::Symbol(intern("!!")), "!!".into(), start_offset)
            }
            '-' if self.peek_n(1) == Some('-') && self.peek_n(2) == Some('>') => {
                self.advance_by(3);
                Token::new(TokenKind::Symbol(intern("-->")), "-->".into(), start_offset)
            }
            '-' => { self.advance(); Token::new(TokenKind::Symbol(intern("-")), '-'.into(), start_offset) }
            '+' => { self.advance(); Token::new(TokenKind::Symbol(intern("+")), '+'.into(), start_offset) }
            '<' if self.peek_n(1) == Some('=') && self.peek_n(2) == Some('>') => {
                self.advance_by(3);
                Token::new(TokenKind::Symbol(intern("<=>")), "<=>".into(), start_offset)
            }
            '<' if self.peek_n(1) == Some('-') && self.peek_n(2) == Some('>') => {
                self.advance_by(3);
                Token::new(TokenKind::Symbol(intern("<->")), "<->".into(), start_offset)
            }
            '<' => { self.advance(); Token::new(TokenKind::Symbol(intern("<")), '<'.into(), start_offset) }

            // Bracketed assumptions: [| ... |]
            '[' if self.peek_n(1) == Some('|') => {
                self.advance_by(2);
                Token::new(TokenKind::Symbol(intern("[|")), "[|".into(), start_offset)
            }
            '|' if self.peek_n(1) == Some(']') => {
                self.advance_by(2);
                Token::new(TokenKind::Symbol(intern("|]")), "|]".into(), start_offset)
            }
            // Inequality: ~=
            '~' if self.peek_n(1) == Some('=') => {
                self.advance_by(2);
                Token::new(TokenKind::Symbol(intern("~=")), "~=".into(), start_offset)
            }

            // Identifiers: start with letter, _, or type variable quote
            c if c.is_alphabetic() || c == '_' => self.lex_ident(),
            '\'' => self.lex_type_var(),

            // Numbers
            c if c.is_ascii_digit() => self.lex_number(),

            '.' => { self.advance(); Token::new(TokenKind::Symbol(intern(".")), '.'.into(), start_offset) }
            '%' => { self.advance(); Token::new(TokenKind::Symbol(intern("%")), '%'.into(), start_offset) }
            ':' if self.peek_n(1) == Some(':') => {
                self.advance_by(2);
                Token::new(TokenKind::Symbol(intern("::")), "::".into(), start_offset)
            }
            // Single-character symbols
            ':' => {
                self.advance();
                Token::new(TokenKind::Symbol(intern(":")), ":".into(), start_offset)
            }
            '&' => { self.advance(); Token::new(TokenKind::Symbol(intern("&")), '&'.into(), start_offset) }
            '|' => { self.advance(); Token::new(TokenKind::Symbol(intern("|")), '|'.into(), start_offset) }
            '~' => { self.advance(); Token::new(TokenKind::Symbol(intern("~")), '~'.into(), start_offset) }
            '(' => { self.advance(); Token::new(TokenKind::Symbol(intern("(")), '('.into(), start_offset) }
            ')' => { self.advance(); Token::new(TokenKind::Symbol(intern(")")), ')'.into(), start_offset) }
            '[' => { self.advance(); Token::new(TokenKind::Symbol(intern("[")), '['.into(), start_offset) }
            ']' => { self.advance(); Token::new(TokenKind::Symbol(intern("]")), ']'.into(), start_offset) }
            '{' => { self.advance(); Token::new(TokenKind::Symbol(intern("{")), '{'.into(), start_offset) }
            '}' => { self.advance(); Token::new(TokenKind::Symbol(intern("}")), '}'.into(), start_offset) }
            '=' => { self.advance(); Token::new(TokenKind::Symbol(intern("=")), '='.into(), start_offset) }
            '#' => { self.advance(); Token::new(TokenKind::Symbol(intern("#")), '#'.into(), start_offset) }
            '>' => { self.advance(); Token::new(TokenKind::Symbol(intern(">")), '>'.into(), start_offset) }
            '@' => { self.advance(); Token::new(TokenKind::Symbol(intern("@")), '@'.into(), start_offset) }
            '`' => { self.advance(); Token::new(TokenKind::Symbol(intern("`")), '`'.into(), start_offset) }
            // Error
            _ => {
                self.advance();
                Token::new(TokenKind::Error, ch.to_string(), start_offset)
            }
        }
    }

    fn lex_ident(&mut self) -> Token {
        let start = self.pos;
        let start_offset = self.offset;
        while self.pos < self.input.len() {
            let ch = self.peek();
            if ch.is_alphanumeric() || ch == '_' || ch == '\'' || ch == '.' {
                if ch == '.' {
                    // Only include dot if it's part of a qualified name (next char is ident char, not another dot)
                    match self.peek_n(1) {
                        Some('.') => break, // don't eat ..
                        Some(c) if !c.is_alphanumeric() && c != '_' && c != '\'' => break,
                        None => break,
                        _ => {} // dot followed by ident char => include it (qualified name)
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

        // Eat the variable name
        while self.pos < self.input.len() && self.peek().is_alphanumeric() {
            self.advance();
        }

        let text: String = self.input[start..self.pos].iter().collect();
        let kind = if text.starts_with("?'") {
            TokenKind::SchematicTypeVar
        } else {
            TokenKind::TypeVar
        };
        Token::new(kind, text, start_offset)
    }

    fn lex_string(&mut self) -> Token {
        let start = self.pos;
        let start_offset = self.offset;
        self.advance(); // opening "
        while self.pos < self.input.len() && self.peek() != '"' {
            if self.peek() == '\\' {
                self.advance(); // skip escape
            }
            self.advance();
        }
        if self.pos < self.input.len() {
            self.advance(); // closing "
        }
        let text: String = self.input[start..self.pos].iter().collect();
        Token::new(TokenKind::String, text, start_offset)
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

    fn skip_comment(&mut self) {
        // Already saw `(*`
        self.advance_by(2);
        let mut depth = 1;
        while self.pos < self.input.len() && depth > 0 {
            match self.peek() {
                '(' if self.peek_n(1) == Some('*') => {
                    self.advance_by(2);
                    depth += 1;
                }
                '*' if self.peek_n(1) == Some(')') => {
                    self.advance_by(2);
                    depth -= 1;
                }
                _ => { self.advance(); }
            }
        }
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            while self.pos < self.input.len() && self.peek().is_whitespace() {
                self.advance();
            }
            // Check if we're at a comment
            if self.peek() == '(' && self.peek_n(1) == Some('*') {
                self.skip_comment();
            } else {
                break;
            }
        }
    }

    fn peek(&self) -> char {
        self.input.get(self.pos).copied().unwrap_or('\0')
    }

    fn peek_n(&self, n: usize) -> Option<char> {
        self.input.get(self.pos + n).copied()
    }

    fn advance(&mut self) {
        if self.pos < self.input.len() {
            self.pos += 1;
            self.offset += 1;
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
        match &tokens[0].kind { TokenKind::Symbol(s) => assert_eq!(s.as_ref(), "==>"), _ => panic!() }
        match &tokens[1].kind { TokenKind::Symbol(s) => assert_eq!(s.as_ref(), "!!"), _ => panic!() }
        match &tokens[2].kind { TokenKind::Symbol(s) => assert_eq!(s.as_ref(), "=="), _ => panic!() }
        match &tokens[3].kind { TokenKind::Symbol(s) => assert_eq!(s.as_ref(), "=>"), _ => panic!() }
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
}
