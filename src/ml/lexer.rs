use super::{MlError, MlErrorKind, Span};
use std::sync::atomic::{AtomicBool, Ordering};

const STOP_CHECK_BYTES: usize = 256;

pub(super) fn check_stop(
    stop: &AtomicBool,
    source_name: &str,
    position: usize,
) -> Result<(), MlError> {
    if stop.load(Ordering::Acquire) {
        return Err(MlError::new(
            MlErrorKind::Stopped,
            Span::new(source_name, position, position),
            "supervisor",
            "evaluation cancelled",
        ));
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum TokenKind {
    Name(String),
    Integer { value: i64, is_negative: bool },
    Real(String),
    Word(u64),
    Text(Vec<u8>),
    Character(u8),
    Symbol(char),
    Eof,
}

#[derive(Clone, Debug)]
pub(super) struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

pub(super) fn tokenize(
    source_name: &str,
    source: &str,
    stop: &AtomicBool,
) -> Result<Vec<Token>, MlError> {
    check_stop(stop, source_name, 0)?;
    let mut lexer = Lexer { source_name, source, position: 0, stop, last_stop_check: 0 };
    let mut tokens = Vec::new();
    while lexer.position < source.len() {
        lexer.poll_stop()?;
        lexer.skip_space_and_comments()?;
        if lexer.position == source.len() {
            break;
        }
        tokens.push(lexer.scan_token()?);
    }
    check_stop(stop, source_name, lexer.position)?;
    tokens.push(Token {
        kind: TokenKind::Eof,
        span: Span::new(source_name, source.len(), source.len()),
    });
    Ok(tokens)
}

struct Lexer<'a> {
    source_name: &'a str,
    source: &'a str,
    position: usize,
    stop: &'a AtomicBool,
    last_stop_check: usize,
}

impl Lexer<'_> {
    fn poll_stop(&mut self) -> Result<(), MlError> {
        if self.position.saturating_sub(self.last_stop_check) >= STOP_CHECK_BYTES {
            self.last_stop_check = self.position;
            check_stop(self.stop, self.source_name, self.position)?;
        }
        Ok(())
    }
    fn span(&self, start: usize) -> Span {
        Span::new(self.source_name, start, self.position)
    }

    fn error(&self, start: usize, message: impl Into<String>) -> MlError {
        MlError::syntax(self.span(start), message)
    }

    fn starts(&self, prefix: &str) -> bool {
        self.source[self.position..].starts_with(prefix)
    }

    fn advance(&mut self) -> Option<char> {
        let c = self.source[self.position..].chars().next()?;
        self.position += c.len_utf8();
        Some(c)
    }

    fn skip_space_and_comments(&mut self) -> Result<(), MlError> {
        loop {
            while self.source[self.position..].starts_with(char::is_whitespace) {
                self.poll_stop()?;
                self.advance();
            }
            if !self.starts("(*") {
                return Ok(());
            }
            let start = self.position;
            self.position += 2;
            let mut depth = 1usize;
            while depth > 0 {
                self.poll_stop()?;
                if self.position == self.source.len() {
                    return Err(self.error(start, "unterminated comment"));
                }
                if self.starts("(*") {
                    depth += 1;
                    self.position += 2;
                } else if self.starts("*)") {
                    depth -= 1;
                    self.position += 2;
                } else {
                    self.advance();
                }
            }
        }
    }

    fn scan_token(&mut self) -> Result<Token, MlError> {
        let start = self.position;
        if self.starts("...") {
            self.position += 3;
            return Ok(Token { kind: TokenKind::Name("...".to_owned()), span: self.span(start) });
        }
        let char_literal = self.starts("#\"");
        if char_literal {
            self.advance();
        }
        let first = self.advance().expect("position is not at end");
        let kind = match first {
            '"' => {
                let value = self.scan_string(start)?;
                if char_literal {
                    match value.as_slice() {
                        [byte] => TokenKind::Character(*byte),
                        _ => {
                            return Err(self
                                .error(start, "character literal must contain exactly one byte"));
                        },
                    }
                } else {
                    TokenKind::Text(value)
                }
            },
            '0'..='9' | '~'
                if first != '~'
                    || self.source[self.position..].starts_with(|c: char| c.is_ascii_digit()) =>
            {
                if first == '0' && self.starts("w") {
                    self.scan_word(start)?
                } else {
                    self.scan_number(start, first)?
                }
            },
            c if c.is_alphabetic() || c == '_' || c == '\'' => {
                while self.source[self.position..]
                    .starts_with(|c: char| c.is_alphanumeric() || c == '_' || c == '\'')
                {
                    self.poll_stop()?;
                    self.advance();
                }
                TokenKind::Name(self.source[start..self.position].to_owned())
            },
            c if "!%&$#+-/:<=>?@\\~`^|*".contains(c) => {
                while self.source[self.position..]
                    .starts_with(|c: char| "!%&$#+-/:<=>?@\\~`^|*".contains(c))
                {
                    self.poll_stop()?;
                    self.advance();
                }
                TokenKind::Name(self.source[start..self.position].to_owned())
            },
            c if "(),;[]{}.".contains(c) => TokenKind::Symbol(c),
            _ => return Err(self.error(start, format!("invalid Standard ML character {first:?}"))),
        };
        Ok(Token { kind, span: self.span(start) })
    }

    fn scan_word(&mut self, start: usize) -> Result<TokenKind, MlError> {
        self.advance();
        let radix = if self.starts("x") {
            self.advance();
            16
        } else {
            10
        };
        let digits_start = self.position;
        while self.source[self.position..].starts_with(|c: char| c.is_digit(radix)) {
            self.poll_stop()?;
            self.advance();
        }
        if self.position == digits_start {
            return Err(self.error(start, "word literal requires digits"));
        }
        let digits = &self.source[digits_start..self.position];
        let value = u64::from_str_radix(digits, radix).map_err(|cause| {
            self.error(start, format!("word literal {digits} out of range: {cause}"))
        })?;
        Ok(TokenKind::Word(value))
    }

    fn scan_number(&mut self, start: usize, first: char) -> Result<TokenKind, MlError> {
        while self.source[self.position..].starts_with(|c: char| c.is_ascii_digit()) {
            self.poll_stop()?;
            self.advance();
        }
        let has_fraction = self.starts(".")
            && self.source[self.position + 1..].starts_with(|c: char| c.is_ascii_digit());
        if has_fraction {
            self.advance();
            while self.source[self.position..].starts_with(|c: char| c.is_ascii_digit()) {
                self.poll_stop()?;
                self.advance();
            }
        }
        let has_exponent = self.starts("e") || self.starts("E");
        if has_exponent {
            self.advance();
            if self.starts("~") {
                self.advance();
            }
            let digits_start = self.position;
            while self.source[self.position..].starts_with(|c: char| c.is_ascii_digit()) {
                self.poll_stop()?;
                self.advance();
            }
            if self.position == digits_start {
                return Err(self.error(start, "real exponent requires digits"));
            }
        }
        if has_fraction || has_exponent {
            return Ok(TokenKind::Real(self.source[start..self.position].replace('~', "-")));
        }
        Ok(TokenKind::Integer {
            value: self.scan_integer(start, first)?,
            is_negative: first == '~',
        })
    }

    fn scan_integer(&mut self, start: usize, first: char) -> Result<i64, MlError> {
        while self.source[self.position..].starts_with(|c: char| c.is_ascii_digit()) {
            self.poll_stop()?;
            self.advance();
        }
        let digits = &self.source[start + usize::from(first == '~')..self.position];
        let magnitude = digits.parse::<u64>().map_err(|cause| {
            self.error(start, format!("integer literal {digits} out of range: {cause}"))
        })?;
        if first == '~' && magnitude == i64::MAX as u64 + 1 {
            return Ok(i64::MIN);
        }
        let number = i64::try_from(magnitude).map_err(|cause| {
            self.error(start, format!("integer literal {digits} out of range: {cause}"))
        })?;
        Ok(if first == '~' { -number } else { number })
    }

    fn scan_string(&mut self, start: usize) -> Result<Vec<u8>, MlError> {
        let mut result = Vec::new();
        loop {
            self.poll_stop()?;
            let c =
                self.advance().ok_or_else(|| self.error(start, "unterminated string literal"))?;
            match c {
                '"' => return Ok(result),
                '\\' => self.scan_escape(start, &mut result)?,
                '\n' => return Err(self.error(start, "newline in string literal")),
                _ => {
                    let mut buffer = [0; 4];
                    result.extend_from_slice(c.encode_utf8(&mut buffer).as_bytes());
                },
            }
        }
    }

    fn scan_escape(&mut self, start: usize, result: &mut Vec<u8>) -> Result<(), MlError> {
        let escape = self.advance().ok_or_else(|| self.error(start, "unterminated escape"))?;
        match escape {
            'n' => result.push(b'\n'),
            't' => result.push(b'\t'),
            'r' => result.push(b'\r'),
            '"' => result.push(b'"'),
            '\\' => result.push(b'\\'),
            '^' => {
                let control = self
                    .advance()
                    .ok_or_else(|| self.error(start, "unterminated control escape"))?;
                let code = control as u32;
                if !(64..=95).contains(&code) {
                    return Err(self.error(start, "invalid control escape"));
                }
                result.push((code - 64) as u8);
            },
            c if c.is_ascii_digit() => result.push(self.scan_numeric_escape(start, c)?),
            c if c.is_whitespace() => {
                while self.source[self.position..].starts_with(char::is_whitespace) {
                    self.poll_stop()?;
                    self.advance();
                }
                if self.advance() != Some('\\') {
                    return Err(self.error(start, "unterminated string gap"));
                }
            },
            _ => return Err(self.error(start, "invalid string escape")),
        }
        Ok(())
    }

    fn scan_numeric_escape(&mut self, start: usize, first: char) -> Result<u8, MlError> {
        let mut code = first as u32 - u32::from(b'0');
        for _ in 0..2 {
            let digit =
                self.advance().ok_or_else(|| self.error(start, "incomplete numeric escape"))?;
            if !digit.is_ascii_digit() {
                return Err(self.error(start, format!("invalid numeric escape digit {digit:?}")));
            }
            code = code * 10 + (digit as u32 - u32::from(b'0'));
        }
        u8::try_from(code).map_err(|cause| {
            self.error(start, format!("numeric escape {code} out of byte range: {cause}"))
        })
    }
}
