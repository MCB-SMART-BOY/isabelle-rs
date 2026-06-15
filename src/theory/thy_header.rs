//! Theory header parser — parse the header section of `.thy` files.
//!
//! Parses the theory header according to Isabelle syntax:
//!
//! ```text
//! theory Foo imports Bar Baz
//!   keywords "define" :: thy_decl and "apply" :: prf_script
//!   abbrevs "==>" = "\<Longrightarrow>" and "!==" = "\<noteq>"
//! begin
//! ```
//!
//! Reference: `isabelle-source/src/Pure/Thy/thy_header.ML`

/// A keyword specification parsed from the theory header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeywordSpec {
    /// The keyword name (e.g., "define")
    pub name: String,
    /// The keyword kind (e.g., "thy_decl", "prf_script", or "" if unspecified)
    pub kind: String,
    /// Optional tags (e.g., "proof", "document")
    pub tags: Vec<String>,
}

/// An abbreviation specification parsed from the theory header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbbrevSpec {
    /// Left-hand side of the abbreviation (e.g., "==>")
    pub lhs: String,
    /// Right-hand side of the abbreviation (e.g., "\<Longrightarrow>")
    pub rhs: String,
}

/// A parsed theory header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TheoryHeader {
    /// Theory name (e.g., "HOL")
    pub name: String,
    /// List of imported theory names (e.g., ["Pure", "Main"])
    pub imports: Vec<String>,
    /// Keyword declarations from the header
    pub keywords: Vec<KeywordSpec>,
    /// Abbreviation declarations from the header
    pub abbrevs: Vec<AbbrevSpec>,
    /// Byte position in the source where the body begins (after "begin")
    pub body_begin_position: usize,
}

// =========================================================================
// Parser state and helpers
// =========================================================================

/// Internal parser state operating on a character vector.
struct Parser {
    chars: Vec<char>,
    pos: usize,
}

impl Parser {
    fn new(source: &str) -> Self {
        let chars: Vec<char> = source.chars().collect();
        Parser { chars, pos: 0 }
    }

    fn eof(&self) -> bool {
        self.pos >= self.chars.len()
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    fn advance(&mut self) -> Option<char> {
        if self.eof() {
            None
        } else {
            let c = self.chars[self.pos];
            self.pos += 1;
            Some(c)
        }
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if c == ' ' || c == '\t' || c == '\n' || c == '\r' {
                self.advance();
            } else {
                break;
            }
        }
    }

    /// Check if the given keyword appears at the current position.
    /// A keyword must be followed by whitespace, a special char, or EOF.
    fn is_keyword_at(&self, word: &str) -> bool {
        let word_chars: Vec<char> = word.chars().collect();
        let wlen = word_chars.len();
        if self.pos + wlen > self.chars.len() {
            return false;
        }
        for (i, &wc) in word_chars.iter().enumerate() {
            if self.chars[self.pos + i] != wc {
                return false;
            }
        }
        // Must be a whole word: followed by whitespace, special char, or EOF
        let next = self.chars.get(self.pos + wlen).copied();
        match next {
            None => true, // EOF
            Some(c) => {
                c.is_whitespace() || c == ':' || c == '=' || c == '(' || c == ')' || c == '"'
            },
        }
    }

    /// Expect and consume the given keyword. Returns error with position info.
    fn expect_keyword(&mut self, word: &str) -> Result<(), String> {
        self.skip_whitespace();
        if self.is_keyword_at(word) {
            // Consume the keyword characters
            for _ in 0..word.chars().count() {
                self.advance();
            }
            Ok(())
        } else {
            let near: String = self.chars[self.pos..].iter().take(20).copied().collect();
            Err(format!("Expected '{}' at position {}, found '{}'", word, self.pos, near))
        }
    }

    fn is_ident_start(c: char) -> bool {
        c.is_alphabetic() || c == '_'
    }

    fn is_ident_cont(c: char) -> bool {
        c.is_alphanumeric() || c == '_' || c == '\'' || c == '.'
    }

    /// Parse an unquoted identifier (theory name, import name).
    fn parse_identifier(&mut self) -> Result<String, String> {
        self.skip_whitespace();
        let start = self.pos;
        if self.eof() {
            return Err(format!("Expected identifier at position {}", self.pos));
        }
        let c = self.chars[self.pos];
        if !Self::is_ident_start(c) {
            return Err(format!("Expected identifier at position {}, found '{}'", self.pos, c));
        }
        self.advance();
        while let Some(c) = self.peek() {
            if Self::is_ident_cont(c) {
                self.advance();
            } else {
                break;
            }
        }
        Ok(self.chars[start..self.pos].iter().copied().collect())
    }

    /// Parse a double-quoted string, handling Isabelle escapes `\<...>`.
    fn parse_string(&mut self) -> Result<String, String> {
        self.skip_whitespace();
        if self.peek() != Some('"') {
            return Err(format!(
                "Expected '\"' at position {}, found '{}'",
                self.pos,
                self.peek().unwrap_or('<')
            ));
        }
        self.advance(); // consume opening quote

        let mut result = String::new();
        loop {
            match self.advance() {
                None => {
                    return Err(format!("Unterminated string starting at position {}", self.pos));
                },
                Some('"') => break, // closing quote
                Some('\\') => {
                    // Isabelle escape: \<name> or any backslash sequence
                    if self.peek() == Some('<') {
                        // Named character escape: \<...>
                        self.advance(); // consume '<'
                        result.push('\\');
                        result.push('<');
                        loop {
                            match self.advance() {
                                None => {
                                    return Err(format!(
                                        "Unterminated escape in string at position {}",
                                        self.pos
                                    ));
                                },
                                Some('>') => {
                                    result.push('>');
                                    break;
                                },
                                Some(c) => result.push(c),
                            }
                        }
                    } else {
                        // Keep backslash and following char as-is
                        result.push('\\');
                        if let Some(c) = self.advance() {
                            result.push(c);
                        }
                    }
                },
                Some(c) => result.push(c),
            }
        }
        Ok(result)
    }

    /// Parse a parenthesized tag list: (tag1, tag2, ...)
    fn parse_tags(&mut self) -> Result<Vec<String>, String> {
        self.skip_whitespace();
        let mut tags = Vec::new();
        if self.peek() == Some('(') {
            self.advance(); // consume '('
            loop {
                self.skip_whitespace();
                if self.peek() == Some(')') {
                    self.advance();
                    break;
                }
                if !tags.is_empty() {
                    // expect comma
                    if self.peek() == Some(',') {
                        self.advance();
                        self.skip_whitespace();
                    } else {
                        return Err(format!(
                            "Expected ',' or ')' in tag list at position {}",
                            self.pos
                        ));
                    }
                }
                let tag = self.parse_identifier()?;
                tags.push(tag);
            }
        }
        Ok(tags)
    }

    /// Parse optional parenthesized content after a keyword kind spec.
    ///
    /// In Isabelle, after the kind name there can be:
    /// - A load command: `("name")` — parenthesized single identifier
    /// - Tags: `(tag1, tag2, ...)` — parenthesized comma-separated list
    ///
    /// These are ambiguous when only one identifier is in the parens.
    /// We peek inside the parentheses to decide:
    /// - If there are commas, it's a tag list (load_command is empty)
    /// - If it's exactly one identifier, treat it as a load command (discarded) since load_command
    ///   has priority in the Isabelle grammar.
    ///
    /// Returns the tag list (empty if no tags present).
    fn parse_post_spec_parens(&mut self) -> Result<Vec<String>, String> {
        self.skip_whitespace();
        if self.peek() != Some('(') {
            return Ok(Vec::new());
        }

        // Save position so we can peek ahead
        let saved_pos = self.pos;
        self.advance(); // consume '('

        // Peek at the content to decide: load_command or tags?
        let mut peek_pos = self.pos;
        let mut has_comma = false;
        let mut depth = 1;
        while peek_pos < self.chars.len() && depth > 0 {
            match self.chars[peek_pos] {
                '(' => depth += 1,
                ')' => depth -= 1,
                ',' if depth == 1 => has_comma = true,
                _ => {},
            }
            peek_pos += 1;
        }

        if has_comma {
            // It's a tag list (commas present). Parse it.
            self.pos = saved_pos;
            self.parse_tags()
        } else {
            // It's a load command: ("name"). Discard it.
            let _load_name = self.parse_identifier()?;
            self.skip_whitespace();
            if self.advance() != Some(')') {
                return Err(format!("Expected ')' closing load command at position {}", self.pos));
            }
            // After load_command, there could still be tags
            self.parse_tags()
        }
    }

    /// Parse a keyword specification: kind [load_command] [tags]
    fn parse_keyword_spec(&mut self) -> Result<(String, Vec<String>), String> {
        let kind = self.parse_identifier()?;
        let tags = self.parse_post_spec_parens()?;
        Ok((kind, tags))
    }

    /// Parse one keyword declaration: strings [:: spec]
    fn parse_keyword_decl(&mut self) -> Result<Vec<KeywordSpec>, String> {
        self.skip_whitespace();
        let mut names = Vec::new();

        // Parse one or more quoted strings
        loop {
            self.skip_whitespace();
            if self.peek() == Some('"') {
                let name = self.parse_string()?;
                names.push(name);
            } else {
                break;
            }
        }

        if names.is_empty() {
            return Err(format!("Expected at least one keyword name at position {}", self.pos));
        }

        // Optional :: spec
        self.skip_whitespace();
        let (kind, tags) = if self.peek() == Some(':') {
            self.advance(); // consume first ':'
            if self.advance() != Some(':') {
                return Err(format!("Expected '::' for keyword spec at position {}", self.pos));
            }
            self.parse_keyword_spec()?
        } else {
            (String::new(), Vec::new())
        };

        Ok(names
            .into_iter()
            .map(|name| KeywordSpec { name, kind: kind.clone(), tags: tags.clone() })
            .collect())
    }

    /// Parse an `and`-separated list of keyword declarations.
    fn parse_keyword_decls(&mut self) -> Result<Vec<KeywordSpec>, String> {
        let mut all_keywords = Vec::new();
        loop {
            let decls = self.parse_keyword_decl()?;
            all_keywords.extend(decls);

            self.skip_whitespace();
            if self.is_keyword_at("and") {
                // consume "and"
                for _ in 0..3 {
                    self.advance();
                }
            } else {
                break;
            }
        }
        Ok(all_keywords)
    }

    /// Parse one abbreviation: strings = strings
    fn parse_abbrev_decl(&mut self) -> Result<Vec<AbbrevSpec>, String> {
        self.skip_whitespace();

        // Parse LHS strings
        let mut lhs_strings = Vec::new();
        while self.peek() == Some('"') {
            lhs_strings.push(self.parse_string()?);
            self.skip_whitespace();
        }
        if lhs_strings.is_empty() {
            return Err(format!(
                "Expected quoted string for abbreviation LHS at position {}",
                self.pos
            ));
        }

        // Expect '='
        self.skip_whitespace();
        if self.advance() != Some('=') {
            return Err(format!("Expected '=' in abbreviation at position {}", self.pos));
        }

        // Parse RHS strings
        let mut rhs_strings = Vec::new();
        self.skip_whitespace();
        while self.peek() == Some('"') {
            rhs_strings.push(self.parse_string()?);
            self.skip_whitespace();
        }
        if rhs_strings.is_empty() {
            return Err(format!(
                "Expected quoted string for abbreviation RHS at position {}",
                self.pos
            ));
        }

        // Cross-product of LHS × RHS (matching Isabelle's map_product behavior)
        let mut result = Vec::new();
        for lhs in &lhs_strings {
            for rhs in &rhs_strings {
                result.push(AbbrevSpec { lhs: lhs.clone(), rhs: rhs.clone() });
            }
        }
        Ok(result)
    }

    /// Parse an `and`-separated list of abbreviation declarations.
    fn parse_abbrevs(&mut self) -> Result<Vec<AbbrevSpec>, String> {
        let mut all_abbrevs = Vec::new();
        loop {
            let decls = self.parse_abbrev_decl()?;
            all_abbrevs.extend(decls);

            self.skip_whitespace();
            if self.is_keyword_at("and") {
                for _ in 0..3 {
                    self.advance();
                }
            } else {
                break;
            }
        }
        Ok(all_abbrevs)
    }
}

// =========================================================================
// Public API
// =========================================================================

/// Parse a theory header from source text.
///
/// Returns a `TheoryHeader` on success, or an error message on parse failure.
///
/// # Examples
///
/// ```
/// use crate::theory::thy_header::parse_header;
///
/// let header = parse_header("theory Foo imports Bar begin").unwrap();
/// assert_eq!(header.name, "Foo");
/// assert_eq!(header.imports, vec!["Bar"]);
/// ```
pub fn parse_header(source: &str) -> Result<TheoryHeader, String> {
    let mut p = Parser::new(source);

    // Parse "theory Name"
    p.skip_whitespace();
    p.expect_keyword("theory")?;
    let name = p.parse_identifier()?;

    // Parse imports (optional for Pure, but we require "imports" for simplicity)
    // Check if there's an imports keyword
    p.skip_whitespace();
    let imports = if p.is_keyword_at("imports") {
        p.expect_keyword("imports")?;
        let mut imports = Vec::new();
        loop {
            p.skip_whitespace();
            // Stop if we hit keywords, abbrevs, or begin
            if p.eof()
                || p.is_keyword_at("keywords")
                || p.is_keyword_at("abbrevs")
                || p.is_keyword_at("begin")
            {
                break;
            }
            let name = p.parse_identifier()?;
            imports.push(name);
        }
        imports
    } else if p.is_keyword_at("begin") {
        // No imports section (like Pure)
        Vec::new()
    } else {
        return Err(format!(
            "Expected 'imports' or 'begin' after theory name at position {}",
            p.pos
        ));
    };

    // Optional keywords block
    p.skip_whitespace();
    let keywords = if p.is_keyword_at("keywords") {
        p.expect_keyword("keywords")?;
        p.parse_keyword_decls()?
    } else {
        Vec::new()
    };

    // Optional abbrevs block
    p.skip_whitespace();
    let abbrevs = if p.is_keyword_at("abbrevs") {
        p.expect_keyword("abbrevs")?;
        p.parse_abbrevs()?
    } else {
        Vec::new()
    };

    // Expect "begin"
    p.skip_whitespace();
    p.expect_keyword("begin")?;

    Ok(TheoryHeader { name, imports, keywords, abbrevs, body_begin_position: p.pos })
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------
    // Basic parsing
    // -----------------------------------------------------------------

    #[test]
    fn test_simple_header() {
        let header = parse_header("theory Foo imports Bar begin").unwrap();
        assert_eq!(header.name, "Foo");
        assert_eq!(header.imports, vec!["Bar"]);
        assert!(header.keywords.is_empty());
        assert!(header.abbrevs.is_empty());
        assert!(header.body_begin_position > 0);
    }

    #[test]
    fn test_multiple_imports() {
        let header = parse_header("theory Foo imports Bar Baz Qux begin").unwrap();
        assert_eq!(header.name, "Foo");
        assert_eq!(header.imports, vec!["Bar", "Baz", "Qux"]);
    }

    #[test]
    fn test_imports_with_newlines() {
        let header = parse_header("theory Foo\nimports\n  Bar\n  Baz\nbegin").unwrap();
        assert_eq!(header.imports, vec!["Bar", "Baz"]);
    }

    #[test]
    fn test_single_import() {
        let header = parse_header("theory HOL imports Pure begin").unwrap();
        assert_eq!(header.name, "HOL");
        assert_eq!(header.imports, vec!["Pure"]);
    }

    // -----------------------------------------------------------------
    // Keywords parsing
    // -----------------------------------------------------------------

    #[test]
    fn test_keywords_single() {
        let header =
            parse_header("theory Foo imports Bar keywords \"define\" :: thy_decl begin").unwrap();
        assert_eq!(header.keywords.len(), 1);
        assert_eq!(header.keywords[0].name, "define");
        assert_eq!(header.keywords[0].kind, "thy_decl");
        assert!(header.keywords[0].tags.is_empty());
    }

    #[test]
    fn test_keywords_multiple_and() {
        let header = parse_header(
            "theory Foo imports Bar keywords \"define\" :: thy_decl and \"apply\" :: prf_script \
             begin",
        )
        .unwrap();
        assert_eq!(header.keywords.len(), 2);
        assert_eq!(header.keywords[0].name, "define");
        assert_eq!(header.keywords[0].kind, "thy_decl");
        assert_eq!(header.keywords[1].name, "apply");
        assert_eq!(header.keywords[1].kind, "prf_script");
    }

    #[test]
    fn test_keywords_no_spec() {
        // Keywords without :: get empty kind
        let header =
            parse_header("theory Foo imports Bar keywords \"chapter\" \"section\" begin").unwrap();
        assert_eq!(header.keywords.len(), 2);
        assert_eq!(header.keywords[0].name, "chapter");
        assert_eq!(header.keywords[0].kind, "");
        assert_eq!(header.keywords[1].name, "section");
        assert_eq!(header.keywords[1].kind, "");
    }

    #[test]
    fn test_keywords_with_tags() {
        let header = parse_header(
            "theory Foo imports Bar keywords \"text_raw\" :: thy_decl (document, raw) begin",
        )
        .unwrap();
        assert_eq!(header.keywords.len(), 1);
        assert_eq!(header.keywords[0].name, "text_raw");
        assert_eq!(header.keywords[0].kind, "thy_decl");
        assert_eq!(header.keywords[0].tags, vec!["document", "raw"]);
    }

    #[test]
    fn test_keywords_multiple_names_one_spec() {
        // "a" "b" :: thy_decl — two names share the same kind
        let header =
            parse_header("theory Foo imports Bar keywords \"a\" \"b\" :: thy_decl begin").unwrap();
        assert_eq!(header.keywords.len(), 2);
        assert_eq!(header.keywords[0].name, "a");
        assert_eq!(header.keywords[0].kind, "thy_decl");
        assert_eq!(header.keywords[1].name, "b");
        assert_eq!(header.keywords[1].kind, "thy_decl");
    }

    // -----------------------------------------------------------------
    // Abbrevs parsing
    // -----------------------------------------------------------------

    #[test]
    fn test_abbrevs_single() {
        let header =
            parse_header("theory Foo imports Bar abbrevs \"==>\" = \"\\<Longrightarrow>\" begin")
                .unwrap();
        assert_eq!(header.abbrevs.len(), 1);
        assert_eq!(header.abbrevs[0].lhs, "==>");
        assert_eq!(header.abbrevs[0].rhs, "\\<Longrightarrow>");
    }

    #[test]
    fn test_abbrevs_multiple_and() {
        let header = parse_header(
            "theory Foo imports Bar abbrevs \"==>\" = \"\\<Longrightarrow>\" and \"!=-\" = \
             \"\\<noteq>\" begin",
        )
        .unwrap();
        assert_eq!(header.abbrevs.len(), 2);
        assert_eq!(header.abbrevs[0].lhs, "==>");
        assert_eq!(header.abbrevs[1].lhs, "!=-");
        assert_eq!(header.abbrevs[1].rhs, "\\<noteq>");
    }

    #[test]
    fn test_abbrevs_cross_product() {
        // Multiple LHS strings × RHS strings
        let header =
            parse_header("theory Foo imports Bar abbrevs \"a\" \"b\" = \"c\" \"d\" begin").unwrap();
        // Cross product: (a,c), (a,d), (b,c), (b,d)
        assert_eq!(header.abbrevs.len(), 4);
    }

    // -----------------------------------------------------------------
    // Combined parsing
    // -----------------------------------------------------------------

    #[test]
    fn test_keywords_and_abbrevs() {
        let header = parse_header(
            "theory Foo imports Bar keywords \"def\" :: thy_decl abbrevs \"-->\" = \
             \"\\<longrightarrow>\" begin",
        )
        .unwrap();
        assert_eq!(header.keywords.len(), 1);
        assert_eq!(header.keywords[0].name, "def");
        assert_eq!(header.abbrevs.len(), 1);
        assert_eq!(header.abbrevs[0].lhs, "-->");
    }

    #[test]
    fn test_hol_style_header() {
        // Simulate a typical HOL theory header
        let source = r#"theory HOL
imports Pure
keywords
  "definition" :: thy_defn
  and "fun" :: thy_defn
  and "primrec" :: thy_defn
  and "lemma" :: thy_goal_stmt
  and "theorem" :: thy_goal_stmt
  and "apply" :: prf_script
  and "done" :: qed_script
begin"#;
        let header = parse_header(source).unwrap();
        assert_eq!(header.name, "HOL");
        assert_eq!(header.imports, vec!["Pure"]);
        assert_eq!(header.keywords.len(), 7);
        assert!(header.abbrevs.is_empty());

        // Check specific entries
        let definition = &header.keywords[0];
        assert_eq!(definition.name, "definition");
        assert_eq!(definition.kind, "thy_defn");

        let lemma = &header.keywords[3];
        assert_eq!(lemma.name, "lemma");
        assert_eq!(lemma.kind, "thy_goal_stmt");

        let done_kw = &header.keywords[6];
        assert_eq!(done_kw.name, "done");
        assert_eq!(done_kw.kind, "qed_script");
    }

    // -----------------------------------------------------------------
    // Error handling
    // -----------------------------------------------------------------

    #[test]
    fn test_error_missing_theory() {
        let result = parse_header("Foo imports Bar begin");
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Expected 'theory'"));
    }

    #[test]
    fn test_error_missing_begin() {
        let result = parse_header("theory Foo imports Bar");
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Expected 'begin'"));
    }

    #[test]
    fn test_error_empty() {
        let result = parse_header("");
        assert!(result.is_err());
    }

    #[test]
    fn test_error_unterminated_string() {
        let result = parse_header("theory Foo imports Bar keywords \"unclosed begin");
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Unterminated string"));
    }

    // -----------------------------------------------------------------
    // Edge cases
    // -----------------------------------------------------------------

    #[test]
    fn test_trailing_whitespace() {
        let header = parse_header("theory Foo imports Bar begin   \n  ").unwrap();
        assert_eq!(header.name, "Foo");
    }

    #[test]
    fn test_leading_whitespace() {
        let header = parse_header("  \n  theory Foo imports Bar begin").unwrap();
        assert_eq!(header.name, "Foo");
    }

    #[test]
    fn test_name_with_underscores() {
        let header = parse_header("theory My_Theory imports Base_Theory begin").unwrap();
        assert_eq!(header.name, "My_Theory");
        assert_eq!(header.imports, vec!["Base_Theory"]);
    }

    #[test]
    fn test_name_with_dots() {
        let header = parse_header("theory HOL.Algebra imports HOL begin").unwrap();
        // Note: dots in names may be handled differently depending on the Isabelle version.
        // This test verifies current behavior.
        assert_eq!(header.name, "HOL.Algebra");
    }

    #[test]
    fn test_keywords_with_escape() {
        let header =
            parse_header("theory Foo imports Bar keywords \"\\<alpha>\" :: thy_decl begin")
                .unwrap();
        assert_eq!(header.keywords[0].name, "\\<alpha>");
    }

    #[test]
    fn test_abbrevs_with_escape() {
        let header =
            parse_header("theory Foo imports Bar abbrevs \"=>\" = \"\\<Rightarrow>\" begin")
                .unwrap();
        assert_eq!(header.abbrevs[0].rhs, "\\<Rightarrow>");
    }
}
