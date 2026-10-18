//! Fail-closed, single-file legacy theory loading. No kernel accepted tokens.

use std::{
    collections::HashMap,
    path::{Path, PathBuf},
    sync::Arc,
};

use crate::{
    core::{
        term::Term,
        theory::{Theory, TheoryMergeError},
        thm::Thm,
    },
    isar::{
        outer_syntax::{CommandSpan, OuterSyntax},
        proof::{IsarProof, ProofMode},
        proof_result::GoalExportError,
        spec::Typedecl,
        term_parser::{parse_term, parse_type},
        token::{LexError, Token, TokenKind},
    },
    theory::{
        local_theory::LocalTheory,
        registry::TheoryRegistry,
        thy_header::{TheoryHeader, has_header_declarations, parse_header},
    },
};

/// Input failures are user-fixable; a processing panic is a fatal implementation error.
#[derive(Debug, Clone, thiserror::Error)]
pub enum TheoryLoadError {
    /// A source file could not be read. Sharing preserves the original I/O error chain.
    #[error("cannot read theory at {path}: {source}")]
    Io { path: PathBuf, source: Arc<std::io::Error> },
    /// The complete source has no valid theory header.
    #[error("invalid theory header: {detail}")]
    Header { detail: String },
    /// Dynamic keywords and abbreviations are not implemented by this loader.
    #[error("theory header keywords and abbreviations are unsupported")]
    UnsupportedHeaderDeclarations,
    /// Only the fixed Pure bootstrap may have no imports.
    #[error("theory `{theory}` requires at least one import")]
    MissingImports { theory: String },
    /// Inherited declarations or parent identities cannot be merged atomically.
    #[error("cannot merge imports of theory `{theory}`: {source}")]
    ImportMerge { theory: String, source: TheoryMergeError },
    /// A named parent is unavailable or failed this build.
    #[error("theory `{theory}` imports unavailable theory `{import}`")]
    MissingImport { theory: String, import: String },
    /// Two files or a reserved theory claim the same identity.
    #[error("duplicate theory name `{name}`")]
    DuplicateTheory { name: String },
    /// A dependency cycle prevents a theory from being scheduled.
    #[error("unresolved dependencies for theory `{theory}`: {imports:?}")]
    UnresolvedDependencies { theory: String, imports: Vec<String> },
    /// The source ended before its theory terminator.
    #[error("theory `{theory}` has no final end command")]
    MissingEnd { theory: String },
    /// A command is unsupported or invalid in the current state.
    #[error("unexpected command `{command}` at line {line}")]
    UnexpectedCommand { command: String, line: usize },
    /// An allowed command did not consume its complete argument syntax.
    #[error("malformed command `{command}` at line {line}")]
    MalformedCommand { command: String, line: usize },
    /// A declaration failed validation in its inherited signature.
    #[error("declaration `{command}` failed at line {line}: {detail}")]
    Declaration { command: String, line: usize, detail: String },
    /// A command did not produce evidence for the requested proposition.
    #[error("proof failed at line {line}: {source}")]
    Proof { line: usize, source: GoalExportError },
    /// Lexing rejected a malformed token in the original source.
    #[error("invalid theory source: {source}")]
    Lexical { source: LexError },
    /// An implementation failure aborted this transaction; no partial result is published.
    #[error("fatal panic processing `{command}` at line {line}: {detail}")]
    ProcessingPanic { command: String, line: usize, detail: String },
    /// A processor owns exactly one source transaction.
    #[error("theory processor has already consumed a source transaction")]
    TransactionConsumed,
}

/// Stages declarations and proofs until the complete source has succeeded.
pub struct TheoryProcessor {
    registry: TheoryRegistry,
    expected_name: Option<String>,
    local: Option<LocalTheory>,
    proof: Option<IsarProof>,
    pending_lemma: Option<String>,
    theorems: HashMap<String, Arc<Thm>>,
    search_db: crate::hol::hol_loader::HolTheoremDb,
    errors: Vec<TheoryLoadError>,
    has_started: bool,
    is_committed: bool,
    has_end: bool,
    /// Number of attempted lemma declarations, including failures.
    pub lemma_count: usize,
    /// Legacy search option; explicitly rejected at this complete-source boundary.
    pub accept_all: bool,
}

impl TheoryProcessor {
    pub fn new(registry: TheoryRegistry) -> Self {
        Self {
            registry,
            expected_name: None,
            local: None,
            proof: None,
            pending_lemma: None,
            theorems: HashMap::new(),
            search_db: crate::hol::hol_loader::HolTheoremDb::new(),
            errors: Vec::new(),
            has_started: false,
            is_committed: false,
            has_end: false,
            lemma_count: 0,
            accept_all: false,
        }
    }

    pub fn for_theory(registry: TheoryRegistry, name: &str) -> Self {
        let mut processor = Self::new(registry);
        processor.expected_name = Some(name.to_string());
        processor
    }

    pub fn process_file(path: &Path) -> Result<Arc<Theory>, Vec<TheoryLoadError>> {
        let source = std::fs::read_to_string(path).map_err(|source| {
            vec![TheoryLoadError::Io { path: path.to_path_buf(), source: Arc::new(source) }]
        })?;
        Self::new(TheoryRegistry::new()).process_source(&source)
    }

    pub fn process_source(&mut self, source: &str) -> Result<Arc<Theory>, Vec<TheoryLoadError>> {
        if self.has_started {
            return Err(vec![TheoryLoadError::TransactionConsumed]);
        }
        self.has_started = true;
        match self.process_complete_source(source) {
            Ok(theory) => {
                self.is_committed = true;
                Ok(theory)
            },
            Err(error) => {
                self.local = None;
                self.proof = None;
                self.pending_lemma = None;
                self.theorems.clear();
                self.errors.push(error);
                self.search_db.by_name.clear();
                Err(self.errors.clone())
            },
        }
    }

    /// Counts are transitional legacy results, never KernelTrustedClosed.
    pub fn process_source_verified(
        &mut self,
        source: &str,
    ) -> Result<(Arc<Theory>, usize, usize), Vec<TheoryLoadError>> {
        let theory = self.process_source(source)?;
        Ok((theory, self.closed_theorem_count(), self.theorem_count()))
    }

    fn process_complete_source(&mut self, source: &str) -> Result<Arc<Theory>, TheoryLoadError> {
        if self.accept_all {
            return Err(TheoryLoadError::UnexpectedCommand {
                command: "accept_all".into(),
                line: 1,
            });
        }
        let header = parse_header(source).map_err(|detail| TheoryLoadError::Header { detail })?;
        let spans = OuterSyntax::standard()
            .parse_spans_checked_from(source, header.body_begin_position)
            .map_err(|source| TheoryLoadError::Lexical { source })?;
        self.begin_theory(source, &header)?;
        for span in &spans {
            self.process_guarded_span(span, span.line_number(source))?;
        }
        if !self.has_end {
            return Err(TheoryLoadError::MissingEnd { theory: header.name });
        }
        self.finalize_completed()
    }

    fn begin_theory(&mut self, source: &str, header: &TheoryHeader) -> Result<(), TheoryLoadError> {
        if has_header_declarations(source).map_err(|detail| TheoryLoadError::Header { detail })? {
            return Err(TheoryLoadError::UnsupportedHeaderDeclarations);
        }
        if self.expected_name.as_ref().is_some_and(|name| name != &header.name) {
            return Err(TheoryLoadError::Header {
                detail: format!("expected {:?}, got `{}`", self.expected_name, header.name),
            });
        }
        if self.registry.lookup(&header.name).is_some() {
            return Err(TheoryLoadError::DuplicateTheory { name: header.name.clone() });
        }
        if header.imports.is_empty() {
            return Err(TheoryLoadError::MissingImports { theory: header.name.clone() });
        }
        let parents = header
            .imports
            .iter()
            .map(|import| {
                self.registry.lookup(import).ok_or_else(|| TheoryLoadError::MissingImport {
                    theory: header.name.clone(),
                    import: import.clone(),
                })
            })
            .collect::<Result<_, _>>()?;
        let local = LocalTheory::begin(parents, &header.name).map_err(|source| {
            TheoryLoadError::ImportMerge { theory: header.name.clone(), source }
        })?;
        for parent in local.parents() {
            for name in parent.all_theorem_names() {
                if let Some(theorem) = parent.lookup_theorem(name) {
                    self.search_db.insert_named_fact(name.to_owned(), Arc::clone(theorem));
                }
            }
        }
        self.local = Some(local);
        Ok(())
    }

    fn process_guarded_span(
        &mut self,
        span: &CommandSpan,
        line: usize,
    ) -> Result<(), TheoryLoadError> {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.process_span(span, line)
        })) {
            Ok(result) => result,
            Err(payload) => {
                let detail = payload
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| payload.downcast_ref::<&str>().map(|text| text.to_string()))
                    .unwrap_or_else(|| "non-string panic payload".into());
                Err(TheoryLoadError::ProcessingPanic { command: span.name.clone(), line, detail })
            },
        }
    }

    fn process_span(&mut self, span: &CommandSpan, line: usize) -> Result<(), TheoryLoadError> {
        if self.has_end {
            return Err(unexpected(span, line));
        }
        match span.name.as_str() {
            "end" if self.proof.is_none() && span.tokens.len() == 1 => self.has_end = true,
            "typedecl" if self.proof.is_none() => self.declare_type(span, line)?,
            "lemma" | "theorem" | "corollary" if self.proof.is_none() => {
                self.begin_lemma(span, line)?
            },
            "chapter" | "section" | "subsection" | "subsubsection" | "paragraph"
            | "subparagraph" | "text" => {
                if self.proof.is_some()
                    || !matches!(&span.tokens[1..], [token] if token.kind == TokenKind::String)
                {
                    return Err(malformed(span, line));
                }
            },
            "proof" | "have" | "show" | "fix" | "assume" | "apply" | "by" | "qed" | "done" => {
                self.process_proof_command(span, line)?;
            },
            _ => return Err(unexpected(span, line)),
        }
        Ok(())
    }

    fn declare_type(&mut self, span: &CommandSpan, line: usize) -> Result<(), TheoryLoadError> {
        let full_command = format!("typedecl {}", span.body);
        let declaration = Typedecl::parse(&full_command).ok_or_else(|| malformed(span, line))?;
        let local = self.local.as_mut().ok_or_else(|| unexpected(span, line))?;
        local.declare_type(&declaration.name, declaration.arity).map_err(|error| {
            TheoryLoadError::Declaration {
                command: span.name.clone(),
                line,
                detail: error.to_string(),
            }
        })
    }

    fn begin_lemma(&mut self, span: &CommandSpan, line: usize) -> Result<(), TheoryLoadError> {
        self.lemma_count += 1;
        let (name, term) = parse_named_proposition(span, line)?;
        if self.theorems.contains_key(&name) {
            return Err(TheoryLoadError::Declaration {
                command: span.name.clone(),
                line,
                detail: format!("duplicate theorem `{name}`"),
            });
        }
        let local = self.local.as_ref().ok_or_else(|| unexpected(span, line))?;
        let theory = local.clone().finalize();
        let mut proof = IsarProof::init(theory);
        proof.lemma(&name, term).map_err(|source| TheoryLoadError::Proof { line, source })?;
        self.proof = Some(proof);
        self.pending_lemma = Some(name);
        Ok(())
    }

    fn process_proof_command(
        &mut self,
        span: &CommandSpan,
        line: usize,
    ) -> Result<(), TheoryLoadError> {
        let proof = self.proof.as_mut().ok_or_else(|| unexpected(span, line))?;
        match span.name.as_str() {
            "proof" if span.tokens.len() == 1 => proof.proof(),
            "have" | "show" => {
                let (name, term) = parse_optional_named_proposition(span, line)?;
                if span.name == "show" { proof.show(&name, term) } else { proof.have(&name, term) }
            },
            "assume" => {
                let (_, term) = parse_optional_named_proposition(span, line)?;
                proof.assume(&[term])
            },
            "fix" => {
                let (name, typ) = parse_fix(span, line)?;
                proof.fix(&[(&name, typ)])
            },
            "apply" if span.tokens.len() > 1 => {
                proof.apply_checked(span.body.trim(), &self.search_db)
            },
            "by" if span.tokens.len() > 1 => proof.by(span.body.trim(), &self.search_db),
            "qed" if span.tokens.len() == 1 => proof.qed(),
            "done" if span.tokens.len() == 1 => proof.done(),
            _ => return Err(malformed(span, line)),
        }
        .map_err(|source| TheoryLoadError::Proof { line, source })?;
        if matches!(span.name.as_str(), "by" | "qed" | "done")
            && proof.level() <= 2
            && proof.mode() == ProofMode::Forward
        {
            self.finish_lemma(span, line)?;
        }
        Ok(())
    }

    fn finish_lemma(&mut self, span: &CommandSpan, line: usize) -> Result<(), TheoryLoadError> {
        let proof = self.proof.as_ref().ok_or_else(|| unexpected(span, line))?;
        let (_, theorem) =
            proof.extract_theorem().map_err(|source| TheoryLoadError::Proof { line, source })?;
        if !theorem.is_strict_closed_proved() {
            return Err(TheoryLoadError::Proof { line, source: GoalExportError::OracleOrAdmitted });
        }
        let name = self.pending_lemma.take().ok_or_else(|| unexpected(span, line))?;
        self.theorems.insert(name.clone(), Arc::clone(&theorem));
        self.search_db.insert_named_fact(name, theorem);
        self.proof = None;
        Ok(())
    }

    fn finalize_completed(&mut self) -> Result<Arc<Theory>, TheoryLoadError> {
        let mut local = self
            .local
            .take()
            .ok_or_else(|| TheoryLoadError::Header { detail: "no active theory".into() })?;
        for (name, theorem) in &self.theorems {
            local.note_theorem(name, Arc::clone(theorem));
        }
        Ok(local.finalize())
    }

    pub fn errors(&self) -> &[TheoryLoadError] {
        &self.errors
    }
    pub fn theorem_count(&self) -> usize {
        if self.is_committed { self.theorems.len() } else { 0 }
    }
    pub fn closed_theorem_count(&self) -> usize {
        self.theorem_count()
    }
    pub fn indexed_theorem_count(&self) -> usize {
        self.theorem_count()
    }
    pub fn lookup_theorem(&self, name: &str) -> Option<Arc<Thm>> {
        if self.is_committed { self.theorems.get(name).cloned() } else { None }
    }
}

fn unexpected(span: &CommandSpan, line: usize) -> TheoryLoadError {
    TheoryLoadError::UnexpectedCommand { command: span.name.clone(), line }
}

fn malformed(span: &CommandSpan, line: usize) -> TheoryLoadError {
    TheoryLoadError::MalformedCommand { command: span.name.clone(), line }
}

fn parse_named_proposition(
    span: &CommandSpan,
    line: usize,
) -> Result<(String, Term), TheoryLoadError> {
    let [_, name, colon, proposition] = span.tokens.as_slice() else {
        return Err(malformed(span, line));
    };
    if !matches!(name.kind, TokenKind::Ident | TokenKind::LongIdent) || colon.source != ":" {
        return Err(malformed(span, line));
    }
    Ok((
        name.source.clone(),
        parse_proposition_token(proposition).ok_or_else(|| malformed(span, line))?,
    ))
}

fn parse_optional_named_proposition(
    span: &CommandSpan,
    line: usize,
) -> Result<(String, Term), TheoryLoadError> {
    if let [_, proposition] = span.tokens.as_slice() {
        return Ok((
            String::new(),
            parse_proposition_token(proposition).ok_or_else(|| malformed(span, line))?,
        ));
    }
    parse_named_proposition(span, line)
}

fn parse_proposition_token(token: &Token) -> Option<Term> {
    if token.kind != TokenKind::String {
        return None;
    }
    parse_term(unquote_token(token)?)
}

fn unquote_token(token: &Token) -> Option<&str> {
    token
        .source
        .strip_prefix('"')
        .and_then(|text| text.strip_suffix('"'))
        .or_else(|| token.source.strip_prefix('‹')?.strip_suffix('›'))
        .or_else(|| token.source.strip_prefix(r"\<open>")?.strip_suffix(r"\<close>"))
}

fn parse_fix(
    span: &CommandSpan,
    line: usize,
) -> Result<(String, crate::core::types::Typ), TheoryLoadError> {
    let [_, name, separator, rest @ ..] = span.tokens.as_slice() else {
        return Err(malformed(span, line));
    };
    if name.kind != TokenKind::Ident || separator.source != "::" || rest.is_empty() {
        return Err(malformed(span, line));
    }
    let type_source;
    let text = if let [token] = rest
        && token.kind == TokenKind::String
    {
        unquote_token(token).ok_or_else(|| malformed(span, line))?
    } else {
        type_source = rest.iter().map(|token| token.source.as_str()).collect::<Vec<_>>().join(" ");
        &type_source
    };
    let typ = parse_type(text).ok_or_else(|| malformed(span, line))?;
    Ok((name.source.clone(), typ))
}
