//! Fail-closed source-to-kernel compiler for the currently supported theory slice.

use thiserror::Error;

use crate::{
    hol::{
        hol_basis::hol_owner,
        hol_theorem_prover::{TrueIProofError, prove_true_i},
    },
    isar::{
        elaborator::{ElaborationError, elaborate_proposition},
        outer_syntax::{CommandSpan, OuterSyntax},
        source_ast::{SourceExpr, SourceId, SourceProposition, SourceType},
        source_parser::parse_source_proposition_at,
        token::LexError,
    },
    kernel::{
        KernelRules, Name, ProofContext, RawTerm, Signature, TrustedTheorem, TrustedTheory, Ty,
        accept_closed_theorem, theorem_builder,
    },
    theory::thy_header::{has_header_declarations, parse_header},
};

/// A successful source build and the exact theorem token accepted by the kernel.
pub struct TrustedSourceBuild {
    pub theory: TrustedTheory,
    pub theorem: TrustedTheorem,
}

#[derive(Debug, Error)]
pub enum TrustedLoadError {
    /// Malformed source bytes are user-fixable and never produce a theorem.
    #[error("failed to tokenize theory source: {0}")]
    Lexical(#[from] LexError),
    #[error(
        "E0301: failed to parse theory header: {0}\n  = help: use `theory NAME imports HOL|Pure begin`"
    )]
    Header(String),
    #[error(
        "E0402: unsupported imports: {0:?}\n  = help: this trusted slice requires exactly `imports HOL` or `imports Pure`"
    )]
    UnsupportedImports(Vec<String>),
    #[error(
        "E0404: unsupported header declarations\n  = help: this trusted slice supports only a plain `theory NAME imports HOL|Pure begin` header"
    )]
    UnsupportedHeaderDeclarations,
    #[error(
        "E0403: unsupported command sequence\n  found: {0}\n  = help: use the supported TrueI proof or `lemma identity: \"!!P::prop. PROP P ==> PROP P\" by assumption`; unsupported commands create no theorem"
    )]
    UnsupportedCommands(String),
    #[error(
        "E0302: malformed or incomplete source proposition\n  = help: provide one fully consumed proposition after the lemma name"
    )]
    InvalidProposition,
    #[error(
        "E0201: trusted TrueI proof failed: {0}\n  = help: check the proposition and proof commands against the supported source form"
    )]
    Proof(#[from] TrueIProofError),
    #[error(
        "E0202: Pure identity source is not `!!P::prop. PROP P ==> PROP P`\n  = help: use `!!`, `⋀`, or `\\<And>` with one prop-typed binder and explicit PROP on both sides"
    )]
    InvalidIdentityBinder,
    #[error(
        "E0203: failed to elaborate Pure identity: {0}\n  = help: check names and types in the source proposition"
    )]
    Elaboration(#[from] ElaborationError),
    #[error(
        "E0204: derived Pure identity does not match the source proposition\n  = help: check the proposition and proof script"
    )]
    PropositionMismatch,
    #[error(
        "E0001: strict kernel proof failed: {0}\n  = help: check the proof or report a kernel invariant failure"
    )]
    Kernel(#[from] Box<crate::kernel::KernelError>),
}

impl From<crate::kernel::KernelError> for TrustedLoadError {
    fn from(source: crate::kernel::KernelError) -> Self {
        Self::Kernel(Box::new(source))
    }
}

/// Compile a source-backed theorem in the supported HOL or Pure slice.
///
/// `imports HOL` uses the independently audited, preinstalled HOL owner. This
/// fixture path does not read, execute or attest to the contents of `HOL.thy`.
///
/// Any syntax or proof outside this exact supported contract is rejected before
/// a theorem is accepted. There is no legacy theorem or admission fallback.
pub fn compile_trusted_source(
    source: &str,
    source_id: SourceId,
) -> Result<TrustedSourceBuild, TrustedLoadError> {
    if has_header_declarations(source).map_err(TrustedLoadError::Header)? {
        return Err(TrustedLoadError::UnsupportedHeaderDeclarations);
    }
    let header = parse_header(source).map_err(TrustedLoadError::Header)?;
    if !header.keywords.is_empty() || !header.abbrevs.is_empty() {
        return Err(TrustedLoadError::UnsupportedHeaderDeclarations);
    }

    let spans =
        OuterSyntax::standard().parse_spans_checked_from(source, header.body_begin_position)?;
    let (statement, statement_offset) = match header.imports.as_slice() {
        [import] if import == "HOL" => extract_true_i_statement(source, &spans)?,
        [import] if import == "Pure" => extract_identity_statement(source, &spans)?,
        _ => return Err(TrustedLoadError::UnsupportedImports(header.imports)),
    };
    let source_proposition = parse_source_proposition_at(statement, source_id, statement_offset)
        .ok_or(TrustedLoadError::InvalidProposition)?;

    let (theory, theorem) = if header.imports == ["Pure"] {
        let pure = TrustedTheory::root("Pure", Signature::new());
        prove_identity(&pure.begin_child(header.name), &source_proposition)?
    } else {
        let hol = hol_owner("HOL")?;
        prove_true_i(&hol.begin_child(header.name), &source_proposition)?
    };
    Ok(TrustedSourceBuild { theory, theorem })
}

fn extract_true_i_statement<'a>(
    source: &'a str,
    spans: &[CommandSpan],
) -> Result<(&'a str, usize), TrustedLoadError> {
    let [lemma, unfolding, by, end] = spans else {
        return Err(unsupported_commands(spans));
    };
    if !command_matches(unfolding, &["unfolding", "True_def"])
        || !command_matches(by, &["by", "(", "rule", "refl", ")"])
        || !command_matches(end, &["end"])
    {
        return Err(unsupported_commands(spans));
    }
    extract_lemma_statement(source, lemma, "TrueI")
}

fn extract_identity_statement<'a>(
    source: &'a str,
    spans: &[CommandSpan],
) -> Result<(&'a str, usize), TrustedLoadError> {
    let [lemma, by, end] = spans else {
        return Err(unsupported_commands(spans));
    };
    if !command_matches(by, &["by", "assumption"]) || !command_matches(end, &["end"]) {
        return Err(unsupported_commands(spans));
    }
    extract_lemma_statement(source, lemma, "identity")
}

fn extract_lemma_statement<'a>(
    source: &'a str,
    lemma: &CommandSpan,
    expected_name: &str,
) -> Result<(&'a str, usize), TrustedLoadError> {
    let [command, name, colon, first, rest @ ..] = lemma.tokens.as_slice() else {
        return Err(unsupported_commands(std::slice::from_ref(lemma)));
    };
    if command.source != "lemma" || name.source != expected_name || colon.source != ":" {
        return Err(unsupported_commands(std::slice::from_ref(lemma)));
    }
    let last = rest.last().unwrap_or(first);
    let end = last.offset + last.source.len();
    let statement = source.get(first.offset..end).ok_or(TrustedLoadError::InvalidProposition)?;
    Ok((statement, first.offset))
}

fn command_matches(span: &CommandSpan, expected: &[&str]) -> bool {
    span.tokens.iter().map(|token| token.source.as_str()).eq(expected.iter().copied())
}

fn unsupported_commands(spans: &[CommandSpan]) -> TrustedLoadError {
    TrustedLoadError::UnsupportedCommands(
        spans.iter().map(|span| span.name.as_str()).collect::<Vec<_>>().join("; "),
    )
}

fn without_groups(mut expr: &SourceExpr) -> &SourceExpr {
    while let SourceExpr::Group { inner, .. } = expr {
        expr = inner;
    }
    expr
}

fn is_identity_operand(expr: &SourceExpr, binder: &str) -> bool {
    let SourceExpr::SyntaxApplication { syntax, arguments, .. } = without_groups(expr) else {
        return false;
    };
    if syntax.spelling.as_ref() != "PROP" {
        return false;
    }
    let [operand] = arguments.as_slice() else { return false };
    matches!(
        without_groups(operand),
        SourceExpr::Name { name, .. } if name.spelling.as_ref() == binder
    )
}

fn is_identity_body(expr: &SourceExpr, binder: &str) -> bool {
    let SourceExpr::SyntaxApplication { syntax, arguments, .. } = without_groups(expr) else {
        return false;
    };
    if !matches!(syntax.spelling.as_ref(), "==>" | "⟹" | r"\<Longrightarrow>") {
        return false;
    }
    let [left, right] = arguments.as_slice() else { return false };
    is_identity_operand(left, binder) && is_identity_operand(right, binder)
}

fn identity_binder(source: &SourceProposition) -> Result<Name, TrustedLoadError> {
    let SourceExpr::Binder { syntax, binders, body, .. } = without_groups(&source.expression)
    else {
        return Err(TrustedLoadError::InvalidIdentityBinder);
    };
    let [binder] = binders.as_slice() else {
        return Err(TrustedLoadError::InvalidIdentityBinder);
    };
    let Some(SourceType::Name { name: typ, .. }) = &binder.typ else {
        return Err(TrustedLoadError::InvalidIdentityBinder);
    };
    if !matches!(syntax.spelling.as_ref(), "!!" | "⋀" | r"\<And>")
        || typ.spelling.as_ref() != "prop"
        || !is_identity_body(body, binder.name.spelling.as_ref())
    {
        return Err(TrustedLoadError::InvalidIdentityBinder);
    }
    Ok(Name::from(binder.name.spelling.clone()))
}

fn prove_identity(
    theory: &TrustedTheory,
    source: &SourceProposition,
) -> Result<(TrustedTheory, TrustedTheorem), TrustedLoadError> {
    let binder = identity_binder(source)?;
    let mut context = ProofContext::new(theory.snapshot().clone());
    context.declare_free(binder.clone(), Ty::prop());
    let goal = elaborate_proposition(source, &context)?;
    let variable = context.certify_term(RawTerm::free(binder.clone(), Ty::prop()))?;
    let assumption = context.certify_prop(RawTerm::free(binder, Ty::prop()))?;
    let assumed = KernelRules::assume(assumption.clone())?;
    let implication = KernelRules::implies_intr(&assumption, assumed.as_kernel())?;
    let derived = KernelRules::forall_intr(&variable, &implication)?;
    if goal.context() != derived.context() || !goal.term().alpha_eq(derived.prop().term()) {
        return Err(TrustedLoadError::PropositionMismatch);
    }
    let closed = theorem_builder::close_thm(derived)?;
    Ok(accept_closed_theorem(theory, "identity", closed)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    const TRUE_I: &str = "theory Smoke\nimports HOL\nbegin\nlemma TrueI: True\n  unfolding True_def by (rule refl)\nend\n";

    const PURE_IDENTITY: &str = include_str!("../../tests/fixtures/TrustedPureIdentity.thy");

    #[test]
    fn compile_trusted_source_true_i_returns_kernel_token() {
        let result = compile_trusted_source(TRUE_I, SourceId::new("Smoke.thy")).unwrap();
        assert_eq!(result.theorem.name().as_str(), "TrueI");
        assert_eq!(result.theory.len(), 2);
    }

    #[test]
    fn compile_trusted_source_wrong_statement_is_rejected() {
        let source = TRUE_I.replace("lemma TrueI: True", "lemma TrueI: HOL.True == HOL.True");
        assert!(matches!(
            compile_trusted_source(&source, SourceId::new("Wrong.thy")),
            Err(TrustedLoadError::Proof(TrueIProofError::PropositionMismatch))
        ));
    }

    #[test]
    fn compile_trusted_source_sorry_is_rejected() {
        let source = TRUE_I.replace("unfolding True_def by (rule refl)", "sorry");
        assert!(matches!(
            compile_trusted_source(&source, SourceId::new("Sorry.thy")),
            Err(TrustedLoadError::UnsupportedCommands(_))
        ));
    }

    #[test]
    fn compile_trusted_source_unicode_whitespace_returns_kernel_token() {
        let source = TRUE_I.replace("begin\nlemma", "begin lemma");
        let result = compile_trusted_source(&source, SourceId::new("Unicode.thy")).unwrap();
        assert_eq!(result.theorem.name().as_str(), "TrueI");
    }

    #[test]
    fn compile_trusted_source_header_declarations_are_rejected() {
        for declaration in ["keywords \"custom\" :: thy_decl\n", "abbrevs \"True\" = \"False\"\n"] {
            let source = TRUE_I.replace("begin\n", &format!("{declaration}begin\n"));
            assert!(matches!(
                compile_trusted_source(&source, SourceId::new("Header.thy")),
                Err(TrustedLoadError::UnsupportedHeaderDeclarations)
            ));
        }
    }

    #[test]
    fn compile_trusted_source_abbrev_expansion_is_rejected_before_parsing() {
        let side = std::iter::repeat_n("\"x\"", 65).collect::<Vec<_>>().join(" ");
        let declaration = format!("abbrevs {side} = {side}\n");
        let source = TRUE_I.replace("begin\n", &format!("{declaration}begin\n"));
        assert!(matches!(
            compile_trusted_source(&source, SourceId::new("Abbrevs.thy")),
            Err(TrustedLoadError::UnsupportedHeaderDeclarations)
        ));
    }

    #[test]
    fn extract_true_i_statement_preserves_file_byte_span() {
        let source = TRUE_I.replace("begin\nlemma", "begin lemma");
        let header = parse_header(&source).unwrap();
        let body_source = &source[header.body_begin_position..];
        let spans = OuterSyntax::standard().parse_spans(body_source);
        let (statement, statement_offset) = extract_true_i_statement(body_source, &spans).unwrap();
        let absolute_offset = header.body_begin_position + statement_offset;
        let proposition =
            parse_source_proposition_at(statement, SourceId::new("Unicode.thy"), absolute_offset)
                .unwrap();
        assert_eq!(&source[proposition.span.start..proposition.span.end], "True");
    }

    #[test]
    fn compile_trusted_source_pure_identity_returns_kernel_token() {
        let result =
            compile_trusted_source(PURE_IDENTITY, SourceId::new("TrustedPureIdentity.thy"))
                .unwrap();
        assert_eq!(result.theorem.name().as_str(), "identity");
        assert_eq!(result.theory.len(), 1);
        assert!(result.theorem.dependencies().is_empty());
        assert_eq!(
            result.theorem.proved_context(),
            result.theory.parents().first().unwrap().stamp()
        );
    }

    #[test]
    fn compile_trusted_source_pure_identity_renamed_binder_is_derived_from_source() {
        let renamed =
            PURE_IDENTITY.replace("!!P::prop. PROP P ==> PROP P", "!!Q::prop. PROP Q ==> PROP Q");
        let result = compile_trusted_source(&renamed, SourceId::new("Renamed.thy")).unwrap();
        assert_eq!(result.theorem.name().as_str(), "identity");
        assert_eq!(result.theory.len(), 1);
    }

    #[test]
    fn compile_trusted_source_pure_identity_aliases_and_groups_return_kernel_tokens() {
        for (binder, implication) in [("⋀", "⟹"), (r"\<And>", r"\<Longrightarrow>")] {
            let statement = format!("({binder}Q::prop. (PROP (Q)) {implication} (PROP Q))");
            let source = PURE_IDENTITY.replace("!!P::prop. PROP P ==> PROP P", &statement);
            let result = compile_trusted_source(&source, SourceId::new("Alias.thy")).unwrap();
            assert_eq!(result.theorem.name().as_str(), "identity");
            assert!(result.theorem.dependencies().is_empty());
        }
    }

    #[test]
    fn compile_trusted_source_pure_identity_changed_propositions_are_rejected() {
        for altered in [
            "!!P::prop. P ==> P",
            "!!P::prop. PROP P ==> P",
            "!!P::prop. P ==> PROP P",
            "!!P::prop. PROP True ==> PROP True",
            "!!P::prop. PROP ==> PROP P",
            "!!P::prop. PROP P ==> PROP",
            "!!P::prop. PROP P ==> (PROP P ==> PROP P)",
            "!!P::prop. PROP P ==> PROP P ==> PROP P",
            "!!P::prop. PROP P ==> PROP Q",
            "!!P::bool. PROP P ==> PROP P",
            "PROP P ==> PROP P",
            "!!P. PROP P ==> PROP P",
        ] {
            let source = PURE_IDENTITY.replace("!!P::prop. PROP P ==> PROP P", altered);
            assert!(
                compile_trusted_source(&source, SourceId::new("Changed.thy")).is_err(),
                "incorrectly accepted `{altered}`"
            );
        }
    }

    #[test]
    fn compile_trusted_source_pure_identity_fake_proofs_are_rejected() {
        for proof in
            ["by (rule impI)", "by (rule refl)", "by simp", "sorry", "by assumption by (rule refl)"]
        {
            let source = PURE_IDENTITY.replace("by assumption", proof);
            assert!(matches!(
                compile_trusted_source(&source, SourceId::new("FakeProof.thy")),
                Err(TrustedLoadError::UnsupportedCommands(_))
            ));
        }
    }

    #[test]
    fn compile_trusted_source_pure_identity_extra_commands_and_imports_are_rejected() {
        let extra = PURE_IDENTITY.replace(
            "\nend\n",
            "\nlemma extra: \"!!P::prop. PROP P ==> PROP P\" by assumption\nend\n",
        );
        assert!(matches!(
            compile_trusted_source(&extra, SourceId::new("Extra.thy")),
            Err(TrustedLoadError::UnsupportedCommands(_))
        ));
        let changed_import = PURE_IDENTITY.replace("imports Pure", "imports Pure HOL");
        assert!(matches!(
            compile_trusted_source(&changed_import, SourceId::new("Imports.thy")),
            Err(TrustedLoadError::UnsupportedImports(_))
        ));
        let declaration =
            PURE_IDENTITY.replace("lemma identity:", "consts Fake :: prop\nlemma identity:");
        assert!(matches!(
            compile_trusted_source(&declaration, SourceId::new("Declaration.thy")),
            Err(TrustedLoadError::UnsupportedCommands(_))
        ));
    }

    #[test]
    fn extract_identity_statement_preserves_source_byte_span() {
        let source = PURE_IDENTITY.replace("begin\n", "begin ");
        let header = parse_header(&source).unwrap();
        let body = &source[header.body_begin_position..];
        let spans = OuterSyntax::standard().parse_spans(body);
        let (statement, offset) = extract_identity_statement(body, &spans).unwrap();
        let parsed = parse_source_proposition_at(
            statement,
            SourceId::new("UnicodeIdentity.thy"),
            header.body_begin_position + offset,
        )
        .unwrap();
        assert_eq!(&source[parsed.span.start..parsed.span.end], "!!P::prop. PROP P ==> PROP P");
    }

    #[test]
    fn compile_trusted_source_nested_comments_preserve_accepted_identity() {
        for fixture in [TRUE_I, PURE_IDENTITY] {
            let expected = compile_trusted_source(fixture, SourceId::new("Plain.thy")).unwrap();
            let commented = format!(
                "(* header (* nested *) comment *)\n{}(* trailing comment *)",
                fixture
                    .replace("imports", "(* before imports *) imports")
                    .replace("begin\n", "begin\n(* before lemma *)\n")
                    .replace("by ", "by (* method *) ")
            );
            let actual =
                compile_trusted_source(&commented, SourceId::new("Commented.thy")).unwrap();
            assert_eq!(actual.theorem.id(), expected.theorem.id());
        }
    }

    #[test]
    fn compile_trusted_source_unterminated_suffix_reports_absolute_byte_offset() {
        for suffix in ["(* unterminated", "\"unterminated", "‹unterminated"] {
            let source = format!("{PURE_IDENTITY}{suffix}");
            let result = compile_trusted_source(&source, SourceId::new("Suffix.thy"));
            assert!(matches!(
                result,
                Err(TrustedLoadError::Lexical(LexError { offset, .. }))
                    if offset == PURE_IDENTITY.len()
            ));
        }
    }

    #[test]
    fn compile_trusted_source_end_argument_cannot_authorize_token() {
        for fixture in [TRUE_I, PURE_IDENTITY] {
            let source = format!("{fixture}?");
            assert!(matches!(
                compile_trusted_source(&source, SourceId::new("EndArgument.thy")),
                Err(TrustedLoadError::UnsupportedCommands(_))
            ));
        }
    }

    #[test]
    fn compile_trusted_source_orphan_and_separator_tokens_are_rejected() {
        for source in [
            PURE_IDENTITY.replace("begin\n", "begin\norphan "),
            format!("{PURE_IDENTITY}; garbage"),
            format!("{PURE_IDENTITY}unexpected"),
        ] {
            assert!(compile_trusted_source(&source, SourceId::new("Garbage.thy")).is_err());
        }
    }
}
