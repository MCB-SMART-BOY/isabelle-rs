//! Audited source projection for the sampled `HOL.TrueI` milestone.
//!
//! This adapter checks only the declarations needed to replay `TrueI`.
//! Checked outer spans provide command boundaries, not execution semantics:
//! ML, imported commands and unrelated HOL declarations do not enter its owner.

use thiserror::Error;

use crate::{
    hol::{
        hol_basis::hol_owner,
        hol_theorem_prover::{TrueIProofError, prove_true_i_from_definition},
    },
    isar::{
        elaborator::{ElaborationError, elaborate_raw_term},
        keyword::{Keywords, QED_GLOBAL},
        outer_syntax::{CommandSpan, OuterSyntax},
        source_ast::{SourceExpr, SourceId, SourceProposition, SourceType},
        source_parser::{parse_source_proposition_at, parse_source_type_at},
        token::{LexError, Lexer, Token, TokenKind},
    },
    kernel::{KernelError, Name, ProofContext},
    theory::{
        thy_header::{TheoryHeader, parse_header},
        trusted_loader::TrustedSourceBuild,
    },
};

const DECLARATION_TYPE_OFFSET: usize = 3;
const TRUE_DEFINITION_BODY_OFFSET: usize = 5;
const TRUE_I_STATEMENT_OFFSET: usize = 3;
const REFL_PROPOSITION_OFFSET: usize = 4;
const EQ_AXIOMATIZATION_PREFIX_DISTANCE: usize = 9;
const QUOTED_CONTENT_OFFSET: usize = 1;
const EQUALITY_POSITION: usize = 8;
const TRUE_DEFINITION_POSITION: usize = 9;
const TRUE_I_POSITION: usize = 11;
const CLASS_SETUP_TOKENS: &[&str] =
    &["setup", r"\<open>Axclass.class_axiomatization (\<^binding>\<open>type\<close>, [])\<close>"];
const BASE_SORT_SETUP_TOKENS: &[&str] =
    &["setup", r"\<open>Object_Logic.add_base_sort \<^sort>\<open>type\<close>\<close>"];
const ADDITIONAL_COMMANDS: &[&str] = &[
    "private",
    "qualified",
    "hide_const",
    "hide_fact",
    "hide_type",
    "open_bundle",
    "close_bundle",
    "syntax_consts",
    "no_syntax_consts",
    "alias",
    "default_sort",
    "instance",
    "typed_print_translation",
    "print_translation",
];

#[derive(Debug, Error)]
pub enum SampledTrueIError {
    /// User-fixable malformed source bytes.
    #[error("failed to tokenize sampled HOL source: {0}")]
    Lexical(#[from] LexError),
    /// User-fixable malformed or unexpected theory header.
    #[error("failed to parse sampled HOL header: {0}")]
    Header(String),
    /// User-fixable source outside the audited projection.
    #[error("sampled HOL projection rejected its input: {0}")]
    Input(String),
    /// User-fixable declaration or term elaboration failure.
    #[error("failed to elaborate a sampled HOL term: {0}")]
    Elaboration(#[from] ElaborationError),
    /// A rejected proof replay, preserving the proof-layer cause.
    #[error("failed to prove sampled HOL.TrueI: {0}")]
    Proof(#[from] TrueIProofError),
    /// Fatal kernel rejection, preserving the kernel cause.
    #[error("kernel rejected the sampled HOL projection: {0}")]
    Kernel(#[from] Box<KernelError>),
}

impl From<KernelError> for SampledTrueIError {
    fn from(source: KernelError) -> Self {
        Self::Kernel(Box::new(source))
    }
}

/// Compile the audited `HOL.TrueI` source projection into an accepted token.
///
/// Only the audited source slice is interpreted. Unrelated commands, including
/// executable ML, are neither executed nor copied into the immutable owner;
/// this is not a whole-theory HOL semantics checker.
pub fn compile_sampled_true_i(
    source: &str,
    source_id: SourceId,
) -> Result<TrustedSourceBuild, SampledTrueIError> {
    compile_sampled_true_i_with_location(source, source_id).map(|(build, _)| build)
}

/// Return the audited outer-command byte offset alongside the kernel-owned token.
/// Legacy candidates may consume the token only when their sealed command matches.
pub(crate) fn compile_sampled_true_i_with_location(
    source: &str,
    source_id: SourceId,
) -> Result<(TrustedSourceBuild, usize), SampledTrueIError> {
    let tokens = Lexer::new(source).tokenize_checked()?;
    let header = parse_projection_header(source, &tokens)?;
    validate_header(&header)?;
    let commands = parse_commands(source, &header)?;
    let declarations = SourceDeclarations::extract(&commands)?;
    declarations.validate(&commands)?;
    let true_i_offset = commands[declarations.positions[TRUE_I_POSITION]]
        .tokens
        .first()
        .ok_or_else(|| input_error("missing TrueI command token"))?
        .offset;

    let base = hol_owner(header.name)?;
    let context = ProofContext::new(base.snapshot().clone());
    let rhs = extract_true_rhs(declarations.true_definition, source_id.clone())?;
    let rhs_raw = elaborate_raw_term(&rhs, &context)?;
    let (defined, true_definition) = base.define_const(Name::from("HOL.True"), rhs_raw)?;
    let statement = parse_statement(declarations.true_i_statement, source_id)?;
    let (theory, theorem) = prove_true_i_from_definition(&defined, &true_definition, &statement)?;
    Ok((TrustedSourceBuild { theory, theorem }, true_i_offset))
}

fn parse_projection_header(
    source: &str,
    mut tokens: &[Token],
) -> Result<TheoryHeader, SampledTrueIError> {
    loop {
        let Some(first) = tokens.first() else {
            return Err(input_error("missing theory header"));
        };
        if first.is_keyword("theory") {
            let mut header =
                parse_header(&source[first.offset..]).map_err(SampledTrueIError::Header)?;
            header.body_begin_position += first.offset;
            return Ok(header);
        }
        let [command, body, remaining @ ..] = tokens else {
            return Err(input_error("incomplete document preamble"));
        };
        if !matches!(
            command.source.as_str(),
            "chapter" | "section" | "subsection" | "subsubsection" | "text" | "text_raw"
        ) || body.kind != TokenKind::String
        {
            return Err(input_error("only document commands may precede the theory header"));
        }
        tokens = remaining;
    }
}

fn parse_commands(
    source: &str,
    header: &TheoryHeader,
) -> Result<Vec<CommandSpan>, SampledTrueIError> {
    let mut keywords = Keywords::standard();
    // Boundary recognition only: none of these commands are executed by this projection.
    for &name in ADDITIONAL_COMMANDS {
        keywords.add_command(name, "thy_decl");
    }
    keywords.add_command("oops", QED_GLOBAL);
    for spec in &header.keywords {
        keywords.add_command(&spec.name, &spec.kind);
    }
    OuterSyntax::new(keywords)
        .parse_spans_checked_from(source, header.body_begin_position)
        .map_err(SampledTrueIError::Lexical)
}

struct SourceDeclarations<'a> {
    true_definition: &'a Token,
    true_i_statement: &'a Token,
    // Source-order anchors, including the proof that precedes bool.
    positions: [usize; TRUE_I_POSITION + 1],
}

impl<'a> SourceDeclarations<'a> {
    fn extract(commands: &'a [CommandSpan]) -> Result<Self, SampledTrueIError> {
        let class_setup = find_command(commands, "setup", CLASS_SETUP_TOKENS)?;
        let default_sort = find_command(commands, "default_sort", &["default_sort", "type"])?;
        let base_sort = find_command(commands, "setup", BASE_SORT_SETUP_TOKENS)?;
        let fun_axiom = find_command(
            commands,
            "axiomatization",
            &["axiomatization", "where", "fun_arity", ":"],
        )?;
        let fun_instance = find_command(commands, "instance", &["instance", "\"fun\"", "::"])?;
        let fun_proof = fun_instance + 1;
        let bool_decl = find_command(commands, "typedecl", &["typedecl", "bool"])?;
        let trueprop = find_command(commands, "judgment", &["judgment", "Trueprop", "::"])?;
        let equality =
            find_command(commands, "axiomatization", &["axiomatization", "implies", "::"])?;
        let true_def = find_command(commands, "definition", &["definition", "True", "::"])?;
        let refl =
            find_command(commands, "axiomatization", &["axiomatization", "where", "refl", ":"])?;
        let true_i = find_command(commands, "lemma", &["lemma", "TrueI", ":"])?;
        let positions = [
            class_setup,
            default_sort,
            base_sort,
            fun_axiom,
            fun_instance,
            fun_proof,
            bool_decl,
            trueprop,
            equality,
            true_def,
            refl,
            true_i,
        ];
        validate_declaration_order(&positions)?;
        let definition_tokens = &commands[true_def].tokens;
        let statement_tokens = &commands[true_i].tokens;
        Ok(Self {
            true_definition: token_after(
                definition_tokens,
                0,
                TRUE_DEFINITION_BODY_OFFSET,
                "True definition",
            )?,
            true_i_statement: token_after(
                statement_tokens,
                0,
                TRUE_I_STATEMENT_OFFSET,
                "TrueI statement",
            )?,
            positions,
        })
    }

    fn validate(&self, commands: &[CommandSpan]) -> Result<(), SampledTrueIError> {
        let [
            class_setup,
            default_sort,
            base_sort,
            fun_axiom,
            fun_instance,
            fun_proof,
            bool_decl,
            trueprop,
            equality,
            true_def,
            refl,
            true_i,
        ] = self.positions;
        validate_global_scope(commands, &self.positions)?;
        require_exact(&commands[class_setup].tokens, CLASS_SETUP_TOKENS, "HOL.type class setup")?;
        require_exact(&commands[base_sort].tokens, BASE_SORT_SETUP_TOKENS, "HOL.type base sort")?;
        require_exact(&commands[default_sort].tokens, &["default_sort", "type"], "default sort")?;
        validate_dependency_environment(commands, &self.positions)?;
        validate_function_arity(&commands[fun_axiom].tokens)?;
        require_exact(
            &commands[fun_instance].tokens,
            &["instance", "\"fun\"", "::", "(", "type", ",", "type", ")", "type"],
            "function type-class instance",
        )?;
        require_exact(
            &commands[fun_proof].tokens,
            &["by", "(", "rule", "fun_arity", ")"],
            "function arity proof",
        )?;
        reject_proof_tail(commands, fun_proof + 1, "function arity")?;
        validate_bool_declaration(&commands[bool_decl].tokens)?;
        validate_trueprop_declaration(&commands[trueprop].tokens)?;
        validate_equality_declaration(&commands[equality].tokens)?;
        validate_true_definition(&commands[true_def].tokens)?;
        validate_refl_schema(&commands[refl].tokens)?;
        validate_true_i_proof(commands, true_i)
    }
}

fn validate_header(header: &TheoryHeader) -> Result<(), SampledTrueIError> {
    let has_expected_imports = matches!(
        header.imports.as_slice(),
        [pure, code] if pure == "Pure" && code == "Tools.Code_Generator"
    ) || matches!(
        header.imports.as_slice(),
        [pure, try0, code]
            if pure == "Pure" && try0 == "Try0" && code == "Tools.Code_Generator"
    );
    if header.name != "HOL" || !has_expected_imports {
        return Err(input_error("expected `theory HOL imports Pure [Try0] Tools.Code_Generator`"));
    }
    let standard = Keywords::standard();
    for spec in &header.keywords {
        if standard.is_command(&spec.name)
            || ADDITIONAL_COMMANDS.contains(&spec.name.as_str())
            || is_required_name(&spec.name)
        {
            return Err(input_error("header rebinds an audited command or name"));
        }
    }
    if header.abbrevs.iter().any(|abbrev| {
        is_required_name(&abbrev.lhs)
            || is_required_name(&abbrev.rhs)
            || abbrev.lhs == "="
            || abbrev.rhs == "="
    }) {
        return Err(input_error("header abbreviation affects an audited name"));
    }
    Ok(())
}

fn find_command(
    commands: &[CommandSpan],
    name: &str,
    prefix: &[&str],
) -> Result<usize, SampledTrueIError> {
    let mut found = None;
    for (index, command) in commands.iter().enumerate() {
        if command.name != name || !starts_with_sources(&command.tokens, prefix) {
            continue;
        }
        if found.replace(index).is_some() {
            return Err(input_error(format!("duplicate required command `{}`", prefix.join(" "))));
        }
    }
    found.ok_or_else(|| input_error(format!("missing required command `{}`", prefix.join(" "))))
}

fn starts_with_sources(tokens: &[Token], prefix: &[&str]) -> bool {
    tokens.len() >= prefix.len() && token_sources_equal(&tokens[..prefix.len()], prefix)
}

fn require_exact(
    tokens: &[Token],
    expected: &[&str],
    label: &str,
) -> Result<(), SampledTrueIError> {
    if token_sources_equal(tokens, expected) {
        Ok(())
    } else {
        Err(input_error(format!("{label} must match the complete audited command")))
    }
}

fn token_sources_equal(tokens: &[Token], expected: &[&str]) -> bool {
    tokens.iter().map(|token| token.source.as_str()).eq(expected.iter().copied())
}

fn token_after<'a>(
    tokens: &'a [Token],
    start: usize,
    distance: usize,
    label: &str,
) -> Result<&'a Token, SampledTrueIError> {
    tokens.get(start + distance).ok_or_else(|| input_error(format!("incomplete {label}")))
}

fn validate_declaration_order(positions: &[usize]) -> Result<(), SampledTrueIError> {
    if positions.windows(2).all(|pair| pair[0] < pair[1]) {
        Ok(())
    } else {
        Err(input_error("sampled HOL declarations are out of dependency order"))
    }
}

fn validate_global_scope(
    commands: &[CommandSpan],
    positions: &[usize],
) -> Result<(), SampledTrueIError> {
    let mut depth = 0usize;
    let mut has_theory_end = false;
    for (index, command) in commands.iter().enumerate() {
        if positions.contains(&index) && (depth != 0 || has_theory_end) {
            return Err(input_error("a required declaration is outside global theory scope"));
        }
        match command.name.as_str() {
            "begin" => {
                require_exact(&command.tokens, &["begin"], "scope opening")?;
                depth =
                    depth.checked_add(1).ok_or_else(|| input_error("scope nesting overflow"))?;
            },
            "end" if depth > 0 => {
                require_exact(&command.tokens, &["end"], "scope closing")?;
                depth -= 1;
            },
            "end" if index + 1 == commands.len() => {
                require_exact(&command.tokens, &["end"], "theory closing")?;
                has_theory_end = true;
            },
            "end" => return Err(input_error("theory scope ended before the final command")),
            _ => {},
        }
    }
    if depth != 0 || !has_theory_end {
        return Err(input_error("sampled HOL source has an unclosed scope"));
    }
    Ok(())
}

fn validate_dependency_environment(
    commands: &[CommandSpan],
    positions: &[usize],
) -> Result<(), SampledTrueIError> {
    let mut has_input_equality = false;
    let standard = Keywords::standard();
    for (index, command) in commands.iter().enumerate().take(positions[TRUE_I_POSITION] + 1) {
        if positions.contains(&index)
            && index > 0
            && !standard.is_command(&commands[index - 1].name)
            && !positions.contains(&(index - 1))
        {
            return Err(input_error("required declaration follows an unaudited command modifier"));
        }
        if matches!(command.name.as_str(), "private" | "qualified")
            && positions.contains(&(index + 1))
        {
            return Err(input_error("required declaration has a non-global modifier"));
        }
        if positions.contains(&index) {
            continue;
        }
        if command.name == "notation" && is_equality_output_notation(command) {
            continue;
        }
        if command.name == "notation" && is_equality_notation(command) {
            if has_input_equality
                || index <= positions[EQUALITY_POSITION]
                || index >= positions[TRUE_DEFINITION_POSITION]
            {
                return Err(input_error("input equality notation is duplicated or misplaced"));
            }
            has_input_equality = true;
            continue;
        }
        if changes_dependency(command) {
            return Err(input_error(format!(
                "command `{}` affects sampled HOL dependencies",
                command.name
            )));
        }
    }
    if !has_input_equality {
        return Err(input_error("missing input `=` notation for HOL.eq"));
    }
    Ok(())
}

fn is_required_name(name: &str) -> bool {
    let unquoted = name.strip_prefix('"').and_then(|text| text.strip_suffix('"')).unwrap_or(name);
    matches!(
        unquoted,
        "bool"
            | "fun"
            | "fun_arity"
            | "HOL.fun_arity"
            | "Trueprop"
            | "eq"
            | "True"
            | "refl"
            | "True_def"
            | "TrueI"
            | "HOL.bool"
            | "HOL.Trueprop"
            | "HOL.eq"
            | "HOL.True"
            | "HOL.refl"
            | "HOL.True_def"
            | "HOL.TrueI"
    )
}

fn is_equality_notation(command: &CommandSpan) -> bool {
    token_sources_equal(
        &command.tokens,
        &["notation", "(", "input", ")", "eq", "(", "infixl", r"\<open>=\<close>", "50", ")"],
    )
}

fn is_equality_output_notation(command: &CommandSpan) -> bool {
    token_sources_equal(
        &command.tokens,
        &["notation", "(", "output", ")", "eq", "(", "infix", r"\<open>=\<close>", "50", ")"],
    )
}

fn changes_dependency(command: &CommandSpan) -> bool {
    let name = command.name.as_str();
    let tokens = &command.tokens;
    if matches!(name, "unbundle" | "include" | "including") {
        return true;
    }
    if name == "default_sort" {
        return true;
    }
    if matches!(
        name,
        "hide_const"
            | "hide_fact"
            | "hide_type"
            | "alias"
            | "no_notation"
            | "no_type_notation"
            | "syntax_consts"
            | "no_syntax_consts"
            | "translations"
            | "no_translations"
            | "syntax"
            | "no_syntax"
            | "notation"
            | "type_notation"
    ) {
        return tokens.iter().skip(1).any(|token| {
            is_required_name(&token.source)
                || matches!(token.source.as_str(), r"\<open>=\<close>" | "\"=\"" | "=")
        });
    }
    if name == "axiomatization" {
        return tokens.get(1).is_some_and(|token| is_required_name(&token.source))
            || (tokens.get(1).is_some_and(|token| token.source == "where")
                && tokens.get(2).is_some_and(|token| is_required_name(&token.source)))
            || conflicting_axiom_head(tokens, None);
    }
    if name == "instance" {
        return tokens.get(1).is_some_and(|token| is_required_name(&token.source));
    }
    if matches!(
        name,
        "typedecl"
            | "type_synonym"
            | "judgment"
            | "consts"
            | "definition"
            | "abbreviation"
            | "lemma"
            | "theorem"
            | "corollary"
            | "proposition"
            | "lemmas"
            | "theorems"
    ) {
        return tokens.get(1).is_some_and(|token| is_required_name(&token.source))
            || tokens
                .windows(2)
                .any(|pair| pair[0].source == "and" && is_required_name(&pair[1].source));
    }
    false
}

fn conflicting_axiom_head(tokens: &[Token], allowed_offset: Option<usize>) -> bool {
    tokens.windows(2).enumerate().any(|(index, clause)| {
        Some(index) != allowed_offset
            && clause[0].source == "and"
            && is_required_name(&clause[1].source)
    })
}

fn validate_function_arity(tokens: &[Token]) -> Result<(), SampledTrueIError> {
    require_exact(
        tokens,
        &[
            "axiomatization",
            "where",
            "fun_arity",
            ":",
            r#""OFCLASS('a \<Rightarrow> 'b, type_class)""#,
        ],
        "function arity schema",
    )
}

fn validate_bool_declaration(tokens: &[Token]) -> Result<(), SampledTrueIError> {
    require_exact(tokens, &["typedecl", "bool"], "bool declaration")
}

fn validate_trueprop_declaration(tokens: &[Token]) -> Result<(), SampledTrueIError> {
    let token = token_after(tokens, 0, DECLARATION_TYPE_OFFSET, "Trueprop declaration")?;
    let typ = parse_quoted_type(token)?;
    if !is_arrow(&typ, "bool", "prop") {
        return Err(input_error("Trueprop must have type `bool => prop`"));
    }
    let tail = tokens.get(4..).ok_or_else(|| input_error("missing Trueprop syntax"))?;
    require_exact(
        tail,
        &["(", r"\<open>(\<open>notation=judgment\<close>_)\<close>", "5", ")"],
        "Trueprop syntax",
    )
}

fn validate_equality_declaration(tokens: &[Token]) -> Result<(), SampledTrueIError> {
    let prefix = tokens.get(..3).ok_or_else(|| input_error("incomplete HOL axiomatization"))?;
    if !token_sources_equal(prefix, &["axiomatization", "implies", "::"]) {
        return Err(input_error("eq must belong to the primitive HOL axiomatization"));
    }
    let eq_start = EQ_AXIOMATIZATION_PREFIX_DISTANCE;
    let eq_prefix = tokens
        .get(eq_start..eq_start + 3)
        .ok_or_else(|| input_error("missing primitive HOL.eq declaration"))?;
    if !token_sources_equal(eq_prefix, &["and", "eq", "::"]) {
        return Err(input_error("eq must belong to the primitive HOL axiomatization"));
    }
    let token = token_after(tokens, eq_start, DECLARATION_TYPE_OFFSET, "HOL.eq declaration")?;
    if !is_equality_type(&parse_quoted_type(token)?) {
        return Err(input_error("eq must have polymorphic type `['a, 'a] => bool`"));
    }
    let next = token_after(tokens, eq_start, 4, "HOL.eq declaration")?;
    if next.source != "and" {
        return Err(input_error("HOL.eq declaration has unreviewed trailing syntax"));
    }
    if conflicting_axiom_head(tokens, Some(eq_start)) {
        return Err(input_error("primitive HOL axiomatization redeclares a sampled name"));
    }
    Ok(())
}

fn parse_quoted_type(token: &Token) -> Result<SourceType, SampledTrueIError> {
    let content = quoted_content(token)?;
    parse_source_type_at(content, token.offset + QUOTED_CONTENT_OFFSET)
        .ok_or_else(|| input_error("malformed sampled HOL declaration type"))
}

fn is_arrow(typ: &SourceType, from: &str, to: &str) -> bool {
    let SourceType::Arrow { from: lhs, to: rhs, .. } = typ else { return false };
    is_type_name(lhs, from) && is_type_name(rhs, to)
}

fn is_equality_type(typ: &SourceType) -> bool {
    let SourceType::Arrow { from: first, to, .. } = typ else { return false };
    let SourceType::Arrow { from: second, to: result, .. } = to.as_ref() else { return false };
    is_type_name(first, "'a") && is_type_name(second, "'a") && is_type_name(result, "bool")
}

fn is_type_name(typ: &SourceType, expected: &str) -> bool {
    matches!(typ, SourceType::Name { name, .. } if name.spelling.as_ref() == expected)
}

fn validate_refl_schema(tokens: &[Token]) -> Result<(), SampledTrueIError> {
    let prefix = tokens.get(..3).ok_or_else(|| input_error("incomplete HOL.refl declaration"))?;
    if !token_sources_equal(prefix, &["axiomatization", "where", "refl"]) {
        return Err(input_error("refl must be declared by the expected global axiomatization"));
    }
    if tokens.get(3).is_none_or(|token| token.source != ":") {
        return Err(input_error("refl declaration must contain a proposition"));
    }
    let token = token_after(tokens, 0, REFL_PROPOSITION_OFFSET, "HOL.refl schema")?;
    let proposition = parse_statement(token, SourceId::new("HOL.refl schema"))?;
    if !is_refl_schema(&proposition.expression)
        || tokens.get(5).is_none_or(|token| token.source != "and")
    {
        return Err(input_error("refl must have schema `t = (t::'a)` followed by axioms"));
    }
    if conflicting_axiom_head(tokens, None) {
        return Err(input_error("HOL.refl axiomatization redeclares a sampled name"));
    }
    Ok(())
}

fn is_refl_schema(expr: &SourceExpr) -> bool {
    let SourceExpr::SyntaxApplication { syntax, arguments, .. } = without_groups(expr) else {
        return false;
    };
    let [left, right] = arguments.as_slice() else { return false };
    syntax.spelling.as_ref() == "=" && is_name(left, "t") && is_typed_name(right, "t", "'a")
}

fn is_typed_name(expr: &SourceExpr, name: &str, typ: &str) -> bool {
    let SourceExpr::TypeAscription { expression, typ: source_type, .. } = without_groups(expr)
    else {
        return false;
    };
    is_name(expression, name) && is_type_name(source_type, typ)
}

fn validate_true_definition(tokens: &[Token]) -> Result<(), SampledTrueIError> {
    if tokens.len() != 6
        || !starts_with_sources(tokens, &["definition", "True", "::", "bool", "where"])
    {
        return Err(input_error("True must be a complete global definition with type bool"));
    }
    quoted_content(&tokens[5])?;
    Ok(())
}

fn extract_true_rhs(token: &Token, source_id: SourceId) -> Result<SourceExpr, SampledTrueIError> {
    let proposition = parse_statement(token, source_id)?;
    let SourceExpr::SyntaxApplication { syntax, arguments, .. } =
        without_groups(&proposition.expression)
    else {
        return Err(input_error("True definition must use meta-equality"));
    };
    let [left, right] = arguments.as_slice() else {
        return Err(input_error("True definition must have one left and right side"));
    };
    if !matches!(syntax.spelling.as_ref(), "==" | "≡" | r"\<equiv>") || !is_name(left, "True") {
        return Err(input_error("True definition must define `True` by meta-equality"));
    }
    Ok(right.clone())
}

fn validate_true_i_proof(commands: &[CommandSpan], start: usize) -> Result<(), SampledTrueIError> {
    let expected = [
        (&["lemma", "TrueI", ":", "True"][..], "TrueI statement"),
        (&["unfolding", "True_def"][..], "TrueI unfolding"),
        (&["by", "(", "rule", "refl", ")"][..], "TrueI method"),
    ];
    for (offset, (tokens, label)) in expected.iter().enumerate() {
        let command =
            commands.get(start + offset).ok_or_else(|| input_error(format!("missing {label}")))?;
        require_exact(&command.tokens, tokens, label)?;
    }
    reject_proof_tail(commands, start + expected.len(), "TrueI")
}

fn reject_proof_tail(
    commands: &[CommandSpan],
    next: usize,
    label: &str,
) -> Result<(), SampledTrueIError> {
    if commands
        .get(next)
        .is_some_and(|command| command.kind.starts_with("prf_") || command.kind.starts_with("qed"))
    {
        return Err(input_error(format!("{label} has a trailing proof command")));
    }
    Ok(())
}

fn parse_statement(
    token: &Token,
    source_id: SourceId,
) -> Result<SourceProposition, SampledTrueIError> {
    parse_source_proposition_at(&token.source, source_id, token.offset)
        .ok_or_else(|| input_error("malformed sampled HOL proposition"))
}

fn quoted_content(token: &Token) -> Result<&str, SampledTrueIError> {
    token
        .source
        .strip_prefix('"')
        .and_then(|source| source.strip_suffix('"'))
        .ok_or_else(|| input_error("expected a quoted declaration"))
}

fn without_groups(mut expression: &SourceExpr) -> &SourceExpr {
    while let SourceExpr::Group { inner, .. } = expression {
        expression = inner;
    }
    expression
}

fn is_name(expression: &SourceExpr, expected: &str) -> bool {
    matches!(without_groups(expression), SourceExpr::Name { name, .. } if name.spelling.as_ref() == expected)
}

fn input_error(detail: impl Into<String>) -> SampledTrueIError {
    SampledTrueIError::Input(detail.into())
}
