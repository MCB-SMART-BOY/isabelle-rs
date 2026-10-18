//! Narrow native replacement for the original Pure SHA1 Foreign implementation.
use super::lexer::{self, TokenKind};
use super::{
    Declaration, Expr, MlError, MlErrorKind, ModuleExpr, Pattern, Span, Type, TypeScheme, Value,
    Vm, parser,
};
use sha1::{Digest, Sha1};
use sha2::Sha256;

pub(super) const SHA1_SOURCE: &str = "src/Pure/General/sha1.ML";
const SHA1_SOURCE_SHA256: &str = "84dfc1b515c3fdd1496c40b002fa0c4673395a45ffa3e45d1648bdc934682f7b";
const HASH_CHUNK_BYTES: usize = 64 * 1024;
const FOREIGN_REPLACEMENT: &str = "fun digest_string_external str = Native_SHA1.digest_string str;";
const DIGEST_REPLACEMENT: &str = "fun digest_string str = digest_string_external str;";

/// Source and executable hashes are distinct: only the Foreign block is replaced.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeSha1Transformation {
    pub source_sha256: String,
    pub executable_sha256: String,
}

impl Vm {
    pub(super) fn install_native_sha1(&mut self) -> Result<(), MlError> {
        self.register_native(
            "Native_SHA1.digest_string",
            TypeScheme::mono(Type::Function(
                Box::new(Type::Constructor("string".to_owned(), vec![])),
                Box::new(Type::Constructor("string".to_owned(), vec![])),
            )),
            sha1_digest_string,
        )?;
        Ok(())
    }

    /// Invoked only at the approved source boundary; does not enable general Foreign calls.
    pub fn evaluate_native_sha1_module(
        &mut self,
        source_name: &str,
        original: &str,
    ) -> Result<NativeSha1Transformation, MlError> {
        if source_name != SHA1_SOURCE {
            return Err(sha1_error(source_name, "unexpected SHA1 source identity"));
        }
        let result = self.evaluate_native_sha1_checked(source_name, original);
        if result.is_err() {
            self.request_stop();
        }
        result
    }

    fn evaluate_native_sha1_checked(
        &mut self,
        source_name: &str,
        original: &str,
    ) -> Result<NativeSha1Transformation, MlError> {
        self.check_stop()?;
        let source_sha256 = base16ct::lower::encode_string(&Sha256::digest(original.as_bytes()));
        if source_sha256 != SHA1_SOURCE_SHA256 {
            return Err(sha1_error(
                source_name,
                "SHA1 source bytes differ from the fixed Isabelle2025 source",
            ));
        }
        let declarations =
            parser::parse(source_name, original, &self.fixities, &self.stop.0.requested)?;
        let tokens = lexer::tokenize(source_name, original, &self.stop.0.requested)?;
        let ranges = find_sha1_foreign_ranges(source_name, &declarations, &tokens)?;
        let mut executable = String::with_capacity(original.len());
        let mut position = 0;
        for (start, end, replacement) in ranges {
            let before = original
                .get(position..start)
                .ok_or_else(|| sha1_error(source_name, "invalid SHA1 source boundary"))?;
            executable.push_str(before);
            executable.push_str(replacement);
            position = end;
        }
        executable.push_str(
            original
                .get(position..)
                .ok_or_else(|| sha1_error(source_name, "invalid SHA1 trailing source"))?,
        );
        let identity = NativeSha1Transformation {
            source_sha256,
            executable_sha256: base16ct::lower::encode_string(&Sha256::digest(
                executable.as_bytes(),
            )),
        };
        if identity.source_sha256 == identity.executable_sha256 {
            return Err(sha1_error(
                source_name,
                "original and native SHA1 source identities unexpectedly coincide",
            ));
        }
        self.evaluate(source_name, &executable)?;
        self.hide_host_structure("Native_SHA1")?;
        Ok(identity)
    }
}

fn sha1_digest_string(vm: &mut Vm, args: &[Value]) -> Result<Value, MlError> {
    let bytes = args.first().and_then(Value::as_bytes).ok_or_else(|| {
        vm.error(MlErrorKind::Type, "Native_SHA1.digest_string", "expected SML byte string")
    })?;
    let mut digest = Sha1::new();
    for chunk in bytes.chunks(HASH_CHUNK_BYTES) {
        vm.check_stop()?;
        digest.update(chunk);
    }
    vm.check_stop()?;
    Ok(Value::text(base16ct::lower::encode_string(&digest.finalize())))
}

fn find_sha1_foreign_ranges(
    source: &str,
    declarations: &[Declaration],
    tokens: &[lexer::Token],
) -> Result<Vec<(usize, usize, &'static str)>, MlError> {
    if !declarations.iter().any(|declaration| {
        matches!(declaration,
        Declaration::Signature { name, .. } if name == "SHA1")
    }) {
        return Err(sha1_error(source, "missing original SHA1 signature"));
    }
    let structures: Vec<_> = declarations
        .iter()
        .filter_map(|declaration| match declaration {
            Declaration::Structure {
                name,
                signature: Some((signature, _)),
                body: ModuleExpr::Struct(body),
                ..
            } if name == "SHA1" && signature.is_named("SHA1") => Some(body),
            _ => None,
        })
        .collect();
    let [body] = structures.as_slice() else {
        return Err(sha1_error(source, "expected exactly one original SHA1: SHA1 structure"));
    };
    let locals: Vec<_> = body.iter().filter(|declaration| matches!(declaration,
        Declaration::Local { body, .. } if body.iter().any(|inner| is_named_function(inner, "digest_string_external"))
    )).collect();
    let [foreign] = locals.as_slice() else {
        return Err(sha1_error(source, "expected exactly one SHA1 external Foreign declaration"));
    };
    let digests: Vec<_> =
        body.iter().filter(|declaration| is_named_function(declaration, "digest_string")).collect();
    let [digest] = digests.as_slice() else {
        return Err(sha1_error(source, "expected exactly one original digest_string binding"));
    };
    let has_sample_checks = body.iter().any(|declaration| {
        matches!(declaration,
            Declaration::Local { body, .. }
                if body.iter().any(|inner| is_named_function(inner, "test_samples"))
        )
    });
    if !uses_foreign_handler(digest)
        || !has_sample_checks
        || !body.iter().any(is_test_samples_invocation)
    {
        return Err(sha1_error(source, "SHA1 fallback or original sample checks are missing"));
    }
    let foreign_start = declaration_start(foreign)
        .ok_or_else(|| sha1_error(source, "invalid foreign declaration kind"))?;
    let digest_start = declaration_start(digest)
        .ok_or_else(|| sha1_error(source, "invalid digest declaration kind"))?;
    let mut ranges = vec![
        (foreign_start, end_of_declaration(foreign_start, tokens, source)?, FOREIGN_REPLACEMENT),
        (digest_start, end_of_declaration(digest_start, tokens, source)?, DIGEST_REPLACEMENT),
    ];
    ranges.sort_unstable_by_key(|(start, _, _)| *start);
    if ranges[0].1 > ranges[1].0 {
        return Err(sha1_error(source, "overlapping SHA1 replacement declarations"));
    }
    Ok(ranges)
}

fn declaration_start(declaration: &Declaration) -> Option<usize> {
    match declaration {
        Declaration::Local { span, .. } | Declaration::Function { span, .. } => Some(span.start),
        _ => None,
    }
}

fn end_of_declaration(
    start: usize,
    tokens: &[lexer::Token],
    source: &str,
) -> Result<usize, MlError> {
    // The selected AST declarations each end at a semicolon. Keep all original
    // inter-declaration comments: only consume through the first *top-level* end.
    let mut depth = 0usize;
    let mut brackets = 0usize;
    for token in tokens.iter().filter(|token| token.span.start >= start) {
        match &token.kind {
            TokenKind::Name(name) if name == "local" || name == "let" || name == "struct" => {
                depth += 1
            },
            TokenKind::Name(name) if name == "end" && depth > 0 => depth -= 1,
            TokenKind::Symbol('(' | '[' | '{') => brackets += 1,
            TokenKind::Symbol(')' | ']' | '}') if brackets > 0 => brackets -= 1,
            TokenKind::Symbol(';') if depth == 0 && brackets == 0 => return Ok(token.span.end),
            TokenKind::Eof => break,
            _ => {},
        }
    }
    Err(sha1_error(source, "missing SHA1 declaration terminator"))
}

fn is_named_function(declaration: &Declaration, expected: &str) -> bool {
    matches!(declaration, Declaration::Function { bindings, .. }
        if bindings.len() == 1 && bindings[0].0 == expected)
}

fn uses_foreign_handler(declaration: &Declaration) -> bool {
    let Declaration::Function { bindings, .. } = declaration else { return false };
    let [(_, clauses)] = bindings.as_slice() else { return false };
    let [(_, expression)] = clauses.as_slice() else { return false };
    let mut expression = expression;
    while let Expr::Located(inner, _) = expression {
        expression = inner;
    }
    matches!(expression, Expr::Handle(_, branches) if branches.len() == 1
        && matches!(&branches[0].0, Pattern::Constructor(name, _) if name == "Foreign.Foreign"))
}

fn is_test_samples_invocation(declaration: &Declaration) -> bool {
    matches!(declaration, Declaration::Value { bindings, .. } if bindings.iter().any(|(_, expression)| {
        let mut expression = expression;
        while let Expr::Located(inner, _) = expression { expression = inner; }
        matches!(expression, Expr::Apply(callee, argument)
            if matches!(&**callee, Expr::Name(name) if name == "test_samples")
            && matches!(&**argument, Expr::Unit))
    }))
}

fn sha1_error(source: &str, cause: &str) -> MlError {
    MlError {
        kind: MlErrorKind::Syntax,
        span: Box::new(Span::new(source, 0, 0)),
        operation: "replace native SHA1".into(),
        cause: cause.to_owned(),
        exception: None,
        trace: Vec::new(),
    }
}
