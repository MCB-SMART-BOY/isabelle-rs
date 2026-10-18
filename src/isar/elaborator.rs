//! Declaration-aware elaboration: SourceProposition → CProp.
//!
//! Source syntax is untrusted. Resolve only explicitly declared names and
//! preserve Pure operators and bound-variable scope before kernel certification.

use std::sync::Arc;

use crate::isar::source_ast::{
    SourceBinder, SourceExpr, SourceName, SourceProposition, SourceSpan, SourceSyntax, SourceType,
};
use crate::kernel::{CProp, ConstScheme, KernelError, Name, ProofContext, RawTerm, Ty};

/// Errors that can occur during source proposition elaboration.
#[derive(Debug, Clone)]
pub enum ElaborationError {
    /// A name could not be resolved to a declared constant or free variable.
    UnresolvedName { spelling: Arc<str>, span: SourceSpan },
    /// A binder syntax token is not supported.
    UnknownBinder { spelling: Arc<str>, span: SourceSpan },
    /// A syntax application is not part of the supported Pure fragment.
    UnsupportedSyntax { spelling: Arc<str>, span: SourceSpan },
    /// A binder has no type annotation; guessing a type is not sound.
    MissingBinderType { spelling: Arc<str>, span: SourceSpan },
    /// An operator or binder received the wrong number of arguments.
    InvalidArity { spelling: Arc<str>, span: SourceSpan },
    /// A source type annotation does not match the checked term type.
    TypeAnnotationMismatch { expected: String, actual: String, span: SourceSpan },
    /// Kernel certification rejected the elaborated term.
    Kernel { source: Box<KernelError>, span: SourceSpan },
    /// A polymorphic constant needs a checked, explicit type ascription.
    CannotInferPolymorphicInstance { name: Name, span: SourceSpan },
    /// A source type cannot be represented as a kernel type.
    InvalidType { source: Box<KernelError>, span: SourceSpan },
    /// No source term could be parsed by the caller.
    ElaborationInternal(String),
}

impl std::fmt::Display for ElaborationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnresolvedName { spelling, .. } => write!(f, "unresolved name: {spelling}"),
            Self::UnknownBinder { spelling, .. } => write!(f, "unknown binder syntax: {spelling}"),
            Self::UnsupportedSyntax { spelling, .. } => write!(f, "unsupported syntax: {spelling}"),
            Self::MissingBinderType { spelling, .. } => {
                write!(f, "binder {spelling} requires a type annotation")
            },
            Self::InvalidArity { spelling, .. } => write!(f, "invalid arity for {spelling}"),
            Self::TypeAnnotationMismatch { expected, actual, .. } => {
                write!(f, "type annotation mismatch: expected {expected}, got {actual}")
            },
            Self::Kernel { source, .. } => write!(f, "term certification failed: {source}"),
            Self::CannotInferPolymorphicInstance { name, .. } => {
                write!(f, "cannot infer polymorphic instance for {name:?} without type annotation")
            },
            Self::InvalidType { source, .. } => write!(f, "invalid type annotation: {source}"),
            Self::ElaborationInternal(msg) => write!(f, "elaboration internal error: {msg}"),
        }
    }
}

impl std::error::Error for ElaborationError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Kernel { source, .. } | Self::InvalidType { source, .. } => Some(source.as_ref()),
            _ => None,
        }
    }
}

// ── helpers ──────────────────────────────────────────────────────────

fn source_name_to_kernel(name: &SourceName) -> Name {
    Name::from(name.spelling.clone())
}

/// Elaborate a source type annotation into a kernel `Ty`.
fn elaborate_source_type(st: &SourceType) -> Result<Ty, ElaborationError> {
    match st {
        SourceType::Name { name, span } => {
            Ty::base(source_name_to_kernel(name)).map_err(|source| ElaborationError::InvalidType {
                source: Box::new(source),
                span: *span,
            })
        },
        SourceType::Application { constructor, arguments, span } => {
            let SourceType::Name { name, .. } = constructor.as_ref() else {
                return Err(ElaborationError::UnsupportedSyntax {
                    spelling: "type constructor application".into(),
                    span: *span,
                });
            };
            let args =
                arguments.iter().map(elaborate_source_type).collect::<Result<Vec<_>, _>>()?;
            Ty::apply(source_name_to_kernel(name), args).map_err(|source| {
                ElaborationError::InvalidType { source: Box::new(source), span: *span }
            })
        },
        SourceType::Arrow { from, to, .. } => {
            Ok(Ty::arrow(elaborate_source_type(from)?, elaborate_source_type(to)?))
        },
    }
}

fn source_type_to_display(st: &SourceType) -> String {
    match st {
        SourceType::Name { name, .. } => name.spelling.to_string(),
        SourceType::Arrow { from, to, .. } => {
            format!("{} => {}", source_type_to_display(from), source_type_to_display(to))
        },
        SourceType::Application { constructor, arguments, .. } => {
            let args: Vec<String> = arguments.iter().map(source_type_to_display).collect();
            format!("{}({})", source_type_to_display(constructor), args.join(", "))
        },
    }
}

// ── main elaborator ──────────────────────────────────────────────────

/// Elaborate a source proposition into a kernel-certified `CProp`.
pub fn elaborate_proposition(
    source: &SourceProposition,
    ctx: &ProofContext,
) -> Result<CProp, ElaborationError> {
    let raw = elaborate_raw_term(&source.expression, ctx)?;
    let span = source.expression.span();
    match ctx.certify_prop(raw.clone()) {
        Ok(prop) => Ok(prop),
        Err(KernelError::NotProposition(ty))
            if ty
                == Ty::base("bool").map_err(|source| ElaborationError::InvalidType {
                    source: Box::new(source),
                    span,
                })? =>
        {
            let trueprop_ty = Ty::arrow(ty, Ty::prop());
            let wrapped = RawTerm::app(RawTerm::const_("HOL.Trueprop", trueprop_ty), raw);
            ctx.certify_prop(wrapped)
                .map_err(|source| ElaborationError::Kernel { source: Box::new(source), span })
        },
        Err(source) => Err(ElaborationError::Kernel { source: Box::new(source), span }),
    }
}

/// Elaborate untrusted source syntax into an uncertified term. The caller must
/// certify it against the intended owner before defining a constant or theorem.
pub fn elaborate_raw_term(
    expr: &SourceExpr,
    ctx: &ProofContext,
) -> Result<RawTerm, ElaborationError> {
    elaborate_expr(expr, ctx, &[], None)
}

fn elaborate_name(
    name: &SourceName,
    span: SourceSpan,
    ctx: &ProofContext,
    bounds: &[(Name, Ty)],
    annotated_ty: Option<&Ty>,
) -> Result<RawTerm, ElaborationError> {
    let kname = source_name_to_kernel(name);
    if let Some(index) = bounds.iter().rev().position(|(bound_name, _)| *bound_name == kname) {
        return Ok(RawTerm::bound(index));
    }
    if let Some(ty) = ctx.free_type(&kname) {
        return Ok(RawTerm::free(kname, ty.clone()));
    }
    let resolved = if name.spelling.as_ref() == "True" { Name::from("HOL.True") } else { kname };
    match ctx.signature().get_const(&resolved) {
        Some(ConstScheme::Monomorphic(ty)) => Ok(RawTerm::const_(resolved, ty.clone())),
        Some(ConstScheme::Polymorphic(_)) => {
            let Some(ty) = annotated_ty else {
                return Err(ElaborationError::CannotInferPolymorphicInstance {
                    name: resolved,
                    span,
                });
            };
            ctx.signature()
                .certify_const_instance(&resolved, ty)
                .map_err(|source| ElaborationError::Kernel { source: Box::new(source), span })?;
            Ok(RawTerm::const_(resolved, ty.clone()))
        },
        None => Err(ElaborationError::UnresolvedName { spelling: name.spelling.clone(), span }),
    }
}

fn certify_scoped_type(
    raw: &RawTerm,
    ctx: &ProofContext,
    bounds: &[(Name, Ty)],
    span: SourceSpan,
) -> Result<Ty, ElaborationError> {
    let scoped = bounds
        .iter()
        .rev()
        .fold(raw.clone(), |body, (name, ty)| RawTerm::abs(name.clone(), ty.clone(), body));
    let certified = ctx
        .certify_term(scoped)
        .map_err(|source| ElaborationError::Kernel { source: Box::new(source), span })?;
    let mut term = certified.term();
    for _ in bounds {
        let Some((_, _, body)) = term.dest_abs() else {
            return Err(ElaborationError::ElaborationInternal(
                "certified scope lost binder".into(),
            ));
        };
        term = body;
    }
    Ok(term.ty())
}

fn elaborate_binder(
    syntax: &SourceSyntax,
    binders: &[SourceBinder],
    body: &SourceExpr,
    ctx: &ProofContext,
    bounds: &[(Name, Ty)],
    expected: Option<&Ty>,
) -> Result<RawTerm, ElaborationError> {
    let is_forall = classify_binder(syntax)?;
    if binders.is_empty() {
        return Err(ElaborationError::InvalidArity {
            spelling: syntax.spelling.clone(),
            span: syntax.span,
        });
    }
    let mut scoped = bounds.to_vec();
    let mut body_expected = expected;
    for binder in binders {
        let inferred = if is_forall { None } else { body_expected.and_then(Ty::dest_arrow) };
        let ty = match (&binder.typ, inferred) {
            (Some(annotation), _) => elaborate_source_type(annotation)?,
            (None, Some((from, _))) => from.clone(),
            (None, None) => {
                return Err(ElaborationError::MissingBinderType {
                    spelling: binder.name.spelling.clone(),
                    span: binder.span,
                });
            },
        };
        if let Some((from, to)) = inferred {
            require_expected_type(&ty, from, binder.span)?;
            body_expected = Some(to);
        }
        scoped.push((source_name_to_kernel(&binder.name), ty));
    }
    let mut result = elaborate_expr(body, ctx, &scoped, body_expected)?;
    for (name, ty) in scoped.drain(bounds.len()..).rev() {
        result = if is_forall {
            RawTerm::forall(name, ty, result)
        } else {
            RawTerm::abs(name, ty, result)
        };
    }
    Ok(result)
}

fn classify_binder(syntax: &SourceSyntax) -> Result<bool, ElaborationError> {
    match syntax.spelling.as_ref() {
        "!!" | "⋀" | r"\<And>" => Ok(true),
        "λ" | r"\<lambda>" | "%" => Ok(false),
        _ => Err(ElaborationError::UnknownBinder {
            spelling: syntax.spelling.clone(),
            span: syntax.span,
        }),
    }
}

fn require_expected_type(
    actual: &Ty,
    expected: &Ty,
    span: SourceSpan,
) -> Result<(), ElaborationError> {
    if actual != expected {
        return Err(ElaborationError::TypeAnnotationMismatch {
            expected: format!("{expected:?}"),
            actual: format!("{actual:?}"),
            span,
        });
    }
    Ok(())
}

fn elaborate_syntax_application(
    syntax: &SourceSyntax,
    arguments: &[SourceExpr],
    span: SourceSpan,
    ctx: &ProofContext,
    bounds: &[(Name, Ty)],
) -> Result<RawTerm, ElaborationError> {
    if syntax.spelling.as_ref() == "PROP" {
        let [operand] = arguments else {
            return Err(ElaborationError::InvalidArity { spelling: syntax.spelling.clone(), span });
        };
        let raw = elaborate_expr(operand, ctx, bounds, None)?;
        let actual = certify_scoped_type(&raw, ctx, bounds, operand.span())?;
        if actual != Ty::prop() {
            return Err(ElaborationError::TypeAnnotationMismatch {
                expected: "prop".into(),
                actual: format!("{actual:?}"),
                span: operand.span(),
            });
        }
        return Ok(raw);
    }
    match syntax.spelling.as_ref() {
        "==>" | "⟹" | r"\<Longrightarrow>" | "==" | "≡" | r"\<equiv>" => {
            let [left, right] = arguments else {
                return Err(ElaborationError::InvalidArity {
                    spelling: syntax.spelling.clone(),
                    span,
                });
            };
            let left = elaborate_expr(left, ctx, bounds, None)?;
            let right = elaborate_expr(right, ctx, bounds, None)?;
            if matches!(syntax.spelling.as_ref(), "==>" | "⟹" | r"\<Longrightarrow>") {
                Ok(RawTerm::imp(left, right))
            } else {
                Ok(RawTerm::eq(left, right))
            }
        },
        "=" => elaborate_object_equality(arguments, span, ctx, bounds),
        "ALL" | "∀" | "EX" | "∃" | "-->" | "⟶" => Err(ElaborationError::UnsupportedSyntax {
            spelling: syntax.spelling.clone(),
            span: syntax.span,
        }),
        _ => elaborate_declared_application(syntax, arguments, ctx, bounds),
    }
}

fn elaborate_declared_application(
    syntax: &SourceSyntax,
    arguments: &[SourceExpr],
    ctx: &ProofContext,
    bounds: &[(Name, Ty)],
) -> Result<RawTerm, ElaborationError> {
    let name = Name::from(syntax.spelling.clone());
    let mut result = match ctx.signature().get_const(&name) {
        Some(ConstScheme::Monomorphic(ty)) => RawTerm::const_(name, ty.clone()),
        Some(ConstScheme::Polymorphic(_)) => {
            return Err(ElaborationError::CannotInferPolymorphicInstance {
                name,
                span: syntax.span,
            });
        },
        None => {
            return Err(ElaborationError::UnresolvedName {
                spelling: syntax.spelling.clone(),
                span: syntax.span,
            });
        },
    };
    for argument in arguments {
        result = RawTerm::app(result, elaborate_expr(argument, ctx, bounds, None)?);
    }
    Ok(result)
}

fn elaborate_object_equality(
    arguments: &[SourceExpr],
    span: SourceSpan,
    ctx: &ProofContext,
    bounds: &[(Name, Ty)],
) -> Result<RawTerm, ElaborationError> {
    let [lhs, rhs] = arguments else {
        return Err(ElaborationError::InvalidArity { spelling: "=".into(), span });
    };
    let (left, ty) = match elaborate_expr(lhs, ctx, bounds, None) {
        Ok(left) => {
            let ty = certify_scoped_type(&left, ctx, bounds, lhs.span())?;
            (left, ty)
        },
        Err(ElaborationError::MissingBinderType { .. }) => {
            let right = elaborate_expr(rhs, ctx, bounds, None)?;
            let ty = certify_scoped_type(&right, ctx, bounds, rhs.span())?;
            let left = elaborate_expr(lhs, ctx, bounds, Some(&ty))?;
            let actual = certify_scoped_type(&left, ctx, bounds, lhs.span())?;
            require_expected_type(&actual, &ty, lhs.span())?;
            return apply_object_equality(left, right, ty, span, ctx, bounds);
        },
        Err(err) => return Err(err),
    };
    let right = elaborate_expr(rhs, ctx, bounds, Some(&ty))?;
    let actual = certify_scoped_type(&right, ctx, bounds, rhs.span())?;
    require_expected_type(&actual, &ty, rhs.span())?;
    apply_object_equality(left, right, ty, span, ctx, bounds)
}

fn apply_object_equality(
    left: RawTerm,
    right: RawTerm,
    ty: Ty,
    span: SourceSpan,
    ctx: &ProofContext,
    bounds: &[(Name, Ty)],
) -> Result<RawTerm, ElaborationError> {
    let bool_ty = Ty::base("bool")
        .map_err(|source| ElaborationError::InvalidType { source: Box::new(source), span })?;
    let eq_ty = Ty::arrow(ty.clone(), Ty::arrow(ty, bool_ty));
    ctx.signature()
        .certify_const_instance(&Name::from("HOL.eq"), &eq_ty)
        .map_err(|source| ElaborationError::Kernel { source: Box::new(source), span })?;
    let raw = RawTerm::app(RawTerm::app(RawTerm::const_("HOL.eq", eq_ty), left), right);
    certify_scoped_type(&raw, ctx, bounds, span)?;
    Ok(raw)
}

fn elaborate_ascription(
    expression: &SourceExpr,
    typ: &SourceType,
    span: SourceSpan,
    ctx: &ProofContext,
    bounds: &[(Name, Ty)],
    outer_expected: Option<&Ty>,
) -> Result<RawTerm, ElaborationError> {
    let expected = elaborate_source_type(typ)?;
    if let Some(outer_expected) = outer_expected {
        require_expected_type(&expected, outer_expected, span)?;
    }
    let raw = match expression {
        SourceExpr::Name { name, span } => {
            elaborate_name(name, *span, ctx, bounds, Some(&expected))?
        },
        _ => elaborate_expr(expression, ctx, bounds, Some(&expected))?,
    };
    let actual = certify_scoped_type(&raw, ctx, bounds, span)?;
    if actual != expected {
        return Err(ElaborationError::TypeAnnotationMismatch {
            expected: source_type_to_display(typ),
            actual: format!("{actual:?}"),
            span,
        });
    }
    Ok(raw)
}

fn elaborate_expr(
    expr: &SourceExpr,
    ctx: &ProofContext,
    bounds: &[(Name, Ty)],
    expected: Option<&Ty>,
) -> Result<RawTerm, ElaborationError> {
    match expr {
        SourceExpr::Name { name, span } => elaborate_name(name, *span, ctx, bounds, None),
        SourceExpr::Application { function, argument, .. } => Ok(RawTerm::app(
            elaborate_expr(function, ctx, bounds, None)?,
            elaborate_expr(argument, ctx, bounds, None)?,
        )),
        SourceExpr::Binder { syntax, binders, body, .. } => {
            elaborate_binder(syntax, binders, body, ctx, bounds, expected)
        },
        SourceExpr::SyntaxApplication { syntax, arguments, span } => {
            elaborate_syntax_application(syntax, arguments, *span, ctx, bounds)
        },
        SourceExpr::Group { inner, .. } => elaborate_expr(inner, ctx, bounds, expected),
        SourceExpr::TypeAscription { expression, typ, span } => {
            elaborate_ascription(expression, typ, *span, ctx, bounds, expected)
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::isar::source_ast::{SourceBinder, SourceId, SourceSyntax};
    use crate::kernel::{Signature, TheorySnapshot};

    fn make_context() -> ProofContext {
        let sig = Signature::new()
            .install_empty_class(crate::kernel::EmptyClassDeclCert::hol_type())
            .unwrap()
            .extend_type_constructor("bool", 0)
            .unwrap()
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()))
            .unwrap()
            .extend_const(
                "HOL.eq",
                Ty::arrow(
                    Ty::tvar("alpha", 0, crate::kernel::Sort::hol_type()),
                    Ty::arrow(
                        Ty::tvar("alpha", 0, crate::kernel::Sort::hol_type()),
                        Ty::base("bool").unwrap(),
                    ),
                ),
            )
            .unwrap()
            .extend_const(
                "P",
                Ty::arrow(
                    Ty::tvar("alpha", 0, crate::kernel::Sort::hol_type()),
                    Ty::base("bool").unwrap(),
                ),
            )
            .unwrap();
        let snapshot = TheorySnapshot::root("test", sig);
        ProofContext::new(snapshot)
    }

    fn span() -> SourceSpan {
        SourceSpan { start: 0, end: 0 }
    }

    fn name(s: &str) -> SourceName {
        SourceName { spelling: s.into() }
    }

    fn prop(expr: SourceExpr) -> SourceProposition {
        SourceProposition { source: SourceId::new("test"), span: span(), expression: expr }
    }

    #[test]
    fn unresolved_name_is_rejected() {
        let ctx = make_context();
        let p = prop(SourceExpr::Name { name: name("not_declared"), span: span() });
        let result = elaborate_proposition(&p, &ctx);
        assert!(matches!(result, Err(ElaborationError::UnresolvedName { .. })));
    }

    #[test]
    fn unknown_binder_is_rejected() {
        let ctx = make_context();
        let p = prop(SourceExpr::Binder {
            syntax: SourceSyntax { spelling: "mu".into(), span: span() },
            binders: vec![],
            body: Box::new(SourceExpr::Name { name: name("P"), span: span() }),
            span: span(),
        });
        let result = elaborate_proposition(&p, &ctx);
        assert!(matches!(result, Err(ElaborationError::UnknownBinder { .. })));
    }

    #[test]
    fn type_annotation_mismatch_rejected() {
        let ctx = make_context();
        let p = prop(SourceExpr::TypeAscription {
            expression: Box::new(SourceExpr::Name { name: name("P"), span: span() }),
            typ: SourceType::Name { name: name("bool"), span: span() },
            span: span(),
        });
        let result = elaborate_proposition(&p, &ctx);
        assert!(matches!(result, Err(ElaborationError::TypeAnnotationMismatch { .. })));
    }

    fn make_polymorphic_context() -> ProofContext {
        use crate::kernel::logic::{PolyType, PolyTypeParam};
        let scheme = PolyType::new(
            vec![PolyTypeParam {
                id: crate::kernel::TypeVarId::new("'a", 0, crate::kernel::Sort::hol_type()),
            }],
            Ty::arrow(
                Ty::tvar("'a", 0, crate::kernel::Sort::hol_type()),
                Ty::arrow(
                    Ty::tvar("'a", 0, crate::kernel::Sort::hol_type()),
                    Ty::base("bool").unwrap(),
                ),
            ),
        )
        .unwrap();
        let sig = Signature::new()
            .install_empty_class(crate::kernel::EmptyClassDeclCert::hol_type())
            .unwrap()
            .extend_type_constructor("bool", 0)
            .unwrap()
            .extend_const_scheme("HOL.eq", scheme)
            .unwrap()
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()))
            .unwrap();
        let snapshot = TheorySnapshot::root("test_poly", sig);
        ProofContext::new(snapshot)
    }

    #[test]
    fn polymorphic_const_without_ascription_is_rejected() {
        let ctx = make_polymorphic_context();
        let p = prop(SourceExpr::Name { name: name("HOL.eq"), span: span() });
        let result = elaborate_proposition(&p, &ctx);
        assert!(
            matches!(result, Err(ElaborationError::CannotInferPolymorphicInstance { .. })),
            "must reject polymorphic constant without type annotation, got: {result:?}"
        );
    }
    fn pure_context() -> ProofContext {
        let signature = Signature::new()
            .extend_type_constructor("bool", 0)
            .unwrap()
            .extend_type_constructor("nat", 0)
            .unwrap()
            .extend_const("A", Ty::prop())
            .unwrap()
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()))
            .unwrap()
            .extend_const("HOL.True", Ty::base("bool").unwrap())
            .unwrap()
            .extend_const("N", Ty::base("nat").unwrap())
            .unwrap();
        ProofContext::new(TheorySnapshot::root("pure_elaboration", signature))
    }

    fn source_name(spelling: &str) -> SourceExpr {
        SourceExpr::Name { name: name(spelling), span: span() }
    }

    fn operator(spelling: &str, arguments: Vec<SourceExpr>) -> SourceExpr {
        SourceExpr::SyntaxApplication {
            syntax: SourceSyntax { spelling: spelling.into(), span: span() },
            arguments,
            span: span(),
        }
    }

    fn binder(spelling: &str, names: &[&str], body: SourceExpr) -> SourceExpr {
        SourceExpr::Binder {
            syntax: SourceSyntax { spelling: spelling.into(), span: span() },
            binders: names
                .iter()
                .map(|n| SourceBinder {
                    name: name(n),
                    typ: Some(SourceType::Name { name: name("prop"), span: span() }),
                    span: span(),
                })
                .collect(),
            body: Box::new(body),
            span: span(),
        }
    }

    #[test]
    fn elaborate_proposition_true_alias_requires_declaration_and_bool_judgment() {
        let ctx = pure_context();
        let certified = elaborate_proposition(&prop(source_name("True")), &ctx).unwrap();
        let expected = ctx
            .certify_prop(RawTerm::app(
                RawTerm::const_("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop())),
                RawTerm::const_("HOL.True", Ty::base("bool").unwrap()),
            ))
            .unwrap();
        assert_eq!(certified.term(), expected.term());
        let only_judgment = ProofContext::new(TheorySnapshot::root(
            "no_true",
            Signature::new()
                .extend_type_constructor("bool", 0)
                .unwrap()
                .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()))
                .unwrap(),
        ));
        assert!(matches!(
            elaborate_proposition(&prop(source_name("True")), &only_judgment),
            Err(ElaborationError::UnresolvedName { .. })
        ));
    }

    #[test]
    fn elaborate_proposition_pure_binder_shadows_constant_with_bound_indices() {
        let ctx = pure_context();
        let expression =
            binder("!!", &["A", "x"], operator("==>", vec![source_name("A"), source_name("x")]));
        let certified = elaborate_proposition(&prop(expression), &ctx).unwrap();
        let expected = ctx
            .certify_prop(RawTerm::forall(
                "A",
                Ty::prop(),
                RawTerm::forall(
                    "x",
                    Ty::prop(),
                    RawTerm::imp(RawTerm::bound(1), RawTerm::bound(0)),
                ),
            ))
            .unwrap();
        assert_eq!(certified.term(), expected.term());
    }

    #[test]
    fn elaborate_proposition_nested_shadow_uses_nearest_binder() {
        let ctx = pure_context();
        let inner = SourceExpr::TypeAscription {
            expression: Box::new(source_name("x")),
            typ: SourceType::Name { name: name("prop"), span: span() },
            span: span(),
        };
        let certified = elaborate_proposition(
            &prop(binder("!!", &["x", "x"], operator("==>", vec![inner, source_name("x")]))),
            &ctx,
        )
        .unwrap();
        let expected = ctx
            .certify_prop(RawTerm::forall(
                "x",
                Ty::prop(),
                RawTerm::forall(
                    "x",
                    Ty::prop(),
                    RawTerm::imp(RawTerm::bound(0), RawTerm::bound(0)),
                ),
            ))
            .unwrap();
        assert_eq!(certified.term(), expected.term());
    }

    #[test]
    fn elaborate_proposition_pure_binder_and_implication_spellings_match_ascii() {
        use crate::isar::source_parser::parse_source_proposition;

        let ctx = pure_context();
        let expected = ctx
            .certify_prop(RawTerm::forall(
                "x",
                Ty::prop(),
                RawTerm::imp(RawTerm::bound(0), RawTerm::bound(0)),
            ))
            .unwrap();
        for source in
            ["!!(x::prop). x ==> x", "⋀(x::prop). x ⟹ x", r"\<And>(x::prop). x \<Longrightarrow> x"]
        {
            let parsed = parse_source_proposition(source, SourceId::new("pure")).unwrap();
            let actual = elaborate_proposition(&parsed, &ctx).unwrap();
            assert_eq!(actual.term(), expected.term(), "{source}");
        }
    }

    #[test]
    fn elaborate_proposition_prop_bound_operand_certifies_same_pure_term() {
        use crate::isar::source_parser::parse_source_proposition;

        let ctx = pure_context();
        let source = "!!Q::prop. PROP Q ==> PROP Q";
        let parsed = parse_source_proposition(source, SourceId::new("pure")).unwrap();
        let actual = elaborate_proposition(&parsed, &ctx).unwrap();
        let expected = ctx
            .certify_prop(RawTerm::forall(
                "Q",
                Ty::prop(),
                RawTerm::imp(RawTerm::bound(0), RawTerm::bound(0)),
            ))
            .unwrap();
        assert_eq!(actual.term(), expected.term());
    }

    #[test]
    fn elaborate_proposition_prop_bool_operand_never_receives_trueprop() {
        use crate::isar::source_parser::parse_source_proposition;

        let ctx = pure_context();
        for source in ["PROP True", "PROP (True)", "PROP N"] {
            let parsed = parse_source_proposition(source, SourceId::new("pure")).unwrap();
            assert!(
                matches!(
                    elaborate_proposition(&parsed, &ctx),
                    Err(ElaborationError::TypeAnnotationMismatch { expected, .. })
                        if expected == "prop"
                ),
                "{source}"
            );
        }
        let parsed = parse_source_proposition("True", SourceId::new("hol")).unwrap();
        assert!(elaborate_proposition(&parsed, &ctx).is_ok());
    }

    #[test]
    fn elaborate_proposition_pure_equivalence_spellings_match_ascii() {
        use crate::isar::source_parser::parse_source_proposition;

        let ctx = pure_context();
        let expected = ctx
            .certify_prop(RawTerm::eq(
                RawTerm::const_("A", Ty::prop()),
                RawTerm::const_("A", Ty::prop()),
            ))
            .unwrap();
        for source in ["A == A", "A ≡ A", r"A \<equiv> A"] {
            let parsed = parse_source_proposition(source, SourceId::new("pure")).unwrap();
            let actual = elaborate_proposition(&parsed, &ctx).unwrap();
            assert_eq!(actual.term(), expected.term(), "{source}");
        }
    }

    #[test]
    fn elaborate_proposition_typed_lambda_spellings_match_ascii() {
        use crate::isar::source_parser::parse_source_proposition;

        let ctx = pure_context();
        let expected = ctx
            .certify_prop(RawTerm::eq(
                RawTerm::app(
                    RawTerm::abs("x", Ty::prop(), RawTerm::bound(0)),
                    RawTerm::const_("A", Ty::prop()),
                ),
                RawTerm::const_("A", Ty::prop()),
            ))
            .unwrap();
        for source in [
            "(%(x::prop). x) A == A",
            "(λ(x::prop). x) A ≡ A",
            r"(\<lambda>(x::prop). x) A \<equiv> A",
        ] {
            let parsed = parse_source_proposition(source, SourceId::new("pure")).unwrap();
            let actual = elaborate_proposition(&parsed, &ctx).unwrap();
            assert_eq!(actual.term(), expected.term(), "{source}");
        }
    }

    #[test]
    fn elaborate_proposition_untyped_pure_binders_are_rejected() {
        use crate::isar::source_parser::parse_source_proposition;

        let ctx = pure_context();
        for source in ["⋀x. x ⟹ x", r"\<And>x. x ==> x", "(λx. x) A ≡ A", r"(\<lambda>x. x) A == A"]
        {
            let parsed = parse_source_proposition(source, SourceId::new("pure")).unwrap();
            assert!(
                matches!(
                    elaborate_proposition(&parsed, &ctx),
                    Err(ElaborationError::MissingBinderType { .. })
                ),
                "{source}"
            );
        }
    }

    #[test]
    fn elaborate_proposition_unicode_operator_does_not_bypass_type_checks() {
        use crate::isar::source_parser::parse_source_proposition;

        let ctx = pure_context();
        let source = "⋀(x::nat). x ⟹ x";
        let parsed = parse_source_proposition(source, SourceId::new("pure")).unwrap();
        assert!(matches!(
            elaborate_proposition(&parsed, &ctx),
            Err(ElaborationError::Kernel { source, .. })
                if matches!(source.as_ref(), KernelError::NotProposition(_))
        ));
    }

    #[test]
    fn elaborate_proposition_hol_quantifier_never_becomes_pure_forall() {
        let ctx = pure_context();
        for spelling in ["ALL", "∀", "EX", "∃"] {
            let source = prop(binder(spelling, &["x"], source_name("A")));
            assert!(matches!(
                elaborate_proposition(&source, &ctx),
                Err(ElaborationError::UnknownBinder { .. })
            ));
        }
    }

    #[test]
    fn elaborate_proposition_non_bool_never_receives_trueprop() {
        let ctx = pure_context();
        assert!(matches!(
            elaborate_proposition(&prop(source_name("N")), &ctx),
            Err(ElaborationError::Kernel { source, .. })
                if matches!(source.as_ref(), KernelError::NotProposition(_))
        ));
        let pure = elaborate_proposition(&prop(source_name("A")), &ctx).unwrap();
        assert_eq!(pure.term(), ctx.certify_prop(RawTerm::const_("A", Ty::prop())).unwrap().term());
    }

    #[test]
    fn elaborate_proposition_missing_binder_type_does_not_guess() {
        let ctx = pure_context();
        let source = prop(SourceExpr::Binder {
            syntax: SourceSyntax { spelling: "!!".into(), span: span() },
            binders: vec![SourceBinder {
                name: name("x"),
                typ: None,
                span: SourceSpan { start: 3, end: 4 },
            }],
            body: Box::new(operator("==>", vec![source_name("x"), source_name("x")])),
            span: span(),
        });
        assert!(matches!(
            elaborate_proposition(&source, &ctx),
            Err(ElaborationError::MissingBinderType { span: SourceSpan { start: 3, end: 4 }, .. })
        ));
    }

    #[test]
    fn elaborate_proposition_pure_operator_rejects_partial_source() {
        let ctx = pure_context();
        assert!(matches!(
            elaborate_proposition(&prop(operator("==>", vec![source_name("A")])), &ctx),
            Err(ElaborationError::InvalidArity { .. })
        ));
        assert!(matches!(
            elaborate_proposition(
                &prop(operator("-->", vec![source_name("A"), source_name("A")])),
                &ctx
            ),
            Err(ElaborationError::UnsupportedSyntax { .. })
        ));
    }

    #[test]
    fn elaborate_proposition_syntax_operator_requires_declared_constant() {
        let mut ctx = pure_context();
        ctx.declare_free("f", Ty::arrow(Ty::prop(), Ty::prop()));
        let source = prop(operator("f", vec![source_name("A")]));
        assert!(matches!(
            elaborate_proposition(&source, &ctx),
            Err(ElaborationError::UnresolvedName { .. })
        ));
    }
}
