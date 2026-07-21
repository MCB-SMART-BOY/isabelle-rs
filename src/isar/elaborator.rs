//! Declaration-aware elaboration: SourceProposition → CProp.
//!
//! This module converts the data-only `SourceProposition` AST into a checked
//! kernel `CProp` by resolving names against a `ProofContext` and inserting
//! `HOL.Trueprop` where needed. It is the bridge between untrusted source
//! syntax and the trusted kernel boundary.
//!
//! Trust status: this module is **untrusted** — it runs *before* the kernel's
//! `certify_prop` check. The kernel re-validates every constant type and
//! proposition type independently. A bug here can produce wrong propositions
//! but cannot bypass the kernel's certification.

use std::sync::Arc;

use crate::isar::source_ast::{
    SourceBinder, SourceExpr, SourceId, SourceName, SourceProposition, SourceSpan, SourceSyntax,
    SourceType,
};
use crate::kernel::{CProp, ConstScheme, KernelError, Name, ProofContext, RawTerm, Ty};

/// Errors that can occur during source proposition elaboration.
#[derive(Debug, Clone)]
pub enum ElaborationError {
    /// A name could not be resolved to a constant or free variable.
    UnresolvedName { spelling: Arc<str>, span: SourceSpan },
    /// A binder syntax token is not recognized.
    UnknownBinder { spelling: Arc<str>, span: SourceSpan },
    /// A source type annotation does not match the elaborated type.
    TypeAnnotationMismatch { expected: String, actual: String, span: SourceSpan },
    /// Internal elaboration failure (wraps kernel or other errors).
    ElaborationInternal(String),
}

impl std::fmt::Display for ElaborationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnresolvedName { spelling, span: _ } => {
                write!(f, "unresolved name: {spelling}")
            },
            Self::UnknownBinder { spelling, span: _ } => {
                write!(f, "unknown binder syntax: {spelling}")
            },
            Self::TypeAnnotationMismatch { expected, actual, span: _ } => {
                write!(f, "type annotation mismatch: expected {expected}, got {actual}")
            },
            Self::ElaborationInternal(msg) => {
                write!(f, "elaboration internal error: {msg}")
            },
        }
    }
}

impl std::error::Error for ElaborationError {}

impl From<KernelError> for ElaborationError {
    fn from(e: KernelError) -> Self {
        ElaborationError::ElaborationInternal(format!("{e:?}"))
    }
}

// ── helpers ──────────────────────────────────────────────────────────

fn source_name_to_kernel(name: &SourceName) -> Name {
    Name::from(name.spelling.clone())
}

/// Elaborate a source type annotation into a kernel `Ty`.
fn elaborate_source_type(st: &SourceType, ctx: &ProofContext) -> Result<Ty, ElaborationError> {
    match st {
        SourceType::Name { name, span } => {
            let ty_name = source_name_to_kernel(name);
            Ty::base(ty_name).map_err(|_| {
                ElaborationError::ElaborationInternal(format!(
                    "invalid base type: {}",
                    name.spelling
                ))
            })
        },
        SourceType::Application { constructor, arguments, span } => {
            let ctor = elaborate_source_type(constructor, ctx)?;
            let mut args = Vec::with_capacity(arguments.len());
            for a in arguments {
                args.push(elaborate_source_type(a, ctx)?);
            }
            // Reconstruct: we don't have Ty::apply exposed publicly beyond base/arrow.
            // For now, only support arrow as the only type constructor with args.
            if ctor == Ty::prop() || !args.is_empty() {
                // Arrow is encoded as fun(A, B), not as an application in source.
                // Fall back: just return the base type name.
            }
            Err(ElaborationError::ElaborationInternal("type application not yet supported".into()))
        },
        SourceType::Arrow { from, to, span } => {
            let f = elaborate_source_type(from, ctx)?;
            let t = elaborate_source_type(to, ctx)?;
            Ok(Ty::arrow(f, t))
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
    let raw = elaborate_expr(&source.expression, ctx)?;

    // Trueprop insertion: if the elaborated term's outermost type is bool (not prop),
    // wrap it with HOL.Trueprop.
    let raw = maybe_insert_trueprop(raw, ctx)?;

    let cprop = ctx.certify_prop(raw)?;
    Ok(cprop)
}

fn maybe_insert_trueprop(raw: RawTerm, ctx: &ProofContext) -> Result<RawTerm, ElaborationError> {
    // We can't directly query the type of a RawTerm without certifying.
    // Strategy: try certifying as-is. If the type is prop, good. If the
    // type is bool, wrap with Trueprop and re-certify.
    //
    // But we need to know the type BEFORE certification to decide.
    // Alternative: check if the outermost expression is syntactically
    // a bool-typed constant/application.
    //
    // Simpler: just wrap everything that looks like it could be bool.
    // The kernel will type-check. If already prop, Trueprop(bool=>prop)(prop)
    // would fail type-check. So we try WITHOUT Trueprop first, check the
    // type, and add Trueprop only if it's bool.

    // First, try certifying. We use a temporary certification to check the type.
    match ctx.certify_term(raw.clone()) {
        Ok(cterm) => {
            let ty = cterm.term().ty();
            if ty.is_prop() {
                return Ok(raw);
            }
            // It's not prop — assume it needs Trueprop.
            let trueprop_name = Name::from("HOL.Trueprop");
            let bool_ty = Ty::base("bool")
                .map_err(|_| ElaborationError::ElaborationInternal("bad bool type".into()))?;
            let prop_ty = Ty::prop();
            let trueprop_ty = Ty::arrow(bool_ty, prop_ty);
            let wrapped = RawTerm::app(RawTerm::const_(trueprop_name, trueprop_ty), raw);
            Ok(wrapped)
        },
        Err(KernelError::UndeclaredConst(name)) => {
            // The raw term references an undeclared constant. Don't wrap —
            // let the caller handle the error.
            Err(ElaborationError::UnresolvedName {
                spelling: name.as_str().into(),
                span: SourceSpan { start: 0, end: 0 },
            })
        },
        Err(_) => {
            // Other errors: just return the raw term and let certify_prop catch it.
            Ok(raw)
        },
    }
}

fn elaborate_expr(expr: &SourceExpr, ctx: &ProofContext) -> Result<RawTerm, ElaborationError> {
    match expr {
        SourceExpr::Name { name, span } => {
            let kname = source_name_to_kernel(name);
            // Try constant first
            match ctx.signature().get_const(&kname) {
                Some(ConstScheme::Monomorphic(ty)) => {
                    return Ok(RawTerm::const_(kname, ty.clone()));
                }
                Some(ConstScheme::Polymorphic(scheme)) => {
                    // Return the scheme body - contains type variables that the kernel
                    // will validate as a monomorphic instance at certify_raw time.
                    return Ok(RawTerm::const_(kname, scheme.body().clone()));
                }
                None => { /* fall through to free-variable check */ }
            }
            // Try free variable
            if let Some(declared_ty) = ctx.free_type(&kname) {
                return Ok(RawTerm::free(kname, declared_ty.clone()));
            }
            Err(ElaborationError::UnresolvedName { spelling: name.spelling.clone(), span: *span })
        },
        SourceExpr::Application { function, argument, span } => {
            let func = elaborate_expr(function, ctx)?;
            let arg = elaborate_expr(argument, ctx)?;
            Ok(RawTerm::app(func, arg))
        },
        SourceExpr::Binder { syntax, binders, body, span } => {
            let body = elaborate_expr(body, ctx)?;
            match syntax.spelling.as_ref() {
                "!!" | "⋀" | "!!" => {
                    // Pure universal: nested Forall
                    let mut result = body;
                    for binder in binders.iter().rev() {
                        let kname = source_name_to_kernel(&binder.name);
                        let param_ty = match &binder.typ {
                            Some(st) => elaborate_source_type(st, ctx)?,
                            None => Ty::base("prop").map_err(|_| {
                                ElaborationError::ElaborationInternal("bad prop type".into())
                            })?,
                        };
                        result = RawTerm::Forall { name: kname, param_ty, body: Box::new(result) };
                    }
                    Ok(result)
                },
                "ALL" | "∀" => {
                    // HOL universal: nested Forall, Trueprop insertion handled later
                    let mut result = body;
                    for binder in binders.iter().rev() {
                        let kname = source_name_to_kernel(&binder.name);
                        let param_ty = match &binder.typ {
                            Some(st) => elaborate_source_type(st, ctx)?,
                            None => Ty::base("prop").map_err(|_| {
                                ElaborationError::ElaborationInternal("bad prop type".into())
                            })?,
                        };
                        result = RawTerm::Forall { name: kname, param_ty, body: Box::new(result) };
                    }
                    Ok(result)
                },
                _ => Err(ElaborationError::UnknownBinder {
                    spelling: syntax.spelling.clone(),
                    span: syntax.span,
                }),
            }
        },
        SourceExpr::SyntaxApplication { syntax, arguments, span } => {
            let kname = source_name_to_kernel(&SourceName { spelling: syntax.spelling.clone() });
            let declared_ty = match ctx.signature().get_const(&kname) {
                Some(ConstScheme::Monomorphic(ty)) => ty.clone(),
                Some(ConstScheme::Polymorphic(scheme)) => scheme.body().clone(),
                None => {
                    return Err(ElaborationError::UnresolvedName {
                        spelling: syntax.spelling.clone(),
                        span: syntax.span,
                    })
                }
            };
            let mut result = RawTerm::const_(kname, declared_ty.clone());
            for arg in arguments {
                let arg_term = elaborate_expr(arg, ctx)?;
                result = RawTerm::app(result, arg_term);
            }
            Ok(result)
        },
        SourceExpr::Group { inner, span: _ } => elaborate_expr(inner, ctx),
        SourceExpr::TypeAscription { expression, typ, span } => {
            let elaborated = elaborate_expr(expression, ctx)?;
            let src_ty = elaborate_source_type(typ, ctx)?;

            // Validate by certifying and checking the type
            let certified = ctx.certify_term(elaborated.clone())?;
            let actual_ty = certified.term().ty();

            if actual_ty.clone() != src_ty {
                return Err(ElaborationError::TypeAnnotationMismatch {
                    expected: source_type_to_display(typ),
                    actual: format!("{:?}", actual_ty),
                    span: *span,
                });
            }
            Ok(elaborated)
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{Signature, TheorySnapshot};

    fn make_context() -> ProofContext {
        let sig = Signature::new()
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()))
            .unwrap()
            .extend_const(
                "HOL.eq",
                Ty::arrow(
                    Ty::tvar("alpha", 0, crate::kernel::Sort::typ()),
                    Ty::arrow(
                        Ty::tvar("alpha", 0, crate::kernel::Sort::typ()),
                        Ty::base("bool").unwrap(),
                    ),
                ),
            )
            .unwrap()
            .extend_const(
                "P",
                Ty::arrow(
                    Ty::tvar("alpha", 0, crate::kernel::Sort::typ()),
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
}
