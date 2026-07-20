//! Conversion between new-kernel and legacy core types.
//!
//! This module provides untrusted mechanical translations between the
//! `crate::kernel` type system and the legacy `crate::core` type system.
//! The kernel has already certified the terms; this conversion is purely
//! structural. Returns `Err` for unsupported constructs — never panics
//! or produces dummy types.

use crate::kernel::{Term, Ty};

/// Error type for kernel-to-core conversion failures.
#[derive(Debug)]
pub enum ConversionError {
    /// The kernel type is too complex for legacy representation
    ComplexType(String),
    /// The kernel term uses an unsupported constructor
    UnsupportedTerm(&'static str),
}

impl std::fmt::Display for ConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConversionError::ComplexType(s) => write!(f, "complex type not convertible: {}", s),
            ConversionError::UnsupportedTerm(s) => write!(f, "unsupported term constructor: {}", s),
        }
    }
}

impl std::error::Error for ConversionError {}

/// Convert a new-kernel `Ty` to a legacy core `Typ`.
pub fn kernel_ty_to_core(ty: &Ty) -> Result<crate::core::types::Typ, ConversionError> {
    if ty.is_prop() {
        return Ok(crate::core::types::Typ::base("prop"));
    }
    if let Some((from, to)) = ty.dest_arrow() {
        return Ok(crate::core::types::Typ::arrow(
            kernel_ty_to_core(from)?,
            kernel_ty_to_core(to)?,
        ));
    }
    if ty.is_tvar() {
        return Err(ConversionError::ComplexType(format!(
            "type variable {:?} cannot be converted to legacy type",
            ty
        )));
    }
    // Base types (bool, nat, etc.) — extract the type name
    // Use the Debug representation for known simple types
    let dbg = format!("{:?}", ty);
    if dbg.contains('(') || dbg.contains(' ') {
        Err(ConversionError::ComplexType(format!("type {:?} is not a simple base type", ty)))
    } else {
        Ok(crate::core::types::Typ::base(&*dbg))
    }
}

/// Convert a new-kernel `Term` to a legacy core `Term`.
pub fn kernel_term_to_core(term: &Term) -> Result<crate::core::term::Term, ConversionError> {
    match term {
        Term::Const { name, ty } => {
            Ok(crate::core::term::Term::const_(name.as_ref(), kernel_ty_to_core(ty)?))
        },
        Term::Free { name, ty } => {
            Ok(crate::core::term::Term::free(name.as_ref(), kernel_ty_to_core(ty)?))
        },
        Term::Var { name, index, ty } => {
            Ok(crate::core::term::Term::var(name.as_ref(), *index, kernel_ty_to_core(ty)?))
        },
        Term::Bound { index, ty: _ } => Ok(crate::core::term::Term::bound(*index)),
        Term::Abs { name, param_ty, body, ty: _ } => Ok(crate::core::term::Term::abs(
            name.as_ref(),
            kernel_ty_to_core(param_ty)?,
            kernel_term_to_core(body)?,
        )),
        Term::App { func, arg, ty: _ } => {
            Ok(crate::core::term::Term::app(kernel_term_to_core(func)?, kernel_term_to_core(arg)?))
        },
        Term::Forall { .. } => Err(ConversionError::UnsupportedTerm("Forall")),
        Term::Eq { .. } => Err(ConversionError::UnsupportedTerm("Eq")),
        Term::Imp { .. } => Err(ConversionError::UnsupportedTerm("Imp")),
    }
}
