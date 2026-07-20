//! Conversion between new-kernel and legacy core types.
//!
//! This module provides untrusted mechanical translations between the
//! `crate::kernel` type system and the legacy `crate::core` type system.
//! The kernel has already certified the terms; this conversion is purely
//! structural.

/// Convert a new-kernel `Ty` to a legacy core `Typ`.
pub fn kernel_ty_to_core(ty: &crate::kernel::Ty) -> crate::core::types::Typ {
    if ty.is_prop() {
        return crate::core::types::Typ::base("prop");
    }
    if let Some((from, to)) = ty.dest_arrow() {
        return crate::core::types::Typ::arrow(kernel_ty_to_core(from), kernel_ty_to_core(to));
    }
    let dbg = format!("{:?}", ty);
    if dbg.contains('(') {
        crate::core::types::Typ::dummy()
    } else {
        crate::core::types::Typ::base(&*dbg)
    }
}

/// Convert a new-kernel `Term` to a legacy core `Term`.
pub fn kernel_term_to_core(term: &crate::kernel::Term) -> crate::core::term::Term {
    match term {
        crate::kernel::Term::Const { name, ty } => {
            crate::core::term::Term::const_(name.as_ref(), kernel_ty_to_core(ty))
        },
        crate::kernel::Term::Free { name, ty } => {
            crate::core::term::Term::free(name.as_ref(), kernel_ty_to_core(ty))
        },
        crate::kernel::Term::Var { name, index, ty } => {
            crate::core::term::Term::var(name.as_ref(), *index, kernel_ty_to_core(ty))
        },
        crate::kernel::Term::Bound { index, ty: _ } => crate::core::term::Term::bound(*index),
        crate::kernel::Term::Abs { name, param_ty, body, ty: _ } => crate::core::term::Term::abs(
            name.as_ref(),
            kernel_ty_to_core(param_ty),
            kernel_term_to_core(body),
        ),
        crate::kernel::Term::App { func, arg, ty: _ } => {
            crate::core::term::Term::app(kernel_term_to_core(func), kernel_term_to_core(arg))
        },
        crate::kernel::Term::Forall { .. } => {
            panic!("Forall not yet supported in kernel -> core conversion")
        },
        crate::kernel::Term::Eq { .. } => {
            panic!("Eq not yet supported in kernel -> core conversion")
        },
        crate::kernel::Term::Imp { .. } => {
            panic!("Imp not yet supported in kernel -> core conversion")
        },
    }
}
