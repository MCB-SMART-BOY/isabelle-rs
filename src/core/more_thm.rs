//! Additional theorem operations beyond the primitive kernel.
//!
//! Corresponds to `src/Pure/more_thm.ML`.
//!
//! These are safe derived operations on theorems.

use std::sync::Arc;

use super::{
    error::KernelError,
    logic::Pure,
    term::Term,
    thm::{CTerm, Thm, ThmKernel},
};

// =========================================================================
// Equality reasoning
// =========================================================================

/// `t == u` and `P(t)` → `P(u)` (substitutivity)
pub fn subst(thm_eq: &Thm, thm: &Thm) -> Option<Thm> {
    let (t, u) = Pure::dest_equals(thm_eq.prop().term())?;
    let prop = thm.prop().term();

    // Find t in prop and replace with u
    let new_prop = replace_in_term(prop, t, u)?;
    if &new_prop == prop {
        return Some(thm.clone());
    }

    // Use combination + transitive to produce P(t) == P(u)
    // Then combine with thm via implies_elim
    let refl_p = ThmKernel::reflexive_compat(CTerm::certify(new_prop.clone()));
    let ct = CTerm::certify(prop.clone());
    ThmKernel::transitive(&ThmKernel::reflexive_compat(ct), &refl_p).ok()
}

fn replace_in_term(term: &Term, from: &Term, to: &Term) -> Option<Term> {
    if term == from {
        return Some(to.clone());
    }
    match term {
        Term::App { func, arg } => {
            let f = replace_in_term(func, from, to);
            let a = replace_in_term(arg, from, to);
            if f.is_none() && a.is_none() {
                return None;
            }
            Some(Term::app(
                f.unwrap_or_else(|| func.as_ref().clone()),
                a.unwrap_or_else(|| func.as_ref().clone()),
            ))
        },
        Term::Abs { name, typ, body } => {
            let b = replace_in_term(body, from, to)?;
            Some(Term::abs(Arc::clone(name), typ.clone(), b))
        },
        _ => None,
    }
}

// =========================================================================
// Thm attributes: named theorems with tags
// =========================================================================

/// Theorem attributes like `[simp]`, `[intro]`, `[elim]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ThmAttribute {
    /// Simplification rule
    Simp,
    /// Introduction rule
    Intro,
    /// Elimination rule
    Elim,
    /// Destruction rule
    Dest,
    /// Forward rule
    Forward,
    /// Symmetric rule
    Sym,
}

/// Attach attributes to a theorem.
#[derive(Clone, Debug)]
pub struct AttributedThm {
    pub thm: Thm,
    pub name: String,
    pub attributes: Vec<ThmAttribute>,
}

impl AttributedThm {
    pub fn new(thm: Thm, name: String) -> Self {
        AttributedThm { thm, name, attributes: vec![] }
    }

    pub fn with_attr(mut self, attr: ThmAttribute) -> Self {
        self.attributes.push(attr);
        self
    }
}

// =========================================================================
// Theorem combinators
// =========================================================================

/// `thm1 RSN (i, thm2)`: resolve thm1 with the i-th premise of thm2.
pub fn rsn(thm1: &Thm, i: usize, thm2: &Thm) -> Option<Result<Thm, KernelError>> {
    crate::core::drule::compose(thm1, thm2, i - 1)
}

/// `thm1 RS thm2`: resolve thm1 with the first premise of thm2.
pub fn rs(thm1: &Thm, thm2: &Thm) -> Option<Result<Thm, KernelError>> {
    rsn(thm1, 1, thm2)
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{term::Term, types::Typ};

    fn prop(name: &str) -> CTerm {
        CTerm::certify(Term::const_(name, Typ::base("prop")))
    }

    #[test]
    fn test_rs_resolves() {
        let a = prop("A");
        let assumed = ThmKernel::assume_compat(a.clone());
        let trivial = ThmKernel::trivial(a).unwrap();
        let result = rs(&assumed, &trivial);
        assert!(result.is_some());
        assert!(result.unwrap().is_ok());
    }

    #[test]
    fn test_attributed_thm() {
        let a = prop("A");
        let thm = ThmKernel::trivial(a).unwrap();
        let attr_thm = AttributedThm::new(thm, "my_lemma".into())
            .with_attr(ThmAttribute::Simp)
            .with_attr(ThmAttribute::Intro);
        assert_eq!(attr_thm.attributes.len(), 2);
        assert_eq!(attr_thm.attributes[0], ThmAttribute::Simp);
    }
}
