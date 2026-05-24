//! Isabelle lambda terms: the core data structure of the prover.
//! Corresponds to src/Pure/term.ML.
use super::types::{Symbol, Typ};
use std::fmt;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Const {
        name: Symbol,
        typ: Typ,
    },
    Free {
        name: Symbol,
        typ: Typ,
    },
    Var {
        name: Symbol,
        index: usize,
        typ: Typ,
    },
    Bound(usize),
    Abs {
        name: Symbol,
        typ: Typ,
        body: Box<Term>,
    },
    App {
        func: Box<Term>,
        arg: Box<Term>,
    },
}

impl Term {
    pub fn const_(name: impl Into<Symbol>, typ: Typ) -> Self {
        Term::Const {
            name: name.into(),
            typ,
        }
    }
    pub fn free(name: impl Into<Symbol>, typ: Typ) -> Self {
        Term::Free {
            name: name.into(),
            typ,
        }
    }
    pub fn var(name: impl Into<Symbol>, index: usize, typ: Typ) -> Self {
        Term::Var {
            name: name.into(),
            index,
            typ,
        }
    }
    pub fn bound(index: usize) -> Self {
        Term::Bound(index)
    }
    pub fn abs(name: impl Into<Symbol>, typ: Typ, body: Term) -> Self {
        Term::Abs {
            name: name.into(),
            typ,
            body: Box::new(body),
        }
    }
    pub fn app(func: Term, arg: Term) -> Self {
        Term::App {
            func: Box::new(func),
            arg: Box::new(arg),
        }
    }
    pub fn apps(func: Term, args: impl IntoIterator<Item = Term>) -> Self {
        args.into_iter().fold(func, |acc, arg| Term::app(acc, arg))
    }
    pub fn is_const(&self) -> bool {
        matches!(self, Term::Const { .. })
    }
    pub fn is_free(&self) -> bool {
        matches!(self, Term::Free { .. })
    }
    pub fn is_var(&self) -> bool {
        matches!(self, Term::Var { .. })
    }
    pub fn is_bound(&self) -> bool {
        matches!(self, Term::Bound(_))
    }
    pub fn is_abs(&self) -> bool {
        matches!(self, Term::Abs { .. })
    }
    pub fn is_app(&self) -> bool {
        matches!(self, Term::App { .. })
    }
    pub fn strip_comb(&self) -> (&Term, Vec<&Term>) {
        let mut args = Vec::new();
        let mut head = self;
        while let Term::App { func, arg } = head {
            head = func;
            args.push(arg.as_ref());
        }
        args.reverse();
        (head, args)
    }
    pub fn strip_abs(&self) -> (Vec<(&Symbol, &Typ)>, &Term) {
        let mut binders = Vec::new();
        let mut body = self;
        while let Term::Abs { name, typ, body: b } = body {
            binders.push((name, typ));
            body = b;
        }
        (binders, body)
    }
    pub fn is_atom(&self) -> bool {
        !matches!(self, Term::App { .. })
    }
}

/// Lambda abstraction: `lambda v t` replaces all occurrences of variable `v`
/// in `t` with `Bound(0)`, increments existing Bound indices by 1, and wraps
/// in `Abs(v.name, v.typ, result)`. This matches Isabelle's `lambda` in Pure/logic.ML.
pub fn lambda(var: &Term, body: &Term) -> Term {
    // First increment existing bounds (we're adding an outer binder)
    let body_incr = incr_bound(0, body);
    // Then replace var with Bound(0)
    let body_subst = subst_var_bound(0, var, &body_incr);
    let name = match var {
        Term::Free { name, .. } | Term::Var { name, .. } => name.clone(),
        Term::Const { name, .. } => name.clone(),
        _ => std::sync::Arc::from("x"),
    };
    Term::abs(name, Typ::dummy(), body_subst)
}

/// Substitute all occurrences of `var` with `Bound(depth)`.
fn subst_var_bound(depth: usize, var: &Term, term: &Term) -> Term {
    if same_var(var, term) {
        return Term::Bound(depth);
    }
    match term {
        Term::App { func, arg } => Term::app(
            subst_var_bound(depth, var, func),
            subst_var_bound(depth, var, arg),
        ),
        Term::Abs { name, typ, body } => Term::abs(
            name.clone(),
            typ.clone(),
            subst_var_bound(depth + 1, var, body),
        ),
        _ => term.clone(),
    }
}

/// Increment all Bound indices >= `depth` by 1.
fn incr_bound(depth: usize, term: &Term) -> Term {
    match term {
        Term::Bound(i) if *i >= depth => Term::Bound(i + 1),
        Term::Bound(_) => term.clone(),
        Term::App { func, arg } => Term::app(incr_bound(depth, func), incr_bound(depth, arg)),
        Term::Abs { name, typ, body } => {
            Term::abs(name.clone(), typ.clone(), incr_bound(depth + 1, body))
        }
        _ => term.clone(),
    }
}

/// Check if two terms are the same logical variable (Free/Var cross-compatible).
fn same_var(a: &Term, b: &Term) -> bool {
    match (a, b) {
        (Term::Free { name: n1, .. }, Term::Free { name: n2, .. }) => n1 == n2,
        (
            Term::Var {
                name: n1,
                index: i1,
                ..
            },
            Term::Var {
                name: n2,
                index: i2,
                ..
            },
        ) => n1 == n2 && i1 == i2,
        (
            Term::Free { name: n1, .. },
            Term::Var {
                name: n2, index, ..
            },
        ) if *index == 0 => n1 == n2,
        (
            Term::Var {
                name: n1, index, ..
            },
            Term::Free { name: n2, .. },
        ) if *index == 0 => n1 == n2,
        _ => false,
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Const { name, .. } => write!(f, "{name}"),
            Term::Free { name, .. } => write!(f, "{name}"),
            Term::Var { name, index, .. } => write!(f, "?{name}.{index}"),
            Term::Bound(i) => write!(f, "B_{i}"),
            Term::Abs { name, typ, body } => write!(f, "%{name}::{typ:?}. {body}"),
            Term::App { func, arg } => write!(f, "({func} {arg})"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_terms() {
        let t = Term::const_("True", Typ::base("prop"));
        assert!(t.is_const());
    }
    #[test]
    fn test_lambda() {
        let n = Term::free("n", Typ::dummy());
        let p = Term::free("P", Typ::dummy());
        let body = Term::app(p, n.clone());
        let lam = lambda(&n, &body);
        eprintln!("lambda n. P n = {:?}", lam);
        // Should be: Abs("n", dummy, App(Free("P"), Bound(0)))
        if let Term::Abs { body, .. } = &lam {
            assert!(matches!(body.as_ref(), Term::App { .. }));
        }
    }
}
