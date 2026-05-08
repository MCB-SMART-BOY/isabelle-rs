//! Isabelle lambda terms: the core data structure of the prover.
//! Corresponds to src/Pure/term.ML.
use super::types::{Typ, Symbol};
use std::fmt;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Const { name: Symbol, typ: Typ },
    Free  { name: Symbol, typ: Typ },
    Var   { name: Symbol, index: usize, typ: Typ },
    Bound(usize),
    Abs   { name: Symbol, typ: Typ, body: Box<Term> },
    App   { func: Box<Term>, arg: Box<Term> },
}

impl Term {
    pub fn const_(name: impl Into<Symbol>, typ: Typ) -> Self { Term::Const { name: name.into(), typ } }
    pub fn free(name: impl Into<Symbol>, typ: Typ) -> Self { Term::Free { name: name.into(), typ } }
    pub fn var(name: impl Into<Symbol>, index: usize, typ: Typ) -> Self { Term::Var { name: name.into(), index, typ } }
    pub fn bound(index: usize) -> Self { Term::Bound(index) }
    pub fn abs(name: impl Into<Symbol>, typ: Typ, body: Term) -> Self { Term::Abs { name: name.into(), typ, body: Box::new(body) } }
    pub fn app(func: Term, arg: Term) -> Self { Term::App { func: Box::new(func), arg: Box::new(arg) } }
    pub fn apps(func: Term, args: impl IntoIterator<Item = Term>) -> Self { args.into_iter().fold(func, |acc, arg| Term::app(acc, arg)) }
    pub fn is_const(&self) -> bool { matches!(self, Term::Const { .. }) }
    pub fn is_free(&self) -> bool  { matches!(self, Term::Free { .. }) }
    pub fn is_var(&self) -> bool   { matches!(self, Term::Var { .. }) }
    pub fn is_bound(&self) -> bool { matches!(self, Term::Bound(_)) }
    pub fn is_abs(&self) -> bool   { matches!(self, Term::Abs { .. }) }
    pub fn is_app(&self) -> bool   { matches!(self, Term::App { .. }) }
    pub fn strip_comb(&self) -> (&Term, Vec<&Term>) {
        let mut args = Vec::new(); let mut head = self;
        while let Term::App { func, arg } = head { head = func; args.push(arg.as_ref()); }
        args.reverse(); (head, args)
    }
    pub fn strip_abs(&self) -> (Vec<(&Symbol, &Typ)>, &Term) {
        let mut binders = Vec::new(); let mut body = self;
        while let Term::Abs { name, typ, body: b } = body { binders.push((name, typ)); body = b; }
        (binders, body)
    }
    pub fn is_atom(&self) -> bool { !matches!(self, Term::App { .. }) }
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
    #[test] fn test_terms() { let t = Term::const_("True", Typ::base("prop")); assert!(t.is_const()); }
}
