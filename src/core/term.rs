//! Isabelle lambda terms: the core data structure of the prover.
//! Corresponds to src/Pure/term.ML.
use std::fmt;

use super::types::{Symbol, Typ};

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Const { name: Symbol, typ: Typ },
    Free { name: Symbol, typ: Typ },
    Var { name: Symbol, index: usize, typ: Typ },
    Bound(usize),
    Abs { name: Symbol, typ: Typ, body: Box<Term> },
    App { func: Box<Term>, arg: Box<Term> },
}

impl Term {
    pub fn const_(name: impl Into<Symbol>, typ: Typ) -> Self {
        Term::Const { name: name.into(), typ }
    }
    pub fn free(name: impl Into<Symbol>, typ: Typ) -> Self {
        Term::Free { name: name.into(), typ }
    }
    pub fn var(name: impl Into<Symbol>, index: usize, typ: Typ) -> Self {
        Term::Var { name: name.into(), index, typ }
    }
    pub fn bound(index: usize) -> Self {
        Term::Bound(index)
    }
    pub fn abs(name: impl Into<Symbol>, typ: Typ, body: Term) -> Self {
        Term::Abs { name: name.into(), typ, body: Box::new(body) }
    }
    pub fn app(func: Term, arg: Term) -> Self {
        Term::App { func: Box::new(func), arg: Box::new(arg) }
    }
    pub fn apps(func: Term, args: impl IntoIterator<Item = Term>) -> Self {
        args.into_iter().fold(func, Term::app)
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

    /// Annotate dummy types in this term with known types from the TypeEnv.
    /// Walks the entire term tree and replaces `Typ::dummy()` in Const and Free
    /// nodes with the type from the environment.
    /// Uses iterative traversal to avoid stack overflow on deeply nested terms.
    /// Returns true if any types were changed.
    pub fn type_annotate(&mut self, env: &super::types::TypeEnv) -> bool {
        let mut changed = false;
        let mut stack: Vec<&mut Term> = vec![self];
        while let Some(term) = stack.pop() {
            match term {
                Term::Const { name, typ } => {
                    if typ.is_dummy()
                        && let Some(known) = env.const_type(name.as_ref())
                    {
                        *typ = known.clone();
                        changed = true;
                    }
                },
                Term::Free { name, typ } => {
                    if typ.is_dummy() {
                        if let Some(known) = env.const_type(name.as_ref()) {
                            *typ = known.clone();
                            changed = true;
                        } else if let Some(known) = env.frees.get(name.as_ref()) {
                            *typ = known.clone();
                            changed = true;
                        }
                    }
                },
                Term::Var { typ, .. } => {
                    if typ.is_dummy() {
                        typ.annotate_from_env(env);
                    }
                },
                Term::Abs { name: _, typ, body } => {
                    if typ.is_dummy() {
                        typ.annotate_from_env(env);
                    }
                    stack.push(body);
                },
                Term::App { func, arg } => {
                    stack.push(arg);
                    stack.push(func);
                },
                Term::Bound(_) => {},
            }
        }
        changed
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
/// Iterative implementation to avoid stack overflow on deeply nested terms.
fn subst_var_bound(depth: usize, var: &Term, term: &Term) -> Term {
    enum Frame {
        Process(usize, Term),
        BuildApp,
        BuildAbs(Symbol, Typ),
    }

    let var = var.clone();
    let mut stack: Vec<Frame> = vec![Frame::Process(depth, term.clone())];
    let mut results: Vec<Term> = Vec::new();

    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Process(d, t) => {
                if same_var(&var, &t) {
                    results.push(Term::Bound(d));
                    continue;
                }
                match &t {
                    Term::App { func, arg } => {
                        stack.push(Frame::BuildApp);
                        stack.push(Frame::Process(d, arg.as_ref().clone()));
                        stack.push(Frame::Process(d, func.as_ref().clone()));
                    },
                    Term::Abs { name, typ, body } => {
                        stack.push(Frame::BuildAbs(name.clone(), typ.clone()));
                        stack.push(Frame::Process(d + 1, body.as_ref().clone()));
                    },
                    other => results.push(other.clone()),
                }
            },
            Frame::BuildApp => {
                let arg = results.pop().unwrap_or_else(|| Term::bound(0));
                let func = results.pop().unwrap_or_else(|| Term::bound(0));
                results.push(Term::app(func, arg));
            },
            Frame::BuildAbs(name, typ) => {
                let body = results.pop().unwrap_or_else(|| Term::bound(0));
                results.push(Term::abs(name, typ, body));
            },
        }
    }
    results.pop().unwrap_or_else(|| term.clone())
}

/// Increment all Bound indices >= `depth` by 1.
/// Iterative implementation to avoid stack overflow on deeply nested terms.
fn incr_bound(depth: usize, term: &Term) -> Term {
    enum Frame {
        Process(usize, Term),
        BuildApp,
        BuildAbs(Symbol, Typ),
    }

    let mut stack: Vec<Frame> = vec![Frame::Process(depth, term.clone())];
    let mut results: Vec<Term> = Vec::new();

    while let Some(frame) = stack.pop() {
        match frame {
            Frame::Process(d, t) => match &t {
                Term::Bound(i) if *i >= d => results.push(Term::Bound(i + 1)),
                Term::Bound(_) => results.push(t.clone()),
                Term::App { func, arg } => {
                    stack.push(Frame::BuildApp);
                    stack.push(Frame::Process(d, arg.as_ref().clone()));
                    stack.push(Frame::Process(d, func.as_ref().clone()));
                },
                Term::Abs { name, typ, body } => {
                    stack.push(Frame::BuildAbs(name.clone(), typ.clone()));
                    stack.push(Frame::Process(d + 1, body.as_ref().clone()));
                },
                other => results.push(other.clone()),
            },
            Frame::BuildApp => {
                let arg = results.pop().unwrap_or_else(|| Term::bound(0));
                let func = results.pop().unwrap_or_else(|| Term::bound(0));
                results.push(Term::app(func, arg));
            },
            Frame::BuildAbs(name, typ) => {
                let body = results.pop().unwrap_or_else(|| Term::bound(0));
                results.push(Term::abs(name, typ, body));
            },
        }
    }
    results.pop().unwrap_or_else(|| term.clone())
}

/// Check if two terms are the same logical variable (Free/Var cross-compatible).
fn same_var(a: &Term, b: &Term) -> bool {
    match (a, b) {
        (Term::Free { name: n1, .. }, Term::Free { name: n2, .. }) => n1 == n2,
        (Term::Var { name: n1, index: i1, .. }, Term::Var { name: n2, index: i2, .. }) => {
            n1 == n2 && i1 == i2
        },
        (Term::Free { name: n1, .. }, Term::Var { name: n2, index, .. }) if *index == 0 => n1 == n2,
        (Term::Var { name: n1, index, .. }, Term::Free { name: n2, .. }) if *index == 0 => n1 == n2,
        _ => false,
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Delegate to iterative Display — avoids stack overflow on deep terms
        write!(f, "{self}")
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        /// Iterative term formatter — avoids stack overflow on deeply nested terms.
        /// Uses an explicit stack of formatting frames instead of recursive write! calls.
        fn fmt_iter(term: &Term, f: &mut fmt::Formatter<'_>, depth_limit: usize) -> fmt::Result {
            enum FmtFrame {
                Term(Term, usize),
                Text(String),
            }
            let mut stack: Vec<FmtFrame> = vec![FmtFrame::Term(term.clone(), 0)];
            while let Some(frame) = stack.pop() {
                match frame {
                    FmtFrame::Text(s) => write!(f, "{s}")?,
                    FmtFrame::Term(t, depth) => {
                        if depth > depth_limit {
                            write!(f, "<...>")?;
                            continue;
                        }
                        match &t {
                            Term::Const { name, .. } => write!(f, "{name}")?,
                            Term::Free { name, .. } => write!(f, "{name}")?,
                            Term::Var { name, index, .. } => write!(f, "?{name}.{index}")?,
                            Term::Bound(i) => write!(f, "B_{i}")?,
                            Term::Abs { name, typ, body } => {
                                // Push in reverse order for correct output
                                stack.push(FmtFrame::Term((**body).clone(), depth + 1));
                                stack.push(FmtFrame::Text(format!("%{name}::{typ:?}. ")));
                            },
                            Term::App { func, arg } => {
                                stack.push(FmtFrame::Text(")".to_string()));
                                stack.push(FmtFrame::Term((**arg).clone(), depth + 1));
                                stack.push(FmtFrame::Text(" ".to_string()));
                                stack.push(FmtFrame::Term((**func).clone(), depth + 1));
                                stack.push(FmtFrame::Text("(".to_string()));
                            },
                        }
                    },
                }
            }
            Ok(())
        }
        fmt_iter(self, f, 64)
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
