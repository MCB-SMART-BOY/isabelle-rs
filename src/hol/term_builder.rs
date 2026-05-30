//! Helper: build simple Isabelle terms without calling the parser.
//! Used by BNF/Ctr_Sugar/Lfp generators to avoid parser recursion.

use crate::core::term::Term;
use crate::core::types::Typ;

/// Build an equality term: `lhs = rhs` (both sides must be valid Term strings or Term values).
/// For simple constants/free vars, use `mk_eq_const(lhs_name, rhs_name)`.
pub fn mk_eq(lhs: Term, rhs: Term) -> Term {
    let eq_typ = Typ::base("prop");
    Term::app(
        Term::app(
            Term::const_("HOL.eq", Typ::arrow(Typ::dummy(), Typ::arrow(Typ::dummy(), eq_typ))),
            lhs,
        ),
        rhs,
    )
}

/// Build a simple constant term.
pub fn mk_const(name: &str) -> Term {
    Term::const_(name, Typ::dummy())
}

/// Build a simple free variable.
pub fn mk_free(name: &str) -> Term {
    Term::free(name, Typ::dummy())
}

/// Build an application: `f x`
pub fn mk_app(f: Term, x: Term) -> Term {
    Term::app(f, x)
}

/// Build a multi-arg application: `f x1 x2 ... xn`
pub fn mk_apps(f: Term, args: Vec<Term>) -> Term {
    args.into_iter().fold(f, |acc, arg| Term::app(acc, arg))
}

/// Build "True" constant.
pub fn mk_true() -> Term {
    Term::const_("True", Typ::base("prop"))
}
