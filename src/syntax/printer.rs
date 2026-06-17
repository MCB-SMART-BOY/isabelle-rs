//! Pretty printer — format terms as human-readable strings.
//!
//! Corresponds to `src/Pure/Syntax/printer.ML`.
//!
//! ## Supported notations
//!
//! - Infix operators: `+`, `-`, `*`, `/`, `=`, `==>`, `∧`, `∨`, `⟹`
//! - Binders: `∀x. P`, `∃x. P`, `λx. t`
//! - Function application: `f x y`
//! - Parenthesized grouping for precedence

use crate::core::term::Term;

/// Format a term as a human-readable string.
pub fn print_term(term: &Term) -> String {
    let mut buf = String::new();
    print_term_to(term, Precedence::Top, &mut buf);
    buf
}

/// Precedence levels for operator grouping.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Precedence {
    /// Top-level (no wrapping needed)
    Top = 0,
    /// Implication: `==>`
    Implication = 10,
    /// Disjunction / conjunction: `∨`, `∧`
    LogicBin = 20,
    /// Equality / ordering: `=`, `<`, `≤`
    Relation = 30,
    /// Addition / subtraction: `+`, `-`
    Additive = 40,
    /// Multiplication / division: `*`, `/`
    Multiplicative = 50,
    /// Function application
    Application = 60,
    /// Atomic: variable, constant, parenthesized
    Atomic = 100,
}

/// Known infix operators and their precedences.
struct InfixInfo {
    names: &'static [&'static str],
    symbol: &'static str,
    prec: Precedence,
}

const INFIX_TABLE: &[InfixInfo] = &[
    // Logic
    InfixInfo { names: &["Pure.imp", "HOL.implies"], symbol: "==>", prec: Precedence::Implication },
    InfixInfo { names: &["HOL.conj", "HOL.and"], symbol: "∧", prec: Precedence::LogicBin },
    InfixInfo { names: &["HOL.disj", "HOL.or"], symbol: "∨", prec: Precedence::LogicBin },
    InfixInfo { names: &["HOL.imp"], symbol: "⟶", prec: Precedence::Implication },
    InfixInfo {
        names: &["HOL.iff", "HOL.eq_reflection"], symbol: "⟷", prec: Precedence::Relation
    },
    // Equality / ordering
    InfixInfo { names: &["HOL.eq", "Pure.eq"], symbol: "=", prec: Precedence::Relation },
    InfixInfo { names: &["HOL.less", "HOL.ordLess"], symbol: "<", prec: Precedence::Relation },
    InfixInfo {
        names: &["HOL.lessEq", "HOL.ordLessEq"], symbol: "≤", prec: Precedence::Relation
    },
    InfixInfo {
        names: &["HOL.greater", "HOL.ordGreater"],
        symbol: ">",
        prec: Precedence::Relation,
    },
    InfixInfo {
        names: &["HOL.greaterEq", "HOL.ordGreaterEq"],
        symbol: "≥",
        prec: Precedence::Relation,
    },
    // Arithmetic
    InfixInfo {
        names: &["HOL.plus", "Groups.plus", "HOL.groups_plus"],
        symbol: "+",
        prec: Precedence::Additive,
    },
    InfixInfo {
        names: &["HOL.minus", "Groups.minus", "HOL.groups_minus"],
        symbol: "-",
        prec: Precedence::Additive,
    },
    InfixInfo {
        names: &["HOL.times", "Groups.times"],
        symbol: "*",
        prec: Precedence::Multiplicative,
    },
    InfixInfo {
        names: &["HOL.divide", "HOL.inverse_divide"],
        symbol: "/",
        prec: Precedence::Multiplicative,
    },
    // Set operations
    InfixInfo { names: &["HOL.member", "Set.member"], symbol: "∈", prec: Precedence::Relation },
    InfixInfo { names: &["HOL.subset", "Set.subset"], symbol: "⊆", prec: Precedence::Relation },
    InfixInfo { names: &["HOL.union", "Lattices.sup"], symbol: "∪", prec: Precedence::Additive },
    InfixInfo {
        names: &["HOL.inter", "Lattices.inf"],
        symbol: "∩",
        prec: Precedence::Multiplicative,
    },
    // Lists
    InfixInfo { names: &["List.append", "HOL.append"], symbol: "@", prec: Precedence::Additive },
    InfixInfo { names: &["HOL.cons", "List.cons"], symbol: "#", prec: Precedence::Additive },
    // Function composition
    InfixInfo { names: &["Fun.comp", "HOL.comp"], symbol: "∘", prec: Precedence::Multiplicative },
];

/// Known binder constants.
const BINDER_TABLE: &[(&str, &str)] =
    &[("Pure.all", "∀"), ("HOL.All", "∀"), ("HOL.Ex", "∃"), ("HOL.Ex1", "∃!")];

/// Known unary/prefix operators.
const PREFIX_TABLE: &[(&str, &str)] =
    &[("HOL.Not", "¬"), ("HOL.uminus", "-"), ("Groups.uminus", "-")];

fn print_term_to(term: &Term, outer_prec: Precedence, buf: &mut String) {
    match term {
        // ── Binders ──
        Term::Abs { name, body, .. } => {
            // Check if the abstraction body has a known binder pattern
            if let Term::App { func, arg } = body.as_ref()
                && let Term::Const { name: cname, .. } = func.as_ref()
            {
                for (binder_name, binder_sym) in BINDER_TABLE {
                    if cname.as_ref() == *binder_name {
                        // ∀x. body
                        let need_paren = outer_prec < Precedence::Atomic;
                        if need_paren {
                            buf.push('(');
                        }
                        buf.push_str(binder_sym);
                        buf.push_str(name);
                        buf.push_str(". ");
                        print_term_to(arg, Precedence::Top, buf);
                        if need_paren {
                            buf.push(')');
                        }
                        return;
                    }
                }
            }
            // Plain lambda
            buf.push('λ');
            buf.push_str(name);
            buf.push_str(". ");
            print_term_to(body, Precedence::Top, buf);
        },

        // ── Application (potential infix / prefix) ──
        Term::App { func, arg } => {
            // Check for: App(App(Const(name), left), right) — infix operator
            if let Term::App { func: inner, arg: left } = func.as_ref()
                && let Term::Const { name, .. } = inner.as_ref()
            {
                for info in INFIX_TABLE {
                    if info.names.contains(&name.as_ref()) {
                        let need_paren = outer_prec > info.prec;
                        if need_paren {
                            buf.push('(');
                        }
                        print_term_to(left, info.prec, buf);
                        buf.push(' ');
                        buf.push_str(info.symbol);
                        buf.push(' ');
                        print_term_to(arg, info.prec, buf);
                        if need_paren {
                            buf.push(')');
                        }
                        return;
                    }
                }
            }

            // Check for: App(Const(name), arg) — prefix operator
            if let Term::Const { name, .. } = func.as_ref() {
                for (prefix_name, prefix_sym) in PREFIX_TABLE {
                    if name.as_ref() == *prefix_name {
                        buf.push_str(prefix_sym);
                        print_term_to(arg, Precedence::Atomic, buf);
                        return;
                    }
                }
            }

            // Simple function application: f x
            let need_paren = outer_prec > Precedence::Application;
            if need_paren {
                buf.push('(');
            }
            print_term_to(func, Precedence::Application, buf);
            buf.push(' ');
            print_term_to(arg, Precedence::Atomic, buf);
            if need_paren {
                buf.push(')');
            }
        },

        // ── Constants ──
        Term::Const { name, .. } => {
            let short = short_name(name);
            buf.push_str(&short);
        },

        // ── Free variables ──
        Term::Free { name, .. } => {
            buf.push_str(name);
        },

        // ── Schematic variables ──
        Term::Var { name, index, .. } => {
            buf.push('?');
            buf.push_str(name);
            if *index > 0 {
                use std::fmt::Write;
                write!(buf, ".{index}").unwrap();
            }
        },

        // ── Bound variables ──
        Term::Bound(idx) => {
            buf.push('B');
            use std::fmt::Write;
            write!(buf, "{idx}").unwrap();
        },
    }
}

/// Get the short (unqualified) name for a constant.
fn short_name(name: &str) -> String {
    if let Some(pos) = name.rfind('.') { name[pos + 1..].to_string() } else { name.to_string() }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{term::Term, types::Typ};

    fn c(name: &str) -> Term {
        Term::const_(name, Typ::dummy())
    }
    fn f(name: &str) -> Term {
        Term::free(name, Typ::dummy())
    }
    fn lam(x: &str, body: Term) -> Term {
        Term::abs(x, Typ::dummy(), body)
    }

    #[test]
    fn test_print_constant() {
        assert_eq!(print_term(&c("True")), "True");
        assert_eq!(print_term(&c("HOL.eq")), "eq");
    }

    #[test]
    fn test_print_variable() {
        assert_eq!(print_term(&f("x")), "x");
    }

    #[test]
    fn test_print_application() {
        let app = Term::app(f("P"), f("x"));
        assert_eq!(print_term(&app), "P x");
    }

    #[test]
    fn test_print_infix_equality() {
        // a = b
        let eq = Term::app(Term::app(c("HOL.eq"), f("a")), f("b"));
        assert_eq!(print_term(&eq), "a = b");
    }

    #[test]
    fn test_print_infix_arithmetic() {
        // a + b
        let plus = Term::app(Term::app(c("HOL.plus"), f("a")), f("b"));
        assert_eq!(print_term(&plus), "a + b");

        // a * b
        let times = Term::app(Term::app(c("HOL.times"), f("a")), f("b"));
        assert_eq!(print_term(&times), "a * b");
    }

    #[test]
    fn test_print_precedence() {
        // a + b = c  (should be (a + b) = c — actually = binds tighter since Relation > Additive)
        // Let's test: a = b + c
        let plus = Term::app(Term::app(c("HOL.plus"), f("b")), f("c"));
        let eq = Term::app(Term::app(c("HOL.eq"), f("a")), plus);
        let result = print_term(&eq);
        // = has prec 30, + has prec 40. Since outer(=) prec(30) < inner(+) prec(40),
        // the inner + needs no paren (it binds tighter). Result: a = b + c
        assert_eq!(result, "a = b + c");
    }

    #[test]
    fn test_print_lambda() {
        // λx. x
        let t = lam("x", Term::bound(0));
        assert_eq!(print_term(&t), "λx. B0");
    }

    #[test]
    fn test_print_forall() {
        // ∀x. P x
        let px = Term::app(f("P"), Term::bound(0));
        let all = lam("x", Term::app(c("Pure.all"), px));
        let result = print_term(&all);
        assert!(result.contains("∀x"), "Expected ∀x in: {result}");
    }

    #[test]
    fn test_print_negation() {
        // ¬ P
        let neg = Term::app(c("HOL.Not"), f("P"));
        assert_eq!(print_term(&neg), "¬P");
    }

    #[test]
    fn test_print_nested() {
        // (a + b) * c
        let plus = Term::app(Term::app(c("HOL.plus"), f("a")), f("b"));
        let times = Term::app(Term::app(c("HOL.times"), plus), f("c"));
        let result = print_term(&times);
        // * has prec 50, + has prec 40. Since outer(*) prec(50) > inner(+) prec(40),
        // the inner + needs parens. Result: (a + b) * c
        assert_eq!(result, "(a + b) * c");
    }

    #[test]
    fn test_print_implication() {
        // A ==> B
        let imp = Term::app(Term::app(c("Pure.imp"), f("A")), f("B"));
        assert_eq!(print_term(&imp), "A ==> B");
    }
}
