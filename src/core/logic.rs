//! Pure meta-logic: the minimal logical framework.
use super::term::{Term, lambda};
use super::types::{Symbol, Typ};

pub struct Pure;
impl Pure {
    pub fn prop_type() -> Typ {
        Typ::base("prop")
    }
    pub fn imp_const() -> Term {
        Term::const_(
            "Pure.imp",
            Typ::arrow(
                Typ::base("prop"),
                Typ::arrow(Typ::base("prop"), Typ::base("prop")),
            ),
        )
    }
    pub fn mk_implies(a: Term, b: Term) -> Term {
        Term::app(Term::app(Self::imp_const(), a), b)
    }
    pub fn dest_implies(term: &Term) -> Option<(&Term, &Term)> {
        match term {
            Term::App { func, arg } => match func.as_ref() {
                Term::App {
                    func: inner,
                    arg: a,
                } => match inner.as_ref() {
                    Term::Const { name, .. } if name.as_ref() == "Pure.imp" => {
                        Some((a.as_ref(), arg.as_ref()))
                    }
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }
    pub fn mk_all(name: &str, typ: Typ, body: Term) -> Term {
        let v = Term::free(name, typ.clone());
        let all_const = Term::const_(
            "Pure.all",
            Typ::arrow(Typ::arrow(typ, Typ::base("prop")), Typ::base("prop")),
        );
        Term::app(all_const, lambda(&v, &body))
    }
    pub fn dest_all(term: &Term) -> Option<((&Symbol, &Typ), &Term)> {
        match term {
            Term::App { func, arg } => match func.as_ref() {
                Term::Const { name, .. } if name.as_ref() == "Pure.all" => match arg.as_ref() {
                    Term::Abs { name, typ, body } => Some(((name, typ), body)),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }
    pub fn mk_equals(typ: Typ, t: Term, u: Term) -> Term {
        Term::app(
            Term::app(
                Term::const_(
                    "Pure.eq",
                    Typ::arrow(typ.clone(), Typ::arrow(typ, Typ::base("prop"))),
                ),
                t,
            ),
            u,
        )
    }
    pub fn dest_equals(term: &Term) -> Option<(&Term, &Term)> {
        match term {
            Term::App { func, arg } => match func.as_ref() {
                Term::App {
                    func: inner,
                    arg: t,
                } => match inner.as_ref() {
                    Term::Const { name, .. }
                        if name.as_ref() == "Pure.eq"
                            || name.as_ref() == "HOL.eq"
                            || name.as_ref().ends_with(".eq") =>
                    {
                        Some((t.as_ref(), arg.as_ref()))
                    }
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }
    pub fn strip_imp_prems(term: &Term) -> (Vec<&Term>, &Term) {
        let mut prems = Vec::new();
        let mut body = term;
        while let Some((a, b)) = Self::dest_implies(body) {
            prems.push(a);
            body = b;
        }
        (prems, body)
    }
    pub fn count_prems(term: &Term) -> usize {
        Self::strip_imp_prems(term).0.len()
    }

    /// Get the i-th premise (0-indexed).
    pub fn nth_premise(term: &Term, i: usize) -> Option<&Term> {
        let (prems, _) = Self::strip_imp_prems(term);
        prems.get(i).copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_implies() {
        let a = Term::const_("A", Typ::base("prop"));
        let b = Term::const_("B", Typ::base("prop"));
        let imp = Pure::mk_implies(a.clone(), b.clone());
        let (x, y) = Pure::dest_implies(&imp).unwrap();
        assert_eq!(x, &a);
        assert_eq!(y, &b);
    }
    #[test]
    fn test_equals() {
        let t = Term::free("t", Typ::base("nat"));
        let u = Term::free("u", Typ::base("nat"));
        let eq = Pure::mk_equals(Typ::base("nat"), t.clone(), u.clone());
        let (x, y) = Pure::dest_equals(&eq).unwrap();
        assert_eq!(x, &t);
        assert_eq!(y, &u);
    }
}
