//! Term ordering functions — ordering for terms, types, sorts, and variable names.
//!
//! Corresponds to `src/Pure/term_ord.ML`.
//!
//! Isabelle uses several different orderings depending on context:
//!
//! - **fast_term_ord**: syntactic ordering (structure first, then atoms, then types) Optimized for
//!   speed with pointer equality shortcuts. Used in discrimination nets, table lookups, and any
//!   context where structural equality is needed.
//!
//! - **term_ord**: size-based lexicographic ordering. Well-founded total order. Used for sorting
//!   theorems and stable term presentation.
//!
//! - **typ_ord**: type ordering (constructor nr → name → arguments)
//!
//! - **indexname_ord**: variable ordering (name, index)
//!
//! ## Key principles
//!
//! 1. Pointer equality short-circuit: if `std::ptr::eq(a, b)`, return `Equal`
//! 2. Constructor number ordering: `Const < Free < Var < Bound < Abs < App`
//! 3. Lexicographic on subterms: compare head first, then arguments
//! 4. Well-founded total ordering for `term_ord` via size comparison

use std::cmp::Ordering;

use super::{
    term::Term,
    types::{Sort, Typ},
};

// =========================================================================
// Variable index ordering
// =========================================================================

/// Fast ordering on `(name, index)` pairs.
/// Compares index first for efficiency (fewer string comparisons),
/// then falls back to name comparison.
pub fn fast_indexname_ord(a: (&str, usize), b: (&str, usize)) -> Ordering {
    match a.1.cmp(&b.1) {
        Ordering::Equal => a.0.cmp(b.0),
        ord => ord,
    }
}

/// Full indexname ordering (index first).
pub fn indexname_ord(a: (&str, usize), b: (&str, usize)) -> Ordering {
    fast_indexname_ord(a, b)
}

// =========================================================================
// Sort ordering
// =========================================================================

/// Dictionary ordering on sorts (sets of classes).
pub fn sort_ord(a: &Sort, b: &Sort) -> Ordering {
    let ac: Vec<&str> = a.iter().map(|c| c.as_ref()).collect();
    let bc: Vec<&str> = b.iter().map(|c| c.as_ref()).collect();
    ac.cmp(&bc)
}

// =========================================================================
// Type ordering
// =========================================================================

/// Constructor number for types: TVar(0) < TFree(1) < Type(2)
fn type_cons_nr(typ: &Typ) -> u8 {
    match typ {
        Typ::TVar { .. } => 0,
        Typ::TFree { .. } => 1,
        Typ::Type { .. } => 2,
    }
}

/// Full type ordering.
/// Order: constructor number → name → arguments
pub fn typ_ord(a: &Typ, b: &Typ) -> Ordering {
    // Pointer equality shortcut
    if std::ptr::eq(a, b) {
        return Ordering::Equal;
    }

    match (a, b) {
        (Typ::Type { name: na, args: as_a }, Typ::Type { name: nb, args: bs_b }) => {
            match na.as_ref().cmp(nb.as_ref()) {
                Ordering::Equal => {
                    // Dictionary ordering on arguments
                    let n = usize::min(as_a.len(), bs_b.len());
                    for i in 0..n {
                        let ord = typ_ord(&as_a[i], &bs_b[i]);
                        if ord != Ordering::Equal {
                            return ord;
                        }
                    }
                    as_a.len().cmp(&bs_b.len())
                },
                ord => ord,
            }
        },
        (Typ::TFree { name: na, sort: sa }, Typ::TFree { name: nb, sort: sb }) => {
            match na.as_ref().cmp(nb.as_ref()) {
                Ordering::Equal => sort_ord(sa, sb),
                ord => ord,
            }
        },
        (
            Typ::TVar { name: na, index: ia, sort: sa },
            Typ::TVar { name: nb, index: ib, sort: sb },
        ) => match fast_indexname_ord((na.as_ref(), *ia), (nb.as_ref(), *ib)) {
            Ordering::Equal => sort_ord(sa, sb),
            ord => ord,
        },
        (a, b) => type_cons_nr(a).cmp(&type_cons_nr(b)),
    }
}

// =========================================================================
// Fast term ordering — for discrimination nets
// =========================================================================

/// Constructor number for terms.
/// Const(0) < Free(1) < Var(2) < Bound(3) < Abs(4) < App(5)
fn term_cons_nr(t: &Term) -> u8 {
    match t {
        Term::Const { .. } => 0,
        Term::Free { .. } => 1,
        Term::Var { .. } => 2,
        Term::Bound(_) => 3,
        Term::Abs { .. } => 4,
        Term::App { .. } => 5,
    }
}

/// Structural ordering: ignores names, compares only structure.
fn struct_ord(a: &Term, b: &Term) -> Ordering {
    if std::ptr::eq(a, b) {
        return Ordering::Equal;
    }
    match (a, b) {
        (Term::Abs { body: ba, .. }, Term::Abs { body: bb, .. }) => struct_ord(ba, bb),
        (Term::App { func: fa, arg: aa }, Term::App { func: fb, arg: ab }) => {
            match struct_ord(fa, fb) {
                Ordering::Equal => struct_ord(aa, ab),
                ord => ord,
            }
        },
        (a, b) => term_cons_nr(a).cmp(&term_cons_nr(b)),
    }
}

/// Atom ordering: compare names/variable indices.
fn atoms_ord(a: &Term, b: &Term) -> Ordering {
    if std::ptr::eq(a, b) {
        return Ordering::Equal;
    }
    match (a, b) {
        (Term::Abs { body: ba, .. }, Term::Abs { body: bb, .. }) => atoms_ord(ba, bb),
        (Term::App { func: fa, arg: aa }, Term::App { func: fb, arg: ab }) => {
            match atoms_ord(fa, fb) {
                Ordering::Equal => atoms_ord(aa, ab),
                ord => ord,
            }
        },
        (Term::Const { name: na, .. }, Term::Const { name: nb, .. }) => {
            na.as_ref().cmp(nb.as_ref())
        },
        (Term::Free { name: na, .. }, Term::Free { name: nb, .. }) => na.as_ref().cmp(nb.as_ref()),
        (Term::Var { name: na, index: ia, .. }, Term::Var { name: nb, index: ib, .. }) => {
            fast_indexname_ord((na.as_ref(), *ia), (nb.as_ref(), *ib))
        },
        (Term::Bound(ia), Term::Bound(ib)) => ia.cmp(ib),
        _ => Ordering::Equal,
    }
}

/// Type comparison on terms: compare embedded types.
fn types_ord(a: &Term, b: &Term) -> Ordering {
    if std::ptr::eq(a, b) {
        return Ordering::Equal;
    }
    match (a, b) {
        (Term::Abs { typ: ta, body: ba, .. }, Term::Abs { typ: tb, body: bb, .. }) => {
            match typ_ord(ta, tb) {
                Ordering::Equal => types_ord(ba, bb),
                ord => ord,
            }
        },
        (Term::App { func: fa, arg: aa }, Term::App { func: fb, arg: ab }) => {
            match types_ord(fa, fb) {
                Ordering::Equal => types_ord(aa, ab),
                ord => ord,
            }
        },
        (Term::Const { typ: ta, .. }, Term::Const { typ: tb, .. }) => typ_ord(ta, tb),
        (Term::Free { typ: ta, .. }, Term::Free { typ: tb, .. }) => typ_ord(ta, tb),
        (Term::Var { typ: ta, .. }, Term::Var { typ: tb, .. }) => typ_ord(ta, tb),
        _ => Ordering::Equal,
    }
}

/// Fast syntactic term ordering. Used in discrimination nets and table lookups.
///
/// Order: structure → atoms → types
pub fn fast_term_ord(a: &Term, b: &Term) -> Ordering {
    match struct_ord(a, b) {
        Ordering::Equal => match atoms_ord(a, b) {
            Ordering::Equal => types_ord(a, b),
            ord => ord,
        },
        ord => ord,
    }
}

// =========================================================================
// Full term ordering — well-founded total order
// =========================================================================

/// Compute term size (number of nodes in the term tree).
fn term_size(t: &Term) -> usize {
    match t {
        Term::Const { .. } | Term::Free { .. } | Term::Var { .. } | Term::Bound(_) => 1,
        Term::Abs { body, .. } => 1 + term_size(body),
        Term::App { func, arg } => 1 + term_size(func) + term_size(arg),
    }
}

/// Destructure head for ordering: ((name, index), type, kind).
/// Returns (((name, index), type), kind) where kind = 0:Const, 1:Free, 2:Var, 3:Bound, 4:Abs
fn dest_hd(t: &Term) -> ((String, usize), Typ, u8) {
    match t {
        Term::Const { name, typ } => ((name.as_ref().to_string(), 0), typ.clone(), 0),
        Term::Free { name, typ } => ((name.as_ref().to_string(), 0), typ.clone(), 1),
        Term::Var { name, index, typ } => ((name.as_ref().to_string(), *index), typ.clone(), 2),
        Term::Bound(i) => ((String::new(), *i), Typ::dummy(), 3),
        Term::Abs { typ, .. } => ((String::new(), 0), typ.clone(), 4),
        Term::App { .. } => panic!("dest_hd: application"),
    }
}

/// Compute the depth of the head (length of application chain at top level).
fn hd_depth(t: &Term, n: usize) -> (usize, &Term) {
    match t {
        Term::App { func, .. } => hd_depth(func, n + 1),
        _ => (n, t),
    }
}

/// Head ordering: compare heads of terms.
fn hd_ord(a: &Term, b: &Term) -> Ordering {
    let (n_a, a_head) = hd_depth(a, 0);
    let (n_b, b_head) = hd_depth(b, 0);

    // Compare depth first (longer application = larger)
    match n_a.cmp(&n_b) {
        Ordering::Equal => {},
        ord => return ord,
    }

    let ((na, ia), ta, ka) = dest_hd(a_head);
    let ((nb, ib), tb, kb) = dest_hd(b_head);

    match fast_indexname_ord((&na, ia), (&nb, ib)) {
        Ordering::Equal => match typ_ord(&ta, &tb) {
            Ordering::Equal => ka.cmp(&kb),
            ord => ord,
        },
        ord => ord,
    }
}

/// Argument ordering: compare term arguments lexicographically.
fn args_ord(a: &Term, b: &Term) -> Ordering {
    match (a, b) {
        (Term::App { func: fa, arg: aa }, Term::App { func: fb, arg: ab }) => {
            match args_ord(fa, fb) {
                Ordering::Equal => term_ord(aa, ab),
                ord => ord,
            }
        },
        _ => Ordering::Equal,
    }
}

/// Full well-founded term ordering.
///
/// Order:
/// 1. Size (smaller first)
/// 2. Head depth and head ordering (for equal size)
/// 3. Argument lexicographic (for equal heads)
pub fn term_ord(a: &Term, b: &Term) -> Ordering {
    if std::ptr::eq(a, b) {
        return Ordering::Equal;
    }

    match (a, b) {
        (Term::Abs { typ: ta, body: ba, .. }, Term::Abs { typ: tb, body: bb, .. }) => {
            match term_ord(ba, bb) {
                Ordering::Equal => typ_ord(ta, tb),
                ord => ord,
            }
        },
        (a, b) => {
            // Compare sizes first
            let size_a = term_size(a);
            let size_b = term_size(b);
            match size_a.cmp(&size_b) {
                Ordering::Equal => {
                    // Same size: compare head depth, then head, then arguments
                    let (n_a, _) = hd_depth(a, 0);
                    let (n_b, _) = hd_depth(b, 0);
                    match n_a.cmp(&n_b) {
                        Ordering::Equal => match hd_ord(a, b) {
                            Ordering::Equal => args_ord(a, b),
                            ord => ord,
                        },
                        ord => ord,
                    }
                },
                ord => ord,
            }
        },
    }
}

// =========================================================================
// Lexicographic path order (LPO) for term rewriting
// =========================================================================

/// Lexicographic path order with user-defined precedence function.
///
/// `prec` maps a term's head (Const/Free/Var/Bound/Abs) to an integer precedence:
/// - `-1` means unrecognized (treated as a constant with minimal precedence)
/// - `>= 0` gives the precedence (larger = higher precedence)
///
/// See Baader & Nipkow, "Term Rewriting and All That" (1998).
pub fn term_lpo(prec: &dyn Fn(&Term) -> i32, s: &Term, t: &Term) -> Ordering {
    fn lpo_inner(prec: &dyn Fn(&Term) -> i32, s: &Term, t: &Term) -> Ordering {
        // Decompose into head + arguments
        let (s_head, s_args) = strip_comb(s);
        let (t_head, t_args) = strip_comb(t);

        // LPO-1: s = f(s1..sm), t = g(t1..tn)
        // If any s_i >= t, then s > t
        let all_s_lt_t = s_args.iter().all(|si| lpo_inner(prec, si, t) == Ordering::Less);
        if !all_s_lt_t {
            return Ordering::Greater;
        }

        // Compare heads
        match hd_lpo_ord(prec, s_head, t_head) {
            Ordering::Greater => {
                // LPO-2b: f > g and for all t_j, s > t_j
                if t_args.iter().all(|tj| lpo_inner(prec, s, tj) == Ordering::Greater) {
                    Ordering::Greater
                } else {
                    Ordering::Less
                }
            },
            Ordering::Equal => {
                // LPO-2a: f = g, compare arguments lexicographically
                let n = usize::min(s_args.len(), t_args.len());
                for i in 0..n {
                    let ord = lpo_inner(prec, s_args[i], t_args[i]);
                    if ord != Ordering::Equal {
                        return ord;
                    }
                }
                // Equal up to common prefix: shorter = smaller
                s_args.len().cmp(&t_args.len())
            },
            Ordering::Less => Ordering::Less,
        }
    }

    lpo_inner(prec, s, t)
}

/// Strip off applications: `f $ a1 $ a2 $ ... $ an` → `(f, [a1, a2, ..., an])`
fn strip_comb(t: &Term) -> (&Term, Vec<&Term>) {
    let mut args = Vec::new();
    let mut head = t;
    while let Term::App { func, arg } = head {
        head = func;
        args.push(arg.as_ref());
    }
    args.reverse();
    (head, args)
}

/// Head ordering for LPO: uses precedence function.
fn hd_lpo_ord(prec: &dyn Fn(&Term) -> i32, f: &Term, g: &Term) -> Ordering {
    match (f, g) {
        (Term::Abs { typ: tf, body: bf, .. }, Term::Abs { typ: tg, body: bg, .. }) => {
            match term_lpo(prec, bf, bg) {
                Ordering::Equal => typ_ord(tf, tg),
                ord => ord,
            }
        },
        (f, g) => {
            let pf = prec(f);
            let pg = prec(g);
            if pf < 0 && pg < 0 {
                // Both unrecognized: fall back to head ordering
                hd_ord(f, g)
            } else {
                pf.cmp(&pg)
            }
        },
    }
}

// =========================================================================
// Convenience: comparison that considers alpha-equivalence
// =========================================================================

/// Compare two terms up to alpha-equivalence.
/// For bound names, this is the same as structural equality.
/// For everything else, uses `fast_term_ord`.
pub fn aconv(a: &Term, b: &Term) -> bool {
    fast_term_ord(a, b) == Ordering::Equal
}

/// Compare two types for equality.
pub fn typ_eq(a: &Typ, b: &Typ) -> bool {
    typ_ord(a, b) == Ordering::Equal
}

// =========================================================================
// Tables keyed by term/type (using ordering)
// =========================================================================

/// A hash key derived from fast term ordering.
/// This is a lightweight "fingerprint" for quick equality checks.
pub fn term_hash(t: &Term) -> u64 {
    use std::hash::Hasher;
    // We use a custom hash that's compatible with fast_term_ord equality
    struct TermHasher(u64);
    impl Hasher for TermHasher {
        fn finish(&self) -> u64 {
            self.0
        }
        fn write(&mut self, _bytes: &[u8]) {
            // Not used for term hashing
        }
        fn write_u8(&mut self, i: u8) {
            self.0 = self.0.wrapping_mul(31).wrapping_add(i as u64);
        }
        fn write_u64(&mut self, i: u64) {
            self.0 = self.0.wrapping_mul(31).wrapping_add(i);
        }
        fn write_usize(&mut self, i: usize) {
            self.write_u64(i as u64);
        }
    }

    fn hash_term(t: &Term, h: &mut TermHasher) {
        match t {
            Term::Const { name, typ } => {
                h.write_u8(0);
                h.write_usize(name.as_ref().len());
                hash_typ(typ, h);
            },
            Term::Free { name, typ } => {
                h.write_u8(1);
                h.write_usize(name.as_ref().len());
                hash_typ(typ, h);
            },
            Term::Var { name, index, typ } => {
                h.write_u8(2);
                h.write_usize(name.as_ref().len());
                h.write_usize(*index);
                hash_typ(typ, h);
            },
            Term::Bound(i) => {
                h.write_u8(3);
                h.write_usize(*i);
            },
            Term::Abs { name: _, typ, body } => {
                h.write_u8(4);
                hash_typ(typ, h);
                hash_term(body, h);
            },
            Term::App { func, arg } => {
                h.write_u8(5);
                hash_term(func, h);
                hash_term(arg, h);
            },
        }
    }

    fn hash_typ(typ: &Typ, h: &mut TermHasher) {
        match typ {
            Typ::Type { name, args } => {
                h.write_u8(0);
                h.write_usize(name.as_ref().len());
                for a in args {
                    hash_typ(a, h);
                }
            },
            Typ::TFree { name, .. } => {
                h.write_u8(1);
                h.write_usize(name.as_ref().len());
            },
            Typ::TVar { name, index, .. } => {
                h.write_u8(2);
                h.write_usize(name.as_ref().len());
                h.write_usize(*index);
            },
        }
    }

    let mut h = TermHasher(0);
    hash_term(t, &mut h);
    h.finish()
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn typ_base(name: &str) -> Typ {
        Typ::base(name)
    }

    fn const_(name: &str, typ: Typ) -> Term {
        Term::const_(name, typ)
    }

    fn free(name: &str, typ: Typ) -> Term {
        Term::free(name, typ)
    }

    #[test]
    fn test_fast_indexname_ord() {
        assert_eq!(fast_indexname_ord(("x", 1), ("x", 1)), Ordering::Equal);
        assert_eq!(fast_indexname_ord(("x", 0), ("x", 1)), Ordering::Less);
        assert_eq!(fast_indexname_ord(("y", 0), ("x", 0)), Ordering::Greater);
    }

    #[test]
    fn test_typ_ord() {
        let nat = typ_base("nat");
        let bool = typ_base("bool");
        assert_eq!(typ_ord(&nat, &nat), Ordering::Equal);
        assert_eq!(typ_ord(&nat, &bool), Ordering::Greater); // "nat" > "bool" alphabetically
    }

    #[test]
    fn test_fast_term_ord_same() {
        let a = const_("HOL.eq", typ_base("bool"));
        let b = const_("HOL.eq", typ_base("bool"));
        assert_eq!(fast_term_ord(&a, &b), Ordering::Equal);
    }

    #[test]
    fn test_fast_term_ord_different_consts() {
        let a = const_("A", typ_base("bool"));
        let b = const_("B", typ_base("bool"));
        assert_eq!(fast_term_ord(&a, &b), Ordering::Less); // "A" < "B"
    }

    #[test]
    fn test_term_ord_size() {
        // f(a) has size 2, a has size 1, so f(a) > a
        let a = const_("a", typ_base("bool"));
        let fa = Term::app(const_("f", Typ::arrow(typ_base("bool"), typ_base("bool"))), a.clone());
        assert_eq!(term_ord(&fa, &a), Ordering::Greater);
    }

    #[test]
    fn test_term_ord_transitive() {
        let a = const_("a", typ_base("bool"));
        let b = const_("b", typ_base("bool"));
        let c = const_("c", typ_base("bool"));
        assert_eq!(term_ord(&a, &b), Ordering::Less);
        assert_eq!(term_ord(&b, &c), Ordering::Less);
        assert_eq!(term_ord(&a, &c), Ordering::Less);
    }

    #[test]
    fn test_term_lpo() {
        let prec = |t: &Term| -> i32 {
            match t {
                Term::Const { name, .. } if name.as_ref() == "f" => 2,
                Term::Const { name, .. } if name.as_ref() == "g" => 1,
                Term::Const { name, .. } if name.as_ref() == "a" => 0,
                _ => -1,
            }
        };

        let a = const_("a", typ_base("bool"));
        let fa = Term::app(const_("f", Typ::arrow(typ_base("bool"), typ_base("bool"))), a.clone());
        let ga = Term::app(const_("g", Typ::arrow(typ_base("bool"), typ_base("bool"))), a);

        // f > g, so f(a) > g(a)
        assert_eq!(term_lpo(&prec, &fa, &ga), Ordering::Greater);
    }

    #[test]
    fn test_aconv() {
        let a = free("x", typ_base("bool"));
        let b = free("x", typ_base("bool"));
        assert!(aconv(&a, &b));

        let c = free("y", typ_base("bool"));
        assert!(!aconv(&a, &c));
    }

    #[test]
    fn test_term_hash_consistent() {
        let a = free("x", typ_base("bool"));
        let b = free("x", typ_base("bool"));
        assert_eq!(term_hash(&a), term_hash(&b));
    }

    #[test]
    fn test_app_order() {
        // f(a, b) should compare properly
        let a = free("a", typ_base("bool"));
        let b = free("b", typ_base("bool"));
        let fab = Term::apps(
            free("f", Typ::arrows(vec![typ_base("bool"), typ_base("bool")], typ_base("bool"))),
            vec![a.clone(), b.clone()],
        );
        let fac = Term::apps(
            free("f", Typ::arrows(vec![typ_base("bool"), typ_base("bool")], typ_base("bool"))),
            vec![a, free("c", typ_base("bool"))],
        );
        assert!(fast_term_ord(&fab, &fac) != Ordering::Equal);
    }

    #[test]
    fn test_bound_var_ordering() {
        let b0 = Term::bound(0);
        let b1 = Term::bound(1);
        let b2 = Term::bound(2);
        assert_eq!(fast_term_ord(&b0, &b0), Ordering::Equal);
        assert_eq!(fast_term_ord(&b0, &b1), Ordering::Less);
        assert_eq!(fast_term_ord(&b2, &b1), Ordering::Greater);
    }
}
