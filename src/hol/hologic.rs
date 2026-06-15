//! Abstract syntax operations for HOL.
//! Corresponds to Isabelle's src/HOL/Tools/hologic.ML.
//!
//! Provides:
//! - Centralized HOL constant definitions (Trueprop, eq, conj, disj, imp, Not, etc.)
//! - mk_*/dest_*/is_* functions for safe term construction and pattern matching
//! - Type helpers (boolT, natT, setT, prodT, listT, etc.)
//! - Structured term builders (conjuncts, disjuncts, etc.)
//!
//! Design principle: all HOL syntactic operations go through this module.
//! Ad-hoc `Term::const_("HOL.xxx", ...)` in other files should be migrated here.
//!
//! Naming follows Isabelle/ML conventions (boolT, natT, etc.) for easy cross-reference.

#![allow(non_snake_case)]

use crate::core::term::Term;
use crate::core::types::Typ;

// ============================================================================
// Core HOL Constants (lazily interned)
// ============================================================================

/// The `Trueprop` constant: `bool => prop`.
/// Wraps a HOL boolean into a Pure proposition.
#[inline]
pub fn trueprop_const() -> Term {
    Term::const_("HOL.Trueprop", Typ::arrow(Typ::base("bool"), Typ::base("prop")))
}

/// The `HOL.eq` constant for a given type T: `T => T => bool`.
#[inline]
pub fn eq_const(typ: Typ) -> Term {
    Term::const_("HOL.eq", Typ::arrow(typ.clone(), Typ::arrow(typ, Typ::base("bool"))))
}

/// The `HOL.conj` constant: `bool => bool => bool`.
#[inline]
pub fn conj_const() -> Term { Term::const_("HOL.conj", bool_bin_type()) }

/// The `HOL.disj` constant: `bool => bool => bool`.
#[inline]
pub fn disj_const() -> Term { Term::const_("HOL.disj", bool_bin_type()) }

/// The `HOL.implies` constant: `bool => bool => bool`.
#[inline]
pub fn imp_const() -> Term { Term::const_("HOL.implies", bool_bin_type()) }

/// The `HOL.Not` constant: `bool => bool`.
#[inline]
pub fn not_const() -> Term { Term::const_("HOL.Not", Typ::arrow(Typ::base("bool"), Typ::base("bool"))) }

/// The `HOL.All` constant for type T: `(T => bool) => bool`.
#[inline]
pub fn all_const(typ: Typ) -> Term {
    Term::const_("HOL.All", Typ::arrow(Typ::arrow(typ, Typ::base("bool")), Typ::base("bool")))
}

/// The `HOL.Ex` constant for type T: `(T => bool) => bool`.
#[inline]
pub fn exists_const(typ: Typ) -> Term {
    Term::const_("HOL.Ex", Typ::arrow(Typ::arrow(typ, Typ::base("bool")), Typ::base("bool")))
}

/// Helper: `bool => bool => bool` type (used for binary connectives).
#[inline]
fn bool_bin_type() -> Typ {
    Typ::arrow(Typ::base("bool"), Typ::arrow(Typ::base("bool"), Typ::base("bool")))
}

/// The `HOL.True` constant: `bool`.
#[inline]
pub fn true_const() -> Term { Term::const_("HOL.True", Typ::base("bool")) }

/// The `HOL.False` constant: `bool`.
#[inline]
pub fn false_const() -> Term { Term::const_("HOL.False", Typ::base("bool")) }

/// The `HOL.If` constant: `bool => 'a => 'a => 'a`. Type parameterized.
#[inline]
pub fn if_const(typ: Typ) -> Term {
    Term::const_("HOL.If",
        Typ::arrow(Typ::base("bool"),
        Typ::arrow(typ.clone(),
        Typ::arrow(typ.clone(), typ))))
}

/// The `HOL.Let` constant: `'a => ('a => 'b) => 'b`. Type parameterized.
#[inline]
pub fn let_const(a_typ: Typ, b_typ: Typ) -> Term {
    Term::const_("HOL.Let",
        Typ::arrow(a_typ.clone(),
        Typ::arrow(Typ::arrow(a_typ, b_typ.clone()), b_typ)))
}

// ============================================================================
// Common Types
// ============================================================================

/// `bool` type.
#[inline]
pub fn boolT() -> Typ { Typ::base("bool") }

/// `prop` type (Pure).
#[inline]
pub fn propT() -> Typ { Typ::base("prop") }

/// `nat` type (from Nat theory).
#[inline]
pub fn natT() -> Typ { Typ::base("Nat.nat") }

/// `int` type (from Int theory).
#[inline]
pub fn intT() -> Typ { Typ::base("Int.int") }

/// `real` type (from Real theory).
#[inline]
pub fn realT() -> Typ { Typ::base("Real.real") }

/// `Set.set` type: `T => bool`.
#[inline]
pub fn mk_setT(typ: Typ) -> Typ { Typ::apply("Set.set", vec![typ]) }

/// Extract element type from set type. Returns None if not a set type.
pub fn dest_setT(typ: &Typ) -> Option<Typ> {
    match typ {
        Typ::Type { name, args } if name.as_ref() == "Set.set" => args.first().cloned(),
        _ => None,
    }
}

/// `Product_Type.prod` type: `T1 * T2`.
#[inline]
pub fn mk_prodT(t1: Typ, t2: Typ) -> Typ {
    Typ::Type { name: "Product_Type.prod".into(), args: vec![t1, t2] }
}

/// Extract component types from a product type.
pub fn dest_prodT(typ: &Typ) -> Option<(Typ, Typ)> {
    match typ {
        Typ::Type { name, args } if name.as_ref() == "Product_Type.prod" && args.len() == 2 => {
            Some((args[0].clone(), args[1].clone()))
        }
        _ => None,
    }
}

/// `Product_Type.unit` type.
#[inline]
pub fn unitT() -> Typ { Typ::base("Product_Type.unit") }

/// `List.list` type.
#[inline]
pub fn listT(typ: Typ) -> Typ {
    Typ::Type { name: "List.list".into(), args: vec![typ] }
}

/// Extract element type from list type.
pub fn dest_listT(typ: &Typ) -> Option<Typ> {
    match typ {
        Typ::Type { name, args } if name.as_ref() == "List.list" && args.len() == 1 => Some(args[0].clone()),
        _ => None,
    }
}

// ============================================================================
// Trueprop: bridging HOL bool and Pure prop
// ============================================================================

/// Wrap a boolean term into a Pure proposition: `Trueprop P`.
#[inline]
pub fn mk_Trueprop(p: Term) -> Term {
    Term::app(trueprop_const(), p)
}

/// Destruct `Trueprop P` into `P`. Returns None if not a Trueprop.
pub fn dest_Trueprop(term: &Term) -> Option<&Term> {
    match term {
        Term::App { func, arg } if is_trueprop_const(func) => Some(arg),
        _ => None,
    }
}

/// Check if a term is `Trueprop _`.
#[inline]
pub fn is_Trueprop(term: &Term) -> bool {
    matches!(term, Term::App { func, .. } if is_trueprop_const(func))
}

#[inline]
pub fn is_trueprop_const(term: &Term) -> bool {
    matches!(term, Term::Const { name, .. } if name.as_ref() == "HOL.Trueprop")
}

// ============================================================================
// Logic: conjunction, disjunction, implication, negation
// ============================================================================

/// Build `t1 & t2` (HOL.conj).
#[inline]
pub fn mk_conj(t1: Term, t2: Term) -> Term {
    Term::apps(conj_const(), vec![t1, t2])
}

/// Destruct `A & B` into (A, B). Returns None if not a conjunction.
pub fn dest_conj(term: &Term) -> Option<(&Term, &Term)> {
    match term {
        Term::App { func, arg: b } => match func.as_ref() {
            Term::App { func, arg: a } if is_conj_const(func) => Some((a, b)),
            _ => None,
        },
        _ => None,
    }
}

/// Flatten nested conjunctions: `(A & B) & C -> [A, B, C]`.
pub fn conjuncts(term: &Term) -> Vec<&Term> {
    let mut result = Vec::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        match dest_conj(t) {
            Some((a, b)) => { stack.push(b); stack.push(a); }
            None => result.push(t),
        }
    }
    result
}

/// Build `t1 | t2` (HOL.disj).
#[inline]
pub fn mk_disj(t1: Term, t2: Term) -> Term {
    Term::apps(disj_const(), vec![t1, t2])
}

/// Destruct `A | B` into (A, B). Returns None if not a disjunction.
pub fn dest_disj(term: &Term) -> Option<(&Term, &Term)> {
    match term {
        Term::App { func, arg: b } => match func.as_ref() {
            Term::App { func, arg: a } if is_disj_const(func) => Some((a, b)),
            _ => None,
        },
        _ => None,
    }
}

/// Flatten nested disjunctions: `(A | B) | C -> [A, B, C]`.
pub fn disjuncts(term: &Term) -> Vec<&Term> {
    let mut result = Vec::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        match dest_disj(t) {
            Some((a, b)) => { stack.push(b); stack.push(a); }
            None => result.push(t),
        }
    }
    result
}

/// Build `A --> B` (HOL.implies).
#[inline]
pub fn mk_imp(prem: Term, concl: Term) -> Term {
    Term::apps(imp_const(), vec![prem, concl])
}

/// Destruct `A --> B` into (A, B). Returns None if not an implication.
pub fn dest_imp(term: &Term) -> Option<(&Term, &Term)> {
    match term {
        Term::App { func, arg: b } => match func.as_ref() {
            Term::App { func, arg: a } if is_imp_const(func) => Some((a, b)),
            _ => None,
        },
        _ => None,
    }
}

/// Build `~P` (HOL.Not).
#[inline]
pub fn mk_not(p: Term) -> Term {
    Term::app(not_const(), p)
}

/// Destruct `~P` into `P`. Returns None if not a negation.
pub fn dest_not(term: &Term) -> Option<&Term> {
    match term {
        Term::App { func, arg } if is_not_const(func) => Some(arg),
        _ => None,
    }
}

/// Check if a term is `HOL.conj` or its alias `HOL.and`.
#[inline]
pub fn is_conj_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "HOL.conj" || name.as_ref() == "HOL.and")
}
/// Check if a term is `HOL.disj` or its alias `HOL.or`.
#[inline]
pub fn is_disj_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "HOL.disj" || name.as_ref() == "HOL.or")
}
/// Check if a term is `HOL.implies`.
#[inline]
pub fn is_imp_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "HOL.implies")
}
/// Check if a term is `HOL.Not`.
#[inline]
pub fn is_not_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "HOL.Not")
}
/// Check if a term is `HOL.True`.
#[inline]
pub fn is_true_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "HOL.True")
}
/// Check if a term is `HOL.False`.
#[inline]
pub fn is_false_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "HOL.False")
}
/// Check if a term is `HOL.eq` or `Pure.eq`.
#[inline]
pub fn is_eq_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "HOL.eq" || name.as_ref() == "Pure.eq")
}

// ============================================================================
// Equality
// ============================================================================

/// Build `lhs = rhs` (HOL.eq). Uses dummy type — caller should ensure proper typing
/// via certify or type inference.
#[inline]
pub fn mk_eq(lhs: Term, rhs: Term) -> Term {
    Term::apps(eq_const(Typ::dummy()), vec![lhs, rhs])
}

/// Build `lhs = rhs` with an explicit element type.
#[inline]
pub fn mk_eq_typed(typ: Typ, lhs: Term, rhs: Term) -> Term {
    Term::apps(eq_const(typ), vec![lhs, rhs])
}

/// Destruct `lhs = rhs` into (lhs, rhs). Returns None if not an equality.
pub fn dest_eq(term: &Term) -> Option<(&Term, &Term)> {
    match term {
        Term::App { func, arg: rhs } => match func.as_ref() {
            Term::App { func, arg: lhs } if is_eq_const(func) => Some((lhs, rhs)),
            _ => None,
        },
        _ => None,
    }
}

#[inline]
pub fn is_eq_const_hol(t: &Term) -> bool { matches!(t, Term::Const { name, .. } if name.as_ref() == "HOL.eq") }

// ============================================================================
// Quantifiers
// ============================================================================

/// Build `ALL x. P(x)`.
pub fn mk_all(x: &str, typ: Typ, body: Term) -> Term {
    Term::app(all_const(typ.clone()), Term::abs(x, typ, body))
}

/// Destruct `ALL x. P(x)` into (variable name, type, body). Returns None if not an All.
pub fn dest_all(term: &Term) -> Option<(&str, &Typ, &Term)> {
    match term {
        Term::App { func, arg: body } if is_all_const(func) => {
            match body.as_ref() {
                Term::Abs { name, typ, body } => Some((name.as_ref(), typ, body)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Build `EX x. P(x)`.
pub fn mk_exists(x: &str, typ: Typ, body: Term) -> Term {
    Term::app(exists_const(typ.clone()), Term::abs(x, typ, body))
}

/// Destruct `EX x. P(x)` into (variable name, type, body). Returns None if not an Ex.
pub fn dest_exists(term: &Term) -> Option<(&str, &Typ, &Term)> {
    match term {
        Term::App { func, arg: body } if is_exists_const(func) => {
            match body.as_ref() {
                Term::Abs { name, typ, body } => Some((name.as_ref(), typ, body)),
                _ => None,
            }
        }
        _ => None,
    }
}

#[inline]
pub fn is_all_const(t: &Term) -> bool { matches!(t, Term::Const { name, .. } if name.as_ref() == "HOL.All") }
#[inline]
pub fn is_exists_const(t: &Term) -> bool { matches!(t, Term::Const { name, .. } if name.as_ref() == "HOL.Ex") }

// ============================================================================
// Set operations
// ============================================================================

/// Build `Collect_const T = Set.Collect :: (T => bool) => Set.set T`.
#[inline]
pub fn collect_const(typ: Typ) -> Term {
    Term::const_("Set.Collect", Typ::arrow(
        Typ::arrow(typ.clone(), Typ::base("bool")),
        mk_setT(typ),
    ))
}

/// Build `{x. P(x)}` or `Collect A P`.
pub fn mk_Collect(x: &str, typ: Typ, pred: Term) -> Term {
    Term::app(collect_const(typ.clone()), Term::abs(x, typ, pred))
}

/// Build `x : A` (Set.member).
pub fn mk_mem(x: Term, a: Term) -> Term {
    let set_typ = Typ::dummy(); // ideally dest_setT from a's type
    Term::apps(
        Term::const_("Set.member", Typ::arrow(set_typ.clone(), Typ::arrow(mk_setT(set_typ), Typ::base("bool")))),
        vec![x, a],
    )
}

/// Destruct `x : A` into (x, A). Returns None if not a membership.
pub fn dest_mem(term: &Term) -> Option<(&Term, &Term)> {
    match term {
        Term::App { func, arg: a } => match func.as_ref() {
            Term::App { func, arg: x } if is_member_const(func) => Some((x, a)),
            _ => None,
        },
        _ => None,
    }
}

#[inline]
pub fn is_member_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "Set.member")
}

/// Build a finite set `{t1, t2, ..., tn}`.
pub fn mk_set(typ: Typ, ts: Vec<Term>) -> Term {
    let st = mk_setT(typ.clone());
    let empty = Term::const_("Orderings.bot_class.bot", st.clone());
    let insert = Term::const_("Set.insert", Typ::arrow(typ, Typ::arrow(st.clone(), st)));
    ts.into_iter().rfold(empty, |acc, t| Term::apps(insert.clone(), vec![t, acc]))
}

/// Destruct a finite set `{t1, ..., tn}` into `[t1, ..., tn]`.
pub fn dest_set(term: &Term) -> Option<Vec<&Term>> {
    match term {
        t if is_bot_const(t) => Some(vec![]),
        t => {
            let (elem, rest) = dest_insert(t)?;
            let mut elems = dest_set(rest)?;
            elems.insert(0, elem);
            Some(elems)
        }
    }
}

fn dest_insert(term: &Term) -> Option<(&Term, &Term)> {
    match term {
        Term::App { func, arg: rest } => match func.as_ref() {
            Term::App { func, arg: elem } if is_insert_const(func) => Some((elem, rest)),
            _ => None,
        },
        _ => None,
    }
}

#[inline]
pub fn is_bot_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "Orderings.bot_class.bot")
}
#[inline]
pub fn is_insert_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "Set.insert")
}

/// Build `UNIV :: Set.set T`.
pub fn mk_UNIV(typ: Typ) -> Term {
    Term::const_("Orderings.top_class.top", mk_setT(typ))
}

// ============================================================================
// Product type operations
// ============================================================================

/// The unit value `()`.
#[inline]
pub fn unit_val() -> Term { Term::const_("Product_Type.Unity", unitT()) }

/// Check if a term is `()`.
#[inline]
pub fn is_unit(term: &Term) -> bool {
    matches!(term, Term::Const { name, .. } if name.as_ref() == "Product_Type.Unity")
}

/// `Pair_const T1 T2 :: T1 => T2 => T1 * T2`.
#[inline]
pub fn pair_const(t1: Typ, t2: Typ) -> Term {
    Term::const_("Product_Type.Pair", Typ::arrow(t1.clone(), Typ::arrow(t2.clone(), mk_prodT(t1, t2))))
}

/// Build `(t1, t2)`.
#[inline]
pub fn mk_prod(t1: Term, t2: Term) -> Term {
    Term::apps(pair_const(Typ::dummy(), Typ::dummy()), vec![t1, t2])
}

/// Destruct `(t1, t2)` into (t1, t2). Returns None if not a pair.
pub fn dest_prod(term: &Term) -> Option<(&Term, &Term)> {
    match term {
        Term::App { func, arg: t2 } => match func.as_ref() {
            Term::App { func, arg: t1 } if is_pair_const(func) => Some((t1, t2)),
            _ => None,
        },
        _ => None,
    }
}

/// Build `fst p`.
pub fn mk_fst(p: Term) -> Term {
    Term::app(
        Term::const_("Product_Type.prod.fst", Typ::arrow(Typ::dummy(), Typ::dummy())),
        p,
    )
}

/// Build `snd p`.
pub fn mk_snd(p: Term) -> Term {
    Term::app(
        Term::const_("Product_Type.prod.snd", Typ::arrow(Typ::dummy(), Typ::dummy())),
        p,
    )
}

/// `case_prod_const A B C :: (A => B => C) => (A*B) => C`.
pub fn case_prod_const(a: Typ, b: Typ, c: Typ) -> Term {
    Term::const_("Product_Type.prod.case_prod",
        Typ::arrow(
            Typ::arrow(a.clone(), Typ::arrow(b.clone(), c.clone())),
            Typ::arrow(mk_prodT(a, b), c),
        ))
}

/// Build `case_prod f`.
pub fn mk_case_prod(f: Term) -> Term {
    Term::app(
        Term::const_("Product_Type.prod.case_prod", Typ::arrow(Typ::dummy(), Typ::dummy())),
        f,
    )
}

#[inline]
pub fn is_pair_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "Product_Type.Pair")
}

// ============================================================================
// Natural numbers
// ============================================================================

/// Zero: `0 :: nat`.
#[inline]
pub fn zero_nat() -> Term { Term::const_("Groups.zero_class.zero", natT()) }

/// Check if a term is `0 :: nat`.
#[inline]
pub fn is_zero_nat(term: &Term) -> bool {
    matches!(term, Term::Const { name, typ } if name.as_ref() == "Groups.zero_class.zero"
        && matches!(typ, Typ::Type { name, .. } if name.as_ref() == "Nat.nat"))
}

/// `Suc t`.
#[inline]
pub fn mk_Suc(t: Term) -> Term {
    Term::app(Term::const_("Nat.Suc", Typ::arrow(natT(), natT())), t)
}

/// Destruct `Suc t` into `t`. Returns None if not a Suc.
pub fn dest_Suc(term: &Term) -> Option<&Term> {
    match term {
        Term::App { func, arg } if is_suc_const(func) => Some(arg),
        _ => None,
    }
}

#[inline]
pub fn is_suc_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "Nat.Suc")
}

/// Build natural number literal: `0`, `Suc 0`, `Suc (Suc 0)`, ...
pub fn mk_nat(n: usize) -> Term {
    let mut acc = zero_nat();
    for _ in 0..n {
        acc = mk_Suc(acc);
    }
    acc
}

/// Destruct natural number literal into usize. Returns None if not a nat literal.
pub fn dest_nat(term: &Term) -> Option<usize> {
    match term {
        t if is_zero_nat(t) => Some(0),
        t => {
            let inner = dest_Suc(t)?;
            dest_nat(inner).map(|n| n + 1)
        }
    }
}

// ============================================================================
// Integer numerals
// ============================================================================

/// `Num.num` type.
#[inline]
pub fn numT() -> Typ { Typ::base("Num.num") }

/// `1` as a numeral bit: `Num.One`.
#[inline]
pub fn one_const() -> Term { Term::const_("Num.num.One", numT()) }

/// `Bit0` constructor: `num => num`.
#[inline]
pub fn bit0_const() -> Term {
    Term::const_("Num.num.Bit0", Typ::arrow(numT(), numT()))
}

/// `Bit1` constructor: `num => num`.
#[inline]
pub fn bit1_const() -> Term {
    Term::const_("Num.num.Bit1", Typ::arrow(numT(), numT()))
}

/// Build a positive numeral: `1`, `Bit0 1`, `Bit1 (Bit0 1)`, etc.
pub fn mk_numeral(n: usize) -> Option<Term> {
    if n == 0 {
        return None;
    }
    fn build(n: usize) -> Term {
        if n == 1 {
            one_const()
        } else if n % 2 == 0 {
            Term::app(bit0_const(), build(n / 2))
        } else {
            Term::app(bit1_const(), build(n / 2))
        }
    }
    Some(build(n))
}

/// Destruct a positive numeral to usize. Returns None if not a numeral.
pub fn dest_numeral(term: &Term) -> Option<usize> {
    match term {
        t if is_one_const(t) => Some(1),
        Term::App { func, arg } if is_bit0_const(func) => dest_numeral(arg).map(|n| 2 * n),
        Term::App { func, arg } if is_bit1_const(func) => dest_numeral(arg).map(|n| 2 * n + 1),
        _ => None,
    }
}

#[inline]
pub fn is_one_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "Num.num.One")
}
#[inline]
fn is_bit0_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "Num.num.Bit0")
}
#[inline]
fn is_bit1_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "Num.num.Bit1")
}

/// `numeral_const T: `num => T`.
#[inline]
pub fn numeral_const(typ: Typ) -> Term {
    Term::const_("Num.numeral_class.numeral", Typ::arrow(numT(), typ))
}

/// Build a number of type T: `0`, `1`, `numeral n`, or `- numeral n`.
pub fn mk_number(typ: Typ, n: i64) -> Term {
    if n == 0 {
        Term::const_("Groups.zero_class.zero", typ)
    } else if n == 1 {
        Term::const_("Groups.one_class.one", typ)
    } else if n > 0 {
        if let Some(num) = mk_numeral(n as usize) {
            Term::app(numeral_const(typ), num)
        } else {
            Term::const_("Groups.one_class.one", typ) // fallback
        }
    } else {
        // negative: uminus (mk_number T (-n))
        let pos = mk_number(typ.clone(), -n);
        Term::app(
            Term::const_("Groups.uminus_class.uminus", Typ::arrow(typ.clone(), typ)),
            pos,
        )
    }
}

/// Destruct a number into (type, value).
pub fn dest_number(term: &Term) -> Option<(Typ, i64)> {
    match term {
        Term::Const { name, typ } if name.as_ref() == "Groups.zero_class.zero" => Some((typ.clone(), 0)),
        Term::Const { name, typ } if name.as_ref() == "Groups.one_class.one" => Some((typ.clone(), 1)),
        Term::App { func, arg } if is_numeral_class_const(func) => {
            dest_numeral(arg).map(|n| (Typ::dummy(), n as i64))
        }
        Term::App { func, arg } if is_uminus_const(func) => {
            dest_number(arg).map(|(_, n)| (Typ::dummy(), -n))
        }
        _ => None,
    }
}

#[inline]
pub fn is_numeral_class_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "Num.numeral_class.numeral")
}
#[inline]
pub fn is_uminus_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "Groups.uminus_class.uminus")
}

// ============================================================================
// List type operations
// ============================================================================

/// `Nil` constant for list of T.
#[inline]
pub fn nil_const(typ: Typ) -> Term {
    Term::const_("List.list.Nil", listT(typ))
}

/// `Cons` constant for list of T: `T => list T => list T`.
#[inline]
pub fn cons_const(typ: Typ) -> Term {
    let lt = listT(typ.clone());
    Term::const_("List.list.Cons", Typ::arrow(typ, Typ::arrow(lt.clone(), lt)))
}

/// Build a list `[t1, t2, ..., tn]`.
pub fn mk_list(typ: Typ, ts: Vec<Term>) -> Term {
    let nil = nil_const(typ.clone());
    let cons = cons_const(typ);
    ts.into_iter().rfold(nil, |acc, t| Term::apps(cons.clone(), vec![t, acc]))
}

/// Destruct a list `[t1, ..., tn]` into elements.
pub fn dest_list(term: &Term) -> Option<Vec<&Term>> {
    match term {
        t if is_nil_const(t) => Some(vec![]),
        t => {
            let (elem, rest) = dest_cons(t)?;
            let mut elems = dest_list(rest)?;
            elems.insert(0, elem);
            Some(elems)
        }
    }
}

fn dest_cons(term: &Term) -> Option<(&Term, &Term)> {
    match term {
        Term::App { func, arg: rest } => match func.as_ref() {
            Term::App { func, arg: elem } if is_cons_const(func) => Some((elem, rest)),
            _ => None,
        },
        _ => None,
    }
}

#[inline]
pub fn is_nil_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "List.list.Nil")
}
#[inline]
pub fn is_cons_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "List.list.Cons")
}

// ============================================================================
// If-then-else
// ============================================================================

/// Build `if cond then t else f`.
pub fn mk_if(cond: Term, t: Term, f: Term) -> Term {
    let if_const = Term::const_("HOL.If",
        Typ::arrow(
            Typ::base("bool"),
            Typ::arrow(Typ::dummy(), Typ::arrow(Typ::dummy(), Typ::dummy())),
        ));
    Term::apps(if_const, vec![cond, t, f])
}

/// Destruct `if cond then t else f`. Returns None if not an if-term.
pub fn dest_if(term: &Term) -> Option<(&Term, &Term, &Term)> {
    match term {
        Term::App { func: _, arg: _ } => {
            // if c t f = ((If c) t) f
            let (head, args) = term.strip_comb();
            if args.len() == 3 && is_if_const(head) {
                Some((args[0], args[1], args[2]))
            } else {
                None
            }
        }
        _ => None,
    }
}

#[inline]
pub fn is_if_const(t: &Term) -> bool {
    matches!(t, Term::Const { name, .. } if name.as_ref() == "HOL.If")
}

// ============================================================================
// Let expression
// ============================================================================

/// Build `Let v = rhs in body`.
pub fn mk_let(v: &str, typ: Typ, rhs: Term, body: Term) -> Term {
    let let_const = Term::const_("HOL.Let",
        Typ::arrow(typ.clone(), Typ::arrow(
            Typ::arrow(typ, Typ::dummy()),
            Typ::dummy(),
        )));
    Term::apps(let_const, vec![rhs, Term::abs(v, Typ::dummy(), body)])
}

// ============================================================================
// Binary operators
// ============================================================================

/// Build a binary operation: `c $ t $ u` (e.g. `t + u`, `t < u`).
pub fn mk_binop(c: &str, t: Term, u: Term) -> Term {
    let bop = Term::const_(c, Typ::arrow(Typ::dummy(), Typ::arrow(Typ::dummy(), Typ::dummy())));
    Term::apps(bop, vec![t, u])
}

/// Build a binary relation: `c $ t $ u` returning bool.
pub fn mk_binrel(c: &str, t: Term, u: Term) -> Term {
    let brel = Term::const_(c, Typ::arrow(Typ::dummy(), Typ::arrow(Typ::dummy(), Typ::base("bool"))));
    Term::apps(brel, vec![t, u])
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trueprop_roundtrip() {
        let p = Term::free("P", Typ::base("bool"));
        let tp = mk_Trueprop(p.clone());
        assert!(is_Trueprop(&tp));
        let p2 = dest_Trueprop(&tp).unwrap();
        assert_eq!(*p2, p);
    }

    #[test]
    fn test_dest_trueprop_non_trueprop() {
        let p = Term::free("P", Typ::base("bool"));
        assert!(dest_Trueprop(&p).is_none());
        assert!(!is_Trueprop(&p));
    }

    #[test]
    fn test_conj_roundtrip() {
        let a = Term::free("A", Typ::base("bool"));
        let b = Term::free("B", Typ::base("bool"));
        let c = mk_conj(a.clone(), b.clone());
        let (a2, b2) = dest_conj(&c).unwrap();
        assert_eq!(*a2, a);
        assert_eq!(*b2, b);
    }

    #[test]
    fn test_conjuncts_flat() {
        let a = Term::free("A", Typ::base("bool"));
        let b = Term::free("B", Typ::base("bool"));
        let c = Term::free("C", Typ::base("bool"));
        let nested = mk_conj(mk_conj(a.clone(), b.clone()), c.clone());
        let cs = conjuncts(&nested);
        assert_eq!(cs.len(), 3);
        assert_eq!(*cs[0], a);
        assert_eq!(*cs[1], b);
        assert_eq!(*cs[2], c);
    }

    #[test]
    fn test_conjuncts_single() {
        let a = Term::free("A", Typ::base("bool"));
        let cs = conjuncts(&a);
        assert_eq!(cs.len(), 1);
        assert_eq!(*cs[0], a);
    }

    #[test]
    fn test_disj_roundtrip() {
        let a = Term::free("A", Typ::base("bool"));
        let b = Term::free("B", Typ::base("bool"));
        let d = mk_disj(a.clone(), b.clone());
        let (a2, b2) = dest_disj(&d).unwrap();
        assert_eq!(*a2, a);
        assert_eq!(*b2, b);
    }

    #[test]
    fn test_disjuncts_flat() {
        let a = Term::free("A", Typ::base("bool"));
        let b = Term::free("B", Typ::base("bool"));
        let c = Term::free("C", Typ::base("bool"));
        let nested = mk_disj(mk_disj(a.clone(), b.clone()), c.clone());
        let ds = disjuncts(&nested);
        assert_eq!(ds.len(), 3);
    }

    #[test]
    fn test_imp_roundtrip() {
        let a = Term::free("A", Typ::base("bool"));
        let b = Term::free("B", Typ::base("bool"));
        let imp = mk_imp(a.clone(), b.clone());
        let (a2, b2) = dest_imp(&imp).unwrap();
        assert_eq!(*a2, a);
        assert_eq!(*b2, b);
    }

    #[test]
    fn test_not_roundtrip() {
        let p = Term::free("P", Typ::base("bool"));
        let np = mk_not(p.clone());
        let p2 = dest_not(&np).unwrap();
        assert_eq!(*p2, p);
    }

    #[test]
    fn test_dest_not_non_not() {
        let p = Term::free("P", Typ::base("bool"));
        assert!(dest_not(&p).is_none());
    }

    #[test]
    fn test_eq_roundtrip() {
        let x = Term::free("x", Typ::dummy());
        let y = Term::free("y", Typ::dummy());
        let eq = mk_eq(x.clone(), y.clone());
        let (x2, y2) = dest_eq(&eq).unwrap();
        assert_eq!(*x2, x);
        assert_eq!(*y2, y);
    }

    #[test]
    fn test_dest_eq_non_eq() {
        let x = Term::free("x", Typ::dummy());
        assert!(dest_eq(&x).is_none());
    }

    #[test]
    fn test_all_roundtrip() {
        let p = Term::free("P", Typ::base("bool"));
        let all = mk_all("x", Typ::dummy(), p);
        let (name, _typ, _body) = dest_all(&all).unwrap();
        assert_eq!(name, "x");
    }

    #[test]
    fn test_exists_roundtrip() {
        let p = Term::free("P", Typ::base("bool"));
        let ex = mk_exists("x", Typ::dummy(), p);
        let (name, _typ, _body) = dest_exists(&ex).unwrap();
        assert_eq!(name, "x");
    }

    #[test]
    fn test_set_roundtrip() {
        let t = Typ::base("nat");
        let a = Term::free("a", t.clone());
        let b = Term::free("b", t.clone());
        let s = mk_set(t, vec![a.clone(), b.clone()]);
        let elems = dest_set(&s).unwrap();
        assert_eq!(elems.len(), 2);
        assert_eq!(*elems[0], a);
        assert_eq!(*elems[1], b);
    }

    #[test]
    fn test_prod_roundtrip() {
        let a = Term::free("a", Typ::dummy());
        let b = Term::free("b", Typ::dummy());
        let p = mk_prod(a.clone(), b.clone());
        let (a2, b2) = dest_prod(&p).unwrap();
        assert_eq!(*a2, a);
        assert_eq!(*b2, b);
    }

    #[test]
    fn test_nat_roundtrip() {
        let n5 = mk_nat(5);
        assert_eq!(dest_nat(&n5), Some(5));
        let n0 = mk_nat(0);
        assert_eq!(dest_nat(&n0), Some(0));
    }

    #[test]
    fn test_numeral_roundtrip() {
        let num = mk_numeral(42).unwrap();
        assert_eq!(dest_numeral(&num), Some(42));
        let one = mk_numeral(1).unwrap();
        assert_eq!(dest_numeral(&one), Some(1));
    }

    #[test]
    fn test_list_roundtrip() {
        let t = Typ::base("nat");
        let a = mk_nat(1);
        let b = mk_nat(2);
        let lst = mk_list(t, vec![a, b]);
        let elems = dest_list(&lst).unwrap();
        assert_eq!(elems.len(), 2);
    }

    #[test]
    fn test_dest_conj_single() {
        let a = Term::free("A", Typ::base("bool"));
        assert!(dest_conj(&a).is_none());
    }

    #[test]
    fn test_dest_imp_non_imp() {
        let a = Term::free("A", Typ::base("bool"));
        assert!(dest_imp(&a).is_none());
    }
}
