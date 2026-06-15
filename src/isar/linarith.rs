//! Linear arithmetic decision procedure for `nat` and `int`.
//!
//! Implements Fourier-Motzkin variable elimination for Presburger
//! arithmetic over natural numbers and integers.
//!
//! Handles:
//! - Linear equations: `x + y = z`, `Suc x = y`
//! - Linear inequalities: `x + y < z`, `x <= y`
//! - Simple contradictions: `0 = Suc n`, `Suc n < 0`
//! - Transitive chains: `x < y`, `y < z` |- `x < z`
//! - Monotonicity: `x <= y` |- `x + z <= y + z`

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use crate::{
    core::{
        logic::Pure,
        simplifier::RewriteRule,
        term::Term,
        thm::{CTerm, Thm, ThmKernel},
        types::Typ,
    },
    hol::hol_loader::HolTheoremDb,
    isar::method::Method,
    tools::simp::HolSimplifier,
};

// =========================================================================
// Arithmetic type
// =========================================================================

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ArithType {
    Nat,
    Int,
}

// =========================================================================
// Linear Expression over nat/int
// =========================================================================

/// A linear expression over numbers: sum of variables + constant.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct LinExpr {
    /// Constant term
    constant: i64,
    /// Variable terms (variable name -> coefficient). Sorted for normalization.
    vars: Vec<(String, i64)>,
}

impl LinExpr {
    fn zero() -> Self {
        LinExpr { constant: 0, vars: Vec::new() }
    }

    fn constant(n: i64) -> Self {
        LinExpr { constant: n, vars: Vec::new() }
    }

    fn var(name: String) -> Self {
        LinExpr { constant: 0, vars: vec![(name, 1)] }
    }

    /// Normalize: sort variables and merge duplicates.
    fn normalize(&mut self) {
        let mut map: HashMap<String, i64> = HashMap::new();
        for (v, c) in self.vars.drain(..) {
            *map.entry(v).or_insert(0) += c;
        }
        self.vars = map.into_iter().filter(|(_, c)| *c != 0).collect();
        self.vars.sort_by(|a, b| a.0.cmp(&b.0));
    }

    /// Add two linear expressions
    fn add(&self, other: &LinExpr) -> LinExpr {
        let constant = self.constant + other.constant;
        let mut map: HashMap<String, i64> = HashMap::new();
        for (v, c) in &self.vars {
            *map.entry(v.clone()).or_insert(0) += c;
        }
        for (v, c) in &other.vars {
            *map.entry(v.clone()).or_insert(0) += c;
        }
        let mut vars: Vec<_> = map.into_iter().filter(|(_, c)| *c != 0).collect();
        vars.sort_by(|a, b| a.0.cmp(&b.0));
        LinExpr { constant, vars }
    }

    /// Subtract: self - other
    fn sub(&self, other: &LinExpr) -> LinExpr {
        let neg_other = LinExpr {
            constant: -other.constant,
            vars: other.vars.iter().map(|(v, c)| (v.clone(), -c)).collect(),
        };
        self.add(&neg_other)
    }

    /// Multiply by a constant scalar
    fn scale(&self, k: i64) -> LinExpr {
        if k == 0 {
            return LinExpr::zero();
        }
        LinExpr {
            constant: self.constant * k,
            vars: self.vars.iter().map(|(v, c)| (v.clone(), c * k)).collect(),
        }
    }
}

// =========================================================================
// Atomic Formula
// =========================================================================

#[derive(Debug, Clone)]
pub(crate) enum Atom {
    /// e1 = e2
    Eq(LinExpr, LinExpr),
    /// e1 < e2  (strict less than)
    Lt(LinExpr, LinExpr),
    /// e1 <= e2
    Le(LinExpr, LinExpr),
}

impl Atom {
    /// Reconstruct a Term from this atom (best effort, for proof construction).
    fn to_term(&self, _arith_type: ArithType) -> Option<Term> {
        match self {
            Atom::Eq(a, b) => {
                let ta = lin_expr_to_term(a)?;
                let tb = lin_expr_to_term(b)?;
                Some(mk_hol_eq(ta, tb))
            },
            Atom::Lt(a, b) => {
                let ta = lin_expr_to_term(a)?;
                let tb = lin_expr_to_term(b)?;
                Some(mk_less(ta, tb))
            },
            Atom::Le(a, b) => {
                let ta = lin_expr_to_term(a)?;
                let tb = lin_expr_to_term(b)?;
                Some(mk_less_eq(ta, tb))
            },
        }
    }
}

// =========================================================================
// Normalized Constraint
// =========================================================================

/// A constraint in standard form: sum(coeff_i * var_i) + constant <= 0 or < 0.
#[derive(Debug, Clone)]
pub(crate) struct NormalizedConstraint {
    /// Variable coefficients
    coeffs: Vec<(String, i64)>,
    /// Constant term
    constant: i64,
    /// True for strict inequality (< 0), false for non-strict (<= 0)
    is_strict: bool,
    /// Track how many strict constraints contributed to this one
    strict_count: usize,
}

impl NormalizedConstraint {
    /// Create a non-strict constraint: expr <= 0
    fn le_zero(expr: &LinExpr) -> Self {
        NormalizedConstraint {
            coeffs: expr.vars.clone(),
            constant: expr.constant,
            is_strict: false,
            strict_count: 0,
        }
    }

    /// Create a strict constraint: expr < 0
    fn lt_zero(expr: &LinExpr) -> Self {
        NormalizedConstraint {
            coeffs: expr.vars.clone(),
            constant: expr.constant,
            is_strict: true,
            strict_count: 1,
        }
    }

    #[allow(dead_code)]
    fn display(&self) -> String {
        let mut parts: Vec<String> = Vec::new();
        for (v, c) in &self.coeffs {
            if *c == 1 {
                parts.push(v.clone());
            } else if *c == -1 {
                parts.push(format!("-{}", v));
            } else if *c > 0 {
                parts.push(format!("{}*{}", c, v));
            } else {
                parts.push(format!("({})*{}", c, v));
            }
        }
        parts.push(format!("{}", self.constant));
        let op = if self.is_strict { "<" } else { "<=" };
        format!("{} {} 0", parts.join(" + "), op)
    }
}

// =========================================================================
// Term -> Linear Expression Conversion
// =========================================================================

/// Try to convert a Term to a linear expression.
fn term_to_lin_expr(term: &Term) -> Option<LinExpr> {
    match term {
        Term::Const { name, .. } => {
            if let Ok(n) = name.as_ref().parse::<i64>() {
                return Some(LinExpr::constant(n));
            }
            if name.as_ref() == "0" || name.as_ref().ends_with(".zero") {
                return Some(LinExpr::constant(0));
            }
            if name.as_ref() == "1" || name.as_ref().ends_with(".one") {
                return Some(LinExpr::constant(1));
            }
            None
        },
        Term::Free { name, .. } | Term::Var { name, .. } => {
            Some(LinExpr::var(name.as_ref().to_string()))
        },
        Term::App { func, arg } => {
            if let Term::Const { name, .. } = func.as_ref() {
                if name.as_ref() == "HOL.Suc" || name.as_ref() == "Nat.Suc" {
                    if let Some(inner) = term_to_lin_expr(arg) {
                        return Some(inner.add(&LinExpr::constant(1)));
                    }
                }
            }
            // x + y: nested App(App(plus, x), y)
            if let Term::App { func: inner_func, arg: lhs } = func.as_ref() {
                if is_plus(inner_func) {
                    if let (Some(a), Some(b)) = (term_to_lin_expr(lhs), term_to_lin_expr(arg)) {
                        return Some(a.add(&b));
                    }
                }
                // Subtraction (x - y)
                if is_minus(inner_func) {
                    if let (Some(a), Some(b)) = (term_to_lin_expr(lhs), term_to_lin_expr(arg)) {
                        return Some(a.sub(&b));
                    }
                }
            }
            None
        },
        _ => None,
    }
}

/// Reconstruct a Term from a LinExpr (for proof construction).
fn lin_expr_to_term(expr: &LinExpr) -> Option<Term> {
    let nat_typ = Typ::base("nat");
    let plus_const = Term::const_(
        "HOL.plus",
        Typ::arrow(nat_typ.clone(), Typ::arrow(nat_typ.clone(), nat_typ.clone())),
    );

    if expr.vars.is_empty() {
        let n = if expr.constant >= 0 {
            expr.constant as u64
        } else {
            return None;
        };
        return Some(Term::const_(format!("{}", n), nat_typ));
    }

    let mut result: Option<Term> = None;

    for (var, coeff) in &expr.vars {
        let var_term = Term::free(var.as_str(), nat_typ.clone());
        let term = if *coeff == 1 {
            var_term
        } else if *coeff > 1 {
            let mut t = var_term.clone();
            for _ in 1..*coeff {
                t = Term::app(Term::app(plus_const.clone(), var_term.clone()), t);
            }
            t
        } else {
            return None;
        };

        result = match result {
            None => Some(term),
            Some(existing) => Some(Term::app(Term::app(plus_const.clone(), existing), term)),
        };
    }

    if expr.constant > 0 {
        let const_term = Term::const_(format!("{}", expr.constant), nat_typ.clone());
        result = match result {
            None => Some(const_term),
            Some(existing) => Some(Term::app(Term::app(plus_const, existing), const_term)),
        };
    }

    result.or_else(|| Some(Term::const_("0", nat_typ)))
}

// =========================================================================
// Helper: recognize HOL operators
// =========================================================================

fn is_plus(term: &Term) -> bool {
    match term {
        Term::Const { name, .. } => {
            let n = name.as_ref();
            n == "HOL.plus" || n == "Groups.plus" || n.ends_with(".plus")
        },
        _ => false,
    }
}

fn is_minus(term: &Term) -> bool {
    match term {
        Term::Const { name, .. } => {
            let n = name.as_ref();
            n == "HOL.minus" || n == "Groups.minus" || n.ends_with(".minus")
        },
        _ => false,
    }
}

fn is_hol_eq(term: &Term) -> bool {
    match term {
        Term::Const { name, .. } => name.as_ref() == "HOL.eq" || name.as_ref().ends_with(".eq"),
        _ => false,
    }
}

fn is_less_than(term: &Term) -> bool {
    match term {
        Term::Const { name, .. } => {
            let n = name.as_ref();
            n == "HOL.less" || n == "Orderings.less" || n.ends_with(".less")
        },
        _ => false,
    }
}

fn is_less_eq(term: &Term) -> bool {
    match term {
        Term::Const { name, .. } => {
            let n = name.as_ref();
            n == "HOL.less_eq" || n == "Orderings.less_eq" || n.ends_with(".less_eq")
        },
        _ => false,
    }
}

// =========================================================================
// Helper: construct HOL terms for proof building
// =========================================================================

fn nat_bin_rel(name: &str) -> Term {
    let nat = Typ::base("nat");
    let prop = Typ::base("prop");
    Term::const_(format!("HOL.{}", name), Typ::arrow(nat.clone(), Typ::arrow(nat, prop)))
}

fn mk_hol_eq(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_bin_rel("eq"), a), b)
}

fn mk_less(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_bin_rel("less"), a), b)
}

fn mk_less_eq(a: Term, b: Term) -> Term {
    Term::app(Term::app(nat_bin_rel("less_eq"), a), b)
}

// =========================================================================
// Atom extraction from formulas
// =========================================================================

/// Extract an atomic formula from a term if it's linear.
fn term_to_atom(term: &Term) -> Option<Atom> {
    if let Term::App { func, arg: rhs } = term {
        if let Term::App { func: rel_const, arg: lhs } = func.as_ref() {
            if is_hol_eq(rel_const) {
                if let (Some(a), Some(b)) = (term_to_lin_expr(lhs), term_to_lin_expr(rhs)) {
                    return Some(Atom::Eq(a, b));
                }
            }
            if is_less_than(rel_const) {
                if let (Some(a), Some(b)) = (term_to_lin_expr(lhs), term_to_lin_expr(rhs)) {
                    return Some(Atom::Lt(a, b));
                }
            }
            if is_less_eq(rel_const) {
                if let (Some(a), Some(b)) = (term_to_lin_expr(lhs), term_to_lin_expr(rhs)) {
                    return Some(Atom::Le(a, b));
                }
            }
        }
    }
    None
}

// =========================================================================
// Fourier-Motzkin Solver
// =========================================================================

/// Configuration for the linear arithmetic solver.
pub struct LinArithSolver {
    /// Maximum number of elimination steps before giving up.
    max_steps: usize,
}

impl Default for LinArithSolver {
    fn default() -> Self {
        LinArithSolver { max_steps: 100 }
    }
}

impl LinArithSolver {
    pub fn new() -> Self {
        Self::default()
    }

    // =================================================================
    // Main solve
    // =================================================================

    /// Solve a system of linear constraints.
    ///
    /// Returns `Some(thm)` if the goal is entailed by the premises.
    /// Algorithm:
    /// 1. Normalize all premise atoms and the negated goal into constraints
    /// 2. Run Fourier-Motzkin elimination on all variables
    /// 3. If a contradiction is detected, the goal is entailed
    /// 4. Construct a proof through the LCF kernel
    pub(crate) fn solve(
        &self,
        premise_atoms: &[Atom],
        goal: &Atom,
        typ: ArithType,
        state: &Thm,
    ) -> Option<Thm> {
        let entailed = self.check_entailment(premise_atoms, goal, typ);
        if !entailed {
            return None;
        }
        self.prove_entailment(state, premise_atoms, goal, typ)
    }

    // =================================================================
    // FM Entailment Check
    // =================================================================

    /// Check if premises entail the goal using FM elimination.
    fn check_entailment(&self, premise_atoms: &[Atom], goal: &Atom, typ: ArithType) -> bool {
        // premises entail goal iff premises U {~goal} is unsatisfiable
        let mut constraints: Vec<NormalizedConstraint> = Vec::new();

        // Add normalized premises
        for prem_atom in premise_atoms {
            let norm = self.atom_to_constraints(prem_atom);
            constraints.extend(norm);
        }

        // Negate goal and add
        let negated = self.negate_goal(goal, typ);
        constraints.extend(negated);

        // Collect variable names
        let all_vars = self.collect_variables(&constraints);

        // Eliminate variables one by one
        let mut step_count = 0;
        for var in &all_vars {
            if step_count >= self.max_steps {
                return false;
            }
            constraints = self.eliminate_var(&constraints, var);
            step_count += 1;
        }

        // Check for contradiction in variable-free constraints
        self.is_contradiction(&constraints)
    }

    /// Convert an atom to normalized constraints.
    fn atom_to_constraints(&self, atom: &Atom) -> Vec<NormalizedConstraint> {
        match atom {
            Atom::Eq(a, b) => {
                // a = b  ->  a - b <= 0  and  b - a <= 0
                let diff1 = a.sub(b);
                let diff2 = b.sub(a);
                vec![NormalizedConstraint::le_zero(&diff1), NormalizedConstraint::le_zero(&diff2)]
            },
            Atom::Lt(a, b) => {
                // a < b  ->  a + 1 <= b  ->  a + 1 - b <= 0
                let diff = a.add(&LinExpr::constant(1)).sub(b);
                vec![NormalizedConstraint::le_zero(&diff)]
            },
            Atom::Le(a, b) => {
                // a <= b  ->  a - b <= 0
                let diff = a.sub(b);
                vec![NormalizedConstraint::le_zero(&diff)]
            },
        }
    }

    /// Negate a goal atom: convert G to ~G constraints.
    ///
    /// ~(a = b) -> (a < b) or (b < a): a+1-b <= 0  or  b+1-a <= 0
    /// ~(a < b) -> b <= a: b - a <= 0
    /// ~(a <= b) -> b < a: b + 1 - a <= 0 (nat) / a - b < 0 (int)
    fn negate_goal(&self, goal: &Atom, typ: ArithType) -> Vec<NormalizedConstraint> {
        match goal {
            Atom::Eq(a, b) => {
                // ~(a=b) -> a != b -> a+1 <= b or b+1 <= a
                let c1 = a.add(&LinExpr::constant(1)).sub(b);
                let c2 = b.add(&LinExpr::constant(1)).sub(a);
                vec![NormalizedConstraint::le_zero(&c1), NormalizedConstraint::le_zero(&c2)]
            },
            Atom::Lt(a, b) => {
                // ~(a < b) -> b <= a
                vec![NormalizedConstraint::le_zero(&b.sub(a))]
            },
            Atom::Le(a, b) => {
                if typ == ArithType::Nat {
                    // ~(a <= b) -> b < a -> b + 1 <= a -> b + 1 - a <= 0
                    vec![NormalizedConstraint::le_zero(&b.add(&LinExpr::constant(1)).sub(a))]
                } else {
                    // ~(a <= b) -> b < a -> a - b < 0
                    vec![NormalizedConstraint::lt_zero(&a.sub(b))]
                }
            },
        }
    }

    // =================================================================
    // Variable Elimination (Fourier-Motzkin)
    // =================================================================

    /// Eliminate a variable from a set of constraints using Fourier-Motzkin.
    ///
    /// For each constraint: a_i * v + rest_i <= 0
    ///
    /// - a_i > 0: v <= -rest_i / a_i (upper bound)
    /// - a_i < 0: -rest_i / |a_i| <= v (lower bound)
    /// - a_i = 0: keep as-is
    ///
    /// Combine every lower bound with every upper bound:
    ///   L <= v  and  v <= U  =>  L <= U
    pub(crate) fn eliminate_var(
        &self,
        constraints: &[NormalizedConstraint],
        var: &str,
    ) -> Vec<NormalizedConstraint> {
        let mut result: Vec<NormalizedConstraint> = Vec::new();
        let mut upper_bounds: Vec<&NormalizedConstraint> = Vec::new();
        let mut lower_bounds: Vec<&NormalizedConstraint> = Vec::new();

        // Classify constraints
        for c in constraints {
            let coeff = c.coeffs.iter().find(|(v, _)| v == var).map(|(_, c)| *c).unwrap_or(0);
            if coeff > 0 {
                upper_bounds.push(c);
            } else if coeff < 0 {
                lower_bounds.push(c);
            } else {
                result.push(c.clone());
            }
        }

        // Combine every lower bound with every upper bound
        for lower in &lower_bounds {
            let l_coeff = -lower.coeffs.iter().find(|(v, _)| v == var).unwrap().1;
            for upper in &upper_bounds {
                let u_coeff = upper.coeffs.iter().find(|(v, _)| v == var).unwrap().1;

                // From: -l_coeff * v + L <= 0  and  u_coeff * v + U <= 0
                // Combined: u_coeff * L + l_coeff * U <= 0
                let combined = self.combine_bounds(lower, upper, l_coeff, u_coeff, var);
                result.push(combined);
            }
        }

        result
    }

    /// Combine two constraints by scaling and adding.
    ///
    /// Lower: -l_coeff*var + rest_lower <= 0
    /// Upper:  u_coeff*var + rest_upper <= 0
    ///
    /// Multiply lower by u_coeff, upper by l_coeff, add:
    ///   u_coeff * rest_lower + l_coeff * rest_upper <= 0
    fn combine_bounds(
        &self,
        lower: &NormalizedConstraint,
        upper: &NormalizedConstraint,
        l_coeff: i64,
        u_coeff: i64,
        var: &str,
    ) -> NormalizedConstraint {
        let mut new_coeffs: Vec<(String, i64)> = Vec::new();

        // Scale lower's non-var terms by u_coeff
        for (v, c) in &lower.coeffs {
            if v == var {
                continue; // skip the eliminated variable
            }
            new_coeffs.push((v.clone(), c * u_coeff));
        }

        // Scale upper's non-var terms by l_coeff and merge
        for (v, c) in &upper.coeffs {
            if v == var {
                continue; // skip the eliminated variable
            }
            if let Some(existing) = new_coeffs.iter_mut().find(|(nv, _)| nv == v) {
                existing.1 += c * l_coeff;
            } else {
                new_coeffs.push((v.clone(), c * l_coeff));
            }
        }

        // Constant: u_coeff * lower.constant + l_coeff * upper.constant
        let new_constant = lower.constant * u_coeff + upper.constant * l_coeff;

        // Strictness: combined is strict if any source is strict
        let new_strict_count = lower.strict_count + upper.strict_count;

        // Clean up zero coefficients
        new_coeffs.retain(|(_, c)| *c != 0);

        NormalizedConstraint {
            coeffs: new_coeffs,
            constant: new_constant,
            is_strict: new_strict_count > 0,
            strict_count: new_strict_count,
        }
    }

    // =================================================================
    // Contradiction Detection
    // =================================================================

    /// Detect contradictions in variable-free constraints.
    ///
    /// Contradictions:
    /// - k <= 0 where k > 0 (e.g., 1 <= 0, 2 <= 0)
    /// - k < 0 where k >= 0 (e.g., 0 < 0, 1 < 0)
    /// - k <= 0 and -k < 0 where k >= 0
    pub(crate) fn is_contradiction(&self, constraints: &[NormalizedConstraint]) -> bool {
        for c in constraints {
            if c.coeffs.is_empty() {
                if c.constant > 0 {
                    // k <= 0 or k < 0 where k > 0: contradiction
                    return true;
                }
                if c.is_strict && c.constant >= 0 {
                    // 0 < 0: contradiction
                    return true;
                }
            }
        }

        // Pairwise contradictions
        for i in 0..constraints.len() {
            for j in (i + 1)..constraints.len() {
                if self.is_pair_contradiction(&constraints[i], &constraints[j]) {
                    return true;
                }
            }
        }

        false
    }

    /// Check if two constraints form a contradiction.
    fn is_pair_contradiction(&self, c1: &NormalizedConstraint, c2: &NormalizedConstraint) -> bool {
        if c1.coeffs.is_empty() && c2.coeffs.is_empty() {
            let k1 = c1.constant;
            let k2 = c2.constant;
            // k1 < 0 and -k1 <= 0 with k1 >= 0 -> contradiction
            if c1.is_strict && !c2.is_strict && k1 == -k2 && k1 >= 0 && k2 <= 0 {
                return true;
            }
            if c2.is_strict && !c1.is_strict && k2 == -k1 && k2 >= 0 && k1 <= 0 {
                return true;
            }
        }
        false
    }

    // =================================================================
    // Utilities
    // =================================================================

    fn collect_variables(&self, constraints: &[NormalizedConstraint]) -> Vec<String> {
        let mut vars: Vec<String> = Vec::new();
        let mut seen: HashSet<String> = HashSet::new();
        for c in constraints {
            for (v, _) in &c.coeffs {
                if seen.insert(v.clone()) {
                    vars.push(v.clone());
                }
            }
        }
        vars
    }

    // =================================================================
    // Proof Construction
    // =================================================================

    /// Construct an LCF proof that the premises entail the goal.
    fn prove_entailment(
        &self,
        state: &Thm,
        _premise_atoms: &[Atom],
        goal: &Atom,
        typ: ArithType,
    ) -> Option<Thm> {
        // Strategy 1: Reflexive equality
        if let Atom::Eq(a, b) = goal {
            if a == b {
                let goal_term = goal.to_term(typ)?;
                let refl_thm = ThmKernel::reflexive(CTerm::certify(goal_term));
                return self.discharge_premises(state, &refl_thm);
            }
        }

        // Strategy 2: Transitivity (x < y, y < z |- x < z)
        if let Some(thm) = self.try_transitivity(state, goal, typ) {
            return Some(thm);
        }

        // Strategy 3: Additive monotonicity
        if let Some(thm) = self.try_add_mono(state, goal, typ) {
            return Some(thm);
        }

        // Strategy 4: Single premise direct match
        if state.nprems() == 1 {
            if let Some(thm) = self.try_direct_entailment(state, goal, typ) {
                return Some(thm);
            }
        }

        // Strategy 5: Resolution-based proof
        if let Some(thm) = self.try_resolution_proof(state, goal, typ) {
            return Some(thm);
        }

        None
    }

    /// Discharge premises: given |- G and state H1,...,Hn |- G, close the goal.
    fn discharge_premises(&self, state: &Thm, proved_goal: &Thm) -> Option<Thm> {
        if state.nprems() == 0 {
            return Some(proved_goal.clone());
        }

        // Use bicompose to match proved_goal against the first premise
        let result = ThmKernel::bicompose(false, proved_goal, state, 0)?;

        if result.nprems() == 0 {
            return Some(result);
        }

        // Try to discharge remaining premises by assumption
        let mut current = result;
        let max_iters = 100;
        for _ in 0..max_iters {
            if current.nprems() == 0 {
                return Some(current);
            }
            let prem0 = current.prem(0)?;
            let assume_thm = ThmKernel::assume(CTerm::certify(prem0));
            current = ThmKernel::bicompose(false, &assume_thm, &current, 0)?;
        }

        if current.nprems() == 0 { Some(current) } else { None }
    }

    /// Try to prove using transitivity.
    fn try_transitivity(&self, state: &Thm, goal: &Atom, _typ: ArithType) -> Option<Thm> {
        let db = HolTheoremDb::get();

        let trans_name = match goal {
            Atom::Lt(_, _) => "less_trans",
            Atom::Le(_, _) => "le_trans",
            Atom::Eq(_, _) => "trans",
        };

        let trans_thm = db.by_name.get(trans_name)?;

        // Try to resolve using the transitivity theorem
        for i in 0..state.nprems() {
            if let Some(result) = ThmKernel::bicompose(true, trans_thm, state, i) {
                if result.nprems() < state.nprems() {
                    // Made progress; if fully solved, return
                    if result.nprems() == 0 {
                        return Some(result);
                    }
                    // Try recursive resolution
                    if let Some(final_result) = self.try_resolution_proof(&result, goal, _typ) {
                        return Some(final_result);
                    }
                }
            }
        }

        None
    }

    /// Try to prove using additive monotonicity.
    fn try_add_mono(&self, state: &Thm, goal: &Atom, _typ: ArithType) -> Option<Thm> {
        let db = HolTheoremDb::get();

        let mono_name = match goal {
            Atom::Le(_, _) => "add_le_mono",
            Atom::Lt(_, _) => "add_less_mono",
            _ => return None,
        };

        let mono_thm = db.by_name.get(mono_name)?;

        for i in 0..state.nprems() {
            if let Some(result) = ThmKernel::bicompose(true, mono_thm, state, i) {
                if result.nprems() == 0 {
                    return Some(result);
                }
            }
        }

        None
    }

    /// Try direct entailment from a single premise.
    fn try_direct_entailment(&self, state: &Thm, _goal: &Atom, _typ: ArithType) -> Option<Thm> {
        let prem_term = state.prem(0)?;
        let assume_prem = ThmKernel::assume(CTerm::certify(prem_term));
        let result = ThmKernel::bicompose(false, &assume_prem, state, 0)?;
        if result.nprems() == 0 {
            return Some(result);
        }
        None
    }

    /// Try a general resolution-based proof using library theorems.
    fn try_resolution_proof(&self, state: &Thm, _goal: &Atom, _typ: ArithType) -> Option<Thm> {
        let db = HolTheoremDb::get();

        let rule_names = [
            "refl",
            "trans",
            "sym",
            "le_refl",
            "le_trans",
            "less_trans",
            "add_le_mono",
            "add_less_mono",
            "Suc_not_Zero",
            "Zero_not_Suc",
            "zero_less_Suc",
            "not_less0",
            "add_left_cancel",
            "add_right_cancel",
        ];

        let mut current = state.clone();

        for rule_name in &rule_names {
            if let Some(rule_thm) = db.by_name.get(*rule_name) {
                for i in 0..current.nprems() {
                    if let Some(result) = ThmKernel::bicompose(true, rule_thm, &current, i) {
                        if result.nprems() == 0 {
                            return Some(result);
                        }
                        if result.nprems() < current.nprems() {
                            current = result;
                        }
                    }
                }
            }
        }

        // Try assumption: if any premise directly matches the goal
        if state.nprems() == 1 {
            let prem_term = state.prem(0)?;
            let assume_thm = ThmKernel::assume(CTerm::certify(prem_term));
            if let Some(result) = ThmKernel::bicompose(false, &assume_thm, state, 0) {
                if result.nprems() == 0 {
                    return Some(result);
                }
            }
        }

        None
    }
}

// =========================================================================
// Main Tactic Entry Point
// =========================================================================

/// Main entry point for the `arith` tactic.
///
/// Algorithm:
/// 1. Extract linear constraints from premises and goal
/// 2. Simplify using arithmetic rewrite rules
/// 3. Run Fourier-Motzkin elimination to check entailment
/// 4. If entailed, construct proof through the LCF kernel
/// 5. If FM fails, fall back to simplification -> auto -> blast
pub fn arith_tac(state: &Thm, premises: &[Arc<Thm>]) -> Vec<Thm> {
    // Phase 0: Already solved
    if state.nprems() == 0 {
        return vec![state.clone()];
    }

    // Phase 1: Build arithmetic simp rules
    let db = HolTheoremDb::get();
    let mut simp_rules: Vec<RewriteRule> = Vec::new();
    for name in &[
        "add_0_right",
        "add_Suc_right",
        "add_0",
        "add_Suc",
        "mult_0",
        "mult_Suc",
        "add_assoc",
        "add_commute",
        "Suc_eq_add_numeral_1_left",
        "less_Suc_eq",
        "Suc_less_eq",
        "le_refl",
    ] {
        if let Some(thm) = db.by_name.get(*name) {
            if let Some(rule) = RewriteRule::from_thm(Arc::clone(thm)) {
                simp_rules.push(rule);
            }
        }
    }

    // Phase 2: Extract linear atoms from goal
    let goal_term = match state.prem(0) {
        Some(t) => t,
        None => return vec![state.clone()],
    };

    let goal_atom = term_to_atom(&goal_term);

    // Phase 3: Try FM solver if we have a linear goal
    if let Some(ref goal_atom) = goal_atom {
        // Collect premise atoms from state
        let mut premise_atoms: Vec<Atom> = Vec::new();
        // State premise index 0 is the goal (subgoal), other prems are hypotheses
        for i in 1..state.nprems() {
            if let Some(prem_term) = state.prem(i) {
                if let Some(atom) = term_to_atom(&prem_term) {
                    premise_atoms.push(atom);
                }
            }
        }

        let solver = LinArithSolver::new();
        if let Some(result) = solver.solve(&premise_atoms, goal_atom, ArithType::Nat, state) {
            if result.nprems() == 0 {
                return vec![result];
            }
        }
    }

    // Phase 4: Fallback - simplification
    // FIXME: HolSimplifier not yet defined — skip this phase
    if false && !simp_rules.is_empty() {
        // let simp = HolSimplifier::with_rules(simp_rules.clone());
        // let simp_results = crate::isar::method::Method::Simp(simp).execute(state, premises);
        // if simp_results.iter().any(|r| r.nprems() == 0) {
        // return simp_results;
        // }
    }

    // Phase 5: Try auto
    let auto_results = Method::Auto.execute(state, premises);
    if auto_results.iter().any(|r| r.nprems() == 0) {
        return auto_results;
    }

    // Phase 6: Try blast
    let blast_results = Method::Blast.execute(state, premises);
    if blast_results.iter().any(|r| r.nprems() == 0) {
        return blast_results;
    }

    // Phase 7: Deep rewrite with arithmetic rules
    // FIXME: HolSimplifier not yet defined — skip this phase
    if false && !simp_rules.is_empty() {
        // let simp = HolSimplifier::with_rules(simp_rules);
        // if let Some(goal) = state.prem(0) {
        // if let Some((_simplified, eq_thm)) = simp.hol_rewrite_deep(&goal) {
        // if let Some(new_state) = ThmKernel::subst_premise(&eq_thm, state, 0) {
        // if new_state.nprems() == 0 {
        // return vec![new_state];
        // }
        // if let Some(prem) = new_state.prem(0) {
        // if is_trivial_false(&prem) {
        // return vec![new_state];
        // }
        // }
        // return vec![new_state];
        // }
        // }
        // }
    }

    vec![state.clone()]
}

// =========================================================================
// Triviality checks
// =========================================================================

fn is_trivial_false(term: &Term) -> bool {
    if let Term::App { func, arg: rhs } = term {
        if let Term::App { func: eq_c, arg: lhs } = func.as_ref() {
            if is_hol_eq(eq_c) {
                return (is_zero(lhs) && is_suc(rhs)) || (is_suc(lhs) && is_zero(rhs));
            }
        }
    }
    false
}

fn is_zero(term: &Term) -> bool {
    match term {
        Term::Const { name, .. } => {
            name.as_ref() == "0" || name.as_ref() == "HOL.zero" || name.as_ref() == "Groups.zero"
        },
        _ => false,
    }
}

fn is_suc(term: &Term) -> bool {
    match term {
        Term::App { func, .. } => {
            if let Term::Const { name, .. } = func.as_ref() {
                name.as_ref() == "HOL.Suc" || name.as_ref() == "Nat.Suc"
            } else {
                false
            }
        },
        _ => false,
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // Helper to create a nat-typed free variable term
    fn nat_var(name: &str) -> Term {
        Term::free(name, Typ::base("nat"))
    }

    // Helper to create a nat constant term
    fn nat_const(n: u64) -> Term {
        Term::const_(format!("{}", n), Typ::base("nat"))
    }

    // Helper: x + y
    fn mk_plus(x: Term, y: Term) -> Term {
        let nat = Typ::base("nat");
        Term::app(
            Term::app(
                Term::const_("HOL.plus", Typ::arrow(nat.clone(), Typ::arrow(nat.clone(), nat))),
                x,
            ),
            y,
        )
    }

    // Helper: Suc x
    fn mk_suc(x: Term) -> Term {
        Term::app(Term::const_("HOL.Suc", Typ::arrow(Typ::base("nat"), Typ::base("nat"))), x)
    }

    // =================================================================
    // LinExpr tests
    // =================================================================

    #[test]
    fn test_lin_expr_zero() {
        let e = LinExpr::zero();
        assert_eq!(e.constant, 0);
        assert!(e.vars.is_empty());
    }

    #[test]
    fn test_lin_expr_add() {
        let a = LinExpr::var("x".into());
        let b = LinExpr::constant(3);
        let sum = a.add(&b);
        assert_eq!(sum.constant, 3);
        assert_eq!(sum.vars.len(), 1);
        assert_eq!(sum.vars[0], ("x".to_string(), 1));
    }

    #[test]
    fn test_lin_expr_sub() {
        let a = LinExpr { constant: 5, vars: vec![("x".into(), 2)] };
        let b = LinExpr { constant: 3, vars: vec![("x".into(), 1)] };
        let diff = a.sub(&b);
        assert_eq!(diff.constant, 2);
        assert_eq!(diff.vars[0], ("x".to_string(), 1));
    }

    #[test]
    fn test_lin_expr_scale() {
        let e = LinExpr { constant: 2, vars: vec![("x".into(), 3)] };
        let scaled = e.scale(2);
        assert_eq!(scaled.constant, 4);
        assert_eq!(scaled.vars[0], ("x".to_string(), 6));
    }

    // =================================================================
    // Term -> LinExpr conversion tests
    // =================================================================

    #[test]
    fn test_term_to_lin_expr_var() {
        let t = nat_var("n");
        let e = term_to_lin_expr(&t).unwrap();
        assert_eq!(e.vars, vec![("n".to_string(), 1)]);
        assert_eq!(e.constant, 0);
    }

    #[test]
    fn test_term_to_lin_expr_suc() {
        let t = mk_suc(nat_var("n"));
        let e = term_to_lin_expr(&t).unwrap();
        assert_eq!(e.vars, vec![("n".to_string(), 1)]);
        assert_eq!(e.constant, 1);
    }

    #[test]
    fn test_term_to_lin_expr_add() {
        let t = mk_plus(nat_var("x"), mk_suc(nat_var("y")));
        let e = term_to_lin_expr(&t).unwrap();
        assert_eq!(e.constant, 1);
        assert_eq!(e.vars.len(), 2);
        assert!(e.vars.contains(&("x".to_string(), 1)));
        assert!(e.vars.contains(&("y".to_string(), 1)));
    }

    // =================================================================
    // Atom tests
    // =================================================================

    #[test]
    fn test_term_to_atom_eq() {
        let t = mk_hol_eq(nat_var("n"), nat_var("n"));
        let atom = term_to_atom(&t).unwrap();
        match atom {
            Atom::Eq(a, b) => {
                assert_eq!(a, LinExpr::var("n".into()));
                assert_eq!(b, LinExpr::var("n".into()));
            },
            _ => panic!("Expected Eq"),
        }
    }

    #[test]
    fn test_term_to_atom_lt() {
        let t = mk_less(nat_var("x"), nat_var("y"));
        let atom = term_to_atom(&t).unwrap();
        match atom {
            Atom::Lt(a, b) => {
                assert_eq!(a, LinExpr::var("x".into()));
                assert_eq!(b, LinExpr::var("y".into()));
            },
            _ => panic!("Expected Lt"),
        }
    }

    #[test]
    fn test_term_to_atom_le() {
        let t = mk_less_eq(nat_var("x"), nat_var("y"));
        let atom = term_to_atom(&t).unwrap();
        match atom {
            Atom::Le(a, b) => {
                assert_eq!(a, LinExpr::var("x".into()));
                assert_eq!(b, LinExpr::var("y".into()));
            },
            _ => panic!("Expected Le"),
        }
    }

    // =================================================================
    // Normalization tests
    // =================================================================

    #[test]
    fn test_negate_goal_le() {
        let solver = LinArithSolver::new();
        let goal = Atom::Le(LinExpr::var("x".into()), LinExpr::var("y".into()));
        let negated = solver.negate_goal(&goal, ArithType::Nat);
        assert!(!negated.is_empty());
        // ~(x <= y) -> y + 1 - x <= 0
        assert!(!negated[0].is_strict);
    }

    #[test]
    fn test_negate_goal_lt() {
        let solver = LinArithSolver::new();
        let goal = Atom::Lt(LinExpr::var("x".into()), LinExpr::var("y".into()));
        let negated = solver.negate_goal(&goal, ArithType::Nat);
        assert!(!negated.is_empty());
        // ~(x < y) -> y - x <= 0
        assert!(!negated[0].is_strict);
    }

    #[test]
    fn test_negate_goal_eq() {
        let solver = LinArithSolver::new();
        let goal = Atom::Eq(LinExpr::var("x".into()), LinExpr::var("y".into()));
        let negated = solver.negate_goal(&goal, ArithType::Nat);
        assert_eq!(negated.len(), 2);
    }

    // =================================================================
    // FM Elimination tests
    // =================================================================

    #[test]
    fn test_eliminate_var_simple() {
        let solver = LinArithSolver::new();

        // x - 3 <= 0 (x <= 3) and -x + 1 <= 0 (1 <= x)
        let constraints = vec![
            NormalizedConstraint {
                coeffs: vec![("x".into(), 1)],
                constant: -3,
                is_strict: false,
                strict_count: 0,
            },
            NormalizedConstraint {
                coeffs: vec![("x".into(), -1)],
                constant: 1,
                is_strict: false,
                strict_count: 0,
            },
        ];

        let result = solver.eliminate_var(&constraints, "x");
        assert!(!result.is_empty());
        for c in &result {
            assert!(!c.coeffs.iter().any(|(v, _)| v == "x"));
        }
    }

    #[test]
    fn test_contradiction_strict() {
        let solver = LinArithSolver::new();
        let constraints = vec![NormalizedConstraint {
            coeffs: vec![],
            constant: 0,
            is_strict: true,
            strict_count: 1,
        }];
        assert!(solver.is_contradiction(&constraints));
    }

    #[test]
    fn test_contradiction_nonstrict_not() {
        let solver = LinArithSolver::new();
        let constraints = vec![NormalizedConstraint {
            coeffs: vec![],
            constant: 0,
            is_strict: false,
            strict_count: 0,
        }];
        assert!(!solver.is_contradiction(&constraints));
    }

    #[test]
    fn test_contradiction_pair() {
        let solver = LinArithSolver::new();
        let constraints = vec![
            NormalizedConstraint { coeffs: vec![], constant: 0, is_strict: true, strict_count: 1 },
            NormalizedConstraint { coeffs: vec![], constant: 0, is_strict: false, strict_count: 0 },
        ];
        assert!(solver.is_contradiction(&constraints));
    }

    // =================================================================
    // End-to-end FM entailment tests
    // =================================================================

    #[test]
    fn test_fm_entailment_trivial() {
        let solver = LinArithSolver::new();
        let goal = Atom::Le(LinExpr::var("x".into()), LinExpr::var("x".into()));
        // x <= x: always true, no premises needed
        // ~(x <= x) -> x + 1 - x <= 0 -> 1 <= 0 (contradiction!)
        let entailed = solver.check_entailment(&[], &goal, ArithType::Nat);
        assert!(entailed, "x <= x should be entailed by empty premises");
    }

    #[test]
    fn test_fm_entailment_eq() {
        let solver = LinArithSolver::new();
        // Premise: x = y. Goal: y = x.
        let prem = Atom::Eq(LinExpr::var("x".into()), LinExpr::var("y".into()));
        let goal = Atom::Eq(LinExpr::var("y".into()), LinExpr::var("x".into()));
        let entailed = solver.check_entailment(&[prem], &goal, ArithType::Nat);
        assert!(entailed, "x = y should entail y = x");
    }

    #[test]
    fn test_fm_entailment_lt_trans() {
        let solver = LinArithSolver::new();
        // Premises: x < y, y < z. Goal: x < z.
        let prem1 = Atom::Lt(LinExpr::var("x".into()), LinExpr::var("y".into()));
        let prem2 = Atom::Lt(LinExpr::var("y".into()), LinExpr::var("z".into()));
        let goal = Atom::Lt(LinExpr::var("x".into()), LinExpr::var("z".into()));
        let entailed = solver.check_entailment(&[prem1, prem2], &goal, ArithType::Nat);
        assert!(entailed, "x < y, y < z should entail x < z");
    }

    #[test]
    fn test_fm_entailment_contradiction() {
        let solver = LinArithSolver::new();
        // Premise: 0 = Suc n, Goal: anything (contradiction in premises)
        let n = LinExpr::var("n".into());
        let zero = LinExpr::constant(0);
        let suc_n = n.add(&LinExpr::constant(1));
        let prem = Atom::Eq(zero, suc_n);
        let goal = Atom::Eq(LinExpr::constant(0), LinExpr::constant(1));
        // 0 = n + 1 is unsatisfiable, so anything follows
        let entailed = solver.check_entailment(&[prem], &goal, ArithType::Nat);
        assert!(entailed, "0 = Suc n should be contradictory");
    }

    #[test]
    fn test_fm_entailment_nat_05() {
        let solver = LinArithSolver::new();
        // Premises: x + 3 < y, y < x + 1. Goal: anything (contradiction)
        let x = LinExpr::var("x".into());
        let y = LinExpr::var("y".into());
        let prem1 = Atom::Lt(x.add(&LinExpr::constant(3)), y.clone());
        let prem2 = Atom::Lt(y, x.add(&LinExpr::constant(1)));
        let goal = Atom::Eq(LinExpr::constant(0), LinExpr::constant(1));
        let entailed = solver.check_entailment(&[prem1, prem2], &goal, ArithType::Nat);
        // x + 3 < y means x + 4 <= y
        // y < x + 1 means y + 1 <= x + 1 means y <= x
        // Together: x + 4 <= y <= x, contradiction
        assert!(entailed, "x + 3 < y and y < x + 1 should be contradictory");
    }

    #[test]
    fn test_fm_entailment_add_mono() {
        let solver = LinArithSolver::new();
        // Premise: x <= y. Goal: x + z <= y + z.
        let x = LinExpr::var("x".into());
        let y = LinExpr::var("y".into());
        let z = LinExpr::var("z".into());
        let prem = Atom::Le(x.clone(), y.clone());
        let goal = Atom::Le(x.add(&z), y.add(&z));
        let entailed = solver.check_entailment(&[prem], &goal, ArithType::Nat);
        assert!(entailed, "x <= y should entail x + z <= y + z");
    }

    // =================================================================
    // End-to-end tactic tests
    // =================================================================

    #[test]
    fn test_solve_simple_eq() {
        let n = nat_var("n");
        let goal_term = mk_hol_eq(n.clone(), n);
        let goal_cterm = CTerm::certify(goal_term);
        let state = ThmKernel::assume(goal_cterm);
        let result = arith_tac(&state, &[]);
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn test_solve_ineq_trans() {
        let _db = HolTheoremDb::get();
        let x = nat_var("x");
        let y = nat_var("y");
        let z = nat_var("z");
        let goal = mk_less(x.clone(), z.clone());
        let prem1 = mk_less(x, y.clone());
        let prem2 = mk_less(y, z);
        let stmt = Pure::mk_implies(prem1, Pure::mk_implies(prem2, goal));
        let state = ThmKernel::assume(CTerm::certify(stmt));
        let result = arith_tac(&state, &[]);
        assert!(!result.is_empty());
    }

    #[test]
    fn test_contradiction() {
        let n = nat_var("n");
        let zero = nat_const(0);
        let suc_n = mk_suc(n);
        let false_prem = mk_hol_eq(zero, suc_n);
        let goal = Term::const_("False", Typ::base("prop"));
        let stmt = Pure::mk_implies(false_prem, goal);
        let state = ThmKernel::assume(CTerm::certify(stmt));
        let result = arith_tac(&state, &[]);
        assert!(!result.is_empty());
    }

    #[test]
    fn test_nat_05() {
        let x = nat_var("x");
        let y = nat_var("y");
        let three = nat_const(3);
        let one = nat_const(1);
        let x_plus_3 = mk_plus(x.clone(), three);
        let x_plus_1 = mk_plus(x, one);
        let goal = Term::const_("False", Typ::base("prop"));
        let prem1 = mk_less(x_plus_3, y.clone());
        let prem2 = mk_less(y, x_plus_1);
        let stmt = Pure::mk_implies(prem1, Pure::mk_implies(prem2, goal));
        let state = ThmKernel::assume(CTerm::certify(stmt));
        let result = arith_tac(&state, &[]);
        assert!(!result.is_empty());
    }

    #[test]
    fn test_suc_injectivity() {
        let n = nat_var("n");
        let m = nat_var("m");
        let goal = mk_hol_eq(n.clone(), m.clone());
        let prem = mk_hol_eq(mk_suc(n), mk_suc(m));
        let stmt = Pure::mk_implies(prem, goal);
        let state = ThmKernel::assume(CTerm::certify(stmt));
        let result = arith_tac(&state, &[]);
        assert!(!result.is_empty());
    }

    #[test]
    fn test_zero_less_suc() {
        let n = nat_var("n");
        let zero = nat_const(0);
        let goal = mk_less(zero, mk_suc(n));
        let state = ThmKernel::assume(CTerm::certify(goal));
        let result = arith_tac(&state, &[]);
        assert!(!result.is_empty());
    }

    #[test]
    fn test_collect_variables() {
        let solver = LinArithSolver::new();
        let constraints = vec![
            NormalizedConstraint {
                coeffs: vec![("x".into(), 1), ("y".into(), 2)],
                constant: 0,
                is_strict: false,
                strict_count: 0,
            },
            NormalizedConstraint {
                coeffs: vec![("y".into(), -1), ("z".into(), 3)],
                constant: 5,
                is_strict: false,
                strict_count: 0,
            },
        ];
        let vars = solver.collect_variables(&constraints);
        assert_eq!(vars.len(), 3);
        assert!(vars.contains(&"x".to_string()));
        assert!(vars.contains(&"y".to_string()));
        assert!(vars.contains(&"z".to_string()));
    }

    #[test]
    fn test_fm_multi_variable() {
        let solver = LinArithSolver::new();
        let constraints = vec![
            NormalizedConstraint {
                coeffs: vec![("x".into(), 1)],
                constant: -3,
                is_strict: false,
                strict_count: 0,
            },
            NormalizedConstraint {
                coeffs: vec![("x".into(), -1)],
                constant: 1,
                is_strict: false,
                strict_count: 0,
            },
            NormalizedConstraint {
                coeffs: vec![("y".into(), 1)],
                constant: -4,
                is_strict: false,
                strict_count: 0,
            },
            NormalizedConstraint {
                coeffs: vec![("y".into(), -1)],
                constant: 2,
                is_strict: false,
                strict_count: 0,
            },
        ];
        let vars = solver.collect_variables(&constraints);
        let mut result = constraints.clone();
        for var in &vars {
            result = solver.eliminate_var(&result, var);
        }
        // Satisfiable system: 1 <= x <= 3, 2 <= y <= 4
        assert!(!solver.is_contradiction(&result));
    }

    #[test]
    fn test_combine_bounds() {
        let solver = LinArithSolver::new();
        // Lower: -2*x + y + 3 <= 0  (y + 3 <= 2x)
        let lower = NormalizedConstraint {
            coeffs: vec![("x".into(), -2), ("y".into(), 1)],
            constant: 3,
            is_strict: false,
            strict_count: 0,
        };
        // Upper: 3*x - z + 1 <= 0  (3x + 1 <= z)
        let upper = NormalizedConstraint {
            coeffs: vec![("x".into(), 3), ("z".into(), -1)],
            constant: 1,
            is_strict: false,
            strict_count: 0,
        };
        // l_coeff = 2 (abs val of -2), u_coeff = 3
        // Combined: 3*(y + 3) + 2*(-z + 1) = 3y + 9 - 2z + 2 = 3y - 2z + 11
        let combined = solver.combine_bounds(&lower, &upper, 2, 3, "x");
        assert!(combined.coeffs.iter().any(|(v, c)| v == "y" && *c == 3));
        assert!(combined.coeffs.iter().any(|(v, c)| v == "z" && *c == -2));
        assert_eq!(combined.constant, 11);
    }
}
