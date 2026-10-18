//! HOL simplifier backed by the core theorem-producing rewrite engine.
//!
//! Only closed unconditional equality theorems can authorize rewrites.
//! Search solvers and conditional candidates are retained as compatibility
//! data, but a Boolean solver answer is not proof of a rewrite condition.
//!
//! ## Built-in HOL Rules
//!
//! Boolean connectives:
//! - `True ∧ P ↔ P`, `False ∧ P ↔ False`
//! - `P ∧ True ↔ P`, `P ∧ False ↔ False`
//! - `True ∨ P ↔ True`, `False ∨ P ↔ P`
//! - `P ∨ True ↔ True`, `P ∨ False ↔ P`
//! - `True → P ↔ P`, `False → P ↔ True`
//! - `P → True ↔ True`, `P → False ↔ ¬P`
//! - `¬True ↔ False`, `¬False ↔ True`
//!
//! Quantifiers:
//! - `∀x. True ↔ True`, `∃x. False ↔ False`
//!
//! Conditionals:
//! - `if True then A else B ↔ A`
//! - `if False then A else B ↔ B`
//!
//! Let-in is handled by beta-reduction.

use std::sync::Arc;

use crate::{
    core::{
        logic::Pure,
        simplifier::{RewriteRule, Simplifier, beta_simp},
        tactic::TacticFn,
        term::Term,
        thm::{CTerm, Thm, ThmKernel},
        types::Typ,
    },
    hol::{hol_loader::HolTheoremDb, hologic},
    isar::{linarith, proof_result::validate_proof_result},
};

// =========================================================================
// Solver trait
// =========================================================================

/// A solver is a decision procedure that can prove a subgoal (condition)
/// against an explicit theorem database. Returns `Some(thm)` if the goal is
/// proved, or `None` if the solver cannot handle it.
pub trait Solver: Send + Sync {
    /// Try to prove `goal`. `context` contains the current assumptions.
    fn solve(&self, goal: &Term, context: &[Thm], db: &HolTheoremDb) -> Option<Thm>;
}

// =========================================================================
// Arithmetic Solver
// =========================================================================

/// Solver for arithmetic subgoals using the `linarith` module.
/// Returns only checked legacy evidence for the complete goal, with hypotheses
/// supplied by `context`; unsupported inputs and unproved goals return `None`.
/// This solver does not construct a strict-kernel accepted token.
pub struct ArithSolver;

impl Solver for ArithSolver {
    fn solve(&self, goal: &Term, context: &[Thm], db: &HolTheoremDb) -> Option<Thm> {
        // Certification/rule rejection means this optional solver cannot prove
        // the request. An assumption of the goal is not a solved obligation.
        let goal_ct = CTerm::certify_checked(goal.clone(), &db.type_env).ok()?;
        let state = ThmKernel::trivial(goal_ct).ok()?;
        let premises: Vec<Arc<Thm>> = context.iter().map(|t| Arc::new(t.clone())).collect();
        let allowed_hypotheses: Vec<CTerm> =
            context.iter().flat_map(|fact| fact.hyps().iter().cloned()).collect();
        linarith::arith_tac(&state, &premises, db)
            .into_iter()
            .find(|result| validate_proof_result(goal, result, &allowed_hypotheses).is_ok())
    }
}

// =========================================================================
// Assumption Solver
// =========================================================================

/// Solver that checks if a goal matches any assumption (by α-equivalence).
pub struct AsmSolver;

impl Solver for AsmSolver {
    fn solve(&self, goal: &Term, _context: &[Thm], _db: &HolTheoremDb) -> Option<Thm> {
        // Check if the goal is trivially true
        if is_trivial_true(goal) {
            return Some(ThmKernel::reflexive_compat(CTerm::certify(goal.clone())));
        }
        None
    }
}

// =========================================================================
// HOL Simplifier
// =========================================================================

/// HOL rewrite facade; only the core simplifier produces equality certificates.
/// Registered solvers remain search hints, not rewrite evidence.
pub struct HolSimplifier {
    kernel: Simplifier,
    solvers: Vec<Arc<dyn Solver>>,
    conditional_depth: usize,
}

impl HolSimplifier {
    /// Create a new empty HOL simplifier (no rules, no solvers).
    pub fn new() -> Self {
        HolSimplifier {
            kernel: Simplifier::new(Vec::new()),
            solvers: Vec::new(),
            conditional_depth: 3,
        }
    }

    /// Create a HOL simplifier with the given rewrite rules.
    pub fn with_rules(rules: Vec<RewriteRule>) -> Self {
        HolSimplifier { kernel: Simplifier::new(rules), solvers: Vec::new(), conditional_depth: 3 }
    }

    /// Create a HOL simplifier with beta-reduction only.
    pub fn with_beta() -> Self {
        HolSimplifier { kernel: beta_simp(), solvers: Vec::new(), conditional_depth: 3 }
    }

    /// Create a HOL simplifier from `db`, loading all `[simp]`-annotated
    /// rules and built-in HOL connective rules.
    pub fn from_db(db: &crate::hol::hol_loader::HolTheoremDb) -> Self {
        let mut rules: Vec<RewriteRule> = Vec::new();

        // Load DB simps
        for thm in &db.simps {
            if let Some(rule) = RewriteRule::from_thm(Arc::clone(thm)) {
                rules.push(rule);
            }
        }

        // Add built-in HOL rewrite rules
        rules.extend(Self::builtin_rules(db));

        let mut hs = HolSimplifier {
            kernel: Simplifier::new(rules),
            solvers: Vec::new(),
            conditional_depth: 3,
        };

        // Register default solvers
        hs.register_solver(Arc::new(ArithSolver));
        hs.register_solver(Arc::new(AsmSolver));

        hs
    }

    /// Register a solver plugin.
    pub fn register_solver(&mut self, solver: Arc<dyn Solver>) {
        self.solvers.push(solver);
    }

    /// Set the legacy search depth (not a rewrite authorization).
    pub fn set_conditional_depth(&mut self, depth: usize) {
        self.conditional_depth = depth;
    }

    /// Rewrite only when the underlying rule proves an unconditional equality.
    /// Solver hints cannot discharge rewrite conditions without a kernel proof.
    pub fn hol_rewrite(&self, term: &Term) -> Option<(Term, Thm)> {
        self.kernel.rewrite(term)
    }

    /// Bottom-up rewriting shares the core certificate composition path.
    pub fn hol_rewrite_deep(&self, term: &Term) -> Option<(Term, Thm)> {
        self.kernel.rewrite_deep(term)
    }

    /// Produce a tactic from this simplifier.
    /// The tactic applies `hol_rewrite_deep` to the first subgoal.
    pub fn simp_tactic(&self) -> TacticFn {
        // We need to capture the HolSimplifier's state for the tactic.
        // Since TacticFn is `Arc<dyn Fn(&Thm) -> Vec<Thm>>`, we create
        // a tactic that uses a fresh HolSimplifier with the same rules.
        let rules: Vec<RewriteRule> = self.kernel.rules().to_vec();
        let hs = HolSimplifier::with_rules(rules);
        Arc::new(move |st: &Thm| {
            if let Some(goal) = st.prem(0)
                && let Some((_simplified, eq_thm)) = hs.hol_rewrite_deep(&goal)
                && let Some(result) = ThmKernel::subst_premise(&eq_thm, st, 0)
            {
                return vec![result];
            }
            vec![]
        })
    }

    /// Repeatedly rewrite a term until no rule applies.
    pub fn rewrite_all(&self, term: &Term) -> Term {
        let mut current = term.clone();
        loop {
            match self.hol_rewrite(&current) {
                Some((next, _)) if next != current => current = next,
                _ => break,
            }
        }
        current
    }

    /// Get a reference to the underlying kernel simplifier.
    pub fn kernel(&self) -> &Simplifier {
        &self.kernel
    }

    /// Get a mutable reference to the underlying kernel simplifier.
    pub fn kernel_mut(&mut self) -> &mut Simplifier {
        &mut self.kernel
    }

    // =================================================================
    // Built-in HOL rewrite rules
    // =================================================================

    /// Generate built-in HOL rewrite rules for boolean connectives,
    /// quantifiers, and conditionals.
    pub fn builtin_rules(db: &crate::hol::hol_loader::HolTheoremDb) -> Vec<RewriteRule> {
        let mut rules = Vec::new();

        // First try to get rules from the selected theorem DB
        if let Some(db_rules) = Self::builtin_rules_from_db(db) {
            rules.extend(db_rules);
        }

        // Add kernel-constructed rules as fallback
        rules.extend(Self::builtin_rules_kernel());

        rules
    }

    /// Get built-in rules from the theorem database by name.
    fn builtin_rules_from_db(
        db: &crate::hol::hol_loader::HolTheoremDb,
    ) -> Option<Vec<RewriteRule>> {
        let mut rules = Vec::new();

        let names = [
            "conj_ac",
            "disj_ac",
            "imp_ac",
            "True_and",
            "False_and",
            "and_True",
            "and_False",
            "True_or",
            "False_or",
            "or_True",
            "or_False",
            "True_imp",
            "False_imp",
            "imp_True",
            "imp_False",
            "not_True",
            "not_False",
            "if_True",
            "if_False",
            "all_True",
            "ex_False",
        ];

        for name in &names {
            if let Some(thm) = db.by_name.get(*name)
                && let Some(rule) = RewriteRule::from_thm(Arc::clone(thm))
            {
                rules.push(rule);
            }
        }

        if rules.is_empty() { None } else { Some(rules) }
    }

    /// Construct built-in HOL rules using the kernel.
    /// These are fallback rules when the DB doesn't have them.
    fn builtin_rules_kernel() -> Vec<RewriteRule> {
        let mut rules = Vec::new();
        let prop_typ = Typ::base("prop");
        let dummy_typ = Typ::dummy();

        // Helper constants
        let eq_const = Term::const_(
            "HOL.eq",
            Typ::arrow(prop_typ.clone(), Typ::arrow(prop_typ.clone(), prop_typ.clone())),
        );
        let true_c = hologic::true_const();
        let false_c = hologic::false_const();
        let not_c = hologic::not_const();
        let conj_c = hologic::conj_const();
        let disj_c = hologic::disj_const();
        let imp_const = hologic::imp_const();
        let all_c = hologic::all_const(Typ::dummy());
        let ex_c = hologic::exists_const(Typ::dummy());

        fn mk_eq(eqc: &Term, a: Term, b: Term) -> Term {
            Term::app(Term::app(eqc.clone(), a), b)
        }

        fn mk_conj(c: &Term, a: Term, b: Term) -> Term {
            Term::app(Term::app(c.clone(), a), b)
        }

        fn mk_disj(d: &Term, a: Term, b: Term) -> Term {
            Term::app(Term::app(d.clone(), a), b)
        }

        fn mk_imp(i: &Term, a: Term, b: Term) -> Term {
            Term::app(Term::app(i.clone(), a), b)
        }

        fn mk_not(n: &Term, a: Term) -> Term {
            Term::app(n.clone(), a)
        }

        // Variable counter used across all rules
        let mut var_idx = 0usize;

        // True ∧ P = P
        {
            var_idx += 1;
            let p = Term::var("P", var_idx, prop_typ.clone());
            let lhs = mk_conj(&conj_c, true_c.clone(), p.clone());
            let rhs = p.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // False ∧ P = False
        {
            var_idx += 1;
            let p = Term::var("P", var_idx, prop_typ.clone());
            let lhs = mk_conj(&conj_c, false_c.clone(), p);
            let rhs = false_c.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // P ∧ True = P
        {
            var_idx += 1;
            let p = Term::var("P", var_idx, prop_typ.clone());
            let lhs = mk_conj(&conj_c, p.clone(), true_c.clone());
            let rhs = p.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // P ∧ False = False
        {
            var_idx += 1;
            let p = Term::var("P", var_idx, prop_typ.clone());
            let lhs = mk_conj(&conj_c, p, false_c.clone());
            let rhs = false_c.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // True ∨ P = True
        {
            var_idx += 1;
            let p = Term::var("P", var_idx, prop_typ.clone());
            let lhs = mk_disj(&disj_c, true_c.clone(), p);
            let rhs = true_c.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // False ∨ P = P
        {
            var_idx += 1;
            let p = Term::var("P", var_idx, prop_typ.clone());
            let lhs = mk_disj(&disj_c, false_c.clone(), p.clone());
            let rhs = p.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // P ∨ True = True
        {
            var_idx += 1;
            let p = Term::var("P", var_idx, prop_typ.clone());
            let lhs = mk_disj(&disj_c, p, true_c.clone());
            let rhs = true_c.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // P ∨ False = P
        {
            var_idx += 1;
            let p = Term::var("P", var_idx, prop_typ.clone());
            let lhs = mk_disj(&disj_c, p.clone(), false_c.clone());
            let rhs = p.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // True → P = P
        {
            var_idx += 1;
            let p = Term::var("P", var_idx, prop_typ.clone());
            let lhs = mk_imp(&imp_const, true_c.clone(), p.clone());
            let rhs = p.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // False → P = True
        {
            var_idx += 1;
            let p = Term::var("P", var_idx, prop_typ.clone());
            let lhs = mk_imp(&imp_const, false_c.clone(), p);
            let rhs = true_c.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // P → True = True
        {
            var_idx += 1;
            let p = Term::var("P", var_idx, prop_typ.clone());
            let lhs = mk_imp(&imp_const, p, true_c.clone());
            let rhs = true_c.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // P → False = ¬P
        {
            var_idx += 1;
            let p = Term::var("P", var_idx, prop_typ.clone());
            let lhs = mk_imp(&imp_const, p.clone(), false_c.clone());
            let rhs = mk_not(&not_c, p.clone());
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // ¬True = False
        {
            let lhs = mk_not(&not_c, true_c.clone());
            let rhs = false_c.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // ¬False = True
        {
            let lhs = mk_not(&not_c, false_c.clone());
            let rhs = true_c.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // if True then A else B = A
        {
            let if_c = hologic::if_const(Typ::dummy());
            var_idx += 1;
            let a = Term::var("a", var_idx, Typ::dummy());
            var_idx += 1;
            let b = Term::var("b", var_idx, Typ::dummy());
            let lhs = Term::apps(if_c.clone(), [true_c.clone(), a.clone(), b.clone()]);
            let rhs = a.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // if False then A else B = B
        {
            let if_c = hologic::if_const(Typ::dummy());
            var_idx += 1;
            let a = Term::var("a", var_idx, Typ::dummy());
            var_idx += 1;
            let b = Term::var("b", var_idx, Typ::dummy());
            let lhs = Term::apps(if_c, [false_c.clone(), a.clone(), b.clone()]);
            let rhs = b.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // ∀x. True = True
        {
            var_idx += 1;
            let x_name = format!("x{}", var_idx);
            let body = true_c.clone();
            let lhs = Term::app(all_c.clone(), Term::abs(x_name, dummy_typ.clone(), body));
            let rhs = true_c.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // ∃x. False = False
        {
            var_idx += 1;
            let x_name = format!("x{}", var_idx);
            let body = false_c.clone();
            let lhs = Term::app(ex_c.clone(), Term::abs(x_name, dummy_typ, body));
            let rhs = false_c.clone();
            let stmt = mk_eq(&eq_const, lhs, rhs);
            let thm = Arc::new(ThmKernel::assume_compat(CTerm::certify(stmt)));
            if let Some(rule) = RewriteRule::from_thm(thm) {
                rules.push(rule);
            }
        }

        // let x = a in b[x]  →  b[a] (beta reduction handles this)
        // No need for special rule — beta conversion already handles let-in.

        rules
    }
}

impl Default for HolSimplifier {
    fn default() -> Self {
        Self::new()
    }
}

// =========================================================================
// Helpers
// =========================================================================

/// Check if a term is trivially true (reflexive equality: t = t).
fn is_trivial_true(term: &Term) -> bool {
    if let Some((a, b)) = Pure::dest_equals(term) {
        return a == b;
    }
    // Also check if it's a Pure equality (t ≡ t)
    match term {
        Term::App { func, arg } => match func.as_ref() {
            Term::App { func: inner, arg: lhs } => match inner.as_ref() {
                Term::Const { name, .. } if name.as_ref() == "Pure.eq" => {
                    lhs.as_ref() == arg.as_ref()
                },
                _ => false,
            },
            _ => false,
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

    fn global_builtin_rules() -> Vec<RewriteRule> {
        HolSimplifier::builtin_rules(crate::hol::hol_loader::HolTheoremDb::global())
    }

    #[test]
    fn test_hol_simplifier_new() {
        let hs = HolSimplifier::new();
        assert!(hs.kernel.rules().is_empty());
    }

    #[test]
    fn test_hol_simplifier_with_rules() {
        let rules = vec![];
        let hs = HolSimplifier::with_rules(rules);
        assert!(hs.kernel.rules().is_empty());
    }

    #[test]
    fn test_builtin_rules_require_closed_theorem_sources() {
        let rules = global_builtin_rules();
        // Built-in HOL rewrite templates used to be admitted through
        // `assume_compat`. They now require real closed theorem sources.
        assert!(rules.is_empty(), "unproved built-in rewrite templates must not be rules");
    }

    #[test]
    fn test_builtin_rules_valid() {
        let rules = global_builtin_rules();
        for rule in &rules {
            // Each rule should have a valid theorem
            let prop = rule.thm.prop().term();
            // The proposition should be an equality
            assert!(
                Pure::dest_equals(prop).is_some(),
                "Rule theorem is not an equality: {:?}",
                prop
            );
        }
    }

    #[test]
    fn test_hol_rewrite_conj_true() {
        let hs = HolSimplifier::with_rules(global_builtin_rules());
        // Construct: True ∧ P
        let conj_c = hologic::conj_const();
        let true_c = hologic::true_const();
        let p = Term::free("P", Typ::dummy());
        let term = Term::app(Term::app(conj_c, true_c), p.clone());

        let result = hs.hol_rewrite(&term);
        assert!(result.is_none(), "True ∧ P needs a closed rewrite theorem source");
    }

    #[test]
    fn test_hol_rewrite_conj_false() {
        let hs = HolSimplifier::with_rules(global_builtin_rules());
        let conj_c = hologic::conj_const();
        let false_c = hologic::false_const();
        let p = Term::free("P", Typ::dummy());
        let term = Term::app(Term::app(conj_c, false_c.clone()), p);

        let result = hs.hol_rewrite(&term);
        assert!(result.is_none(), "False ∧ P needs a closed rewrite theorem source");
    }

    #[test]
    fn test_hol_rewrite_disj_true() {
        let hs = HolSimplifier::with_rules(global_builtin_rules());
        let disj_c = hologic::disj_const();
        let true_c = hologic::true_const();
        let p = Term::free("P", Typ::dummy());
        let term = Term::app(Term::app(disj_c, true_c.clone()), p);

        let result = hs.hol_rewrite(&term);
        assert!(result.is_none(), "True ∨ P needs a closed rewrite theorem source");
    }

    #[test]
    fn test_hol_rewrite_disj_false() {
        let hs = HolSimplifier::with_rules(global_builtin_rules());
        let disj_c = hologic::disj_const();
        let false_c = hologic::false_const();
        let p = Term::free("P", Typ::dummy());
        let term = Term::app(Term::app(disj_c, false_c), p.clone());

        let result = hs.hol_rewrite(&term);
        assert!(result.is_none(), "False ∨ P needs a closed rewrite theorem source");
    }

    #[test]
    fn test_hol_rewrite_not_true() {
        let hs = HolSimplifier::with_rules(global_builtin_rules());
        let not_c = hologic::not_const();
        let true_c = hologic::true_const();
        let term = Term::app(not_c, true_c);

        let result = hs.hol_rewrite(&term);
        assert!(result.is_none(), "¬True needs a closed rewrite theorem source");
    }

    #[test]
    fn test_hol_rewrite_not_false() {
        let hs = HolSimplifier::with_rules(global_builtin_rules());
        let not_c = hologic::not_const();
        let false_c = hologic::false_const();
        let term = Term::app(not_c, false_c);

        let result = hs.hol_rewrite(&term);
        assert!(result.is_none(), "¬False needs a closed rewrite theorem source");
    }

    #[test]
    fn test_hol_rewrite_imp_true() {
        let hs = HolSimplifier::with_rules(global_builtin_rules());
        let imp_c = hologic::imp_const();
        let true_c = hologic::true_const();
        let p = Term::free("P", Typ::dummy());
        let term = Term::app(Term::app(imp_c, true_c), p.clone());

        let result = hs.hol_rewrite(&term);
        assert!(result.is_none(), "True → P needs a closed rewrite theorem source");
    }

    #[test]
    fn test_hol_rewrite_imp_false() {
        let hs = HolSimplifier::with_rules(global_builtin_rules());
        let imp_c = hologic::imp_const();
        let false_c = hologic::false_const();
        let p = Term::free("P", Typ::dummy());
        let term = Term::app(Term::app(imp_c, false_c), p);

        let result = hs.hol_rewrite(&term);
        assert!(result.is_none(), "False → P needs a closed rewrite theorem source");
    }

    #[test]
    fn test_hol_rewrite_deep_nested() {
        let hs = HolSimplifier::with_rules(global_builtin_rules());
        let conj_c = hologic::conj_const();
        let true_c = hologic::true_const();
        let false_c = hologic::false_const();
        let p = Term::free("P", Typ::dummy());

        // (True ∧ P) ∧ False  →  P ∧ False  →  False
        let inner = Term::app(Term::app(conj_c.clone(), true_c), p.clone());
        let term = Term::app(Term::app(conj_c.clone(), inner), false_c.clone());

        let result = hs.hol_rewrite_deep(&term);
        assert!(result.is_none(), "nested HOL rewrite needs closed theorem sources");
    }

    #[test]
    fn test_solver_asm_trivial_true() {
        let solver = AsmSolver;
        // t = t should be provable
        let t = Term::free("t", Typ::dummy());
        let eq_const = Term::const_(
            "HOL.eq",
            Typ::arrow(Typ::dummy(), Typ::arrow(Typ::dummy(), Typ::base("prop"))),
        );
        let goal = Term::app(Term::app(eq_const, t.clone()), t);
        let result = solver.solve(&goal, &[], HolTheoremDb::global());
        assert!(result.is_some(), "AsmSolver should prove t = t");
    }

    #[test]
    fn test_hol_simplifier_from_db() {
        let hs = HolSimplifier::from_db(crate::hol::hol_loader::HolTheoremDb::global());
        // Should have rules from DB + builtin
        let rule_count = hs.kernel.rules().len();
        assert!(rule_count > 0, "from_db should have at least some rules");
    }

    #[test]
    fn test_rewrite_all_terminates() {
        let hs = HolSimplifier::with_rules(global_builtin_rules());
        // A term that shouldn't loop
        let p = Term::free("P", Typ::base("prop"));
        let result = hs.rewrite_all(&p);
        // Should terminate without panicking
        let _ = result;
    }

    #[test]
    fn test_simp_tactic_produces_tactic() {
        let hs = HolSimplifier::with_rules(global_builtin_rules());
        let tac = hs.simp_tactic();
        // Create a simple proof state
        let true_c = hologic::true_const();
        let goal_ct = CTerm::certify(true_c);
        let state = ThmKernel::assume_compat(goal_ct);
        let results = tac(&state);
        // Tactic should not panic
        let _ = results;
    }

    #[test]
    fn test_if_true_rewrite() {
        let hs = HolSimplifier::with_rules(global_builtin_rules());
        let if_c = hologic::if_const(Typ::dummy());
        let true_c = hologic::true_const();
        let a = Term::free("a", Typ::dummy());
        let b = Term::free("b", Typ::dummy());
        let term = Term::apps(if_c, [true_c, a.clone(), b.clone()]);

        let result = hs.hol_rewrite(&term);
        assert!(result.is_none(), "if True rewrite needs a closed theorem source");
    }

    #[test]
    fn test_if_false_rewrite() {
        let hs = HolSimplifier::with_rules(global_builtin_rules());
        let if_c = hologic::if_const(Typ::dummy());
        let false_c = hologic::false_const();
        let a = Term::free("a", Typ::dummy());
        let b = Term::free("b", Typ::dummy());
        let term = Term::apps(if_c, [false_c, a.clone(), b.clone()]);

        let result = hs.hol_rewrite(&term);
        assert!(result.is_none(), "if False rewrite needs a closed theorem source");
    }

    #[test]
    fn test_all_true_rewrite() {
        let hs = HolSimplifier::with_rules(global_builtin_rules());
        let all_c = hologic::all_const(Typ::dummy());
        let true_c = hologic::true_const();
        let body = true_c.clone();
        let term = Term::app(all_c, Term::abs("x", Typ::dummy(), body));

        let result = hs.hol_rewrite(&term);
        assert!(result.is_none(), "∀x. True rewrite needs a closed theorem source");
    }

    #[test]
    fn test_ex_false_rewrite() {
        let hs = HolSimplifier::with_rules(global_builtin_rules());
        let ex_c = hologic::exists_const(Typ::dummy());
        let false_c = hologic::false_const();
        let body = false_c.clone();
        let term = Term::app(ex_c, Term::abs("x", Typ::dummy(), body));

        let result = hs.hol_rewrite(&term);
        assert!(result.is_none(), "∃x. False rewrite needs a closed theorem source");
    }

    #[test]
    fn test_non_matching_term_returns_none() {
        let hs = HolSimplifier::with_rules(global_builtin_rules());
        // A free variable shouldn't match any rule
        let p = Term::free("P", Typ::dummy());
        let result = hs.hol_rewrite(&p);
        // It might rewrite if P matches a rule LHS as a variable, but that's fine
        // The key is it doesn't panic
        let _ = result;
    }

    #[test]
    fn test_solver_registration() {
        let mut hs = HolSimplifier::new();
        assert_eq!(hs.solvers.len(), 0);
        hs.register_solver(Arc::new(ArithSolver));
        hs.register_solver(Arc::new(AsmSolver));
        assert_eq!(hs.solvers.len(), 2);
    }

    #[test]
    fn test_conditional_depth_default() {
        let hs = HolSimplifier::new();
        assert_eq!(hs.conditional_depth, 3);
    }

    #[test]
    fn test_conditional_depth_set() {
        let mut hs = HolSimplifier::new();
        hs.set_conditional_depth(5);
        assert_eq!(hs.conditional_depth, 5);
    }
}
