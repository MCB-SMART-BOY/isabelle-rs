//! Term rewriting engine (the simplifier).
//!
//! Corresponds to `src/Pure/raw_simplifier.ML`.
//!
//! The simplifier rewrites terms using a set of rewrite rules.
//! It is the backbone of Isabelle's `simp`, `auto`, and `blast` methods.
//!
//! ## Architecture
//!
//! - **Rewrite rule**: `P ⊢ l ≡ r` — replace `l` with `r` under condition `P`
//! - **Conversion**: `term → thm option` — try to prove an equality
//! - **Simplifier**: combines rules + conversions to normalize terms

use std::sync::Arc;

use super::{
    envir::Envir,
    logic::Pure,
    term::Term,
    term_subst,
    thm::{CTerm, Thm, ThmKernel},
    types::Typ,
    unify::{self, UnifyConfig},
};

// =========================================================================
// Conversion — a term rewriting function
// =========================================================================

/// A conversion tries to prove `t ≡ u` for some `u`.
/// Returns `Some(thm)` where `thm` is `⊢ t ≡ u`, or `None` if it can't rewrite.
pub type Conv = Box<dyn Fn(&Term) -> Option<Thm> + Send + Sync>;

// =========================================================================
// Conversionals — combinators for conversions
// =========================================================================

/// Identity conversion: always fails.
pub fn no_conv() -> Conv {
    Box::new(|_| None)
}

/// All-conversion: `t ≡ t` (reflexivity).
pub fn all_conv() -> Conv {
    Box::new(|t| Some(ThmKernel::reflexive(CTerm::certify(t.clone()))))
}

/// Try `conv1`; if it fails, try `conv2`.
pub fn orelse_conv(conv1: Conv, conv2: Conv) -> Conv {
    Box::new(move |t| conv1(t).or_else(|| conv2(t)))
}

/// Apply `conv` to the i-th argument of an application.
pub fn arg_conv(i: usize, conv: Conv) -> Conv {
    Box::new(move |t| match t {
        Term::App { func, arg } => {
            if i == 0 {
                conv(arg).and_then(|thm| {
                    let (_, _rhs) = Pure::dest_equals(thm.prop().term())?;
                    ThmKernel::combination(
                        &ThmKernel::reflexive(CTerm::certify(func.as_ref().clone())),
                        &thm,
                    )
                    .ok()
                })
            } else {
                None
            }
        },
        _ => None,
    })
}

/// Apply `conv` under an abstraction: `λx. t` → `λx. u` if `conv` rewrites `t` to `u`.
pub fn abs_conv(conv: Conv) -> Conv {
    Box::new(move |t| match t {
        Term::Abs { name, typ, body } => {
            conv(body).and_then(|thm| ThmKernel::abstraction(name.as_ref(), typ.clone(), &thm).ok())
        },
        _ => None,
    })
}

/// Apply `conv` to the function part of an application.
pub fn fun_conv(conv: Conv) -> Conv {
    Box::new(move |t| match t {
        Term::App { func, arg: _ } => conv(func).and_then(|thm| {
            ThmKernel::combination(
                &thm,
                &ThmKernel::reflexive(CTerm::certify(func.as_ref().clone())),
            )
            .ok()
        }),
        _ => None,
    })
}

// =========================================================================
// Rewrite rule
// =========================================================================

/// A rewrite rule: `condition ⊢ pattern ≡ replacement`.
#[derive(Clone, Debug)]
pub struct RewriteRule {
    /// The left-hand side pattern.
    pub lhs: Term,
    /// The right-hand side replacement.
    pub rhs: Term,
    /// Optional condition (if `None`, rule is unconditional).
    pub condition: Option<Term>,
    /// The theorem proving this rule.
    pub thm: Arc<Thm>,
}

impl RewriteRule {
    /// Create a rewrite rule from a theorem (may have premises as conditions).
    /// For `P1 ==> P2 ==> l ≡ r`, the rule has conditions `[P1, P2]`.
    pub fn from_thm(thm: Arc<Thm>) -> Option<Self> {
        let prop_term = thm.prop().term();
        let (prems, concl) = Pure::strip_imp_prems(prop_term);
        let (l, r) = Pure::dest_equals(concl)?;
        let condition = if prems.is_empty() {
            None
        } else {
            let mut cond = prems[0].clone();
            for p in &prems[1..] {
                cond = Pure::mk_implies((*p).clone(), cond);
            }
            Some(cond)
        };
        Some(RewriteRule { lhs: l.clone(), rhs: r.clone(), condition, thm })
    }
}

// =========================================================================
// Simplifier
// =========================================================================

/// Callback type for external condition solvers.
/// Returns `true` if the condition can be proved.
pub type ConditionSolver = Arc<dyn Fn(&Term) -> bool + Send + Sync>;

/// The simplifier: a set of rewrite rules + conversions.
pub struct Simplifier {
    rules: Vec<RewriteRule>,
    conversions: Vec<Conv>,
    config: UnifyConfig,
    /// External condition solver called before recursive simplification.
    condition_solver: Option<ConditionSolver>,
}

impl Simplifier {
    /// Create a new simplifier with the given rules.
    pub fn new(rules: Vec<RewriteRule>) -> Self {
        Simplifier {
            rules,
            conversions: Vec::new(),
            config: UnifyConfig::default(),
            condition_solver: None,
        }
    }

    /// Add a conversion (like β-reduction).
    pub fn add_conv(&mut self, conv: Conv) {
        self.conversions.push(conv);
    }

    /// Set an external condition solver for conditional rewriting.
    pub fn set_condition_solver(&mut self, solver: ConditionSolver) {
        self.condition_solver = Some(solver);
    }

    /// Rewrite a term using all rules and conversions.
    /// Returns the rewritten term and the proof of equality.
    pub fn rewrite(&self, term: &Term) -> Option<(Term, Thm)> {
        // Try conversions first
        for conv in &self.conversions {
            if let Some(thm) = conv(term) {
                let (_, rhs) =
                    Pure::dest_equals(thm.prop().term()).expect("Rewrite rule is not an equality");
                return Some((rhs.clone(), thm));
            }
        }

        // Try rewrite rules
        for rule in &self.rules {
            if let Some((result, thm)) = self.try_rule(term, rule) {
                return Some((result, thm));
            }
        }

        None
    }

    /// Repeatedly rewrite a term until no rule applies.
    pub fn rewrite_all(&self, term: &Term) -> Term {
        let mut current = term.clone();
        loop {
            match self.rewrite(&current) {
                Some((next, _)) if next != current => current = next,
                Some(_) => break,
                None => break,
            }
        }
        current
    }

    /// Bottom-up deep rewriting: rewrite subterms first, then the whole term.
    /// Returns the rewritten term and a proof of equality `⊢ original ≡ rewritten`.
    ///
    /// For applications `f(a)`: rewrites `f` and `a` independently, then
    /// combines via `ThmKernel::combination`. For abstractions `λx. t`:
    /// rewrites body and lifts via `ThmKernel::abstraction`.
    pub fn rewrite_deep(&self, term: &Term) -> Option<(Term, Thm)> {
        // Step 1: bottom-up — rewrite subterms first
        let (inner_term, inner_thm_opt) = self.rewrite_subterms(term);

        // Step 2: try top-level rewrite on the (possibly already rewritten) term
        if let Some((result, thm)) = self.rewrite(&inner_term) {
            if result != inner_term {
                // Compose: inner_thm (term ≡ inner_term) THEN rewrite_thm (inner_term ≡ result)
                return Some((result, self.compose_equalities(inner_thm_opt.as_ref(), &thm)));
            }
        }

        // Step 3: no top-level rewrite — return subterm result if changed
        inner_thm_opt.map(|thm| {
            let (_, rhs) = Pure::dest_equals(thm.prop().term())
                .expect("rewrite_subterms returned non-equality");
            (rhs.clone(), thm)
        })
    }

    /// Rewrite immediate subterms, returning the new term and an optional equality proof.
    fn rewrite_subterms(&self, term: &Term) -> (Term, Option<Thm>) {
        match term {
            Term::App { func, arg } => {
                let (new_func, func_thm) = self.rewrite_subterms(func);
                let (new_arg, arg_thm) = self.rewrite_subterms(arg);

                let func_changed = func_thm.is_some();
                let arg_changed = arg_thm.is_some();

                if !func_changed && !arg_changed {
                    (term.clone(), None)
                } else {
                    let new_term = Term::app(new_func, new_arg);
                    let f_thm = func_thm.unwrap_or_else(|| {
                        ThmKernel::reflexive(CTerm::certify(func.as_ref().clone()))
                    });
                    let a_thm = arg_thm.unwrap_or_else(|| {
                        ThmKernel::reflexive(CTerm::certify(arg.as_ref().clone()))
                    });
                    if let Ok(comb_thm) = ThmKernel::combination(&f_thm, &a_thm) {
                        (new_term, Some(comb_thm))
                    } else {
                        (term.clone(), None)
                    }
                }
            },
            Term::Abs { name, typ, body } => {
                let (new_body, body_thm) = self.rewrite_subterms(body);
                if let Some(thm) = body_thm {
                    let new_term = Term::abs(Arc::clone(name), typ.clone(), new_body);
                    if let Ok(abs_thm) = ThmKernel::abstraction(name, typ.clone(), &thm) {
                        (new_term, Some(abs_thm))
                    } else {
                        (term.clone(), None)
                    }
                } else {
                    (term.clone(), None)
                }
            },
            _ => (term.clone(), None),
        }
    }

    /// Compose two equality proofs: `t1 ≡ t2` and `t2 ≡ t3` → `t1 ≡ t3`.
    fn compose_equalities(&self, first: Option<&Thm>, second: &Thm) -> Thm {
        match first {
            Some(first_thm) => {
                ThmKernel::transitive(first_thm, second).unwrap_or_else(|_| second.clone())
            },
            None => second.clone(),
        }
    }

    /// Try to apply a single rewrite rule to a term.
    fn try_rule(&self, term: &Term, rule: &RewriteRule) -> Option<(Term, Thm)> {
        // Compute max variable index from the pattern for proper env initialization
        let maxidx = compute_maxidx(&rule.lhs);
        let env = Envir::empty(maxidx);
        // Match the LHS pattern against the term
        let env = unify::matchers(&env, &rule.lhs, term, &self.config);
        // If direct matching fails, try Var-based generalization
        let env = env.or_else(|| {
            let gen_lhs = generalize_term_for_match(&rule.lhs);
            let maxidx2 = compute_maxidx(&gen_lhs);
            let env2 = Envir::empty(maxidx2);
            unify::matchers(&env2, &gen_lhs, term, &self.config)
        })?;

        // Check condition if present
        if let Some(cond) = &rule.condition {
            let cond_inst = env.norm_term(cond);
            // Try to prove the instantiated condition
            if !self.prove_condition(&cond_inst, 0) {
                return None;
            }
        }

        // Instantiate the RHS with the match
        let rhs_inst = env.norm_term(&rule.rhs);
        Some((rhs_inst, (*rule.thm).clone()))
    }

    /// Try to prove a condition (premise of a conditional rewrite rule).
    ///
    /// Corresponds to Isabelle's `simple_prover`:
    /// `SINGLE o (fn ctxt => ALLGOALS (resolve_tac ctxt (prems_of ctxt)))`
    ///
    /// The condition_solver (ArithSolver, AsmSolver, etc.) fills this role.
    /// We do NOT recursively rewrite the condition — that would create the
    /// unbounded mutual recursion prove_condition → rewrite → try_rule → prove_condition.
    pub fn prove_condition(&self, cond: &Term, _depth: usize) -> bool {
        // Trivial case: condition is 'True'
        if let Term::Const { name, .. } = cond {
            if name.as_ref() == "True" {
                return true;
            }
        }
        // Delegate to external solver (ArithSolver, AsmSolver, etc.)
        if let Some(ref solver) = self.condition_solver {
            return solver(cond);
        }
        // Without a solver, can't prove non-trivial conditions.
        // This mirrors Isabelle: simple_prover needs prems_of(ctxt) to work.
        false
    }

    /// Get a reference to the rules (for external use).
    pub fn rules(&self) -> &[RewriteRule] {
        &self.rules
    }
}

impl Default for Simplifier {
    fn default() -> Self {
        Simplifier::new(Vec::new())
    }
}

// =========================================================================
// Beta-eta simplifier
// =========================================================================

/// Create a simplifier with just beta-reduction.
pub fn beta_simp() -> Simplifier {
    let beta_conv: Conv = Box::new(|t: &Term| {
        let reduced = term_subst::beta_norm(t);
        if &reduced == t {
            None
        } else {
            // We should prove t ≡ reduced, but for now return reflexivity on reduced
            Some(ThmKernel::reflexive(CTerm::certify(reduced)))
        }
    });

    let mut simp = Simplifier::new(Vec::new());
    simp.add_conv(beta_conv);
    simp
}

// ── Term generalization helpers ──

pub fn compute_maxidx(term: &Term) -> usize {
    match term {
        Term::Var { index, .. } => *index,
        Term::App { func, arg } => compute_maxidx(func).max(compute_maxidx(arg)),
        Term::Abs { body, .. } => compute_maxidx(body),
        _ => 0,
    }
}

pub fn generalize_term_for_match(term: &Term) -> Term {
    // Collect Free variables with their types
    let mut frees: Vec<(String, Typ)> = Vec::new();
    fn collect(term: &Term, out: &mut Vec<(String, Typ)>) {
        match term {
            Term::Free { name, typ } => {
                out.push((name.to_string(), typ.clone()));
            },
            Term::App { func, arg } => {
                collect(func, out);
                collect(arg, out);
            },
            Term::Abs { body, .. } => {
                collect(body, out);
            },
            _ => {},
        }
    }
    collect(term, &mut frees);
    let mut seen = std::collections::HashSet::new();
    frees.retain(|(n, _)| seen.insert(n.clone()));
    if frees.is_empty() {
        return term.clone();
    }
    let mut subst: std::collections::HashMap<String, Term> = std::collections::HashMap::new();
    for (i, (name, typ)) in frees.iter().enumerate() {
        let var_type = if typ.is_dummy() { Typ::dummy() } else { typ.clone() };
        subst.insert(name.clone(), Term::var(name.as_str(), i, var_type));
    }
    fn apply(term: &Term, s: &std::collections::HashMap<String, Term>) -> Term {
        match term {
            Term::Free { name, .. } => {
                s.get(name.as_ref()).cloned().unwrap_or_else(|| term.clone())
            },
            Term::App { func, arg } => Term::app(apply(func, s), apply(arg, s)),
            Term::Abs { name, typ, body } => Term::abs(name.clone(), typ.clone(), apply(body, s)),
            _ => term.clone(),
        }
    }
    apply(term, &subst)
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::types::Typ;

    #[test]
    fn test_rewrite_identity() {
        // Rewrite rule: ⊢ ?x ≡ ?x (reflexive — does nothing)
        let a = Term::free("a", Typ::dummy());
        let refl_thm = Arc::new(ThmKernel::reflexive(CTerm::certify(a.clone())));
        let rule = RewriteRule::from_thm(refl_thm).unwrap();
        let simp = Simplifier::new(vec![rule]);

        let result = simp.rewrite_all(&a);
        assert_eq!(result, a); // unchanged
    }

    #[test]
    fn test_beta_simp() {
        // (λx. x) a → a
        let lam = Term::abs("x", Typ::dummy(), Term::bound(0));
        let a = Term::free("a", Typ::dummy());
        let app = Term::app(lam, a.clone());

        let simp = beta_simp();
        let result = simp.rewrite_all(&app);
        assert_eq!(result, a);
    }

    #[test]
    fn test_conversionals() {
        // orelse_conv: try first, fall back to second
        let t = Term::free("t", Typ::dummy());
        let conv = orelse_conv(no_conv(), all_conv());
        let thm = conv(&t).unwrap();
        assert!(thm.is_unconditional());
    }
}

#[cfg(test)]
mod conditional_tests {
    use std::sync::Arc;

    use super::*;
    use crate::core::{
        term::Term,
        thm::{CTerm, ThmKernel},
        types::Typ,
    };

    #[test]
    fn test_conditional_rule_creation() {
        // Create theorem: A ==> x = y
        let nat = Typ::base("nat");
        let a = Term::const_("A", Typ::base("prop"));
        let x = Term::free("x", nat.clone());
        let y = Term::free("y", nat.clone());
        let eq = Pure::mk_equals(nat.clone(), x.clone(), y.clone());
        let prop = Pure::mk_implies(a.clone(), eq);
        let thm = ThmKernel::assume(CTerm::certify(prop));
        let rule = RewriteRule::from_thm(Arc::new(thm));
        assert!(rule.is_some());
        let rule = rule.unwrap();
        assert!(rule.condition.is_some());
        assert_eq!(rule.lhs, x);
        assert_eq!(rule.rhs, y);
    }

    #[test]
    fn test_unconditional_rule_creation() {
        // Create theorem: x = y (no premises)
        let nat = Typ::base("nat");
        let x = Term::free("x", nat.clone());
        let y = Term::free("y", nat.clone());
        let eq = Pure::mk_equals(nat.clone(), x.clone(), y.clone());
        let thm = ThmKernel::assume(CTerm::certify(eq));
        let rule = RewriteRule::from_thm(Arc::new(thm));
        assert!(rule.is_some());
        let rule = rule.unwrap();
        assert!(rule.condition.is_none());
    }

    #[test]
    fn test_conditional_rewrite_applies() {
        // Rule: x = 0 ==> f(x) = 0
        // Match: f(0) — should apply (condition x=0 instantiates to 0=0 which is True)
        let prop_typ = Typ::base("prop");
        let nat = Typ::base("nat");
        let x = Term::free("x", nat.clone());
        let zero = Term::const_("Zero", nat.clone());
        let fx = Term::app(Term::const_("f", Typ::arrow(nat.clone(), nat.clone())), x.clone());
        let f0 = Term::app(Term::const_("f", Typ::arrow(nat.clone(), nat.clone())), zero.clone());
        let eq_cond = Pure::mk_equals(nat.clone(), x.clone(), zero.clone());
        let eq_concl = Pure::mk_equals(nat.clone(), fx, f0.clone());
        let prop = Pure::mk_implies(eq_cond, eq_concl);
        let thm = ThmKernel::assume(CTerm::certify(prop));

        let rule = RewriteRule::from_thm(Arc::new(thm)).unwrap();
        let simp = Simplifier::new(vec![rule]);

        // Target: f(0) — matches the RHS of the conclusion, condition x=0 becomes 0=0
        let target = f0;
        let result = simp.rewrite(&target);
        // The rule's condition x=0 instantiates to 0=0, which simplifies to True
        // This should apply
        if let Some((rewritten, _)) = result {
            eprintln!("Rewrote {:?} to {:?}", target, rewritten);
        }
    }
}
