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
    thm::{CTerm, Thm, ThmKernel, ThmTrust},
    types::{Typ, TypeEnv},
    unify::{self, UnifyConfig},
};

// =========================================================================
// Conversion — a term rewriting function
// =========================================================================

/// A conversion tries to prove `t ≡ u` for some `u`.
/// Returns `Some(thm)` where `thm` is `⊢ t ≡ u`, or `None` if it can't rewrite.
pub type Conv = Arc<dyn Fn(&Term) -> Option<Thm> + Send + Sync>;

// =========================================================================
// Conversionals — combinators for conversions
// =========================================================================

/// Identity conversion: always fails.
pub fn no_conv() -> Conv {
    Arc::new(|_| None)
}

/// All-conversion: `t ≡ t` (reflexivity).
pub fn all_conv() -> Conv {
    Arc::new(|t| Some(ThmKernel::reflexive_compat(CTerm::certify(t.clone()))))
}

/// Try `conv1`; if it fails, try `conv2`.
pub fn orelse_conv(conv1: Conv, conv2: Conv) -> Conv {
    Arc::new(move |t| conv1(t).or_else(|| conv2(t)))
}

/// Apply `conv` to the i-th argument of an application.
pub fn arg_conv(i: usize, conv: Conv) -> Conv {
    Arc::new(move |term| {
        let Term::App { func, arg } = term else { return None };
        if i != 0 {
            return None;
        }
        let rewritten = conv(arg)?;
        equality_endpoint(&rewritten, arg)?;
        let proof = ThmKernel::combination(&reflexive_for(func)?, &rewritten).ok()?;
        equality_endpoint(&proof, term)?;
        Some(proof)
    })
}

/// Apply `conv` under an abstraction without capturing another free variable.
pub fn abs_conv(conv: Conv) -> Conv {
    Arc::new(move |term| {
        let Term::Abs { name, typ, body } = term else { return None };
        lift_abstraction(term, name, typ, body, &[], |opened| {
            let proof = conv(opened)?;
            equality_endpoint(&proof, opened)?;
            Some(proof)
        })
    })
}

/// Apply `conv` to the function part of an application.
pub fn fun_conv(conv: Conv) -> Conv {
    Arc::new(move |term| {
        let Term::App { func, arg } = term else { return None };
        let rewritten = conv(func)?;
        equality_endpoint(&rewritten, func)?;
        let proof = ThmKernel::combination(&rewritten, &reflexive_for(arg)?).ok()?;
        equality_endpoint(&proof, term)?;
        Some(proof)
    })
}

/// Compare exact endpoints modulo display-only abstraction binder names.
pub(crate) fn same_endpoint(left: &Term, right: &Term) -> bool {
    match (left, right) {
        (Term::Abs { typ: lt, body: lb, .. }, Term::Abs { typ: rt, body: rb, .. }) => {
            lt == rt && same_endpoint(lb, rb)
        },
        (Term::App { func: lf, arg: la }, Term::App { func: rf, arg: ra }) => {
            same_endpoint(lf, rf) && same_endpoint(la, ra)
        },
        _ => left == right,
    }
}

/// Return the proven right endpoint only for a closed, exact equality.
pub(crate) fn equality_endpoint<'a>(proof: &'a Thm, expected: &Term) -> Option<&'a Term> {
    if !RewriteRule::is_closed_unconditional_source(proof) {
        return None;
    }
    let (left, right) = Pure::dest_equals(proof.prop().term())?;
    same_endpoint(left, expected).then_some(right)
}

pub(crate) fn compose_rewrite_equalities(
    original: &Term,
    middle: &Term,
    first: Option<&Thm>,
    second: &Thm,
) -> Option<Thm> {
    equality_endpoint(second, middle)?;
    let proof = match first {
        Some(first) => {
            same_endpoint(equality_endpoint(first, original)?, middle).then_some(())?;
            ThmKernel::transitive(first, second).ok()?
        },
        None => same_endpoint(original, middle).then(|| second.clone())?,
    };
    equality_endpoint(&proof, original)?;
    Some(proof)
}

fn reflexive_for(term: &Term) -> Option<Thm> {
    let checked = CTerm::certify_checked(term.clone(), &TypeEnv::new());
    Some(match checked {
        Ok(ct) => ThmKernel::reflexive(ct).ok()?,
        Err(_) => ThmKernel::reflexive_compat(CTerm::certify(term.clone())),
    })
}

fn contains_free_name(term: &Term, candidate: &str) -> bool {
    match term {
        Term::Free { name, .. } => name.as_ref() == candidate,
        Term::App { func, arg } => {
            contains_free_name(func, candidate) || contains_free_name(arg, candidate)
        },
        Term::Abs { body, .. } => contains_free_name(body, candidate),
        _ => false,
    }
}

fn lift_abstraction(
    original: &Term,
    name: &str,
    typ: &Typ,
    body: &Term,
    rules: &[RewriteRule],
    rewrite_opened: impl FnOnce(&Term) -> Option<Thm>,
) -> Option<Thm> {
    let fresh = (0..).map(|i| format!("_simp_bound_{i}")).find(|candidate| {
        !contains_free_name(original, candidate)
            && rules.iter().all(|rule| {
                !contains_free_name(&rule.lhs, candidate)
                    && !contains_free_name(&rule.rhs, candidate)
                    && !contains_free_name(rule.thm.prop().term(), candidate)
            })
    })?;
    let opened = term_subst::subst_bounds(&[Term::free(fresh.as_str(), typ.clone())], body);
    let proof = rewrite_opened(&opened)?;
    equality_endpoint(&proof, &opened)?;
    let lifted = ThmKernel::abstraction(&fresh, typ.clone(), &proof).ok()?;
    equality_endpoint(&lifted, &Term::abs(name, typ.clone(), body.clone()))?;
    Some(lifted)
}

// =========================================================================
// Rewrite rule
// =========================================================================

/// A rewrite rule: closed unconditional `pattern ≡ replacement`.
///
/// Conditional rewriting is future work. The current simplifier must not treat
/// theorem hypotheses or Pure premises as silently solved rewrite conditions.
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
    /// Create a rewrite rule from a closed unconditional theorem.
    ///
    /// V1 deliberately rejects theorem hypotheses, oracle/admitted footprints,
    /// unresolved tpairs, and Pure premises (`P ==> l ≡ r`). Without a
    /// conditional-rewrite proof path, accepting those theorems would let simp
    /// import unknown hypotheses into proof results.
    pub fn from_thm(thm: Arc<Thm>) -> Option<Self> {
        if !Self::is_closed_unconditional_source(&thm) {
            return None;
        }
        let prop_term = thm.prop().term();
        let (prems, concl) = Pure::strip_imp_prems(prop_term);
        if !prems.is_empty() {
            return None;
        }
        let (l, r) = Pure::dest_equals(concl)?;
        Some(RewriteRule { lhs: l.clone(), rhs: r.clone(), condition: None, thm })
    }

    fn is_closed_unconditional_source(thm: &Thm) -> bool {
        thm.hyps().is_empty()
            && thm.oracles().is_empty()
            && thm.tpairs().is_empty()
            && thm.nprems() == 0
            && thm.trust_status() != ThmTrust::Admitted
    }
}

/// Instantiate the theorem itself, never the cached RHS in isolation.
pub(crate) fn instantiate_rewrite_rule(
    term: &Term,
    rule: &RewriteRule,
    config: &UnifyConfig,
) -> Option<(Term, Thm)> {
    if rule.condition.is_some() || !RewriteRule::is_closed_unconditional_source(&rule.thm) {
        return None;
    }
    let (source_left, source_right) = Pure::dest_equals(rule.thm.prop().term())?;
    let source = if same_endpoint(source_left, &rule.lhs) && same_endpoint(source_right, &rule.rhs)
    {
        rule.thm.as_ref().clone()
    } else if same_endpoint(source_left, &rule.rhs) && same_endpoint(source_right, &rule.lhs) {
        ThmKernel::symmetric(&rule.thm).ok()?
    } else {
        return None;
    };
    let env = unify::matchers(&Envir::empty(compute_maxidx(&rule.lhs)), &rule.lhs, term, config)?;
    let instantiated = ThmKernel::instantiate_checked(&env, &source).ok()?;
    let result = equality_endpoint(&instantiated, term)?.clone();
    Some((result, instantiated))
}

// =========================================================================
// Simplifier
// =========================================================================

/// Search hint for condition solvers. A Boolean hint is not a theorem and
/// therefore never authorizes a conditional rewrite certificate.
pub type ConditionSolver = Arc<dyn Fn(&Term) -> bool + Send + Sync>;

/// The simplifier: a set of rewrite rules + conversions.
#[derive(Clone)]
pub struct Simplifier {
    rules: Vec<RewriteRule>,
    conversions: Vec<Conv>,
    config: UnifyConfig,
    /// Legacy search hint, not consulted by the certified rewrite path.
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
        for conv in &self.conversions {
            if let Some(thm) = conv(term)
                && let Some(rhs) = equality_endpoint(&thm, term)
            {
                return Some((rhs.clone(), thm));
            }
        }
        self.rules.iter().find_map(|rule| instantiate_rewrite_rule(term, rule, &self.config))
    }

    /// Maximum rewrite depth (aligned with Isabelle's simp_depth_limit = 40).
    const MAX_REWRITE_DEPTH: usize = 40;

    /// Repeatedly rewrite a term until no rule applies.
    pub fn rewrite_all(&self, term: &Term) -> Term {
        let mut current = term.clone();
        for _ in 0..Self::MAX_REWRITE_DEPTH {
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
        self.rewrite_deep_at(term, 0)
    }

    fn rewrite_deep_at(&self, term: &Term, depth: usize) -> Option<(Term, Thm)> {
        if depth > Self::MAX_REWRITE_DEPTH {
            return None;
        }
        let inner = self.rewrite_subterms(term, depth);
        let middle = inner.as_ref().map_or(term, |(next, _)| next);
        let outer = self.rewrite(middle).filter(|(next, _)| !same_endpoint(next, middle));
        let proof = match (inner.as_ref(), outer.as_ref()) {
            (Some((next, first)), Some((_, second))) => {
                compose_rewrite_equalities(term, next, Some(first), second)?
            },
            (Some((_, first)), None) => first.clone(),
            (None, Some((_, second))) => second.clone(),
            (None, None) => return None,
        };
        let final_term = equality_endpoint(&proof, term)?.clone();
        Some((final_term, proof))
    }

    fn rewrite_subterms(&self, term: &Term, depth: usize) -> Option<(Term, Thm)> {
        if depth >= Self::MAX_REWRITE_DEPTH {
            return None;
        }
        let proof = match term {
            Term::App { func, arg } => {
                let rewritten_func = self.rewrite_deep_at(func, depth + 1);
                let rewritten_arg = self.rewrite_deep_at(arg, depth + 1);
                if rewritten_func.is_none() && rewritten_arg.is_none() {
                    return None;
                }
                let func_proof = match rewritten_func {
                    Some((_, thm)) => thm,
                    None => reflexive_for(func)?,
                };
                let arg_proof = match rewritten_arg {
                    Some((_, thm)) => thm,
                    None => reflexive_for(arg)?,
                };
                equality_endpoint(&func_proof, func)?;
                equality_endpoint(&arg_proof, arg)?;
                ThmKernel::combination(&func_proof, &arg_proof).ok()?
            },
            Term::Abs { name, typ, body } => {
                lift_abstraction(term, name, typ, body, &self.rules, |opened| {
                    self.rewrite_deep_at(opened, depth + 1).map(|(_, proof)| proof)
                })?
            },
            _ => return None,
        };
        Some((equality_endpoint(&proof, term)?.clone(), proof))
    }

    /// Legacy condition search hint; never discharges a rewrite rule premise.
    /// Rewriting requires an actual unconditional equality theorem instead.
    pub fn prove_condition(&self, cond: &Term, _depth: usize) -> bool {
        // Trivial case: condition is 'True'
        if let Term::Const { name, .. } = cond
            && name.as_ref() == "True"
        {
            return true;
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

/// Create a simplifier with just kernel-certified beta reduction.
pub fn beta_simp() -> Simplifier {
    let beta_conv: Conv = Arc::new(|term: &Term| {
        let Term::App { func, .. } = term else { return None };
        if !matches!(func.as_ref(), Term::Abs { .. }) {
            return None;
        }
        let ct = CTerm::certify_checked(term.clone(), &TypeEnv::new())
            .unwrap_or_else(|_| CTerm::certify(term.clone()));
        ThmKernel::beta_conversion(ct).ok()
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
        let refl_thm = Arc::new(ThmKernel::reflexive_compat(CTerm::certify(a.clone())));
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

    #[test]
    fn compose_rewrite_equalities_mismatched_middle_rejects_certificate() {
        let ty = Typ::base("prop");
        let x = Term::free("x", ty.clone());
        let y = Term::free("y", ty);
        let first =
            ThmKernel::reflexive(CTerm::certify_checked(x.clone(), &TypeEnv::new()).unwrap())
                .unwrap();
        let wrong_second =
            ThmKernel::reflexive(CTerm::certify_checked(y, &TypeEnv::new()).unwrap()).unwrap();
        assert!(compose_rewrite_equalities(&x, &x, Some(&first), &wrong_second).is_none());
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
    fn rewrite_rule_rejects_conditional_rule_in_v1() {
        // Create theorem: A ==> x = y. Conditional rewriting is not supported
        // yet because the current simplifier cannot turn A into a checked
        // residual subgoal.
        let nat = Typ::base("nat");
        let a = Term::const_("A", Typ::base("prop"));
        let x = Term::free("x", nat.clone());
        let y = Term::free("y", nat.clone());
        let eq = Pure::mk_equals(nat.clone(), x.clone(), y.clone());
        let prop = Pure::mk_implies(a.clone(), eq);
        let thm = ThmKernel::assume_compat(CTerm::certify(prop));
        let rule = RewriteRule::from_thm(Arc::new(thm));
        assert!(rule.is_none());
    }

    #[test]
    fn test_unconditional_rule_creation() {
        // Create closed theorem: x = x (no theorem hyps, no prop premises).
        let nat = Typ::base("nat");
        let x = Term::free("x", nat.clone());
        let thm = ThmKernel::reflexive_compat(CTerm::certify(x.clone()));
        let rule = RewriteRule::from_thm(Arc::new(thm));
        assert!(rule.is_some());
        let rule = rule.unwrap();
        assert!(rule.condition.is_none());
        assert_eq!(rule.lhs, x);
        assert_eq!(rule.rhs, rule.lhs);
    }

    #[test]
    fn rewrite_rule_rejects_theorem_with_hyps() {
        let nat = Typ::base("nat");
        let x = Term::free("x", nat.clone());
        let y = Term::free("y", nat.clone());
        let eq = Pure::mk_equals(nat.clone(), x, y);
        let thm = ThmKernel::assume_compat(CTerm::certify(eq));

        let rule = RewriteRule::from_thm(Arc::new(thm));

        assert!(rule.is_none());
    }

    #[test]
    fn rewrite_rule_rejects_oracle_or_admitted_theorem() {
        let nat = Typ::base("nat");
        let x = Term::free("x", nat.clone());
        let y = Term::free("y", nat.clone());
        let eq = Pure::mk_equals(nat.clone(), x, y);
        let thm = ThmKernel::admit(CTerm::certify(eq), "admitted:proof_engine_failed");

        let rule = RewriteRule::from_thm(Arc::new(thm));

        assert!(rule.is_none());
    }

    #[test]
    fn rewrite_rule_rejects_unresolved_tpairs() {
        let nat = Typ::base("nat");
        let x = Term::free("x", nat.clone());
        let thm = ThmKernel::reflexive_compat(CTerm::certify(x))
            .with_test_tpair(Term::var("u", 0, nat.clone()), Term::var("v", 0, nat));

        let rule = RewriteRule::from_thm(Arc::new(thm));

        assert!(rule.is_none());
    }

    #[test]
    fn simp_does_not_import_rule_hyps_into_result() {
        let nat = Typ::base("nat");
        let x = Term::free("x", nat.clone());
        let y = Term::free("y", nat.clone());
        let open_eq =
            ThmKernel::assume_compat(CTerm::certify(Pure::mk_equals(nat.clone(), x.clone(), y)));
        let rules: Vec<RewriteRule> =
            [Arc::new(open_eq)].into_iter().filter_map(RewriteRule::from_thm).collect();
        let simp = Simplifier::new(rules);

        let result = simp.rewrite_deep(&x);

        assert!(result.is_none());
    }

    #[test]
    fn simp_skips_conditional_rule_in_v1() {
        let nat = Typ::base("nat");
        let a = Term::const_("A", Typ::base("prop"));
        let x = Term::free("x", nat.clone());
        let y = Term::free("y", nat.clone());
        let prop = Pure::mk_implies(a, Pure::mk_equals(nat.clone(), x.clone(), y));
        let conditional = ThmKernel::assume_compat(CTerm::certify(prop));
        let rules: Vec<RewriteRule> =
            [Arc::new(conditional)].into_iter().filter_map(RewriteRule::from_thm).collect();
        let simp = Simplifier::new(rules);

        let result = simp.rewrite_deep(&x);

        assert!(result.is_none());
    }
}
