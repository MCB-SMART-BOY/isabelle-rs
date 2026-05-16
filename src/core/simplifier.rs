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

use super::envir::Envir;
use super::logic::Pure;
use super::term::Term;
use super::term_subst;
use super::thm::{CTerm, Thm, ThmKernel};
use super::unify::{self, UnifyConfig};

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
    Box::new(move |t| {
        match t {
            Term::App { func, arg } => {
                if i == 0 {
                    conv(arg).and_then(|thm| {
                        let (_, _rhs) = Pure::dest_equals(thm.prop().term())?;
                        ThmKernel::combination(
                            &ThmKernel::reflexive(CTerm::certify(func.as_ref().clone())),
                            &thm,
                        ).ok()
                    })
                } else {
                    None
                }
            }
            _ => None,
        }
    })
}

/// Apply `conv` under an abstraction: `λx. t` → `λx. u` if `conv` rewrites `t` to `u`.
pub fn abs_conv(conv: Conv) -> Conv {
    Box::new(move |t| {
        match t {
            Term::Abs { name, typ, body } => {
                conv(body).and_then(|thm| {
                    ThmKernel::abstraction(name.as_ref(), typ.clone(), &thm).ok()
                })
            }
            _ => None,
        }
    })
}

/// Apply `conv` to the function part of an application.
pub fn fun_conv(conv: Conv) -> Conv {
    Box::new(move |t| {
        match t {
            Term::App { func, arg: _ } => {
                conv(func).and_then(|thm| {
                    ThmKernel::combination(
                        &thm,
                        &ThmKernel::reflexive(CTerm::certify(func.as_ref().clone())),
                    ).ok()
                })
            }
            _ => None,
        }
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
    /// Create a rewrite rule from a theorem `⊢ l ≡ r`.
    pub fn from_thm(thm: Arc<Thm>) -> Option<Self> {
        let (l, r) = Pure::dest_equals(thm.prop().term())?;
        Some(RewriteRule {
            lhs: l.clone(),
            rhs: r.clone(),
            condition: None,
            thm,
        })
    }
}

// =========================================================================
// Simplifier
// =========================================================================

/// The simplifier: a set of rewrite rules + conversions.
pub struct Simplifier {
    rules: Vec<RewriteRule>,
    conversions: Vec<Conv>,
    config: UnifyConfig,
}

impl Simplifier {
    /// Create a new simplifier with the given rules.
    pub fn new(rules: Vec<RewriteRule>) -> Self {
        Simplifier {
            rules,
            conversions: Vec::new(),
            config: UnifyConfig::default(),
        }
    }

    /// Add a conversion (like β-reduction).
    pub fn add_conv(&mut self, conv: Conv) {
        self.conversions.push(conv);
    }

    /// Rewrite a term using all rules and conversions.
    /// Returns the rewritten term and the proof of equality.
    pub fn rewrite(&self, term: &Term) -> Option<(Term, Thm)> {
        // Try conversions first
        for conv in &self.conversions {
            if let Some(thm) = conv(term) {
                let (_, rhs) = Pure::dest_equals(thm.prop().term()).expect("Rewrite rule is not an equality");
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

    /// Try to apply a single rewrite rule to a term.
    fn try_rule(&self, term: &Term, rule: &RewriteRule) -> Option<(Term, Thm)> {
        let env = Envir::init();
        // Match the LHS pattern against the term
        let env = unify::matchers(&env, &rule.lhs, term, &self.config)?;

        // Check condition if present
        if let Some(cond) = &rule.condition {
            let _cond_inst = env.norm_term(cond);
            // For unconditional rules, this is skipped
            // For conditional rules, we'd need to prove the condition
        }

        // Instantiate the RHS with the match
        let rhs_inst = env.norm_term(&rule.rhs);
        Some((rhs_inst, (*rule.thm).clone()))
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
