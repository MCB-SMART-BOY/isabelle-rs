//! Isabelle theorem kernel — the LCF trusted core.
//!
//! Corresponds to `src/Pure/thm.ML`.
//!
//! ## Isabelle's LCF Philosophy
//!
//! The theorem type `Thm` is **abstract** — it has no public constructors.
//! The only way to create a `Thm` is through the primitive inference rules
//! in `ThmKernel`. This guarantees that every `Thm` is indeed a logical
//! consequence of the axioms.
//!
//! ## Key design decisions aligned with Isabelle
//!
//! 1. **Abstract type**: `Thm` fields are private; only `ThmKernel` creates them
//! 2. **Pure logic**: uses `Pure` module for `==>`, `!!`, `==`
//! 3. **Hyps as α-equivalence classes**: hypotheses are identified modulo α
//! 4. **Derivations**: theorems carry proof terms (or oracle tags)
//! 5. **Maxidx**: proper tracking for fresh variable generation

use std::fmt;

use super::error::KernelError;
use super::logic::Pure;
use super::term::Term;
use super::types::Typ;

// =========================================================================
// Certified terms (cterm) — align with Isabelle's cterm
// =========================================================================

/// A certified term — a term that has been type-checked against a theory
/// signature. In Isabelle, `cterm` is an abstract type.
///
/// For now this is a simple wrapper; the full implementation requires
/// a `Theory` context for type checking.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct CTerm {
    term: Term,
    maxidx: usize,
}

impl CTerm {
    /// Create a certified term.
    /// In the full implementation, this would verify the term against a signature.
    pub fn certify(term: Term) -> Self {
        let maxidx = Self::compute_maxidx(&term);
        CTerm { term, maxidx }
    }

    pub fn term(&self) -> &Term { &self.term }
    pub fn maxidx(&self) -> usize { self.maxidx }

    fn compute_maxidx(t: &Term) -> usize {
        let mut maxidx = 0;
        match t {
            Term::Var { index, typ, .. } => {
                maxidx = *index;
                // Also track type-level maxidx
                maxidx = usize::max(maxidx, typ.maxidx());
            }
            Term::Const { typ, .. } | Term::Free { typ, .. } => {
                maxidx = typ.maxidx();
            }
            Term::Abs { typ, body, .. } => {
                maxidx = usize::max(typ.maxidx(), Self::compute_maxidx(body));
            }
            Term::App { func, arg } => {
                maxidx = usize::max(Self::compute_maxidx(func), Self::compute_maxidx(arg));
            }
            Term::Bound(_) => {}
        }
        maxidx
    }
}

impl fmt::Debug for CTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CTerm({:?})", self.term)
    }
}

// =========================================================================
// Hypotheses — α-equivalence classes
// =========================================================================

/// A set of hypotheses (assumptions).
///
/// In Isabelle, hypotheses are identified modulo α-equivalence.
/// Two hypotheses that differ only in bound variable names are the same.
#[derive(Clone, PartialEq, Eq)]
pub struct Hyps {
    entries: Vec<CTerm>,
}

impl Hyps {
    pub fn empty() -> Self { Hyps { entries: Vec::new() } }

    pub fn singleton(h: CTerm) -> Self {
        Hyps { entries: vec![h] }
    }

    pub fn insert(&mut self, h: CTerm) {
        // Check α-equivalence against existing hypotheses
        if !self.contains(&h) {
            self.entries.push(h);
        }
    }

    /// Check if a hypothesis is already present (modulo α-equivalence).
    pub fn contains(&self, h: &CTerm) -> bool {
        self.entries.iter().any(|existing| Self::alpha_eq(existing.term(), h.term()))
    }

    pub fn len(&self) -> usize { self.entries.len() }
    pub fn is_empty(&self) -> bool { self.entries.is_empty() }
    pub fn iter(&self) -> impl Iterator<Item = &CTerm> { self.entries.iter() }

    /// Union: H1 ∪ H2.
    pub fn union(&self, other: &Hyps) -> Hyps {
        let mut result = self.clone();
        for h in &other.entries {
            result.insert(h.clone());
        }
        result
    }

    /// Remove a hypothesis.
    pub fn remove(&self, h: &CTerm) -> Hyps {
        Hyps {
            entries: self
                .entries
                .iter()
                .filter(|existing| !Self::alpha_eq(existing.term(), h.term()))
                .cloned()
                .collect(),
        }
    }

    /// α-equivalence check for terms.
    ///
    /// Two terms are α-equivalent if they are equal modulo bound variable renaming.
    /// This is a simplified structural comparison; a full implementation would
    /// use de Bruijn normalization or nominal techniques.
    fn alpha_eq(a: &Term, b: &Term) -> bool {
        match (a, b) {
            (Term::Const { name: n1, .. }, Term::Const { name: n2, .. }) => n1 == n2,
            (Term::Free { name: n1, .. }, Term::Free { name: n2, .. }) => n1 == n2,
            (Term::Var { name: n1, index: i1, .. }, Term::Var { name: n2, index: i2, .. }) =>
                n1 == n2 && i1 == i2,
            (Term::Bound(i1), Term::Bound(i2)) => i1 == i2,
            (Term::Abs { body: b1, .. }, Term::Abs { body: b2, .. }) =>
                Self::alpha_eq(b1, b2), // de Bruijn: bodies must match
            (Term::App { func: f1, arg: a1 }, Term::App { func: f2, arg: a2 }) =>
                Self::alpha_eq(f1, f2) && Self::alpha_eq(a1, a2),
            _ => false,
        }
    }
}

impl fmt::Debug for Hyps {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, h) in self.entries.iter().enumerate() {
            if i > 0 { write!(f, ", ")?; }
            write!(f, "{:?}", h.term())?;
        }
        write!(f, "]")
    }
}

// =========================================================================
// Derivation — the proof record
// =========================================================================

/// A derivation records how a theorem was proved.
///
/// In Isabelle's `proofterm.ML`, every theorem carries a derivation object
/// that can be replayed for proof checking.
///
/// - `Oracle`: the theorem came from an external source (tagged as untrusted)
/// - `Axiom`: a primitive inference rule with no premises
/// - `Rule`: a primitive inference rule applied to premises
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Derivation {
    Oracle { name: String, prop: CTerm },
    Axiom { name: &'static str },
    Rule { name: &'static str, premises: Vec<ThmDeriv> },
}

/// A reference to a premise theorem's derivation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThmDeriv {
    pub serial: u64,
    pub prop: CTerm,
}

// =========================================================================
// Thm — the abstract theorem type
// =========================================================================

/// A **theorem**: `Γ ⊢ φ` where Γ are hypotheses and φ is the conclusion.
///
/// This is the central type of the LCF trusted kernel.
/// **No public constructors** — use `ThmKernel` to create theorems.
#[derive(Clone, PartialEq, Eq)]
pub struct Thm {
    hyps: Hyps,
    prop: CTerm,
    maxidx: usize,
    derivation: Derivation,
    serial: u64,
}

impl Thm {
    pub fn hyps(&self) -> &Hyps { &self.hyps }
    pub fn prop(&self) -> &CTerm { &self.prop }
    pub fn maxidx(&self) -> usize { self.maxidx }
    pub fn is_unconditional(&self) -> bool { self.hyps.is_empty() }
    pub fn has_oracles(&self) -> bool { matches!(self.derivation, Derivation::Oracle { .. }) }
    pub fn serial(&self) -> u64 { self.serial }

    /// Number of subgoals (premises in the prop chain).
    pub fn nprems(&self) -> usize {
        Pure::count_prems(self.prop.term())
    }

    /// Get the i-th subgoal (0-indexed).
    pub fn prem(&self, i: usize) -> Option<Term> {
        Pure::nth_premise(self.prop.term(), i).cloned()
    }

    /// Get the main conclusion (after stripping all ==>-chain premises).
    pub fn concl(&self) -> Term {
        Pure::strip_imp_prems(self.prop.term()).1.clone()
    }
}

impl fmt::Debug for Thm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let hyps: Vec<String> = self.hyps.iter().map(|h| format!("{:?}", h.term())).collect();
        if hyps.is_empty() {
            write!(f, "⊢ {:?}", self.prop.term())
        } else {
            write!(f, "{} ⊢ {:?}", hyps.join(", "), self.prop.term())
        }
    }
}

impl fmt::Display for Thm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

// =========================================================================
// ThmKernel — the ONLY way to create Thm values
// =========================================================================

static NEXT_SERIAL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn new_serial() -> u64 {
    NEXT_SERIAL.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

/// The trusted kernel.
///
/// Every function here implements one primitive inference rule
/// of Isabelle/Pure. These functions MUST be correct — any bug
/// could allow proving `False`.
pub struct ThmKernel;

impl ThmKernel {
    // =================================================================
    // Primitive: assume
    // =================================================================

    /// **Assume** `ct`: `{ct} ⊢ ct`.
    ///
    /// ```text
    /// —————— (assume)
    /// A ⊢ A
    /// ```
    pub fn assume(ct: CTerm) -> Thm {
        Thm {
            hyps: Hyps::singleton(ct.clone()),
            prop: ct.clone(),
            maxidx: ct.maxidx(),
            derivation: Derivation::Axiom { name: "assume" },
            serial: new_serial(),
        }
    }

    // =================================================================
    // Primitive: reflexive
    // =================================================================

    /// **Reflexivity**: `⊢ t ≡ t`.
    ///
    /// The equality uses `Pure.eq` with the appropriate type.
    ///
    /// ```text
    /// —————— (reflexive)
    /// ⊢ t ≡ t
    /// ```
    pub fn reflexive(ct: CTerm) -> Thm {
        let t = ct.term().clone();
        // Infer the type of t (in full impl, this would come from the signature)
        let eq_term = Pure::mk_equals(Typ::dummy(), t.clone(), t);

        Thm {
            hyps: Hyps::empty(),
            prop: CTerm::certify(eq_term),
            maxidx: ct.maxidx(),
            derivation: Derivation::Axiom { name: "reflexive" },
            serial: new_serial(),
        }
    }

    // =================================================================
    // Primitive: symmetric
    // =================================================================

    /// **Symmetry**: `Γ ⊢ t ≡ u  ⟹  Γ ⊢ u ≡ t`.
    pub fn symmetric(thm: &Thm) -> Result<Thm, KernelError> {
        let (t, u) = Pure::dest_equals(thm.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm.prop.term().clone()))?;

        let new_prop = CTerm::certify(
            Pure::mk_equals(Typ::dummy(), u.clone(), t.clone())
        );

        Ok(Thm {
            hyps: thm.hyps.clone(),
            prop: new_prop,
            maxidx: thm.maxidx,
            derivation: Derivation::Rule {
                name: "symmetric",
                premises: vec![ThmDeriv { serial: thm.serial, prop: thm.prop.clone() }],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: transitive
    // =================================================================

    /// **Transitivity**: `Γ ⊢ t ≡ u` and `Δ ⊢ u ≡ v` ⟹ `Γ ∪ Δ ⊢ t ≡ v`.
    pub fn transitive(thm1: &Thm, thm2: &Thm) -> Result<Thm, KernelError> {
        let (t, u1) = Pure::dest_equals(thm1.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm1.prop.term().clone()))?;
        let (u2, v) = Pure::dest_equals(thm2.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm2.prop.term().clone()))?;

        // In Isabelle, the middle terms must be α-equivalent
        if !Hyps::alpha_eq(u1, u2) {
            return Err(KernelError::MidTermsNotEquiv);
        }

        let new_prop = CTerm::certify(
            Pure::mk_equals(Typ::dummy(), t.clone(), v.clone())
        );

        Ok(Thm {
            hyps: thm1.hyps.union(&thm2.hyps),
            prop: new_prop,
            maxidx: usize::max(thm1.maxidx, thm2.maxidx),
            derivation: Derivation::Rule {
                name: "transitive",
                premises: vec![
                    ThmDeriv { serial: thm1.serial, prop: thm1.prop.clone() },
                    ThmDeriv { serial: thm2.serial, prop: thm2.prop.clone() },
                ],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: combination
    // =================================================================

    /// **Combination**: `Γ ⊢ f ≡ g` and `Δ ⊢ x ≡ y` ⟹ `Γ ∪ Δ ⊢ f x ≡ g y`.
    pub fn combination(thm_f: &Thm, thm_x: &Thm) -> Result<Thm, KernelError> {
        let (f, g) = Pure::dest_equals(thm_f.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm_f.prop.term().clone()))?;
        let (x, y) = Pure::dest_equals(thm_x.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm_x.prop.term().clone()))?;

        let new_prop = CTerm::certify(
            Pure::mk_equals(
                Typ::dummy(),
                Term::app(f.clone(), x.clone()),
                Term::app(g.clone(), y.clone()),
            )
        );

        Ok(Thm {
            hyps: thm_f.hyps.union(&thm_x.hyps),
            prop: new_prop,
            maxidx: usize::max(thm_f.maxidx, thm_x.maxidx),
            derivation: Derivation::Rule {
                name: "combination",
                premises: vec![
                    ThmDeriv { serial: thm_f.serial, prop: thm_f.prop.clone() },
                    ThmDeriv { serial: thm_x.serial, prop: thm_x.prop.clone() },
                ],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: abstraction
    // =================================================================

    /// **Abstraction**: `Γ ⊢ t ≡ u` ⟹ `Γ ⊢ (λx. t) ≡ (λx. u)`.
    ///
    /// Side condition: `x` must not be free in `Γ`.
    pub fn abstraction(x_name: &str, x_typ: Typ, thm: &Thm) -> Result<Thm, KernelError> {
        let (t, u) = Pure::dest_equals(thm.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm.prop.term().clone()))?;

        // Side condition: x must not be free in the hypotheses
        for hyp in thm.hyps.iter() {
            if free_in(x_name, hyp.term()) {
                return Err(KernelError::FreeVarInHypotheses { name: x_name.to_string() });
            }
        }

        let new_prop = CTerm::certify(
            Pure::mk_equals(
                Typ::dummy(),
                Term::abs(x_name, x_typ.clone(), t.clone()),
                Term::abs(x_name, x_typ, u.clone()),
            )
        );

        Ok(Thm {
            hyps: thm.hyps.clone(),
            prop: new_prop,
            maxidx: thm.maxidx,
            derivation: Derivation::Rule {
                name: "abstraction",
                premises: vec![ThmDeriv { serial: thm.serial, prop: thm.prop.clone() }],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: beta conversion
    // =================================================================

    /// **Beta conversion**: `⊢ (λx. t) x ≡ t`.
    pub fn beta_conversion(ct: CTerm) -> Result<Thm, KernelError> {
        // ct should be of the form (λx. t) x
        let (abs, _arg) = match ct.term() {
            Term::App { func, arg } => (func.as_ref(), arg.as_ref()),
            _ => return Err(KernelError::BetaConversion("not an application".into())),
        };

        let body = match abs {
            Term::Abs { body, .. } => body.as_ref().clone(),
            _ => return Err(KernelError::BetaConversion("not a lambda".into())),
        };

        let new_prop = CTerm::certify(
            Pure::mk_equals(Typ::dummy(), ct.term().clone(), body)
        );

        Ok(Thm {
            hyps: Hyps::empty(),
            prop: new_prop,
            maxidx: ct.maxidx(),
            derivation: Derivation::Axiom { name: "beta_conversion" },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: implies introduction (discharge)
    // =================================================================

    /// **Implication introduction**:
    /// `Γ ∪ {A} ⊢ B` ⟹ `Γ ⊢ A ==> B`.
    pub fn implies_intr(assumption: &CTerm, thm: &Thm) -> Result<Thm, KernelError> {
        if !thm.hyps.contains(assumption) {
            return Err(KernelError::HypothesisNotFound);
        }

        let new_prop = CTerm::certify(
            Pure::mk_implies(assumption.term().clone(), thm.prop.term().clone())
        );

        Ok(Thm {
            hyps: thm.hyps.remove(assumption),
            prop: new_prop,
            maxidx: thm.maxidx,
            derivation: Derivation::Rule {
                name: "implies_intr",
                premises: vec![ThmDeriv { serial: thm.serial, prop: thm.prop.clone() }],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: implies elimination (modus ponens)
    // =================================================================

    /// **Implication elimination** (modus ponens):
    /// `Γ ⊢ A ==> B` and `Δ ⊢ A` ⟹ `Γ ∪ Δ ⊢ B`.
    pub fn implies_elim(thm_imp: &Thm, thm_a: &Thm) -> Result<Thm, KernelError> {
        let (a, b) = Pure::dest_implies(thm_imp.prop.term())
            .ok_or_else(|| KernelError::NotImplication(thm_imp.prop.term().clone()))?;

        if !Hyps::alpha_eq(a, thm_a.prop.term()) {
            return Err(KernelError::AntecedentMismatch);
        }

        Ok(Thm {
            hyps: thm_imp.hyps.union(&thm_a.hyps),
            prop: CTerm::certify(b.clone()),
            maxidx: usize::max(thm_imp.maxidx, thm_a.maxidx),
            derivation: Derivation::Rule {
                name: "implies_elim",
                premises: vec![
                    ThmDeriv { serial: thm_imp.serial, prop: thm_imp.prop.clone() },
                    ThmDeriv { serial: thm_a.serial, prop: thm_a.prop.clone() },
                ],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive rules: forall_intr and forall_elim
    // =================================================================

    pub fn forall_intr(x_name: &str, x_typ: Typ, thm: &Thm) -> Result<Thm, KernelError> {
        for hyp in thm.hyps.iter() {
            if free_in(x_name, hyp.term()) {
                return Err(KernelError::FreeVarInHypotheses { name: x_name.to_string() });
            }
        }
        let all_term = Pure::mk_all(x_name, x_typ.clone(), thm.prop.term().clone());
        Ok(Thm {
            hyps: thm.hyps.clone(),
            prop: CTerm::certify(all_term),
            maxidx: thm.maxidx,
            derivation: Derivation::Rule {
                name: "forall_intr",
                premises: vec![ThmDeriv { serial: thm.serial, prop: thm.prop.clone() }],
            },
            serial: new_serial(),
        })
    }

    pub fn forall_elim(ct: CTerm, thm: &Thm) -> Result<Thm, KernelError> {
        let (_, p_body) = Pure::dest_all(thm.prop.term())
            .ok_or_else(|| KernelError::NotForall(thm.prop.term().clone()))?;
        let instantiated = super::term_subst::subst_bounds(&[ct.term().clone()], p_body);
        Ok(Thm {
            hyps: thm.hyps.clone(),
            prop: CTerm::certify(instantiated),
            maxidx: usize::max(thm.maxidx, ct.maxidx()),
            derivation: Derivation::Rule {
                name: "forall_elim",
                premises: vec![ThmDeriv { serial: thm.serial, prop: thm.prop.clone() }],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: instantiate
    // =================================================================

    /// Apply an environment (from unification) to instantiate a theorem.
    ///
    /// If `Γ ⊢ φ` is a theorem schema (with schematic variables), then
    /// for any substitution `θ`, `Γθ ⊢ φθ` is also a theorem.
    pub fn instantiate(env: &super::envir::Envir, thm: &Thm) -> Thm {
        let mut new_hyps = Hyps::empty();
        for h in thm.hyps.iter() {
            new_hyps.insert(CTerm::certify(env.norm_term(h.term())));
        }
        Thm {
            hyps: new_hyps,
            prop: CTerm::certify(env.norm_term(thm.prop.term())),
            maxidx: usize::max(thm.maxidx, env.maxidx()),
            derivation: Derivation::Rule {
                name: "instantiate",
                premises: vec![ThmDeriv {
                    serial: thm.serial,
                    prop: thm.prop.clone(),
                }],
            },
            serial: new_serial(),
        }
    }

    // =================================================================
    // Primitive: bicompose — the core resolution operation
    // =================================================================

    /// Compose `thm1` with `thm2` at position `i`.
    ///
    /// `thm1`: `[| H1; ...; Hm |] ==> A`
    /// `thm2`: `[| G1; ...; Gi; ...; Gn |] ==> C`
    ///
    /// If `match_flag` is true and `A` unifies with `Gi`, or if `match_flag`
    /// is false and `A` is α-equivalent to `Gi`, then:
    ///
    /// `[| G1;...;Gi-1; H1;...;Hm; Gi+1;...;Gn |]`
    ///   `==> G1 ==> ... ==> Gi-1 ==> H1 ==> ... ==> Hm ==> Gi+1 ==> ... ==> Gn ==> C`
    ///
    /// This is the single core operation behind ALL tactics (assume_tac,
    /// resolve_tac, eresolve_tac, ...).
    pub fn bicompose(
        match_flag: bool,
        thm1: &Thm,
        thm2: &Thm,
        i: usize,
    ) -> Option<Thm> {
        // 1. Get the i-th premise of thm2 (0-indexed)
        let prem_i = Pure::nth_premise(thm2.prop.term(), i)?;

        // 2. Get thm1's conclusion (last element after stripping all ==>-premises)
        let (_, concl_1) = Pure::strip_imp_prems(thm1.prop.term());

        // 3. Match or unify
        let (env, full_match) = if match_flag {
            let maxidx = usize::max(thm1.maxidx(), thm2.maxidx());
            let env = super::envir::Envir::empty(maxidx);
            (super::unify::matchers(
                &env,
                concl_1,
                prem_i,
                &super::unify::UnifyConfig::default(),
            )?, false)
        } else {
            if Hyps::alpha_eq(thm1.prop.term(), prem_i) {
                (super::envir::Envir::init(), true)   // full match — assume_tac
            } else if Hyps::alpha_eq(concl_1, prem_i) {
                (super::envir::Envir::init(), false)  // conclusion match — resolve_tac
            } else {
                return None;
            }
        };

        // 4. Instantiate both theorems with the unifier
        let thm1 = Self::instantiate(&env, thm1);
        let thm2 = Self::instantiate(&env, thm2);

        // 5. Build the result: replace thm2's i-th premise with thm1's premise chain
        let prems_1: Vec<Term> = if full_match {
            // Full match: entire subgoal is a hypothesis — no new premises
            Vec::new()
        } else {
            let (p, _) = Pure::strip_imp_prems(thm1.prop.term());
            p.iter().cloned().cloned().collect()
        };
        let (prems_2, concl_2) = Pure::strip_imp_prems(thm2.prop.term());

        let mut new_prems: Vec<Term> = Vec::new();
        new_prems.extend(prems_2[..i].iter().cloned().cloned());
        new_prems.extend(prems_1.iter().cloned());
        new_prems.extend(prems_2[i + 1..].iter().cloned().cloned());

        let mut new_prop = concl_2.clone();
        for p in new_prems.iter().rev() {
            new_prop = Pure::mk_implies(p.clone(), new_prop);
        }

        Some(Thm {
            hyps: thm1.hyps.union(&thm2.hyps),
            prop: CTerm::certify(new_prop),
            maxidx: usize::max(thm1.maxidx, thm2.maxidx),
            derivation: Derivation::Rule {
                name: "bicompose",
                premises: vec![
                    ThmDeriv { serial: thm1.serial, prop: thm1.prop.clone() },
                    ThmDeriv { serial: thm2.serial, prop: thm2.prop.clone() },
                ],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: subst_premise — replace a premise using an equality
    // =================================================================

    /// Replace the i-th premise of `state` using an equality theorem.
    ///
    /// If `eq_thm` proves `t == u` and the i-th premise of `state` is
    /// α-equivalent to `t`, replace it with `u`.
    ///
    /// Soundness: by substitutivity of equality, if `t == u` and `Γ, t ⊢ C`,
    /// then `Γ, u ⊢ C`.
    pub fn subst_premise(eq_thm: &Thm, state: &Thm, i: usize) -> Option<Thm> {
        let (t, u) = Pure::dest_equals(eq_thm.prop.term())?;
        let prem_i = Pure::nth_premise(state.prop.term(), i)?;
        if !Hyps::alpha_eq(t, prem_i) {
            return None;
        }

        let (prems, concl) = Pure::strip_imp_prems(state.prop.term());
        let mut new_prems: Vec<Term> = prems.iter().cloned().cloned().collect();
        new_prems[i] = u.clone();

        let mut new_prop = concl.clone();
        for p in new_prems.iter().rev() {
            new_prop = Pure::mk_implies(p.clone(), new_prop);
        }

        Some(Thm {
            hyps: state.hyps.union(&eq_thm.hyps),
            prop: CTerm::certify(new_prop),
            maxidx: usize::max(state.maxidx, eq_thm.maxidx),
            derivation: Derivation::Rule {
                name: "subst_premise",
                premises: vec![
                    ThmDeriv { serial: eq_thm.serial, prop: eq_thm.prop.clone() },
                    ThmDeriv { serial: state.serial, prop: state.prop.clone() },
                ],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: bicompose_eresolve — resolution with hypothesis elimination
    // =================================================================

    /// Like `bicompose`, but also consumes a matching hypothesis.
    ///
    /// `thm1`: `[| H; G1; ...; Gm |] ==> A`  (H is the "major premise")
    /// `thm2`: goal state with subgoal `i` matching `A`
    ///
    /// If `match_flag` is true, unifies `A` with subgoal `i` and `H` with
    /// some hypothesis of `thm2`. Then replaces subgoal `i` with `G1...Gm`
    /// (excluding `H`) and keeps the consumed hypothesis in hyps.
    ///
    /// This is the kernel implementation of `eresolve_tac`.
    pub fn bicompose_eresolve(
        match_flag: bool,
        thm1: &Thm,
        thm2: &Thm,
        i: usize,
    ) -> Option<Thm> {
        // 1. Get the i-th premise of thm2 and thm1's conclusion
        let prem_i = Pure::nth_premise(thm2.prop.term(), i)?;
        let (prems_1, concl_1) = Pure::strip_imp_prems(thm1.prop.term());

        // thm1 must have at least one premise (the major premise to consume)
        let major_prem = prems_1.first()?;
        let _rest_prems = &prems_1[1..];

        // 2. Unify major premise with some hypothesis of thm2
        let env = if match_flag {
            let maxidx = usize::max(thm1.maxidx(), thm2.maxidx());
            let mut found_env = None;
            for hyp in thm2.hyps.iter() {
                let env = super::envir::Envir::empty(maxidx);
                let pairs: Vec<(Term, Term)> = vec![
                    ((*major_prem).clone(), hyp.term().clone()),
                    ((*concl_1).clone(), prem_i.clone()),
                ];
                if let Some(env) = super::unify::unifiers(
                    &env, &pairs, &super::unify::UnifyConfig::default()
                ) {
                    found_env = Some(env);
                    break;
                }
            }
            found_env?
        } else {
            // Exact match with two-tier support
            let hyp_matches = thm2.hyps.iter().any(|h| Hyps::alpha_eq(major_prem, h.term()));
            if !hyp_matches {
                return None;
            }
            if !Hyps::alpha_eq(thm1.prop.term(), prem_i) 
                && !Hyps::alpha_eq(concl_1, prem_i) {
                return None;
            }
            super::envir::Envir::init()
        };

        // 3. Instantiate both theorems
        let thm1 = Self::instantiate(&env, thm1);
        let thm2 = Self::instantiate(&env, thm2);

        // 4. Build result: thm2's i-th premise replaced by thm1's REST premises (excluding major)
        let (prems_1_inst, _) = Pure::strip_imp_prems(thm1.prop.term());
        let rest_prems_inst: Vec<Term> = if prems_1_inst.is_empty() {
            Vec::new()
        } else {
            prems_1_inst[1..].iter().cloned().cloned().collect()
        };
        let (prems_2, concl_2) = Pure::strip_imp_prems(thm2.prop.term());

        let mut new_prems: Vec<Term> = Vec::new();
        new_prems.extend(prems_2[..i].iter().cloned().cloned());
        new_prems.extend(rest_prems_inst.iter().cloned());
        new_prems.extend(prems_2[i + 1..].iter().cloned().cloned());

        let mut new_prop = concl_2.clone();
        for p in new_prems.iter().rev() {
            new_prop = Pure::mk_implies(p.clone(), new_prop);
        }

        Some(Thm {
            hyps: thm1.hyps.union(&thm2.hyps),
            prop: CTerm::certify(new_prop),
            maxidx: usize::max(thm1.maxidx, thm2.maxidx),
            derivation: Derivation::Rule {
                name: "bicompose_eresolve",
                premises: vec![
                    ThmDeriv { serial: thm1.serial, prop: thm1.prop.clone() },
                    ThmDeriv { serial: thm2.serial, prop: thm2.prop.clone() },
                ],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Derived rule: A ==> A  (identity)
    // =================================================================

    pub fn trivial(ct: CTerm) -> Result<Thm, KernelError> {
        let assumed = ThmKernel::assume(ct.clone());
        ThmKernel::implies_intr(&ct, &assumed)
    }
}

fn free_in(var_name: &str, term: &Term) -> bool {
    match term {
        Term::Free { name, .. } => name.as_ref() == var_name,
        Term::Const { .. } | Term::Bound(_) | Term::Var { .. } => false,
        Term::Abs { body, .. } => free_in(var_name, body),
        Term::App { func, arg } => free_in(var_name, func) || free_in(var_name, arg),
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::envir::Envir;
    use crate::core::types::Symbol;

    fn prop(name: &str) -> CTerm {
        CTerm::certify(Term::const_(name, Typ::base("prop")))
    }

    #[test]
    fn test_assume() {
        let a = prop("A");
        let thm = ThmKernel::assume(a.clone());
        assert_eq!(thm.hyps().len(), 1);
        assert_eq!(thm.prop(), &a);
    }

    #[test]
    fn test_trivial() {
        let a = prop("A");
        let thm = ThmKernel::trivial(a).unwrap();
        assert!(thm.is_unconditional());
        let (x, y) = Pure::dest_implies(thm.prop.term()).expect("Not an implication");
        assert_eq!(x, &Term::const_("A", Typ::base("prop")));
        assert_eq!(y, &Term::const_("A", Typ::base("prop")));
    }

    #[test]
    fn test_reflexive() {
        let t = CTerm::certify(Term::const_("t", Typ::dummy()));
        let thm = ThmKernel::reflexive(t);
        assert!(thm.is_unconditional());
    }

    #[test]
    fn test_alpha_equivalence() {
        let t1 = Term::abs("x", Typ::dummy(), Term::bound(0));
        let t2 = Term::abs("y", Typ::dummy(), Term::bound(0));
        assert_ne!(t1, t2);
        assert!(Hyps::alpha_eq(&t1, &t2));
    }

    // =================================================================
    // Tests for new kernel infrastructure
    // =================================================================

    #[test]
    fn test_nprems_prem_concl() {
        // trivial: [A] ==> A → 1 subgoal (A), conclusion = A
        let a = prop("A");
        let thm = ThmKernel::trivial(a.clone()).unwrap();
        assert_eq!(thm.nprems(), 1);
        assert_eq!(thm.prem(0), Some(a.term().clone()));
        assert_eq!(thm.concl(), a.term().clone());
    }

    #[test]
    fn test_nprems_multiple() {
        // assume(A ==> B): hyps={A==>B}, prop=A==>B → 1 subgoal (A), concl = B
        let a = prop("A");
        let b = prop("B");
        let imp = Pure::mk_implies(a.term().clone(), b.term().clone());
        let thm = ThmKernel::assume(CTerm::certify(imp));
        assert_eq!(thm.nprems(), 1);  // A is the only premise
        assert_eq!(thm.concl(), b.term().clone());  // B is the conclusion
    }

    #[test]
    fn test_instantiate_idempotent() {
        let a = prop("A");
        let thm = ThmKernel::assume(a.clone());
        let env = Envir::init();
        let result = ThmKernel::instantiate(&env, &thm);
        assert_eq!(result.prop(), thm.prop());
        assert_eq!(result.hyps().len(), thm.hyps().len());
    }

    #[test]
    fn test_bicompose_assume_tac() {
        // Simulate assume_tac: use assume(A) to discharge first subgoal
        // state: [A] ==> A  (trivial goal)
        // assume(A): [A] ⊢ A
        // Result should have 0 premises (A discharged)
        let a = prop("A");
        let state = ThmKernel::trivial(a.clone()).unwrap();
        let assume_a = ThmKernel::assume(a.clone());
        let result = ThmKernel::bicompose(false, &assume_a, &state, 0);
        assert!(result.is_some());
        assert_eq!(result.unwrap().nprems(), 0);
    }

    #[test]
    fn test_bicompose_resolve() {
        // Simulate resolve_tac with modus ponens:
        // thm: [B ==> A] ⊢ B ==> A
        // state: [A ==> C] ⊢ A ==> C
        // Result should be: [B ==> A, B] ⊢ B ==> C  (A replaced by B)
        let a = prop("A");
        let b = prop("B");
        let c = prop("C");
        let thm = ThmKernel::assume(CTerm::certify(
            Pure::mk_implies(b.term().clone(), a.term().clone())
        ));
        let state = ThmKernel::assume(CTerm::certify(
            Pure::mk_implies(a.term().clone(), c.term().clone())
        ));
        let result = ThmKernel::bicompose(false, &thm, &state, 0);
        assert!(result.is_some());
        let r = result.unwrap();
        // First premise should be B (from thm's premises)
        assert!(Hyps::alpha_eq(&r.prem(0).unwrap(), b.term()));
    }

    #[test]
    fn test_beta_conversion_ok() {
        // (λx. x) A → A
        let lam = Term::abs("x", Typ::dummy(), Term::bound(0));
        let a = Term::free("a", Typ::dummy());
        let app = CTerm::certify(Term::app(lam, a.clone()));
        let result = ThmKernel::beta_conversion(app);
        assert!(result.is_ok());
    }

    #[test]
    fn test_beta_conversion_err() {
        // Non-application should return Err, not panic
        let t = CTerm::certify(Term::const_("x", Typ::dummy()));
        let result = ThmKernel::beta_conversion(t);
        assert!(result.is_err());
        match result {
            Err(KernelError::BetaConversion(_)) => {} // expected
            _ => panic!("expected BetaConversion error"),
        }
    }

    #[test]
    fn test_instantiate_with_unifier() {
        // Test instantiate with a non-empty environment
        let mut env = Envir::empty(10);
        let x_name: Symbol = "x".into();
        let nat = Typ::base("nat");
        let zero = Term::const_("zero", nat.clone());
        env.update(x_name.clone(), 0, nat.clone(), zero.clone());

        let var_term = Term::var("x", 0, nat);
        let thm = ThmKernel::assume(CTerm::certify(var_term));
        let result = ThmKernel::instantiate(&env, &thm);
        // The var should be replaced by zero
        assert_eq!(result.prop().term(), &zero);
    }
}
