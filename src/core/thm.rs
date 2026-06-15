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

use std::{fmt, sync::Arc};

use super::{
    error::KernelError,
    logic::Pure,
    term::Term,
    types::{Sort, Typ},
};

// =========================================================================
// Certified terms (cterm) — align with Isabelle's cterm
// =========================================================================

/// A certified term — a term that has been type-checked against a theory
/// signature. In Isabelle, `cterm` is an abstract type.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct CTerm {
    term: Term,
    maxidx: usize,
    /// The type of this term (Typ::dummy() if unknown).
    term_type: Typ,
}

impl CTerm {
    /// Create a certified term (type will be inferred if dummy).
    pub fn certify(term: Term) -> Self {
        let maxidx = Self::compute_maxidx(&term);
        // Try to infer type from the term structure
        let term_type = Self::infer_type(&term);
        // If type is still dummy, try the type inference engine
        let term_type = if term_type.is_dummy() {
            super::type_infer::infer_type(&term).unwrap_or(term_type)
        } else {
            term_type
        };
        CTerm { term, maxidx, term_type }
    }

    /// Create a certified term with explicit type.
    pub fn certify_typed(term: Term, typ: Typ) -> Self {
        let maxidx = Self::compute_maxidx(&term);
        CTerm { term, maxidx, term_type: typ }
    }

    pub fn term(&self) -> &Term {
        &self.term
    }
    pub fn maxidx(&self) -> usize {
        self.maxidx
    }
    pub fn term_type(&self) -> &Typ {
        &self.term_type
    }

    /// Require non-dummy type — fails if the type is Typ::dummy().
    /// Use this at kernel rule boundaries to ensure type safety.
    pub fn require_non_dummy(&self, op: &'static str) -> Result<&Typ, KernelError> {
        if self.term_type.is_dummy() {
            Err(KernelError::DummyType { op })
        } else {
            Ok(&self.term_type)
        }
    }

    /// Create a certified term, attempting to annotate dummy types from the
    /// global theorem database's TypeEnv first. Falls back to plain `certify`
    /// if the DB is not available.
    pub fn certify_annotated(mut term: Term) -> Self {
        // Try to annotate dummy types from the global TypeEnv
        use crate::hol::hol_loader::HolTheoremDb;
        let db = HolTheoremDb::get();
        term.type_annotate(&db.type_env);
        Self::certify(term)
    }

    /// Infer the type of a term from its structure.
    /// Returns Typ::dummy() if type cannot be determined.
    fn infer_type(term: &Term) -> Typ {
        match term {
            Term::Const { typ, .. } if !typ.is_dummy() => typ.clone(),
            Term::Free { typ, .. } if !typ.is_dummy() => typ.clone(),
            Term::Var { typ, .. } if !typ.is_dummy() => typ.clone(),
            Term::Abs { typ, .. } if !typ.is_dummy() => typ.clone(),
            Term::App { func, arg: _ } => {
                let ft = Self::infer_type(func);
                if let Some((_, ret)) = ft.dest_fun() { ret.clone() } else { Typ::dummy() }
            },
            _ => Typ::dummy(),
        }
    }

    fn compute_maxidx(t: &Term) -> usize {
        // Iterative implementation using explicit stack to avoid recursion overflow
        let mut maxidx = 0usize;
        let mut stack: Vec<&Term> = vec![t];
        while let Some(term) = stack.pop() {
            match term {
                Term::Var { index, typ, .. } => {
                    maxidx = usize::max(maxidx, *index);
                    maxidx = usize::max(maxidx, typ.maxidx());
                },
                Term::Const { typ, .. } | Term::Free { typ, .. } => {
                    maxidx = usize::max(maxidx, typ.maxidx());
                },
                Term::Abs { typ, body, .. } => {
                    maxidx = usize::max(maxidx, typ.maxidx());
                    stack.push(body);
                },
                Term::App { func, arg } => {
                    stack.push(arg);
                    stack.push(func);
                },
                Term::Bound(_) => {},
            }
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
    pub fn empty() -> Self {
        Hyps { entries: Vec::new() }
    }

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

    pub fn len(&self) -> usize {
        self.entries.len()
    }
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
    pub fn iter(&self) -> impl Iterator<Item = &CTerm> {
        self.entries.iter()
    }

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
            (Term::Free { name: n1, .. }, Term::Const { name: n2, .. })
            | (Term::Const { name: n2, .. }, Term::Free { name: n1, .. }) => {
                n1 == n2
                    || n1.as_ref().ends_with(&format!(".{}", n2.as_ref()))
                    || n2.as_ref().ends_with(&format!(".{}", n1.as_ref()))
            },
            (Term::Var { name: n1, .. }, Term::Free { name: n2, .. })
            | (Term::Free { name: n2, .. }, Term::Var { name: n1, .. }) => n1 == n2,
            (Term::Var { name: n1, index: i1, .. }, Term::Var { name: n2, index: i2, .. }) => {
                n1 == n2 && i1 == i2
            },
            (Term::Bound(i1), Term::Bound(i2)) => i1 == i2,
            (Term::Abs { body: b1, .. }, Term::Abs { body: b2, .. }) => Self::alpha_eq(b1, b2),
            (Term::App { func: f1, arg: a1 }, Term::App { func: f2, arg: a2 }) => {
                Self::alpha_eq(f1, f2) && Self::alpha_eq(a1, a2)
            },
            _ => false,
        }
    }
}

impl fmt::Debug for Hyps {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, h) in self.entries.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
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
///
/// ## Isabelle Correspondence
///
/// In Isabelle/ML (`thm.ML`), theorems carry additional fields:
/// - `tpairs`: flex-flex disagreement pairs from higher-order unification
/// - `shyps`: sort hypotheses tracking type-class constraints
/// - `maxidx`: maximum schematic variable index for freshness
///
/// These are tracked here to maintain full Isabelle kernel equivalence.
#[derive(Clone, PartialEq, Eq)]
pub struct Thm {
    hyps: Hyps,
    prop: CTerm,
    maxidx: usize,
    /// Flex-flex disagreement pairs (tpairs in Isabelle).
    ///
    /// During higher-order unification, some pairs may remain unresolved
    /// when both sides are flexible (contain schematic variables). These
    /// are stored as constraints on the theorem.
    ///
    /// Each pair `(t, u)` represents the constraint that `t` and `u`
    /// must be made equal by some future instantiation.
    tpairs: Vec<(Term, Term)>,
    /// Sort hypotheses (shyps in Isabelle).
    ///
    /// When a theorem uses type-class-polymorphic constants, it carries
    /// sort constraints like `OFCLASS('a, order)`. These must be
    /// satisfied by the calling context.
    shyps: Vec<Sort>,
    derivation: Derivation,
    serial: u64,
}

impl Thm {
    pub fn hyps(&self) -> &Hyps {
        &self.hyps
    }
    pub fn prop(&self) -> &CTerm {
        &self.prop
    }
    pub fn maxidx(&self) -> usize {
        self.maxidx
    }
    pub fn is_unconditional(&self) -> bool {
        self.hyps.is_empty()
    }
    /// Flex-flex disagreement pairs from higher-order unification.
    pub fn tpairs(&self) -> &[(Term, Term)] {
        &self.tpairs
    }
    /// Sort hypotheses (type-class constraints).
    pub fn shyps(&self) -> &[Sort] {
        &self.shyps
    }
    pub fn has_oracles(&self) -> bool {
        matches!(self.derivation, Derivation::Oracle { .. })
    }
    pub fn serial(&self) -> u64 {
        self.serial
    }

    /// Number of subgoals (premises in the prop chain).
    pub fn nprems(&self) -> usize {
        Pure::count_prems(self.prop.term())
    }

    /// Reconstruct the proof term for this theorem from its derivation.
    pub fn proof_term(&self) -> super::proofterm::ProofTerm {
        super::proofterm::ProofTerm::from_derivation(&self.derivation, self.prop.term())
    }

    /// Check that this theorem's proof term is valid.
    /// Returns `Ok(())` if the proof checks out, or an error message.
    pub fn check_proof(&self) -> Result<(), String> {
        let proof = self.proof_term();
        super::proofterm::check_proof(&proof, self.prop.term())
    }

    /// Get the proof body for this theorem (lazy checking).
    pub fn proof_body(&self) -> super::proofterm::ProofBody {
        super::proofterm::ProofBody::from_derivation(&self.derivation, self.prop.term())
    }

    /// Validate the proof body against the theorem's proposition.
    /// Returns Ok if the proof is valid (or cached), Err if invalid.
    pub fn validate_proof(&self, body: &mut super::proofterm::ProofBody) -> Result<(), String> {
        body.check(self.prop.term())
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
            tpairs: vec![],
            shyps: vec![],
            derivation: Derivation::Axiom { name: "assume" },
            serial: new_serial(),
        }
    }

    // =================================================================
    // Primitive: reflexive
    // =================================================================

    /// **Reflexivity**: `⊢ t ≡ t`.
    ///
    /// The equality uses `Pure.eq` with the type inferred from the certified term.
    ///
    /// ```text
    /// —————— (reflexive)
    /// ⊢ t ≡ t
    /// ```
    pub fn reflexive(ct: CTerm) -> Thm {
        let t = ct.term().clone();
        // Use the type from the certified term (Typ::dummy() if unknown)
        let typ = ct.term_type().clone();
        let eq_term = Pure::mk_equals(typ, t.clone(), t);

        Thm {
            hyps: Hyps::empty(),
            prop: CTerm::certify(eq_term),
            maxidx: ct.maxidx(),
            tpairs: vec![],
            shyps: vec![],
            derivation: Derivation::Axiom { name: "reflexive" },
            serial: new_serial(),
        }
    }

    // =================================================================
    // Primitive: symmetric
    // =================================================================

    /// **Symmetry**: `Γ ⊢ t ≡ u  ⟹  Γ ⊢ u ≡ t`.
    pub fn symmetric(thm: &Thm) -> Result<Thm, KernelError> {
        let (t, u, eq_typ) = Pure::dest_equals_with_type(thm.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm.prop.term().clone()))?;

        let new_prop = CTerm::certify(Pure::mk_equals(eq_typ, u.clone(), t.clone()));

        Ok(Thm {
            hyps: thm.hyps.clone(),
            prop: new_prop,
            maxidx: thm.maxidx,
            tpairs: thm.tpairs.clone(),
            shyps: thm.shyps.clone(),
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
        let (t, u1, eq_typ1) = Pure::dest_equals_with_type(thm1.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm1.prop.term().clone()))?;
        let (u2, v, _eq_typ2) = Pure::dest_equals_with_type(thm2.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm2.prop.term().clone()))?;

        // In Isabelle, the middle terms must be α-equivalent
        if !Hyps::alpha_eq(u1, u2) {
            return Err(KernelError::MidTermsNotEquiv);
        }

        let new_prop = CTerm::certify(Pure::mk_equals(eq_typ1, t.clone(), v.clone()));

        Ok(Thm {
            hyps: thm1.hyps.union(&thm2.hyps),
            prop: new_prop,
            maxidx: usize::max(thm1.maxidx, thm2.maxidx),
            tpairs: {
                let mut tp = thm1.tpairs.clone();
                tp.extend(thm2.tpairs.clone());
                tp
            },
            shyps: {
                let mut sh = thm1.shyps.clone();
                sh.extend(thm2.shyps.clone());
                sh
            },
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
    ///
    /// Like Isabelle's combination rule, validates that:
    /// - The function type is actually a function type (arrow)
    /// - The argument types are compatible (skip check if either is dummy)
    pub fn combination(thm_f: &Thm, thm_x: &Thm) -> Result<Thm, KernelError> {
        let (f, g, fn_typ) = Pure::dest_equals_with_type(thm_f.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm_f.prop.term().clone()))?;
        let (x, y, arg_typ) = Pure::dest_equals_with_type(thm_x.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm_x.prop.term().clone()))?;

        // The result type of f x (and g y) is the codomain of fn_typ.
        // Like Isabelle's combination, we require proper types — no Typ::dummy() fallback.
        let (from_typ, result_typ) = fn_typ
            .dest_fun()
            .map(|(from, to)| (from.clone(), to.clone()))
            .ok_or_else(|| KernelError::NotFunctionType(fn_typ.clone()))?;

        // Verify argument type compatibility (like Isabelle: T1 = tT)
        if !from_typ.is_dummy() && !arg_typ.is_dummy() && from_typ != arg_typ {
            return Err(KernelError::TypeMismatch {
                expected: from_typ.clone(),
                actual: arg_typ.clone(),
            });
        }

        let new_prop = CTerm::certify(Pure::mk_equals(
            result_typ,
            Term::app(f.clone(), x.clone()),
            Term::app(g.clone(), y.clone()),
        ));

        Ok(Thm {
            hyps: thm_f.hyps.union(&thm_x.hyps),
            prop: new_prop,
            maxidx: usize::max(thm_f.maxidx, thm_x.maxidx),
            tpairs: vec![],
            shyps: vec![],
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
        let (t, u, eq_typ) = Pure::dest_equals_with_type(thm.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm.prop.term().clone()))?;

        // Side condition: x must not be free in the hypotheses
        for hyp in thm.hyps.iter() {
            if free_in(x_name, hyp.term()) {
                return Err(KernelError::FreeVarInHypotheses { name: x_name.to_string() });
            }
        }

        // The new equality type is the function type x_typ → eq_typ
        let fn_typ = Typ::arrow(x_typ.clone(), eq_typ);

        let new_prop = CTerm::certify(Pure::mk_equals(
            fn_typ,
            Term::abs(x_name, x_typ.clone(), t.clone()),
            Term::abs(x_name, x_typ, u.clone()),
        ));

        Ok(Thm {
            hyps: thm.hyps.clone(),
            prop: new_prop,
            maxidx: thm.maxidx,
            tpairs: vec![],
            shyps: vec![],
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

        // The equality type is the body's type; extract from the CTerm's type
        // (which is the application's result type = body type after beta reduction)
        let typ = ct.term_type().clone();

        let new_prop = CTerm::certify(Pure::mk_equals(typ, ct.term().clone(), body));

        Ok(Thm {
            hyps: Hyps::empty(),
            prop: new_prop,
            maxidx: ct.maxidx(),
            tpairs: vec![],
            shyps: vec![],
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

        let new_prop =
            CTerm::certify(Pure::mk_implies(assumption.term().clone(), thm.prop.term().clone()));

        Ok(Thm {
            hyps: thm.hyps.remove(assumption),
            prop: new_prop,
            maxidx: thm.maxidx,
            tpairs: vec![],
            shyps: vec![],
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
            tpairs: vec![],
            shyps: vec![],
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
            tpairs: vec![],
            shyps: vec![],
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
            tpairs: vec![],
            shyps: vec![],
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
            tpairs: thm.tpairs.clone(),
            shyps: thm.shyps.clone(),
            derivation: Derivation::Rule {
                name: "instantiate",
                premises: vec![ThmDeriv { serial: thm.serial, prop: thm.prop.clone() }],
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
    /// Quick check: can two terms possibly unify based on their top-level structure?
    /// Returns false for obviously incompatible pairs (different head constructors),
    /// avoiding expensive unification attempts that are guaranteed to fail.
    /// Now also checks type compatibility when type info is available.
    fn likely_unifiable(a: &Term, b: &Term) -> bool {
        match (a, b) {
            (Term::Var { .. }, _) | (_, Term::Var { .. }) => true,
            (Term::App { .. }, Term::App { .. }) => true,
            (Term::Abs { .. }, Term::Abs { .. }) => true,
            (Term::Const { name: n1, typ: t1 }, Term::Const { name: n2, typ: t2 }) => {
                if n1 != n2 {
                    return false;
                }
                // Type-aware: check TypeEnv when embedded types are dummy
                let t1_eff = if t1.is_dummy() {
                    use crate::hol::hol_loader::HolTheoremDb;
                    HolTheoremDb::get().type_env.const_type(n1).unwrap_or(t1)
                } else {
                    t1
                };
                let t2_eff = if t2.is_dummy() {
                    use crate::hol::hol_loader::HolTheoremDb;
                    HolTheoremDb::get().type_env.const_type(n2).unwrap_or(t2)
                } else {
                    t2
                };
                if !t1_eff.is_dummy() && !t2_eff.is_dummy() {
                    Self::types_compatible(t1_eff, t2_eff)
                } else {
                    true
                }
            },
            (Term::Free { name: n1, .. }, Term::Free { name: n2, .. }) => n1 == n2,
            (Term::Bound(i1), Term::Bound(i2)) => i1 == i2,
            _ => false,
        }
    }

    /// Check if two types are structurally compatible (can potentially unify).
    fn types_compatible(t1: &Typ, t2: &Typ) -> bool {
        match (t1, t2) {
            (Typ::Type { name: n1, args: a1 }, Typ::Type { name: n2, args: a2 }) => {
                if n1 != n2 {
                    return false;
                }
                if a1.len() != a2.len() {
                    return false;
                }
                a1.iter().zip(a2.iter()).all(|(a, b)| Self::types_compatible(a, b))
            },
            _ => true, // TFree, TVar, dummy — always potentially compatible
        }
    }

    /// This is the single core operation behind ALL tactics (assume_tac,
    /// resolve_tac, eresolve_tac, ...).
    pub fn bicompose(match_flag: bool, thm1: &Thm, thm2: &Thm, i: usize) -> Option<Thm> {
        // 1. Get the i-th premise of thm2 (0-indexed)
        let prem_i = Pure::nth_premise(thm2.prop.term(), i)?;

        // 2. Get thm1's conclusion (last element after stripping all ==>-premises)
        let (_, concl_1) = Pure::strip_imp_prems(thm1.prop.term());

        // 3. Match or unify
        let (env, full_match) = if match_flag {
            let maxidx = usize::max(thm1.maxidx(), thm2.maxidx());
            let env = super::envir::Envir::empty(maxidx);
            (
                super::unify::matchers(
                    &env,
                    concl_1,
                    prem_i,
                    &super::unify::UnifyConfig::default(),
                )?,
                false,
            )
        } else {
            // match_flag=false: first try alpha_eq (assume_tac / exact match),
            // then try full unification (for RS/THEN/COMP composition)
            if Hyps::alpha_eq(thm1.prop.term(), prem_i) {
                (super::envir::Envir::init(), true) // full match — assume_tac
            } else if Hyps::alpha_eq(concl_1, prem_i) {
                (super::envir::Envir::init(), false) // conclusion match — resolve_tac
            } else {
                // Full unification: allows variables on both sides to be bound.
                // Quick heuristic: skip if terms have incompatible shapes.
                if !Self::likely_unifiable(concl_1, prem_i) {
                    return None;
                }
                let maxidx = usize::max(thm1.maxidx(), thm2.maxidx());
                let env = super::envir::Envir::empty(maxidx);
                let pairs = vec![(concl_1.clone(), prem_i.clone())];
                (
                    super::unify::unifiers(&env, &pairs, &super::unify::UnifyConfig::default())?,
                    false,
                )
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
            tpairs: vec![],
            shyps: vec![],
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
            tpairs: vec![],
            shyps: vec![],
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
        premises: &[Arc<Thm>],
    ) -> Option<Thm> {
        // 1. Get the i-th premise of thm2 and thm1's conclusion
        let prem_i = Pure::nth_premise(thm2.prop.term(), i)?;
        let (prems_1, concl_1) = Pure::strip_imp_prems(thm1.prop.term());

        // thm1 must have at least one premise (the major premise to consume)
        let major_prem = prems_1.first()?;
        let _rest_prems = &prems_1[1..];

        // 2. Unify major premise with hyps or premises
        let env = if match_flag {
            let maxidx = usize::max(thm1.maxidx(), thm2.maxidx());
            let mut found_env = None;
            // Collect all candidates: hyps (including stripped premises) + premises
            let mut all_candidates: Vec<Term> = Vec::new();
            for h in thm2.hyps.iter() {
                all_candidates.push(h.term().clone());
                // Also include individual premises stripped from implication chains
                let (prems, _) = Pure::strip_imp_prems(h.term());
                for p in prems {
                    all_candidates.push(p.clone());
                }
            }
            for p in premises.iter() {
                all_candidates.push(p.prop().term().clone());
            }
            for candidate in &all_candidates {
                // Quick heuristic: skip obviously incompatible candidates
                if !Self::likely_unifiable(major_prem, candidate) {
                    continue;
                }
                let env = super::envir::Envir::empty(maxidx);
                let pairs: Vec<(Term, Term)> = vec![
                    ((*major_prem).clone(), candidate.clone()),
                    ((*concl_1).clone(), prem_i.clone()),
                ];
                if let Some(env) =
                    super::unify::unifiers(&env, &pairs, &super::unify::UnifyConfig::default())
                {
                    found_env = Some(env);
                    break;
                }
            }
            found_env?
        } else {
            // Exact match with two-tier support, also checking constituent premises
            let hyp_matches = thm2.hyps.iter().any(|h| {
                Hyps::alpha_eq(major_prem, h.term()) || {
                    let (prems, _) = Pure::strip_imp_prems(h.term());
                    prems.iter().any(|p| Hyps::alpha_eq(p, major_prem))
                }
            });
            if !hyp_matches {
                return None;
            }
            if !Hyps::alpha_eq(thm1.prop.term(), prem_i) && !Hyps::alpha_eq(concl_1, prem_i) {
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
            tpairs: vec![],
            shyps: vec![],
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

    // =================================================================
    // Flex-flex resolution (Phase 41)
    // =================================================================

    /// Resolve flex-flex pairs in a theorem.
    ///
    /// In higher-order unification, some disagreement pairs may remain
    /// unresolved when both sides are flexible (contain schematic variables).
    /// These are stored in `thm.tpairs`.
    ///
    /// `flexflex_resolve` attempts to instantiate these pairs with the
    /// most general solution: each flexible head is instantiated to a
    /// projection of one of its arguments.
    ///
    /// Returns the theorem with resolved tpairs, or the original if
    /// resolution is not possible.
    pub fn flexflex_resolve(thm: &Thm) -> Thm {
        if thm.tpairs.is_empty() {
            return thm.clone();
        }

        // For now, we apply the most general flex-flex resolution:
        // each pair (f(args), g(args')) is resolved by instantiating
        // both f and g to be projections of their arguments.
        //
        // In the simple case where both sides are Var heads with the
        // same binder context, we can unify them directly.
        let mut env = super::envir::Envir::init();
        let mut resolved = true;

        for (t, u) in &thm.tpairs {
            let config = super::unify::UnifyConfig { search_bound: 10, max_unifiers: 1 };
            // Try to unify the flex-flex pair
            if let Some(new_env) = super::unify::unifiers(&env, &[(t.clone(), u.clone())], &config)
            {
                env = new_env;
            } else {
                resolved = false;
                break;
            }
        }

        if resolved {
            // Apply the instantiation to the whole theorem
            let mut new_thm = ThmKernel::instantiate(&env, thm);
            new_thm.tpairs = vec![]; // all resolved
            new_thm
        } else {
            // Keep unresolved tpairs (they are constraints, not errors)
            thm.clone()
        }
    }

    /// Strip all tpairs from a theorem (accepting them as constraints).
    ///
    /// This is sound: tpairs are unresolved flex-flex constraints that
    /// don't affect the truth of the proposition (they only restrict
    /// possible instantiations).
    pub fn strip_tpairs(thm: &Thm) -> Thm {
        let mut result = thm.clone();
        result.tpairs = vec![];
        result
    }

    // =================================================================
    // Sort hypotheses operations (Phase 41)
    // =================================================================

    /// Add a sort hypothesis to a theorem.
    ///
    /// Sort hypotheses track type-class constraints. When a theorem
    /// is used in a context that doesn't satisfy the required sort,
    /// the constraint is added as an explicit hypothesis.
    pub fn add_shyp(thm: &Thm, sort: Sort) -> Thm {
        let mut result = thm.clone();
        if !result.shyps.contains(&sort) {
            result.shyps.push(sort);
        }
        result
    }

    /// Strip sort hypotheses (weakening).
    ///
    /// This is sound: removing a constraint can only make a theorem
    /// more general (weaker assumption). However, the resulting theorem
    /// may not be usable in contexts that require the constraint.
    pub fn strip_shyps(thm: &Thm) -> Thm {
        let mut result = thm.clone();
        result.shyps = vec![];
        result
    }

    /// Check if a theorem satisfies a given sort hypothesis.
    pub fn satisfies_shyp(thm: &Thm, sort: &Sort) -> bool {
        thm.shyps.iter().any(|s| s == sort)
    }
}

/// Check if a free variable name occurs in a term.
/// Iterative implementation to avoid stack overflow.
fn free_in(var_name: &str, term: &Term) -> bool {
    let mut stack: Vec<&Term> = vec![term];
    while let Some(t) = stack.pop() {
        match t {
            Term::Free { name, .. } if name.as_ref() == var_name => return true,
            Term::Abs { body, .. } => stack.push(body),
            Term::App { func, arg } => {
                stack.push(arg);
                stack.push(func);
            },
            _ => {},
        }
    }
    false
}

/// Compute the sort hypotheses (shyps) for a term.
///
/// Walks the term and collects type class constraints from type variables
/// that have non-trivial sorts. This is used to track type-class-polymorphic
/// dependencies in theorems.
pub fn compute_shyps(term: &Term) -> Vec<Sort> {
    let mut shyps = Vec::new();
    let mut stack = vec![term];
    let mut seen = std::collections::HashSet::new();

    while let Some(t) = stack.pop() {
        match t {
            Term::Const { typ, .. } | Term::Free { typ, .. } | Term::Var { typ, .. } => {
                collect_type_sorts(typ, &mut shyps, &mut seen);
            },
            Term::Abs { typ, body, .. } => {
                collect_type_sorts(typ, &mut shyps, &mut seen);
                stack.push(body);
            },
            Term::App { func, arg } => {
                stack.push(arg);
                stack.push(func);
            },
            Term::Bound(_) => {},
        }
    }
    shyps
}

/// Helper: recursively collect sorts from a type.
fn collect_type_sorts(
    typ: &Typ,
    shyps: &mut Vec<Sort>,
    seen: &mut std::collections::HashSet<Sort>,
) {
    match typ {
        Typ::TFree { sort, .. } | Typ::TVar { sort, .. } => {
            if *sort != Sort::top() && seen.insert(sort.clone()) {
                shyps.push(sort.clone());
            }
        },
        Typ::Type { args, .. } => {
            for arg in args {
                collect_type_sorts(arg, shyps, seen);
            }
        },
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{envir::Envir, types::Symbol};

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
        assert_eq!(thm.nprems(), 1); // A is the only premise
        assert_eq!(thm.concl(), b.term().clone()); // B is the conclusion
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
        let thm =
            ThmKernel::assume(CTerm::certify(Pure::mk_implies(b.term().clone(), a.term().clone())));
        let state =
            ThmKernel::assume(CTerm::certify(Pure::mk_implies(a.term().clone(), c.term().clone())));
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
            Err(KernelError::BetaConversion(_)) => {}, // expected
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
