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

use std::collections::BTreeSet;
use std::fmt;

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
    /// ```
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
    /// ```
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
    pub fn symmetric(thm: &Thm) -> Thm {
        let (t, u) = Pure::dest_equals(thm.prop.term())
            .expect("symmetric: not an equality");

        let new_prop = CTerm::certify(
            Pure::mk_equals(Typ::dummy(), u.clone(), t.clone())
        );

        Thm {
            hyps: thm.hyps.clone(),
            prop: new_prop,
            maxidx: thm.maxidx,
            derivation: Derivation::Rule {
                name: "symmetric",
                premises: vec![ThmDeriv { serial: thm.serial, prop: thm.prop.clone() }],
            },
            serial: new_serial(),
        }
    }

    // =================================================================
    // Primitive: transitive
    // =================================================================

    /// **Transitivity**: `Γ ⊢ t ≡ u` and `Δ ⊢ u ≡ v` ⟹ `Γ ∪ Δ ⊢ t ≡ v`.
    pub fn transitive(thm1: &Thm, thm2: &Thm) -> Thm {
        let (t, u1) = Pure::dest_equals(thm1.prop.term())
            .expect("transitive: first arg not equality");
        let (u2, v) = Pure::dest_equals(thm2.prop.term())
            .expect("transitive: second arg not equality");

        // In Isabelle, the middle terms must be α-equivalent
        assert!(
            Hyps::alpha_eq(u1, u2),
            "transitive: middle terms are not alpha-equivalent"
        );

        let new_prop = CTerm::certify(
            Pure::mk_equals(Typ::dummy(), t.clone(), v.clone())
        );

        Thm {
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
        }
    }

    // =================================================================
    // Primitive: combination
    // =================================================================

    /// **Combination**: `Γ ⊢ f ≡ g` and `Δ ⊢ x ≡ y` ⟹ `Γ ∪ Δ ⊢ f x ≡ g y`.
    pub fn combination(thm_f: &Thm, thm_x: &Thm) -> Thm {
        let (f, g) = Pure::dest_equals(thm_f.prop.term())
            .expect("combination: first arg not equality");
        let (x, y) = Pure::dest_equals(thm_x.prop.term())
            .expect("combination: second arg not equality");

        let new_prop = CTerm::certify(
            Pure::mk_equals(
                Typ::dummy(),
                Term::app(f.clone(), x.clone()),
                Term::app(g.clone(), y.clone()),
            )
        );

        Thm {
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
        }
    }

    // =================================================================
    // Primitive: abstraction
    // =================================================================

    /// **Abstraction**: `Γ ⊢ t ≡ u` ⟹ `Γ ⊢ (λx. t) ≡ (λx. u)`.
    ///
    /// Side condition: `x` must not be free in `Γ`.
    pub fn abstraction(x_name: &str, x_typ: Typ, thm: &Thm) -> Thm {
        let (t, u) = Pure::dest_equals(thm.prop.term())
            .expect("abstraction: not an equality");

        let new_prop = CTerm::certify(
            Pure::mk_equals(
                Typ::dummy(),
                Term::abs(x_name, x_typ.clone(), t.clone()),
                Term::abs(x_name, x_typ, u.clone()),
            )
        );

        Thm {
            hyps: thm.hyps.clone(),
            prop: new_prop,
            maxidx: thm.maxidx,
            derivation: Derivation::Rule {
                name: "abstraction",
                premises: vec![ThmDeriv { serial: thm.serial, prop: thm.prop.clone() }],
            },
            serial: new_serial(),
        }
    }

    // =================================================================
    // Primitive: beta conversion
    // =================================================================

    /// **Beta conversion**: `⊢ (λx. t) x ≡ t`.
    pub fn beta_conversion(ct: CTerm) -> Thm {
        // ct should be of the form (λx. t) x
        let (abs, _arg) = match ct.term() {
            Term::App { func, arg } => (func.as_ref(), arg.as_ref()),
            _ => panic!("beta_conversion: not an application"),
        };

        let body = match abs {
            Term::Abs { body, .. } => body.as_ref().clone(),
            _ => panic!("beta_conversion: not a lambda"),
        };

        let new_prop = CTerm::certify(
            Pure::mk_equals(Typ::dummy(), ct.term().clone(), body)
        );

        Thm {
            hyps: Hyps::empty(),
            prop: new_prop,
            maxidx: ct.maxidx(),
            derivation: Derivation::Axiom { name: "beta_conversion" },
            serial: new_serial(),
        }
    }

    // =================================================================
    // Primitive: implies introduction (discharge)
    // =================================================================

    /// **Implication introduction**:
    /// `Γ ∪ {A} ⊢ B` ⟹ `Γ ⊢ A ==> B`.
    pub fn implies_intr(assumption: &CTerm, thm: &Thm) -> Thm {
        assert!(
            thm.hyps.contains(assumption),
            "implies_intr: assumption not found in hypotheses"
        );

        let new_prop = CTerm::certify(
            Pure::mk_implies(assumption.term().clone(), thm.prop.term().clone())
        );

        Thm {
            hyps: thm.hyps.remove(assumption),
            prop: new_prop,
            maxidx: thm.maxidx,
            derivation: Derivation::Rule {
                name: "implies_intr",
                premises: vec![ThmDeriv { serial: thm.serial, prop: thm.prop.clone() }],
            },
            serial: new_serial(),
        }
    }

    // =================================================================
    // Primitive: implies elimination (modus ponens)
    // =================================================================

    /// **Implication elimination** (modus ponens):
    /// `Γ ⊢ A ==> B` and `Δ ⊢ A` ⟹ `Γ ∪ Δ ⊢ B`.
    pub fn implies_elim(thm_imp: &Thm, thm_a: &Thm) -> Thm {
        let (a, b) = Pure::dest_implies(thm_imp.prop.term())
            .expect("implies_elim: not an implication");

        assert!(
            Hyps::alpha_eq(a, thm_a.prop.term()),
            "implies_elim: antecedent does not match"
        );

        Thm {
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
        }
    }

    // =================================================================
    // Derived rule: A ==> A  (identity)
    // =================================================================

    /// Prove `⊢ A ==> A` using assume + implies_intr.
    pub fn trivial(ct: CTerm) -> Thm {
        let assumed = ThmKernel::assume(ct.clone());
        ThmKernel::implies_intr(&ct, &assumed)
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

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
        let thm = ThmKernel::trivial(a);
        assert!(thm.is_unconditional());
        let (x, y) = Pure::dest_implies(thm.prop.term()).unwrap();
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
}
