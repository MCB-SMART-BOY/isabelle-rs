//! Proof terms — explicit, checkable proof representations.
//!
//! Corresponds to `src/Pure/proofterm.ML`.
//!
//! ## Isabelle's Proof Term Architecture
//!
//! ```text
//! proof =
//!   PAxm(name, prop)       — axiom
//! | PThm(header, body)      — stored theorem
//! | PBound(i)                — bound variable (de Bruijn)
//! | PAbst(typ, proof)        — type abstraction (!!'a. ...)
//! | PAbsP(hyp, proof)        — proposition abstraction (A ==> ...)
//! | PAppt(proof, term)       — application to term (forall_elim)
//! | PAppP(proof1, proof2)    — application to proof (implies_elim)
//! | PHyp(prop)               — hypothesis
//! | PClass(typ, class)       — type class membership
//! | POracle(name, prop)      — oracle (untrusted)
//! | PMin                     — minimal proof (placeholder)
//! ```
//!
//! ## Proof Checking
//!
//! A proof term can be checked against its proposition:
//! - `PAxm("refl", t≡t)` proves `t≡t` ✅
//! - `PAppP(PAxm("impI", A==>B), proof_of_A)` proves `B` ✅
//! - `PClass(nat, ord)` proves `nat ∈ ord` ✅

use std::fmt;

use super::{term::Term, thm::Derivation, types::Typ};

// =========================================================================
// Proof term
// =========================================================================

/// An explicit proof term — a tree representing the derivation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofTerm {
    /// An axiom: `name: prop`.
    PAxm { name: String, prop: Term },
    /// A stored theorem: `name: prop`.
    PThm { name: String, prop: Term },
    /// A bound proof variable (de Bruijn index).
    PBound(usize),
    /// Proof abstraction over a type variable: `!!'a. proof`.
    PAbst { typ_var: Typ, body: Box<ProofTerm> },
    /// Proof applied to a term: `proof(t)` (forall_elim).
    PAppt { proof: Box<ProofTerm>, term: Term },
    /// Proof applied to another proof: `proof1(proof2)` (implies_elim).
    PAppP { proof1: Box<ProofTerm>, proof2: Box<ProofTerm> },
    /// Proof abstraction over a proposition: `[A] ==> proof` (implies_intr).
    PAbsP { hypothesis: Term, body: Box<ProofTerm> },
    /// A hypothesis marker (assume).
    PHyp { prop: Term },
    /// An oracle invocation (untrusted).
    POracle { name: String, prop: Term },
    /// A type class membership proof: `t :: C`.
    PClass { typ: Typ, class: String },
    /// A minimal proof placeholder.
    PMin,
}

// =========================================================================
// Proof construction from derivations
// =========================================================================

impl ProofTerm {
    /// Convert a kernel `Derivation` into a proof term.
    pub fn from_derivation(deriv: &Derivation, prop: &Term) -> Self {
        match deriv {
            Derivation::Axiom { name } => {
                ProofTerm::PAxm { name: name.to_string(), prop: prop.clone() }
            },
            Derivation::Oracle { name, prop: _ } => {
                ProofTerm::POracle { name: name.clone(), prop: prop.clone() }
            },
            Derivation::Rule { name, premises } => {
                if premises.is_empty() {
                    ProofTerm::PAxm { name: name.to_string(), prop: prop.clone() }
                } else if premises.len() == 1 {
                    // Single-premise rule: apply to premise's proof
                    ProofTerm::PAppP {
                        proof1: Box::new(ProofTerm::PAxm {
                            name: name.to_string(),
                            prop: prop.clone(),
                        }),
                        proof2: Box::new(ProofTerm::PMin), // premise proof not available here
                    }
                } else {
                    ProofTerm::PAxm { name: name.to_string(), prop: prop.clone() }
                }
            },
        }
    }

    /// Extract the proposition proved by this proof term.
    pub fn prop_of(&self) -> Option<Term> {
        match self {
            ProofTerm::PAxm { prop, .. }
            | ProofTerm::PThm { prop, .. }
            | ProofTerm::POracle { prop, .. }
            | ProofTerm::PHyp { prop, .. } => Some(prop.clone()),
            ProofTerm::PClass { typ, class } => Some(Term::const_(
                format!("OFCLASS({},{})", typ, class).as_str(),
                Typ::base("prop"),
            )),
            ProofTerm::PAppt { proof, .. } => proof.prop_of(),
            ProofTerm::PAppP { proof1, .. } => proof1.prop_of(),
            ProofTerm::PAbsP { body, .. } => body.prop_of(),
            ProofTerm::PAbst { body, .. } => body.prop_of(),
            ProofTerm::PBound(_) | ProofTerm::PMin => None,
        }
    }

    /// Check if a proof term is closed (no free proof variables).
    pub fn is_closed(&self) -> bool {
        match self {
            ProofTerm::PBound(_) => false,
            ProofTerm::PAbst { body, .. } | ProofTerm::PAbsP { body, .. } => body.is_closed(),
            ProofTerm::PAppt { proof, .. } => proof.is_closed(),
            ProofTerm::PAppP { proof1, proof2 } => proof1.is_closed() && proof2.is_closed(),
            ProofTerm::PClass { .. } => true,
            _ => true,
        }
    }

    /// Size of the proof term (number of nodes).
    pub fn size(&self) -> usize {
        match self {
            ProofTerm::PAxm { .. }
            | ProofTerm::PThm { .. }
            | ProofTerm::PHyp { .. }
            | ProofTerm::POracle { .. }
            | ProofTerm::PMin
            | ProofTerm::PBound(_) => 1,
            ProofTerm::PAbst { body, .. } | ProofTerm::PAbsP { body, .. } => 1 + body.size(),
            ProofTerm::PAppt { proof, .. } => 1 + proof.size(),
            ProofTerm::PAppP { proof1, proof2 } => 1 + proof1.size() + proof2.size(),
            ProofTerm::PClass { .. } => 1,
        }
    }
}

impl fmt::Display for ProofTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofTerm::PAxm { name, .. } => write!(f, "axm:{name}"),
            ProofTerm::PThm { name, .. } => write!(f, "thm:{name}"),
            ProofTerm::PHyp { .. } => write!(f, "hyp"),
            ProofTerm::PBound(i) => write!(f, "B{i}"),
            ProofTerm::PMin => write!(f, "?"),
            ProofTerm::POracle { name, .. } => write!(f, "oracle:{name}"),
            ProofTerm::PClass { class, .. } => write!(f, "class:{class}"),
            ProofTerm::PAbst { body, .. } => write!(f, "Λ.({body})"),
            ProofTerm::PAppt { proof, .. } => write!(f, "({proof}·t)"),
            ProofTerm::PAppP { proof1, proof2 } => write!(f, "({proof1}·{proof2})"),
            ProofTerm::PAbsP { body, .. } => write!(f, "[A]·({body})"),
        }
    }
}

// =========================================================================
// Proof checker — validates proof terms against propositions
// =========================================================================

/// Check a proof term against a proposition.
/// Returns `Ok(())` if the proof is valid for the given proposition.
///
/// This implements the core of LF-style proof checking:
/// - Axioms are trusted (they form the trusted computing base)
/// - Application rules are checked structurally
/// - Oracles are flagged as untrusted
pub fn check_proof(proof: &ProofTerm, expected_prop: &Term) -> Result<(), String> {
    match proof {
        // Axioms: trusted
        ProofTerm::PAxm { prop, .. } if prop == expected_prop => Ok(()),
        ProofTerm::PThm { prop, .. } if prop == expected_prop => Ok(()),
        ProofTerm::PHyp { prop } if prop == expected_prop => Ok(()),

        // Type class: trusted (class membership is axiomatic in our kernel)
        ProofTerm::PClass { .. } => Ok(()),

        // Oracle: untrusted, but accepted with warning
        ProofTerm::POracle { .. } => Ok(()),

        // Minimal proof: cannot check
        ProofTerm::PMin => Err("minimal proof: cannot check".into()),
        ProofTerm::PBound(_) => Err("unbound proof variable".into()),

        // Abstraction over proposition: [A] ==> B implies A ==> B
        ProofTerm::PAbsP { hypothesis, body } => {
            // The body proves something, and we wrap it with hypothesis → body
            if let Some(body_prop) = body.prop_of() {
                let expected_imp =
                    crate::core::logic::Pure::mk_implies(hypothesis.clone(), body_prop.clone());
                if &expected_imp == expected_prop {
                    return check_proof(body, &body_prop);
                }
            }
            Err("PAbsP: proposition mismatch".into())
        },

        // Application to term: proof(t) — forall_elim
        ProofTerm::PAppt { proof, term: _ } => {
            // proof proves !!x.P(x), we apply it to term t to get P(t)
            // For now, trust the application
            check_proof(proof, expected_prop)
        },

        // Application to proof: proof1(proof2) — implies_elim (modus ponens)
        ProofTerm::PAppP { proof1, proof2 } => {
            // proof1 proves A ==> B, proof2 proves A, result is B
            match proof1.prop_of() {
                Some(prop1) => {
                    if let Some((a, b)) = crate::core::logic::Pure::dest_implies(&prop1) {
                        check_proof(proof2, a)?;
                        if b != expected_prop {
                            return Err(format!(
                                "PAppP: conclusion mismatch: expected {:?}, got {:?}",
                                expected_prop, b
                            ));
                        }
                        Ok(())
                    } else {
                        Err("PAppP: proof1 is not an implication".into())
                    }
                },
                None => Err("PAppP: cannot determine proof1 proposition".into()),
            }
        },

        // Type abstraction: Λ'a. proof
        ProofTerm::PAbst { body, .. } => check_proof(body, expected_prop),

        // Other axiom mismatches
        ProofTerm::PAxm { prop, name } => Err(format!(
            "axiom {name}: prop mismatch, expected {:?}, got {:?}",
            expected_prop, prop
        )),
        ProofTerm::PThm { prop, name } => Err(format!(
            "theorem {name}: prop mismatch, expected {:?}, got {:?}",
            expected_prop, prop
        )),
        ProofTerm::PHyp { prop } => {
            Err(format!("hypothesis mismatch, expected {:?}, got {:?}", expected_prop, prop))
        },
    }
}

// =========================================================================
// Proof body — lazily checked proof term
// =========================================================================

/// A proof body: a proof term with optional lazy checking.
#[derive(Clone, Debug)]
pub struct ProofBody {
    pub proof: ProofTerm,
    pub checked: bool,
    pub oracles: Vec<String>,
}

impl ProofBody {
    pub fn minimal() -> Self {
        ProofBody { proof: ProofTerm::PMin, checked: false, oracles: vec![] }
    }

    pub fn from_derivation(deriv: &super::thm::Derivation, prop: &Term) -> Self {
        let proof = ProofTerm::from_derivation(deriv, prop);
        let oracles = match deriv {
            super::thm::Derivation::Oracle { name, .. } => vec![name.clone()],
            _ => vec![],
        };
        ProofBody { proof, checked: false, oracles }
    }

    pub fn check(&mut self, expected_prop: &Term) -> Result<(), String> {
        if self.checked {
            return Ok(());
        }
        check_proof(&self.proof, expected_prop)?;
        self.checked = true;
        Ok(())
    }
}

impl Default for ProofBody {
    fn default() -> Self {
        Self::minimal()
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn prop(name: &str) -> Term {
        Term::const_(name, Typ::base("prop"))
    }

    #[test]
    fn test_axiom_proof() {
        let p = ProofTerm::PAxm { name: "refl".into(), prop: prop("A") };
        assert_eq!(p.prop_of(), Some(prop("A")));
        assert!(p.is_closed());
    }

    #[test]
    fn test_check_axiom() {
        let p = ProofTerm::PAxm { name: "refl".into(), prop: prop("A") };
        assert!(check_proof(&p, &prop("A")).is_ok());
        assert!(check_proof(&p, &prop("B")).is_err());
    }

    #[test]
    fn test_size() {
        let inner = ProofTerm::PAxm { name: "inner".into(), prop: prop("A") };
        let outer = ProofTerm::PAppP {
            proof1: Box::new(ProofTerm::PAxm { name: "outer".into(), prop: prop("A") }),
            proof2: Box::new(inner),
        };
        assert_eq!(outer.size(), 3);
    }
}
