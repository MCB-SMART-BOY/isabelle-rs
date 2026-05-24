//! Proof terms — explicit, checkable proof representations.
//!
//! Corresponds to `src/Pure/proofterm.ML`.
//!
//! Isabelle records proof terms that can be independently verified.
//! A proof term is a tree where:
//! - **PAxm**: an axiom (trusted)
//! - **PThm**: a stored theorem (previously proved)
//! - **PBound**: a bound variable (for proof abstractions)
//! - **PAbst**: proof abstraction (corresponds to `!!x.` introduction)
//! - **PAppt**: proof application to a term (corresponds to `forall_elim`)
//! - **PAppP**: proof application to a proof (corresponds to `implies_elim`)
//! - **PAbsP**: proof abstraction over a proposition (corresponds to `implies_intr`)
//! - **PHyp**: a hypothesis (corresponds to `assume`)
//! - **POracle**: an oracle invocation (untrusted)
//! - **PMin**: minimal proof (placeholder)

use std::fmt;

use super::term::Term;
use super::thm::Derivation;
use super::types::Typ;

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
    PAppP {
        proof1: Box<ProofTerm>,
        proof2: Box<ProofTerm>,
    },
    /// Proof abstraction over a proposition: `[A] ==> proof` (implies_intr).
    PAbsP {
        hypothesis: Term,
        body: Box<ProofTerm>,
    },
    /// A hypothesis marker (assume).
    PHyp { prop: Term },
    /// An oracle invocation (untrusted).
    POracle { name: String, prop: Term },
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
            Derivation::Axiom { name } => ProofTerm::PAxm {
                name: name.to_string(),
                prop: prop.clone(),
            },
            Derivation::Oracle { name, prop: _ } => ProofTerm::POracle {
                name: name.clone(),
                prop: prop.clone(),
            },
            Derivation::Rule { name, premises } => {
                if premises.is_empty() {
                    ProofTerm::PAxm {
                        name: name.to_string(),
                        prop: prop.clone(),
                    }
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
                    ProofTerm::PAxm {
                        name: name.to_string(),
                        prop: prop.clone(),
                    }
                }
            }
        }
    }

    /// Extract the proposition proved by this proof term.
    pub fn prop_of(&self) -> Option<Term> {
        match self {
            ProofTerm::PAxm { prop, .. }
            | ProofTerm::PThm { prop, .. }
            | ProofTerm::POracle { prop, .. }
            | ProofTerm::PHyp { prop, .. } => Some(prop.clone()),
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
            ProofTerm::PAbst { body, .. } => write!(f, "Λ.({body})"),
            ProofTerm::PAppt { proof, .. } => write!(f, "({proof}·t)"),
            ProofTerm::PAppP { proof1, proof2 } => write!(f, "({proof1}·{proof2})"),
            ProofTerm::PAbsP { body, .. } => write!(f, "[A]·({body})"),
        }
    }
}

// =========================================================================
// Proof checker
// =========================================================================

/// Check a proof term against a proposition.
/// Returns `Ok(())` if the proof is valid for the given proposition.
pub fn check_proof(proof: &ProofTerm, expected_prop: &Term) -> Result<(), String> {
    match (proof, expected_prop) {
        (ProofTerm::PAxm { prop, .. }, expected) if prop == expected => Ok(()),
        (ProofTerm::PThm { prop, .. }, expected) if prop == expected => Ok(()),
        (ProofTerm::PHyp { prop }, expected) if prop == expected => Ok(()),
        (ProofTerm::POracle { .. }, _) => Err("oracle proof: not verified".into()),
        (ProofTerm::PMin, _) => Err("minimal proof: cannot check".into()),
        (ProofTerm::PAppP { proof1, proof2 }, _) => {
            // proof1 proves A ==> B, proof2 proves A
            match proof1.prop_of() {
                Some(prop1) => {
                    if let Some((_a, b)) = super::logic::Pure::dest_implies(&prop1) {
                        check_proof(proof2, expected_prop)?;
                        if b != expected_prop {
                            return Err("PAppP: conclusion mismatch".into());
                        }
                        Ok(())
                    } else {
                        Err("PAppP: not an implication".into())
                    }
                }
                None => Err("PAppP: cannot determine prop1".into()),
            }
        }
        _ => Err(format!("proof/term mismatch: {proof} vs {expected_prop:?}")),
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
        let p = ProofTerm::PAxm {
            name: "refl".into(),
            prop: prop("A"),
        };
        assert_eq!(p.prop_of(), Some(prop("A")));
        assert!(p.is_closed());
    }

    #[test]
    fn test_check_axiom() {
        let p = ProofTerm::PAxm {
            name: "refl".into(),
            prop: prop("A"),
        };
        assert!(check_proof(&p, &prop("A")).is_ok());
        assert!(check_proof(&p, &prop("B")).is_err());
    }

    #[test]
    fn test_size() {
        let inner = ProofTerm::PAxm {
            name: "inner".into(),
            prop: prop("A"),
        };
        let outer = ProofTerm::PAppP {
            proof1: Box::new(ProofTerm::PAxm {
                name: "outer".into(),
                prop: prop("A"),
            }),
            proof2: Box::new(inner),
        };
        assert_eq!(outer.size(), 3);
    }
}
