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

use std::{fmt, sync::Arc};

use super::{
    logic::Pure,
    term::Term,
    thm::{CTerm, Derivation, Hyps},
    types::{Typ, TypeEnv},
};

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
    /// A primitive kernel rule applied to explicit premise proofs.
    PRule { name: String, prop: Term, premises: Vec<ProofTerm> },
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
    pub(crate) fn from_derivation(deriv: &Derivation) -> Self {
        match deriv {
            Derivation::Axiom { name, prop } if *name == "assume" => {
                ProofTerm::PHyp { prop: prop.term().clone() }
            },
            Derivation::Axiom { name, prop } => {
                ProofTerm::PAxm { name: name.to_string(), prop: prop.term().clone() }
            },
            Derivation::Oracle { name, prop } => {
                ProofTerm::POracle { name: name.clone(), prop: prop.term().clone() }
            },
            Derivation::Rule { name, prop, premises } => {
                let premises = premises
                    .iter()
                    .map(|premise| ProofTerm::from_derivation(&premise.derivation))
                    .collect();
                ProofTerm::PRule { name: name.to_string(), prop: prop.term().clone(), premises }
            },
        }
    }

    /// Extract the proposition proved by this proof term.
    pub fn prop_of(&self) -> Option<Term> {
        match self {
            ProofTerm::PAxm { prop, .. }
            | ProofTerm::PThm { prop, .. }
            | ProofTerm::POracle { prop, .. }
            | ProofTerm::PRule { prop, .. }
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
            ProofTerm::PRule { premises, .. } => premises.iter().all(ProofTerm::is_closed),
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
            ProofTerm::PRule { premises, .. } => {
                1 + premises.iter().map(ProofTerm::size).sum::<usize>()
            },
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
            ProofTerm::PRule { name, .. } => write!(f, "rule:{name}"),
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

/// The theorem shape reconstructed by proof replay.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReplayResult {
    pub prop: Term,
    pub hyps: Hyps,
    pub tpairs: Vec<(Term, Term)>,
    pub oracles: Vec<Arc<str>>,
}

impl ReplayResult {
    fn closed(prop: Term) -> Self {
        ReplayResult { prop, hyps: Hyps::empty(), tpairs: vec![], oracles: vec![] }
    }

    fn hyp(prop: Term) -> Self {
        ReplayResult {
            hyps: Hyps::singleton(CTerm::certify(prop.clone())),
            prop,
            tpairs: vec![],
            oracles: vec![],
        }
    }

    fn union_burdens(mut self, other: ReplayResult) -> Self {
        self.hyps = self.hyps.union(&other.hyps);
        for pair in other.tpairs {
            if !self.tpairs.contains(&pair) {
                self.tpairs.push(pair);
            }
        }
        for oracle in other.oracles {
            if !self.oracles.iter().any(|existing| existing.as_ref() == oracle.as_ref()) {
                self.oracles.push(oracle);
            }
        }
        self
    }

    fn discharge(mut self, hyp: &Term) -> Result<Self, String> {
        let hyp = CTerm::certify(hyp.clone());
        if !self.hyps.contains(&hyp) {
            return Err(format!("implies_intr: missing discharged hypothesis {:?}", hyp.term()));
        }
        self.hyps = self.hyps.remove(&hyp);
        Ok(self)
    }
}

fn types_compatible(t1: &Typ, t2: &Typ) -> bool {
    match (t1, t2) {
        (Typ::Type { name: n1, args: a1 }, Typ::Type { name: n2, args: a2 }) => {
            n1 == n2
                && a1.len() == a2.len()
                && a1.iter().zip(a2.iter()).all(|(a, b)| types_compatible(a, b))
        },
        _ => true,
    }
}

fn known_types_mismatch(expected: &Typ, actual: &Typ) -> bool {
    !expected.is_dummy() && !actual.is_dummy() && !types_compatible(expected, actual)
}

fn term_known_type(term: &Term) -> Typ {
    match term {
        Term::Const { typ, .. } | Term::Free { typ, .. } | Term::Var { typ, .. } => typ.clone(),
        Term::Abs { typ, body, .. } => {
            let body_typ = term_known_type(body);
            if typ.is_dummy() || body_typ.is_dummy() {
                Typ::dummy()
            } else {
                Typ::arrow(typ.clone(), body_typ)
            }
        },
        Term::App { func, .. } => {
            let fn_typ = term_known_type(func);
            fn_typ.dest_fun().map(|(_, ret)| ret.clone()).unwrap_or_else(Typ::dummy)
        },
        Term::Bound(_) => Typ::dummy(),
    }
}

fn known_term_types_compatible(a: &Term, b: &Term) -> bool {
    let a_typ = term_known_type(a);
    let b_typ = term_known_type(b);
    !known_types_mismatch(&a_typ, &b_typ)
}

fn alpha_eq_with_known_types(a: &Term, b: &Term) -> bool {
    Hyps::kernel_alpha_eq(a, b) && known_term_types_compatible(a, b)
}

/// Replay a proof term and reconstruct the theorem shape it proves.
pub fn replay_proof(proof: &ProofTerm) -> Result<ReplayResult, String> {
    match proof {
        ProofTerm::PHyp { prop } => Ok(ReplayResult::hyp(prop.clone())),

        ProofTerm::PAxm { name, prop } if name == "reflexive" => {
            let (lhs, rhs, _) = Pure::dest_equals_with_type(prop)
                .ok_or_else(|| "reflexive: proposition is not equality".to_string())?;
            if lhs != rhs {
                return Err(format!("reflexive: lhs/rhs mismatch: {:?} vs {:?}", lhs, rhs));
            }
            Ok(ReplayResult::closed(prop.clone()))
        },

        ProofTerm::PAxm { name, .. } => Err(format!("unsupported axiom proof rule: {name}")),
        ProofTerm::PThm { name, .. } => Err(format!("stored theorem replay unsupported: {name}")),

        ProofTerm::POracle { name, .. } => {
            Err(format!("oracle proof is not an independent kernel replay: {name}"))
        },

        ProofTerm::PMin => Err("minimal proof: cannot check".into()),
        ProofTerm::PBound(_) => Err("unbound proof variable".into()),

        ProofTerm::PRule { name, prop, premises } => replay_rule(name, prop, premises),

        ProofTerm::PAbsP { hypothesis, body } => {
            let body = replay_proof(body)?;
            let expected = Pure::mk_implies(hypothesis.clone(), body.prop.clone());
            let mut result = body.discharge(hypothesis)?;
            result.prop = expected;
            Ok(result)
        },

        ProofTerm::PAppP { proof1, proof2 } => {
            let proof1 = replay_proof(proof1)?;
            let proof2 = replay_proof(proof2)?;
            let (antecedent, consequent) = Pure::dest_implies(&proof1.prop)
                .ok_or_else(|| "PAppP: proof1 is not an implication".to_string())?;
            if antecedent != &proof2.prop {
                return Err(format!(
                    "PAppP: antecedent mismatch: expected {:?}, got {:?}",
                    antecedent, proof2.prop
                ));
            }
            let consequent = consequent.clone();
            let mut result = proof1.union_burdens(proof2);
            result.prop = consequent;
            Ok(result)
        },

        ProofTerm::PClass { .. } => Err("type class proof replay unsupported".into()),
        ProofTerm::PAppt { .. } => Err("forall_elim proof replay unsupported".into()),
        ProofTerm::PAbst { .. } => Err("type abstraction proof replay unsupported".into()),
    }
}

fn replay_rule(name: &str, prop: &Term, premises: &[ProofTerm]) -> Result<ReplayResult, String> {
    match name {
        "symmetric" => {
            let [premise] = premises else {
                return Err(format!("symmetric: expected 1 premise, got {}", premises.len()));
            };
            let mut premise = replay_proof(premise)?;
            let (lhs, rhs, typ) = Pure::dest_equals_with_type(&premise.prop)
                .ok_or_else(|| "symmetric: premise is not equality".to_string())?;
            let expected = Pure::mk_equals(typ, rhs.clone(), lhs.clone());
            if &expected != prop {
                return Err(format!(
                    "symmetric: result mismatch: expected {:?}, got {:?}",
                    expected, prop
                ));
            }
            premise.prop = prop.clone();
            Ok(premise)
        },

        "transitive" => {
            let [left, right] = premises else {
                return Err(format!("transitive: expected 2 premises, got {}", premises.len()));
            };
            let left = replay_proof(left)?;
            let right = replay_proof(right)?;
            let (lhs, mid_left, typ) = Pure::dest_equals_with_type(&left.prop)
                .ok_or_else(|| "transitive: left premise is not equality".to_string())?;
            let (mid_right, rhs, _) = Pure::dest_equals_with_type(&right.prop)
                .ok_or_else(|| "transitive: right premise is not equality".to_string())?;
            if !alpha_eq_with_known_types(mid_left, mid_right) {
                return Err(format!(
                    "transitive: middle mismatch: {:?} vs {:?}",
                    mid_left, mid_right
                ));
            }
            let (_, _, right_typ) = Pure::dest_equals_with_type(&right.prop)
                .ok_or_else(|| "transitive: right premise is not equality".to_string())?;
            if known_types_mismatch(&typ, &right_typ) {
                return Err(format!(
                    "transitive: equality type mismatch: {:?} vs {:?}",
                    typ, right_typ
                ));
            }
            let expected = Pure::mk_equals(typ, lhs.clone(), rhs.clone());
            if &expected != prop {
                return Err(format!(
                    "transitive: result mismatch: expected {:?}, got {:?}",
                    expected, prop
                ));
            }
            let mut result = left.union_burdens(right);
            result.prop = prop.clone();
            Ok(result)
        },

        "implies_intr" => {
            let [premise] = premises else {
                return Err(format!("implies_intr: expected 1 premise, got {}", premises.len()));
            };
            let premise = replay_proof(premise)?;
            let (hyp, body) = Pure::dest_implies(prop)
                .ok_or_else(|| "implies_intr: result is not implication".to_string())?;
            if body != &premise.prop {
                return Err(format!(
                    "implies_intr: body mismatch: expected {:?}, got {:?}",
                    body, premise.prop
                ));
            }
            let mut result = premise.discharge(hyp)?;
            result.prop = prop.clone();
            Ok(result)
        },

        "implies_elim" => {
            let [major, minor] = premises else {
                return Err(format!("implies_elim: expected 2 premises, got {}", premises.len()));
            };
            let major = replay_proof(major)?;
            let minor = replay_proof(minor)?;
            let (antecedent, consequent) = Pure::dest_implies(&major.prop)
                .ok_or_else(|| "implies_elim: major premise is not implication".to_string())?;
            if !alpha_eq_with_known_types(antecedent, &minor.prop) {
                return Err(format!(
                    "implies_elim: antecedent mismatch: expected {:?}, got {:?}",
                    antecedent, minor.prop
                ));
            }
            if consequent != prop {
                return Err(format!(
                    "implies_elim: conclusion mismatch: expected {:?}, got {:?}",
                    consequent, prop
                ));
            }
            let consequent = consequent.clone();
            let mut result = major.union_burdens(minor);
            debug_assert_eq!(&consequent, prop);
            result.prop = consequent;
            Ok(result)
        },

        _ => Err(format!("unsupported proof replay rule: {name}")),
    }
}

fn hyps_equiv(a: &Hyps, b: &Hyps) -> bool {
    a.len() == b.len() && a.iter().all(|h| b.contains(h)) && b.iter().all(|h| a.contains(h))
}

/// Check a proof term against a proposition only.
///
/// This is useful for small proof-term unit tests, but it is not a trusted
/// theorem validation gate because it intentionally ignores `hyps`, `tpairs`,
/// and `oracles`. Use `check_proof_with_burdens` or `Thm::check_proof()` for
/// independent theorem replay.
pub(crate) fn check_proof(proof: &ProofTerm, expected_prop: &Term) -> Result<(), String> {
    let replay = replay_proof(proof)?;
    if &replay.prop == expected_prop {
        Ok(())
    } else {
        Err(format!(
            "proof proposition mismatch: expected {:?}, got {:?}",
            expected_prop, replay.prop
        ))
    }
}

/// Check a proof term against a complete theorem shape.
pub(crate) fn check_proof_with_burdens(
    proof: &ProofTerm,
    expected_prop: &Term,
    expected_hyps: &Hyps,
    expected_tpairs: &[(Term, Term)],
    expected_oracles: &[Arc<str>],
) -> Result<(), String> {
    let replay = replay_proof(proof)?;
    if &replay.prop != expected_prop {
        return Err(format!(
            "proof proposition mismatch: expected {:?}, got {:?}",
            expected_prop, replay.prop
        ));
    }
    if !hyps_equiv(&replay.hyps, expected_hyps) {
        return Err(format!(
            "proof hypotheses mismatch: expected {:?}, got {:?}",
            expected_hyps, replay.hyps
        ));
    }
    if replay.tpairs.as_slice() != expected_tpairs {
        return Err(format!(
            "proof tpairs mismatch: expected {:?}, got {:?}",
            expected_tpairs, replay.tpairs
        ));
    }
    if replay.oracles.as_slice() != expected_oracles {
        return Err(format!(
            "proof oracle mismatch: expected {:?}, got {:?}",
            expected_oracles, replay.oracles
        ));
    }
    Ok(())
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

    pub(crate) fn from_derivation(deriv: &super::thm::Derivation) -> Self {
        let proof = ProofTerm::from_derivation(deriv);
        let oracles = match deriv {
            super::thm::Derivation::Oracle { name, .. } => vec![name.clone()],
            super::thm::Derivation::Rule { premises, .. } => {
                let mut out = Vec::new();
                for premise in premises {
                    for oracle in &premise.oracles {
                        let oracle = oracle.to_string();
                        if !out.contains(&oracle) {
                            out.push(oracle);
                        }
                    }
                }
                out
            },
            super::thm::Derivation::Axiom { .. } => vec![],
        };
        ProofBody { proof, checked: false, oracles }
    }

    /// Compatibility proposition-only check.
    ///
    /// This is not a trusted theorem validation gate: it does not compare
    /// hypotheses, unresolved `tpairs`, or oracle footprints. Use
    /// `check_with_burdens` via `Thm::validate_proof()` for trusted replay.
    pub fn check(&mut self, expected_prop: &Term) -> Result<(), String> {
        if self.checked {
            return Ok(());
        }
        check_proof(&self.proof, expected_prop)?;
        self.checked = true;
        Ok(())
    }

    /// Check this proof body against a complete theorem shape.
    pub fn check_with_burdens(
        &mut self,
        expected_prop: &Term,
        expected_hyps: &Hyps,
        expected_tpairs: &[(Term, Term)],
        expected_oracles: &[Arc<str>],
    ) -> Result<(), String> {
        check_proof_with_burdens(
            &self.proof,
            expected_prop,
            expected_hyps,
            expected_tpairs,
            expected_oracles,
        )?;
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
    use crate::core::thm::ThmKernel;

    fn prop(name: &str) -> Term {
        Term::const_(name, Typ::base("prop"))
    }

    fn nat(name: &str) -> Term {
        Term::free(name, Typ::base("nat"))
    }

    fn declare_term(term: &Term, env: &mut TypeEnv) {
        match term {
            Term::Const { name, typ } if !typ.is_dummy() && !name.as_ref().starts_with("Pure.") => {
                env.declare_const(name.as_ref(), typ.clone());
            },
            Term::Free { name, typ } if !typ.is_dummy() => {
                env.declare_free(name.as_ref(), typ.clone());
            },
            Term::Var { .. } | Term::Bound(_) | Term::Const { .. } | Term::Free { .. } => {},
            Term::Abs { body, .. } => declare_term(body, env),
            Term::App { func, arg } => {
                declare_term(func, env);
                declare_term(arg, env);
            },
        }
    }

    fn checked_cterm(term: Term) -> CTerm {
        let mut env = TypeEnv::new();
        declare_term(&term, &mut env);
        CTerm::certify_checked(term, &env).unwrap()
    }

    fn refl_prop(name: &str) -> Term {
        let t = nat(name);
        Pure::mk_equals(Typ::base("nat"), t.clone(), t)
    }

    fn checked_eq_cterm(typ: Typ, lhs: Term, rhs: Term) -> CTerm {
        checked_cterm(Pure::mk_equals(typ, lhs, rhs))
    }

    #[test]
    fn test_axiom_proof() {
        let p = ProofTerm::PAxm { name: "reflexive".into(), prop: refl_prop("a") };
        assert_eq!(p.prop_of(), Some(refl_prop("a")));
        assert!(p.is_closed());
    }

    #[test]
    fn test_check_axiom() {
        let p = ProofTerm::PAxm { name: "reflexive".into(), prop: refl_prop("a") };
        assert!(check_proof(&p, &refl_prop("a")).is_ok());
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

    #[test]
    fn assume_replay_succeeds_but_is_open() {
        let a = checked_cterm(prop("A"));
        let thm = ThmKernel::assume(a).unwrap();
        assert!(thm.check_proof().is_ok());
        assert!(thm.is_fully_proved());
        assert!(!thm.is_closed_proved());
        assert!(!thm.is_strict_closed_proved());
    }

    #[test]
    fn reflexive_replay_succeeds_and_is_closed_proved() {
        let thm = ThmKernel::reflexive(checked_cterm(nat("a"))).unwrap();
        assert!(thm.check_proof().is_ok());
        assert!(thm.is_closed_proved());
        assert!(thm.is_strict_closed_proved());
    }

    #[test]
    fn symmetric_replay_succeeds() {
        let refl = ThmKernel::reflexive(checked_cterm(nat("a"))).unwrap();
        let sym = ThmKernel::symmetric(&refl).unwrap();
        assert!(sym.check_proof().is_ok());
        assert!(sym.is_closed_proved());
        assert!(sym.is_strict_closed_proved());
    }

    #[test]
    fn symmetric_replay_preserves_open_premise_hyps() {
        let eq = checked_eq_cterm(Typ::base("nat"), nat("a"), nat("a"));
        let open_eq = ThmKernel::assume(eq).unwrap();
        let sym = ThmKernel::symmetric(&open_eq).unwrap();

        assert!(sym.check_proof().is_ok());
        assert_eq!(sym.hyps().len(), 1);
        assert!(sym.is_fully_proved());
        assert!(!sym.is_closed_proved());
    }

    #[test]
    fn supported_replay_rejects_oracle_premise() {
        let admitted = ThmKernel::admit(
            checked_eq_cterm(Typ::base("nat"), nat("a"), nat("a")),
            "admitted:proof_engine_failed",
        );
        let sym = ThmKernel::symmetric(&admitted).unwrap();

        let err = sym.check_proof().expect_err("oracle premise should not replay independently");
        assert!(err.contains("oracle proof"), "unexpected oracle replay error: {err}");
    }

    #[test]
    fn transitive_replay_succeeds() {
        let refl = ThmKernel::reflexive(checked_cterm(nat("a"))).unwrap();
        let trans = ThmKernel::transitive(&refl, &refl).unwrap();
        assert!(trans.check_proof().is_ok());
        assert!(trans.is_closed_proved());
        assert!(trans.is_strict_closed_proved());
    }

    #[test]
    fn transitive_replay_accepts_alpha_equivalent_middle_terms() {
        let nat = Typ::base("nat");
        let fn_typ = Typ::arrow(nat.clone(), nat);
        let lhs = Term::const_("lhs", fn_typ.clone());
        let mid_x = Term::abs("x", Typ::base("nat"), Term::bound(0));
        let mid_y = Term::abs("y", Typ::base("nat"), Term::bound(0));
        let rhs = Term::const_("rhs", fn_typ.clone());

        assert_ne!(mid_x, mid_y, "test requires syntactically distinct alpha terms");

        let left = ThmKernel::assume(checked_eq_cterm(fn_typ.clone(), lhs, mid_x)).unwrap();
        let right = ThmKernel::assume(checked_eq_cterm(fn_typ, mid_y, rhs)).unwrap();
        let trans = ThmKernel::transitive(&left, &right).unwrap();

        assert!(trans.check_proof().is_ok());
        assert_eq!(trans.hyps().len(), 2);
        assert!(!trans.is_closed_proved());
    }

    #[test]
    fn implies_intro_and_elim_replay_succeed() {
        let a = checked_cterm(prop("A"));
        let assumed = ThmKernel::assume(a.clone()).unwrap();
        let identity = ThmKernel::implies_intr(&a, &assumed).unwrap();
        assert!(identity.check_proof().is_ok());
        assert!(identity.is_closed_proved());
        assert!(identity.is_strict_closed_proved());

        let minor = ThmKernel::assume(a).unwrap();
        let eliminated = ThmKernel::implies_elim(&identity, &minor).unwrap();
        assert!(eliminated.check_proof().is_ok());
        assert!(eliminated.is_fully_proved());
        assert!(!eliminated.is_closed_proved());
    }

    #[test]
    fn admitted_theorem_does_not_pass_kernel_replay() {
        let admitted = ThmKernel::admit(checked_cterm(prop("A")), "admitted:proof_engine_failed");
        assert!(!admitted.is_fully_proved());
        assert!(!admitted.is_closed_proved());
        assert!(admitted.check_proof().is_err());
    }

    #[test]
    fn unsupported_rule_is_reported_separately_from_tampering() {
        let beta = Term::app(Term::abs("x", Typ::base("nat"), Term::bound(0)), nat("a"));
        let thm =
            ThmKernel::beta_conversion(checked_cterm(beta)).expect("well-formed beta conversion");

        let err = thm.check_proof().expect_err("beta replay is not implemented yet");
        assert!(
            err.contains("unsupported axiom proof rule: beta_conversion"),
            "unexpected unsupported-rule error: {err}"
        );
    }
}
