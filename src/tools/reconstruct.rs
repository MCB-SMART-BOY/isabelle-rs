//! Proof reconstruction — convert ATP proofs to Isabelle LCF proofs.
//!
//! Corresponds to `src/HOL/Tools/Sledgehammer/sledgehammer_reconstruct.ML`
//! in the Isabelle/ML sources.
//!
//! # Motivation
//!
//! External ATPs (E, Vampire, Zipperposition) find proofs quickly but
//! outside Isabelle's LCF kernel.  To maintain the trust guarantees of
//! the kernel, every ATP proof must be *reconstructed* — i.e., replayed
//! step-by-step using only primitive inference rules.  This module
//! provides the infrastructure to do that.
//!
//! # Architecture
//!
//! ```text
//! ATP stdout (TSTP)
//!       │
//!       ▼
//!  ┌────────────────┐
//!  │ Parse TSTP      │  Extract ProofStep list (name, formula, rule, premises)
//!  └───────┬────────┘
//!          │
//!          ▼
//!  ┌────────────────┐
//!  │ Translate       │  Map ATP rules → Isabelle inference rules
//!  └───────┬────────┘  (resolution → implies_elim, paramodulation → subst, …)
//!          │
//!          ▼
//!  ┌────────────────┐
//!  │ Replay          │  Execute each step in the LCF kernel (ThmKernel)
//!  └───────┬────────┘  using proven premises as leaves
//!          │
//!          ▼
//!  ┌────────────────┐
//!  │ Minimize        │  Drop unused premises; find minimal dependency set
//!  └────────────────┘
//! ```
//!
//! # Key Types
//!
//! - **[`ProofStep`]** — A single inference in the ATP's proof: a name, the inferred formula, the
//!   inference rule, and references to earlier steps.
//! - **[`ProofReconstructor`]** — The engine that parses TSTP output, looks up premises, and
//!   replays each step through the kernel.
//!
//! # ATP Proof Formats
//!
//! ATPs typically produce output in **TSTP** (Thousands of Solutions
//! from Theorem Provers) format.  Each line has the shape:
//!
//! ```text
//! fof(name, role, formula, inference(rule, status, [premises])).
//! ```
//!
//! For example:
//!
//! ```text
//! fof(f1, plain, p(a), inference(resolution, [], [f0])).
//! ```
//!
//! # Examples
//!
//! ```rust
//! use isabelle_rs::tools::reconstruct::ProofReconstructor;
//!
//! let output = "fof(f1, plain, p, inference(assumption, [], [f0])).";
//! let steps = ProofReconstructor::parse_tstp(output).unwrap();
//! assert_eq!(steps[0].rule, "assumption");
//! ```

use std::{collections::HashMap, sync::Arc};

use crate::core::{
    logic::Pure,
    term::Term,
    thm::{Thm, ThmKernel},
    types::Typ,
};
use crate::isar::proof_result::validate_proof_result;

// =========================================================================
// Proof step
// =========================================================================

/// A single step in an ATP proof.
#[derive(Debug, Clone)]
pub struct ProofStep {
    /// Step name (e.g., "fof_1")
    pub name: String,
    /// The inferred formula
    pub formula: Term,
    /// The inference rule used (e.g., "resolution", "paramodulation")
    pub rule: String,
    /// Premises (references to earlier steps or input formulas)
    pub premises: Vec<String>,
}

// =========================================================================
// Proof reconstruction engine
// =========================================================================

/// Reconstructs Isabelle proofs from ATP output.
pub struct ProofReconstructor {
    premises: Vec<(String, Arc<Thm>)>,
}

/// A malformed proof-bearing ATP line (user-fixable untrusted input).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("invalid ATP proof at line {line}: {detail}")]
pub struct AtpProofParseError {
    pub line: usize,
    pub detail: String,
}

/// Reject ambiguous input names before either replay engine builds its table.
pub(crate) fn initial_proof_steps(
    premises: &[(String, Arc<Thm>)],
) -> Option<HashMap<String, Arc<Thm>>> {
    let mut proven = HashMap::with_capacity(premises.len());
    for (name, thm) in premises {
        if name.is_empty() || proven.insert(name.clone(), Arc::clone(thm)).is_some() {
            return None;
        }
    }
    Some(proven)
}

fn matches_step_formula(candidate: Thm, formula: &Term) -> Option<Arc<Thm>> {
    crate::core::thm::Hyps::kernel_alpha_eq(candidate.prop().term(), formula)
        .then(|| Arc::new(candidate))
}

/// A single guard for both ATP replay entry points: never silently omit names,
/// replace an earlier result, or accept a formula not actually inferred.
pub(crate) fn replay_checked_step(
    proven: &mut HashMap<String, Arc<Thm>>,
    step: &ProofStep,
) -> Option<Arc<Thm>> {
    if step.name.is_empty() || proven.contains_key(&step.name) {
        return None;
    }
    let inputs =
        step.premises.iter().map(|name| proven.get(name).cloned()).collect::<Option<Vec<_>>>()?;
    let derived = match (step.rule.as_str(), inputs.as_slice()) {
        ("assumption" | "axiom", [fact]) => Arc::clone(fact),
        ("resolution" | "binary_resolution", [first, second]) => {
            let (left, _) = Pure::strip_imp_prems(first.prop().term());
            let (right, _) = Pure::strip_imp_prems(second.prop().term());
            right
                .iter()
                .enumerate()
                .find_map(|(i, _)| {
                    ThmKernel::bicompose(false, first, second, i)
                        .and_then(|thm| matches_step_formula(thm, &step.formula))
                })
                .or_else(|| {
                    left.iter().enumerate().find_map(|(i, _)| {
                        ThmKernel::bicompose(false, second, first, i)
                            .and_then(|thm| matches_step_formula(thm, &step.formula))
                    })
                })?
        },
        ("paramodulation" | "superposition", [equality, target]) => {
            (0..target.nprems()).find_map(|i| {
                ThmKernel::subst_premise(equality, target, i)
                    .and_then(|thm| matches_step_formula(thm, &step.formula))
            })?
        },
        ("factoring", [clause]) => {
            let (prems, _) = Pure::strip_imp_prems(clause.prop().term());
            prems.iter().enumerate().find_map(|(i, _)| {
                ThmKernel::bicompose(false, clause, clause, i)
                    .and_then(|thm| matches_step_formula(thm, &step.formula))
            })?
        },
        _ => return None,
    };
    if !crate::core::thm::Hyps::kernel_alpha_eq(derived.prop().term(), &step.formula) {
        return None;
    }
    proven.insert(step.name.clone(), Arc::clone(&derived));
    Some(derived)
}

fn is_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Split comma-separated fields only at depth zero; reject malformed delimiters.
fn split_fields(input: &str) -> Option<Vec<&str>> {
    let mut fields = Vec::new();
    let mut start = 0;
    let mut depth = 0usize;
    for (i, byte) in input.bytes().enumerate() {
        match byte {
            b'(' | b'[' => depth += 1,
            b')' | b']' => depth = depth.checked_sub(1)?,
            b',' if depth == 0 => {
                fields.push(input[start..i].trim());
                start = i + 1;
            },
            _ => {},
        }
    }
    if depth != 0 {
        return None;
    }
    fields.push(input[start..].trim());
    Some(fields)
}

/// Only atomic proposition names and parenthesized Pure implications are
/// currently losslessly mapped. Unsupported TPTP formulas fail closed.
fn parse_tstp_formula(input: &str) -> Option<Term> {
    let text = input.trim();
    if is_identifier(text) && text.starts_with(|c: char| c.is_ascii_lowercase()) {
        return Some(Term::const_(text, Typ::base("prop")));
    }
    let inner = text.strip_prefix('(')?.strip_suffix(')')?;
    let mut depth = 0usize;
    for (i, byte) in inner.bytes().enumerate() {
        match byte {
            b'(' => depth += 1,
            b')' => depth = depth.checked_sub(1)?,
            b'=' if depth == 0 && inner[i..].starts_with("=>") => {
                let lhs = parse_tstp_formula(&inner[..i])?;
                let rhs = parse_tstp_formula(&inner[i + 2..])?;
                return Some(Pure::mk_implies(lhs, rhs));
            },
            _ => {},
        }
    }
    if depth != 0 {
        return None;
    }
    parse_tstp_formula(inner)
}

fn parse_tstp_step(line: &str) -> Option<ProofStep> {
    let fields = split_fields(line.strip_prefix("fof(")?.strip_suffix(").")?)?;
    let [name, role, formula, inference] = fields.as_slice() else {
        return None;
    };
    if !is_identifier(name) || !matches!(*role, "plain" | "axiom" | "lemma" | "conjecture") {
        return None;
    }
    let formula = parse_tstp_formula(formula)?;
    let annotations = split_fields(inference.strip_prefix("inference(")?.strip_suffix(')')?)?;
    let [rule, status, names] = annotations.as_slice() else {
        return None;
    };
    if !is_identifier(rule) || *status != "[]" {
        return None;
    }
    let refs = names.strip_prefix('[')?.strip_suffix(']')?;
    let premises = if refs.is_empty() {
        Vec::new()
    } else {
        let refs = split_fields(refs)?;
        if refs.iter().any(|name| !is_identifier(name)) {
            return None;
        }
        refs.into_iter().map(str::to_owned).collect()
    };
    Some(ProofStep { name: (*name).to_owned(), formula, rule: (*rule).to_owned(), premises })
}

impl ProofReconstructor {
    /// Duplicate input names are invalid, even if they carry the same theorem.
    pub fn new(premises: Vec<(String, Arc<Thm>)>) -> Result<Self, AtpProofParseError> {
        initial_proof_steps(&premises).ok_or_else(|| AtpProofParseError {
            line: 0,
            detail: "duplicate or empty input premise name".to_owned(),
        })?;
        Ok(Self { premises })
    }

    /// Parse only the explicitly supported lossless FOF subset.
    pub fn parse_tstp(output: &str) -> Result<Vec<ProofStep>, AtpProofParseError> {
        let mut steps = Vec::new();
        for (index, line) in output.lines().enumerate() {
            let text = line.trim();
            if text.is_empty() || text.starts_with('%') || text.starts_with('#') {
                continue;
            }
            let step = parse_tstp_step(text).ok_or_else(|| AtpProofParseError {
                line: index + 1,
                detail: "unsupported or malformed FOF proof step".to_owned(),
            })?;
            steps.push(step);
        }
        Ok(steps)
    }

    /// Replay into a fresh local table; a failed run cannot affect a retry.
    pub fn reconstruct(&mut self, steps: &[ProofStep]) -> Option<Arc<Thm>> {
        let mut proven = initial_proof_steps(&self.premises)?;
        let mut last = None;
        for step in steps {
            last = Some(replay_checked_step(&mut proven, step)?);
        }
        last
    }

    pub fn validate(&self, steps: &[ProofStep], goal: &Term) -> bool {
        let mut replay = Self { premises: self.premises.clone() };
        replay
            .reconstruct(steps)
            .is_some_and(|result| validate_proof_result(goal, &result, &[]).is_ok())
    }

    pub fn minimize(&self, steps: &[ProofStep], goal: &Term) -> Vec<String> {
        let mut needed: Vec<String> = self.premises.iter().map(|(name, _)| name.clone()).collect();
        if !self.validate(steps, goal) {
            return needed;
        }
        for (name, _) in &self.premises {
            let reduced =
                self.premises.iter().filter(|(candidate, _)| candidate != name).cloned().collect();
            if let Ok(replay) = Self::new(reduced)
                && replay.validate(steps, goal)
            {
                needed.retain(|candidate| candidate != name);
            }
        }
        needed
    }
}

// =========================================================================
// High-level reconstruction
// =========================================================================

/// Reconstruct a proof from ATP output and validate it.
///
/// Returns `Some(theorem)` if reconstruction succeeds.
pub fn reconstruct_from_atp(
    atp_output: &str,
    premises: Vec<(String, Arc<Thm>)>,
    goal: &Thm,
) -> Option<Arc<Thm>> {
    let steps = match ProofReconstructor::parse_tstp(atp_output) {
        Ok(steps) if !steps.is_empty() => steps,
        Ok(_) => return None,
        Err(error) => {
            eprintln!("ATP proof parse failed: {error}");
            return None;
        },
    };
    let mut replay = ProofReconstructor::new(premises).ok()?;
    let result = replay.reconstruct(&steps)?;
    validate_proof_result(goal.prop().term(), &result, &[]).ok()?;
    Some(result)
}

/// Independent local search, not ATP proof reconstruction.
pub fn reconstruct_with_metis(premises: Vec<(String, Arc<Thm>)>, goal: &Thm) -> Option<Arc<Thm>> {
    initial_proof_steps(&premises)?;
    let premise_arcs: Vec<Arc<Thm>> = premises.into_iter().map(|(_, thm)| thm).collect();
    let mut prover = crate::tools::metis::MetisProver::with_limits(10000);
    prover.add_premises(&premise_arcs);
    prover.prove(goal)
}

/// Try an ATP and independently derive a fully validated result via local Metis
/// search when the ATP status suggests a proof. Status itself is not evidence.
pub fn sledgehammer_prove(goal: &Thm, premises: &[(String, Arc<Thm>)]) -> Option<Arc<Thm>> {
    // First try the Metis-based LCF reconstruction
    crate::tools::metis::sledgehammer_prove_lcf(goal, premises)
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_tstp_unsupported_formula_returns_line_error() {
        let text = "fof(f1, plain, p(a), inference(assumption, [], [p0])).";
        assert_eq!(ProofReconstructor::parse_tstp(text).unwrap_err().line, 1);
    }

    #[test]
    fn parse_tstp_comments_return_empty_proof() {
        assert!(ProofReconstructor::parse_tstp("% status\n# comment").unwrap().is_empty());
    }
}
