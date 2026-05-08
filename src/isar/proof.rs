//! Isar proof state machine.
//!
//! Corresponds to `src/Pure/Isar/proof.ML`.
//!
//! Isar (Intelligible semi-automated reasoning) is Isabelle's structured
//! proof language. The proof state machine manages:
//! - Goals (what we need to prove)
//! - Subgoals (decomposed from goals)
//! - Fix/assume (local context)
//! - `have`/`show` (intermediate statements)
//! - `proof`/`qed` (block structure)
//!
//! ## Proof State
//!
//! A proof state is either:
//! - **State**: a list of subgoals, each with a local context
//! - **Prove**: a single goal with a statement to prove
//! - **Chain**: facts being chained into the next step

use std::sync::Arc;

use crate::core::term::Term;
use crate::core::thm::{CTerm, Thm, ThmKernel};
use crate::core::types::Typ;

// =========================================================================
// Proof Node — one step in the proof tree
// =========================================================================

/// A single node in the proof tree.
/// Each node has a context (fixed vars + assumptions), a statement,
/// and a proof method (how to prove it).
#[derive(Clone, Debug)]
pub struct ProofNode {
    /// Locally fixed variables: `fix x y`
    pub fixes: Vec<(String, Typ)>,
    /// Local assumptions: `assume "A"`
    pub assumes: Vec<Term>,
    /// What we are proving at this node
    pub statement: Term,
    /// How we proved it (method or block)
    pub method: Option<ProofMethod>,
    /// Sub-nodes (for block proofs)
    pub children: Vec<ProofNode>,
}

/// A proof method.
#[derive(Clone, Debug)]
pub enum ProofMethod {
    /// `by method` — a terminal proof
    By(String),
    /// `apply method` — a tactic step
    Apply(String),
    /// `proof` ... `qed` — a block proof
    Block(Vec<ProofNode>),
}

// =========================================================================
// Proof State
// =========================================================================

/// The state of an Isar proof.
#[derive(Clone, Debug)]
pub enum ProofState {
    /// No proof in progress.
    Idle,
    /// A lemma/theorem has been stated, waiting for proof.
    /// Contains: name, statement, enclosing theory context.
    Stated {
        name: String,
        statement: Term,
    },
    /// Inside a proof block, working on subgoals.
    /// Contains: the proof tree built so far.
    Proving {
        root: ProofNode,
        current_goal: Term,
    },
    /// Proof completed successfully.
    Done {
        name: String,
        theorem: Arc<Thm>,
    },
}

impl ProofState {
    /// Start a new lemma.
    pub fn lemma(name: String, statement: Term) -> Self {
        ProofState::Stated { name, statement }
    }

    /// Begin the proof of the currently stated lemma.
    pub fn begin_proof(&self) -> Option<Self> {
        match self {
            ProofState::Stated { name, statement } => {
                let node = ProofNode {
                    fixes: vec![],
                    assumes: vec![],
                    statement: statement.clone(),
                    method: None,
                    children: vec![],
                };
                Some(ProofState::Proving {
                    root: node,
                    current_goal: statement.clone(),
                })
            }
            _ => None,
        }
    }

    /// Apply a method to the current goal.
    pub fn apply_method(&self, method: ProofMethod) -> Option<Self> {
        match self {
            ProofState::Proving { root, current_goal } => {
                let mut new_root = root.clone();
                match &method {
                    ProofMethod::By(_) | ProofMethod::Apply(_) => {
                        new_root.method = Some(method.clone());
                        Some(ProofState::Proving {
                            root: new_root,
                            current_goal: current_goal.clone(),
                        })
                    }
                    ProofMethod::Block(children) => {
                        new_root.children = children.clone();
                        new_root.method = Some(method);
                        Some(ProofState::Proving {
                            root: new_root,
                            current_goal: current_goal.clone(),
                        })
                    }
                }
            }
            _ => None,
        }
    }

    /// Finish the proof (`qed` / `done`).
    pub fn finish(&self, theorem: Arc<Thm>) -> Option<Self> {
        match self {
            ProofState::Stated { name, .. } => {
                Some(ProofState::Done { name: name.clone(), theorem })
            }
            ProofState::Proving { .. } => {
                Some(ProofState::Done { name: "unnamed".into(), theorem })
            }
            _ => None,
        }
    }
}

// =========================================================================
// Proof Manager
// =========================================================================

/// Manages the lifecycle of an Isar proof.
pub struct ProofManager {
    pub state: ProofState,
}

impl ProofManager {
    pub fn new() -> Self {
        ProofManager { state: ProofState::Idle }
    }

    /// Start a new lemma.
    pub fn lemma(&mut self, name: String, statement: Term) {
        self.state = ProofState::lemma(name, statement);
    }

    /// Begin the proof phase.
    pub fn proof(&mut self) -> Option<()> {
        self.state = self.state.begin_proof()?;
        Some(())
    }

    /// Apply a method step.
    pub fn apply(&mut self, method_name: String) -> Option<()> {
        self.state = self.state.apply_method(ProofMethod::Apply(method_name))?;
        Some(())
    }

    /// Terminal proof.
    pub fn by(&mut self, method_name: String) -> Option<()> {
        self.state = self.state.apply_method(ProofMethod::By(method_name))?;
        // For now, skip actual proof checking
        Some(())
    }

    /// Finish the proof.
    pub fn qed(&mut self, thm: Arc<Thm>) -> Option<()> {
        self.state = self.state.finish(thm)?;
        Some(())
    }

    /// Get the current goal (if any).
    pub fn current_goal(&self) -> Option<&Term> {
        match &self.state {
            ProofState::Proving { current_goal, .. } => Some(current_goal),
            _ => None,
        }
    }
}

impl Default for ProofManager {
    fn default() -> Self {
        Self::new()
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_proof_lifecycle() {
        let mut pm = ProofManager::new();

        // lemma foo: "A"
        let stmt = Term::const_("A", Typ::base("prop"));
        pm.lemma("foo".into(), stmt.clone());
        assert!(matches!(pm.state, ProofState::Stated { .. }));

        // proof (enter proof mode)
        pm.proof();
        assert!(matches!(pm.state, ProofState::Proving { .. }));

        // apply auto
        pm.apply("auto".into());
        assert!(pm.current_goal().is_some());

        // qed
        let trivial = Arc::new(ThmKernel::trivial(CTerm::certify(stmt)));
        pm.qed(trivial);
        assert!(matches!(pm.state, ProofState::Done { .. }));
    }
}
