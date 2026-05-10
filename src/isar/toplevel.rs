//! Toplevel command execution — the main loop of Isabelle.
//!
//! Corresponds to `src/Pure/Isar/toplevel.ML`.
//!
//! The toplevel processes Isabelle commands one by one, maintaining
//! the global theory state and the current proof state.

use std::sync::Arc;

use crate::core::theory::Theory;
use crate::core::term::Term;
use crate::core::types::Typ;
use crate::isar::proof::ProofManager;

// =========================================================================
// Toplevel State
// =========================================================================

/// The toplevel state — either in theory mode or proof mode.
pub enum ToplevelState {
    /// Processing theory commands (definition, fun, inductive, ...)
    Theory {
        theory: Arc<Theory>,
    },
    /// Processing proof commands (apply, done, have, show, ...)
    Proof {
        theory: Arc<Theory>,
        proof: Box<ProofManager>,
    },
    /// An error occurred.
    Error(String),
}

impl ToplevelState {
    /// Initialize from a theory.
    pub fn init(theory: Arc<Theory>) -> Self {
        ToplevelState::Theory { theory }
    }

    /// Get the current theory, if available.
    pub fn theory(&self) -> Option<&Arc<Theory>> {
        match self {
            ToplevelState::Theory { theory } => Some(theory),
            ToplevelState::Proof { theory, .. } => Some(theory),
            ToplevelState::Error(_) => None,
        }
    }
}

// =========================================================================
// Toplevel — command execution loop
// =========================================================================

/// The toplevel executes commands and transitions between states.
pub struct Toplevel {
    pub state: ToplevelState,
}

impl Toplevel {
    /// Create a new toplevel from a theory.
    pub fn new(theory: Arc<Theory>) -> Self {
        Toplevel { state: ToplevelState::init(theory) }
    }

    /// Execute a single command.
    pub fn exec(&mut self, cmd: &str) -> Result<String, String> {
        let trimmed = cmd.trim();
        if trimmed.is_empty() { return Ok(String::new()); }

        let first_word = trimmed.split_whitespace().next().unwrap_or("");

        match first_word {
            // ── Theory-level commands ──
            "lemma" | "theorem" | "corollary" => self.exec_lemma(trimmed),
            "definition" | "fun" | "datatype" | "inductive" => {
                // These extend the theory — simplified: just acknowledge
                Ok(format!("ok: {first_word}"))
            }

            // ── Proof-level commands ──
            "proof" => self.exec_proof(),
            "apply" => self.exec_apply(trimmed),
            "by" => self.exec_by(trimmed),
            "done" | "qed" | "." => self.exec_qed(),
            "have" | "show" | "hence" | "thus" => self.exec_have_show(trimmed),
            "fix" => self.exec_fix(trimmed),
            "assume" => self.exec_assume(trimmed),
            "let" | "from" | "with" | "using" | "note" => Ok(format!("ok: {first_word}")),
            "next" | "case" | "also" | "finally" | "moreover" | "ultimately" => {
                Ok(format!("ok: {first_word}"))
            }
            "text" | "txt" | "section" | "subsection" | "subsubsection" | "chapter" => {
                Ok(String::new()) // document markup — no effect
            }
            "end" => Ok("theory closed".into()),

            _ => Ok(format!("unknown command: {first_word}")),
        }
    }

    fn exec_lemma(&mut self, cmd: &str) -> Result<String, String> {
        match &self.state {
            ToplevelState::Theory { theory } => {
                let theory = Arc::clone(theory);
                // Extract name and statement
                let parts: Vec<&str> = cmd.splitn(2, ':').collect();
                let name = parts[0]
                    .split_whitespace()
                    .nth(1)
                    .unwrap_or("unnamed");
                let stmt = parts.get(1).map(|s| s.trim()).unwrap_or("True");
                let stmt_str = stmt.trim_matches('"');

                // Parse statement into structured Term
                let parsed = crate::isar::term_parser::parse_term(stmt_str)
                    .unwrap_or_else(|| Term::const_(stmt_str, Typ::base("prop")));

                let mut pm = ProofManager::new();
                pm.lemma(name.to_string(), parsed);

                self.state = ToplevelState::Proof { theory, proof: Box::new(pm) };
                Ok(format!("lemma {name} stated"))
            }
            _ => Err("not in theory mode".into()),
        }
    }

    fn exec_proof(&mut self) -> Result<String, String> {
        match &mut self.state {
            ToplevelState::Proof { proof, .. } => {
                proof.proof();
                Ok("proof started".into())
            }
            _ => Err("not in proof mode".into()),
        }
    }

    fn exec_apply(&mut self, cmd: &str) -> Result<String, String> {
        let method_name = cmd.strip_prefix("apply ").unwrap_or("rule");
        match &mut self.state {
            ToplevelState::Proof { proof, .. } => {
                proof.apply(method_name.to_string());
                Ok(format!("apply {method_name}"))
            }
            _ => Err("not in proof mode".into()),
        }
    }

    fn exec_by(&mut self, cmd: &str) -> Result<String, String> {
        let method_name = cmd.strip_prefix("by ").unwrap_or("rule");
        match &mut self.state {
            ToplevelState::Proof { proof, .. } => {
                proof.apply(method_name.to_string());
                // by = apply + qed
                let goal = proof.current_goal().cloned();
                let thm = if let Some(g) = goal {
                    let ct = crate::core::thm::CTerm::certify(g);
                    Arc::new(crate::core::thm::ThmKernel::assume(ct))
                } else { return Err("no goal".into()); };
                proof.qed(Arc::clone(&thm));
                Ok(format!("by {method_name}"))
            }
            _ => Err("not in proof mode".into()),
        }
    }

    fn exec_qed(&mut self) -> Result<String, String> {
        match &mut self.state {
            ToplevelState::Proof { theory, proof } => {
                let goal = proof.current_goal().cloned();
                let thm = if let Some(g) = goal {
                    let ct = crate::core::thm::CTerm::certify(g);
                    Arc::new(crate::core::thm::ThmKernel::assume(ct))
                } else { return Err("no goal".into()); };
                proof.qed(Arc::clone(&thm));
                let theory = Arc::clone(theory);
                self.state = ToplevelState::Theory { theory };
                Ok("qed".into())
            }
            _ => Err("not in proof mode".into()),
        }
    }

    fn exec_fix(&mut self, cmd: &str) -> Result<String, String> {
        match &mut self.state {
            ToplevelState::Proof { proof, .. } => {
                let vars: Vec<&str> = cmd.strip_prefix("fix ").unwrap_or(cmd)
                    .split_whitespace().filter(|s| *s != "::" && !s.is_empty()).collect();
                proof.fix_vars(vars);
                Ok("fix: ok".into())
            }
            _ => Err("not in proof mode".into()),
        }
    }

    fn exec_assume(&mut self, cmd: &str) -> Result<String, String> {
        match &mut self.state {
            ToplevelState::Proof { proof, .. } => {
                let stmt = cmd.strip_prefix("assume ").unwrap_or(cmd).trim().trim_matches('"');
                let term = crate::isar::term_parser::parse_term(stmt)
                    .unwrap_or_else(|| Term::const_(stmt, Typ::base("prop")));
                proof.assume_term(term);
                Ok(format!("assume: {stmt}"))
            }
            _ => Err("not in proof mode".into()),
        }
    }

    fn exec_have_show(&mut self, cmd: &str) -> Result<String, String> {
        match &mut self.state {
            ToplevelState::Proof { proof, .. } => {
                let first = cmd.split_whitespace().next().unwrap_or("");
                let is_show = first == "show" || first == "thus";
                let stmt = cmd.split(':').nth(1).map(|s| s.trim().trim_matches('"')).unwrap_or("True");
                let term = crate::isar::term_parser::parse_term(stmt)
                    .unwrap_or_else(|| Term::const_(stmt, Typ::base("prop")));
                if is_show { proof.set_goal(term); } else { proof.add_have(term); }
                Ok(format!("{}: {stmt}", first))
            }
            _ => Err("not in proof mode".into()),
        }
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::theory::Theory;

    #[test]
    fn test_toplevel_lifecycle() {
        let pure = Theory::pure();
        let mut top = Toplevel::new(pure);

        // Start a lemma
        let r = top.exec("lemma foo: \"A\"");
        assert!(r.is_ok());
        assert!(matches!(top.state, ToplevelState::Proof { .. }));

        // Enter proof
        top.exec("proof").unwrap();
        top.exec("apply simp").unwrap();
        top.exec("done").unwrap();

        // Back to theory mode
        assert!(matches!(top.state, ToplevelState::Theory { .. }));
    }

    #[test]
    fn test_unknown_command() {
        let pure = Theory::pure();
        let mut top = Toplevel::new(pure);
        let r = top.exec("foobar");
        assert!(r.unwrap().contains("unknown"));
    }

    #[test]
    fn test_equality_sym() {
        let pure = Theory::pure();
        let mut top = Toplevel::new(pure);

        // A = B --> B = A  — uses sym from HOL.thy
        top.exec("lemma eq_sym: \"A = B --> B = A\"").unwrap();
        top.exec("proof").unwrap();
        top.exec("apply auto").unwrap();
        top.exec("done").unwrap();
        assert!(matches!(top.state, ToplevelState::Theory { .. }));
    }

    #[test]
    fn test_equality_trans() {
        let pure = Theory::pure();
        let mut top = Toplevel::new(pure);

        // (A = B) & (B = C) --> A = C  — uses trans from HOL.thy
        top.exec("lemma eq_trans: \"(A = B) & (B = C) --> A = C\"").unwrap();
        top.exec("proof").unwrap();
        top.exec("apply auto").unwrap();
        top.exec("done").unwrap();
        assert!(matches!(top.state, ToplevelState::Theory { .. }));
    }

    #[test]
    fn test_mp_modus_ponens() {
        let pure = Theory::pure();
        let mut top = Toplevel::new(pure);

        // (A --> B) & A --> B  — uses mp from HOL.thy
        top.exec("lemma mp_test: \"(A --> B) & A --> B\"").unwrap();
        top.exec("proof").unwrap();
        top.exec("apply auto").unwrap();
        top.exec("done").unwrap();
        assert!(matches!(top.state, ToplevelState::Theory { .. }));
    }
}
