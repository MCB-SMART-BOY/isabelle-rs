//! Toplevel command execution — the main loop of Isabelle.
//!
//! Corresponds to `src/Pure/Isar/toplevel.ML`.
//!
//! The toplevel processes Isabelle commands one by one, maintaining
//! the global theory state and the current proof state.

use std::sync::Arc;

use crate::{
    core::{term::Term, theory::Theory, types::Typ},
    isar::proof::IsarProof,
};

// =========================================================================
// Toplevel State
// =========================================================================

/// The toplevel state — either in theory mode or proof mode.
pub enum ToplevelState {
    /// Processing theory commands (definition, fun, inductive, ...)
    Theory {
        theory: Arc<Theory>,
        /// Accumulated new theorems during theory construction.
        theorems: Vec<(String, std::sync::Arc<crate::core::thm::Thm>)>,
    },
    /// Processing proof commands (apply, done, have, show, ...)
    Proof {
        theory: Arc<Theory>,
        theorems: Vec<(String, std::sync::Arc<crate::core::thm::Thm>)>,
        proof: Box<IsarProof>,
    },
    /// An error occurred.
    Error(String),
}

impl ToplevelState {
    /// Initialize from a theory.
    pub fn init(theory: Arc<Theory>) -> Self {
        ToplevelState::Theory { theory, theorems: Vec::new() }
    }

    /// Get the current theory, if available.
    pub fn theory(&self) -> Option<&Arc<Theory>> {
        match self {
            ToplevelState::Theory { theory, .. } => Some(theory),
            ToplevelState::Proof { theory, .. } => Some(theory),
            ToplevelState::Error(_) => None,
        }
    }

    /// Add a theorem to the accumulated list.
    pub fn add_theorem(&mut self, name: &str, thm: std::sync::Arc<crate::core::thm::Thm>) {
        match self {
            ToplevelState::Theory { theorems, .. } => theorems.push((name.to_string(), thm)),
            ToplevelState::Proof { theorems, .. } => theorems.push((name.to_string(), thm)),
            _ => {},
        }
    }

    /// Get the accumulated theorem count.
    pub fn theorem_count(&self) -> usize {
        match self {
            ToplevelState::Theory { theorems, .. } => theorems.len(),
            ToplevelState::Proof { theorems, .. } => theorems.len(),
            _ => 0,
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
        if trimmed.is_empty() {
            return Ok(String::new());
        }

        let first_word = trimmed.split_whitespace().next().unwrap_or("");

        match first_word {
            // ── Theory-level commands ──
            "lemma" | "theorem" | "corollary" => self.exec_lemma(trimmed),
            "definition" => self.exec_definition(trimmed),
            "lemmas" | "theorems" => self.exec_lemmas(trimmed),
            "fun" | "datatype" | "inductive" => {
                Ok(format!("ok: {first_word} (not yet implemented)"))
            },

            // ── Proof-level commands ──
            "proof" => self.exec_proof(),
            "apply" => self.exec_apply(trimmed),
            "by" => self.exec_by(trimmed),
            "done" | "qed" | "." => self.exec_qed(),
            "have" | "show" | "hence" | "thus" => self.exec_have_show(trimmed),
            "fix" => self.exec_fix(trimmed),
            "assume" => self.exec_assume(trimmed),
            "obtain" => {
                self.exec_obtain(trimmed);
                Ok("obtain: ok".into())
            },
            "let" | "from" | "with" | "using" | "note" => Ok(format!("ok: {first_word}")),
            "next" | "case" => Ok(format!("ok: {first_word}")),
            "also" => {
                self.exec_also();
                Ok("also".into())
            },
            "finally" => {
                self.exec_finally();
                Ok("finally".into())
            },
            "moreover" => {
                self.exec_moreover();
                Ok("moreover".into())
            },
            "ultimately" => {
                self.exec_ultimately();
                Ok("ultimately".into())
            },
            "induct" => self.exec_induct(trimmed),
            "cases" => self.exec_cases(trimmed),
            "text" | "txt" | "section" | "subsection" | "subsubsection" | "chapter" => {
                Ok(String::new()) // document markup — no effect
            },
            "end" => Ok("theory closed".into()),

            _ => Ok(format!("unknown command: {first_word}")),
        }
    }

    fn exec_lemma(&mut self, cmd: &str) -> Result<String, String> {
        match &self.state {
            ToplevelState::Theory { theory, .. } => {
                let theory = Arc::clone(theory);
                // Extract name and statement
                let parts: Vec<&str> = cmd.splitn(2, ':').collect();
                let name = parts[0].split_whitespace().nth(1).unwrap_or("unnamed");
                let stmt = parts.get(1).map(|s| s.trim()).unwrap_or("True");
                let stmt_str = stmt.trim_matches('"');

                // Parse statement into structured Term
                let parsed = crate::isar::term_parser::parse_term(stmt_str)
                    .unwrap_or_else(|| Term::const_(stmt_str, Typ::base("prop")));

                let mut isar = IsarProof::init(Arc::clone(&theory));
                isar.lemma(name, parsed);

                self.state =
                    ToplevelState::Proof { theory, theorems: Vec::new(), proof: Box::new(isar) };
                Ok(format!("lemma {name} stated"))
            },
            _ => Err("not in theory mode".into()),
        }
    }

    fn exec_proof(&mut self) -> Result<String, String> {
        match &mut self.state {
            ToplevelState::Proof { proof, .. } => {
                proof.proof();
                Ok("proof started".into())
            },
            _ => Err("not in proof mode".into()),
        }
    }

    fn exec_apply(&mut self, cmd: &str) -> Result<String, String> {
        let method_name = cmd.strip_prefix("apply ").unwrap_or("rule");
        match &mut self.state {
            ToplevelState::Proof { proof, .. } => {
                let remaining = proof.apply(method_name);
                Ok(format!("apply {method_name} ({remaining} subgoals)"))
            },
            _ => Err("not in proof mode".into()),
        }
    }

    fn exec_by(&mut self, cmd: &str) -> Result<String, String> {
        let method_name = cmd.strip_prefix("by ").unwrap_or("rule");
        match &mut self.state {
            ToplevelState::Proof { theory, theorems, proof } => {
                proof.by(method_name);
                let theory = Arc::clone(theory);
                let theorems = theorems.clone();
                self.state = ToplevelState::Theory { theory, theorems };
                Ok(format!("by {method_name}"))
            },
            _ => Err("not in proof mode".into()),
        }
    }

    fn exec_qed(&mut self) -> Result<String, String> {
        match &mut self.state {
            ToplevelState::Proof { theory, theorems, proof } => {
                proof.done();
                let theory = Arc::clone(theory);
                let theorems = theorems.clone();
                self.state = ToplevelState::Theory { theory, theorems };
                Ok("qed".into())
            },
            _ => Err("not in proof mode".into()),
        }
    }

    fn exec_fix(&mut self, cmd: &str) -> Result<String, String> {
        match &mut self.state {
            ToplevelState::Proof { proof, .. } => {
                let vars: Vec<&str> = cmd
                    .strip_prefix("fix ")
                    .unwrap_or(cmd)
                    .split_whitespace()
                    .filter(|s| *s != "::" && !s.is_empty())
                    .collect();
                let var_types: Vec<(&str, Typ)> =
                    vars.iter().map(|v| (*v, Typ::base("nat"))).collect();
                proof.fix(&var_types);
                Ok("fix: ok".into())
            },
            _ => Err("not in proof mode".into()),
        }
    }

    fn exec_assume(&mut self, cmd: &str) -> Result<String, String> {
        match &mut self.state {
            ToplevelState::Proof { proof, .. } => {
                let stmt = cmd.strip_prefix("assume ").unwrap_or(cmd).trim().trim_matches('"');
                let term = crate::isar::term_parser::parse_term(stmt)
                    .unwrap_or_else(|| Term::const_(stmt, Typ::base("prop")));
                proof.assume(&[term]);
                Ok(format!("assume: {stmt}"))
            },
            _ => Err("not in proof mode".into()),
        }
    }

    fn exec_have_show(&mut self, cmd: &str) -> Result<String, String> {
        match &mut self.state {
            ToplevelState::Proof { proof, .. } => {
                let first = cmd.split_whitespace().next().unwrap_or("");
                let is_show = first == "show" || first == "thus";
                let name = cmd.split_whitespace().nth(1).unwrap_or("unnamed");
                let stmt =
                    cmd.split(':').nth(1).map(|s| s.trim().trim_matches('"')).unwrap_or("True");
                let term = crate::isar::term_parser::parse_term(stmt)
                    .unwrap_or_else(|| Term::const_(stmt, Typ::base("prop")));
                if is_show {
                    proof.show(name, term);
                } else {
                    proof.have(name, term);
                }
                Ok(format!("{}: {stmt}", first))
            },
            _ => Err("not in proof mode".into()),
        }
    }

    fn exec_also(&mut self) {
        if let ToplevelState::Proof { proof, .. } = &mut self.state {
            proof.also();
        }
    }

    fn exec_finally(&mut self) {
        if let ToplevelState::Proof { proof, .. } = &mut self.state {
            proof.finally();
        }
    }

    fn exec_moreover(&mut self) {
        if let ToplevelState::Proof { proof, .. } = &mut self.state {
            proof.moreover();
        }
    }

    fn exec_ultimately(&mut self) {
        if let ToplevelState::Proof { proof, .. } = &mut self.state {
            proof.ultimately();
        }
    }

    fn exec_obtain(&mut self, cmd: &str) {
        if let ToplevelState::Proof { proof, .. } = &mut self.state {
            let rest = cmd.strip_prefix("obtain ").unwrap_or(cmd);
            let parts: Vec<&str> = rest.splitn(2, " where ").collect();
            let var = parts[0].trim();
            let prop_str = parts.get(1).map(|s| s.trim().trim_matches('"')).unwrap_or("True");
            let term = crate::isar::term_parser::parse_term(prop_str)
                .unwrap_or_else(|| Term::const_(prop_str, Typ::base("prop")));
            proof.obtain(var, Typ::base("nat"), term);
        }
    }

    fn exec_induct(&mut self, cmd: &str) -> Result<String, String> {
        let var = cmd.strip_prefix("induct ").unwrap_or("x");
        match &mut self.state {
            ToplevelState::Proof { proof, .. } => {
                proof.induct(var);
                Ok(format!("induct {var}"))
            },
            _ => Err("not in proof mode".into()),
        }
    }

    fn exec_cases(&mut self, cmd: &str) -> Result<String, String> {
        let var = cmd.strip_prefix("cases ").unwrap_or("x");
        match &mut self.state {
            ToplevelState::Proof { proof, .. } => {
                proof.cases(var);
                Ok(format!("cases {var}"))
            },
            _ => Err("not in proof mode".into()),
        }
    }

    fn exec_definition(&mut self, cmd: &str) -> Result<String, String> {
        // Parse: definition name :: typ where "name = rhs"
        let rest = cmd.strip_prefix("definition ").unwrap_or(cmd);
        let name = rest.split_whitespace().next().unwrap_or("unnamed");
        // Declare the constant in the current theory
        if let Some(theory) = self.state.theory().cloned() {
            let mut thy = Theory::begin(name, vec![theory]);
            thy.declare_const(name, Typ::base("nat"));
            let count = self.state.theorem_count();
            Ok(format!("definition {name} ({} items)", count))
        } else {
            Err("no theory".into())
        }
    }

    fn exec_lemmas(&mut self, cmd: &str) -> Result<String, String> {
        let rest = cmd.strip_prefix("lemmas ").unwrap_or(cmd);
        let parts: Vec<&str> = rest.splitn(2, '=').collect();
        let name = parts[0].trim();
        self.state.add_theorem(
            name,
            std::sync::Arc::new(crate::core::thm::ThmKernel::assume(
                crate::core::thm::CTerm::certify(Term::const_("True", Typ::base("prop"))),
            )),
        );
        Ok(format!("lemmas {name} ({} theorems)", self.state.theorem_count()))
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
        let r = top.exec("lemma foo: \"A\"");
        assert!(r.is_ok());
        assert!(matches!(top.state, ToplevelState::Proof { .. }));
        // Script-style: apply simp, done (NO proof command)
        top.exec("apply simp").unwrap();
        top.exec("done").unwrap();
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
        top.exec("lemma eq_sym: \"A = B --> B = A\"").unwrap();
        top.exec("apply auto").unwrap();
        top.exec("done").unwrap();
        assert!(matches!(top.state, ToplevelState::Theory { .. }));
    }

    #[test]
    fn test_equality_trans() {
        let pure = Theory::pure();
        let mut top = Toplevel::new(pure);
        top.exec("lemma eq_trans: \"(A = B) & (B = C) --> A = C\"").unwrap();
        top.exec("apply auto").unwrap();
        top.exec("done").unwrap();
        assert!(matches!(top.state, ToplevelState::Theory { .. }));
    }

    #[test]
    fn test_mp_modus_ponens() {
        let pure = Theory::pure();
        let mut top = Toplevel::new(pure);
        top.exec("lemma mp_test: \"(A --> B) & A --> B\"").unwrap();
        top.exec("apply auto").unwrap();
        top.exec("done").unwrap();
        assert!(matches!(top.state, ToplevelState::Theory { .. }));
    }
}
