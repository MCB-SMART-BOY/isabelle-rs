//! Sledgehammer — automatic theorem proving via external ATPs.
//!
//! Corresponds to `src/HOL/Tools/Sledgehammer/` in Isabelle/ML.
//!
//! # Overview
//!
//! Sledgehammer is Isabelle's "push-button" automation: given a goal and
//! a set of relevant premises, it invokes external first-order automatic
//! theorem provers (ATPs) to find a proof.  If an ATP succeeds, the proof
//! can be reconstructed inside the LCF kernel (see [`crate::tools::reconstruct`]).
//!
//! # Architecture
//!
//! ```text
//! Goal + Premises
//!       │
//!       ▼
//!  ┌─────────────┐
//!  │ TPTP Export  │   Convert HOL terms to FOF/TFF0 clauses
//!  └──────┬──────┘
//!         │
//!         ▼
//!  ┌─────────────┐
//!  │  ATP Call    │   Spawn `eprover`, `vampire`, or `zipperposition`
//!  └──────┬──────┘   with a time limit; feed the problem on stdin
//!         │
//!         ▼
//!  ┌─────────────┐
//!  │ Result Parse │   Scan stdout for SZS status (`Theorem`, `Timeout`, …)
//!  └──────┬──────┘
//!         │
//!         ▼
//!  ┌──────────────┐
//!  │ Reconstruct   │   (See `crate::tools::reconstruct`)
//!  └──────────────┘   Parse TSTP proof, replay in LCF kernel
//! ```
//!
//! # Key Types
//!
//! - **[`Atp`]** — Enum of supported provers.  Each variant knows its
//!   binary name and can self-detect via [`Atp::is_available`].
//! - **[`AtpResult`]** — The outcome of a prover run (`Theorem`,
//!   `Timeout`, `CounterSatisfiable`, …).
//! - **[`SledgehammerConfig`]** — Tunables: which provers to try, time
//!   limit per prover, maximum number of premises, and whether to use
//!   typed (TFF0) format.
//! - **[`Sledgehammer`]** — The runner.  Construct with defaults or a
//!   custom config, then call [`Sledgehammer::run`].
//!
//! # Supported ATPs
//!
//! | ATP            | Binary            | Format     |
//! |----------------|-------------------|------------|
//! | E Prover       | `eprover`         | FOF        |
//! | Vampire        | `vampire`         | FOF / TFF0 |
//! | Zipperposition | `zipperposition`  | FOF        |
//!
//! # Examples
//!
//! ```rust,no_run
//! use isabelle_rs::tools::sledgehammer::{Sledgehammer, Atp};
//!
//! let hammer = Sledgehammer::new();
//! println!("Available: {:?}", hammer.available_provers());
//! ```

use std::io::Write;
use std::process::{Command, Stdio};

use crate::core::thm::Thm;

// =========================================================================
// Types
// =========================================================================

/// An external ATP (Automated Theorem Prover).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Atp {
    /// E Prover (https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html)
    EProver,
    /// Vampire (https://vprover.github.io/)
    Vampire,
    /// Zipperposition (https://github.com/sneeuwballen/zipperposition)
    Zipperposition,
}

impl Atp {
    /// The command-line binary name.
    pub fn binary(&self) -> &'static str {
        match self {
            Atp::EProver => "eprover",
            Atp::Vampire => "vampire",
            Atp::Zipperposition => "zipperposition",
        }
    }

    /// Check if this ATP is installed.
    pub fn is_available(&self) -> bool {
        Command::new(self.binary())
            .arg("--version")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
    }
}

/// Result of an ATP run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AtpResult {
    /// The goal was proved (Theorem).
    Theorem,
    /// The goal was disproved (CounterSatisfiable).
    CounterSatisfiable,
    /// The ATP could not find a proof within the time limit.
    Timeout,
    /// The ATP ran out of memory.
    OutOfMemory,
    /// The ATP returned an unknown result.
    Unknown(String),
    /// The ATP could not be executed.
    AtpError(String),
}

impl AtpResult {
    /// Whether this result indicates success.
    pub fn is_success(&self) -> bool {
        matches!(self, AtpResult::Theorem)
    }
}

// =========================================================================
// Sledgehammer configuration
// =========================================================================

/// Configuration for a Sledgehammer run.
#[derive(Debug, Clone)]
pub struct SledgehammerConfig {
    /// Which ATPs to try.
    pub provers: Vec<Atp>,
    /// Time limit per ATP (in seconds).
    pub timeout: u64,
    /// Maximum number of premises to include.
    pub max_premises: usize,
    /// Whether to use typed format (TFF0) where supported.
    pub use_types: bool,
}

impl Default for SledgehammerConfig {
    fn default() -> Self {
        SledgehammerConfig {
            provers: vec![Atp::EProver, Atp::Vampire],
            timeout: 30,
            max_premises: 100,
            use_types: true,
        }
    }
}

// =========================================================================
// Sledgehammer runner
// =========================================================================

/// Run Sledgehammer on a goal.
pub struct Sledgehammer {
    config: SledgehammerConfig,
}

impl Sledgehammer {
    /// Create a new Sledgehammer with default configuration.
    pub fn new() -> Self {
        Sledgehammer {
            config: SledgehammerConfig::default(),
        }
    }

    /// Create with custom configuration.
    pub fn with_config(config: SledgehammerConfig) -> Self {
        Sledgehammer { config }
    }

    /// Run Sledgehammer on a theorem goal.
    ///
    /// Returns the name of the successful ATP (if any) and the result.
    pub fn run(&self, goal: &Thm, premises: &[Thm]) -> Option<(Atp, AtpResult)> {
        // Generate TPTP problem
        let tptp = self.generate_tptp(goal, premises);

        // Try each prover in order
        for atp in &self.config.provers {
            if !atp.is_available() {
                continue;
            }

            let result = self.run_atp(atp, &tptp);
            if result.is_success() {
                return Some((*atp, result));
            }
        }

        None
    }

    /// Generate the TPTP problem string.
    fn generate_tptp(&self, goal: &Thm, premises: &[Thm]) -> String {
        let mut buf = String::new();

        buf.push_str("% TPTP problem generated by isabelle-rs Sledgehammer\n");
        buf.push_str("% Goal: see conjecture below\n\n");

        use crate::core::logic::Pure;
        use crate::tools::tptp;

        // Export premises as axioms
        for (i, prem) in premises.iter().enumerate() {
            let (_prems, concl) = Pure::strip_imp_prems(prem.prop().term());
            buf.push_str("fof(");
            buf.push_str(&format!("premise_{i}"));
            buf.push_str(", axiom,\n    ");
            tptp::term_to_tptp(concl, &mut buf);
            buf.push_str(").\n\n");
        }

        // Export goal as conjecture
        let (_prems, concl) = Pure::strip_imp_prems(goal.prop().term());
        buf.push_str("fof(goal, conjecture,\n    ");
        tptp::term_to_tptp(concl, &mut buf);
        buf.push_str(").\n");

        buf
    }

    /// Run a specific ATP on a TPTP problem.
    fn run_atp(&self, atp: &Atp, tptp: &str) -> AtpResult {
        let timeout = self.config.timeout;

        let mut child = match Command::new(atp.binary())
            .arg("--tstp-format")
            .arg("--auto")
            .arg("--cpu-limit")
            .arg(timeout.to_string())
            .arg("-")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
        {
            Ok(child) => child,
            Err(e) => return AtpResult::AtpError(format!("Failed to start {}: {}", atp.binary(), e)),
        };

        // Write TPTP problem to stdin
        if let Some(mut stdin) = child.stdin.take() {
            let _ = stdin.write_all(tptp.as_bytes());
        }

        // Wait for the result (with timeout)
        let output = match child.wait_with_output() {
            Ok(output) => output,
            Err(e) => return AtpResult::AtpError(format!("ATP wait error: {}", e)),
        };

        let stdout = String::from_utf8_lossy(&output.stdout);
        self.parse_atp_output(atp, &stdout)
    }

    /// Parse the output of an ATP to determine the result.
    fn parse_atp_output(&self, _atp: &Atp, output: &str) -> AtpResult {
        // ATPs output results in TPTP format:
        // "SZS status Theorem" — proved
        // "SZS status CounterSatisfiable" — disproved
        // "SZS status Timeout" — timeout
        // "SZS status GaveUp" — gave up

        if output.contains("SZS status Theorem") || output.contains("Theorem") {
            AtpResult::Theorem
        } else if output.contains("SZS status CounterSatisfiable")
            || output.contains("CounterSatisfiable")
        {
            AtpResult::CounterSatisfiable
        } else if output.contains("SZS status Timeout") || output.contains("Time limit exceeded")
        {
            AtpResult::Timeout
        } else if output.contains("Out of memory") {
            AtpResult::OutOfMemory
        } else if output.contains("SZS status") || output.contains("GaveUp") {
            AtpResult::Unknown("GaveUp".to_string())
        } else if output.trim().is_empty() {
            AtpResult::Unknown("Empty output".to_string())
        } else {
            // Return the first line as context
            let first_line = output.lines().next().unwrap_or("").to_string();
            AtpResult::Unknown(first_line)
        }
    }

    /// Check which ATPs are available on this system.
    pub fn available_provers(&self) -> Vec<Atp> {
        self.config
            .provers
            .iter()
            .filter(|atp| atp.is_available())
            .copied()
            .collect()
    }
}

impl Default for Sledgehammer {
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
    use crate::core::logic::Pure;
    use crate::core::term::Term;
    use crate::core::thm::{CTerm, ThmKernel};
    use crate::core::types::Typ;

    #[test]
    fn test_atp_availability() {
        // Just check that availability detection doesn't crash
        let _ = Atp::EProver.is_available();
        let _ = Atp::Vampire.is_available();
        let _ = Atp::Zipperposition.is_available();
    }

    #[test]
    fn test_generate_tptp() {
        let mut hammer = Sledgehammer::new();
        hammer.config.max_premises = 5;

        // Create a simple goal: A ==> A
        let a = Term::const_("A", Typ::base("prop"));
        let ct = CTerm::certify(a.clone());
        let assume_a = ThmKernel::assume(ct.clone());
        let goal = ThmKernel::trivial(ct).unwrap();

        let tptp = hammer.generate_tptp(&goal, &[assume_a]);
        assert!(tptp.contains("fof(goal, conjecture"));
        assert!(tptp.contains("fof(premise_0, axiom"));
    }

    #[test]
    fn test_sledgehammer_config() {
        let config = SledgehammerConfig {
            provers: vec![Atp::EProver],
            timeout: 10,
            max_premises: 50,
            use_types: false,
        };
        assert_eq!(config.timeout, 10);
        assert_eq!(config.max_premises, 50);
    }
}
