//! Theory session management — ROOT file parsing and session building.
//!
//! ## What this module does
//!
//! In Isabelle, a **session** is a collection of theory files compiled
//! together. Sessions are defined in `ROOT` files:
//!
//! ```text
//! session HOL = Pure +
//!   theories
//!     Main
//!     Complex_Main
//!   theories [condition = ISABELLE_FULL_TEST]
//!     "HOL-Test"
//! ```
//!
//! This module:
//! - Parses `ROOT` files
//! - Builds dependency graphs
//! - Schedules theory compilation in dependency order
//! - Manages session-level state (shared between FileWorkers)
//!
//! ## Status: Stub
//!
//! Currently, theory loading is handled ad-hoc by `hol_loader.rs`.
//! This module will formalize the process.

pub mod cache;

use std::collections::HashMap;
use std::path::PathBuf;

// =========================================================================
// Session description
// =========================================================================

/// A session description (parsed from ROOT file).
#[derive(Debug, Clone)]
pub struct SessionInfo {
    /// Session name (e.g., "HOL", "HOL-Analysis").
    pub name: String,
    /// Parent sessions (e.g., ["Pure"] for HOL).
    pub parents: Vec<String>,
    /// Theory files in this session (in order).
    pub theories: Vec<TheoryInfo>,
    /// Additional options.
    pub options: HashMap<String, String>,
}

/// A theory file entry in a session.
#[derive(Debug, Clone)]
pub struct TheoryInfo {
    /// Theory name (e.g., "Main", "Complex_Main").
    pub name: String,
    /// Path to the .thy file.
    pub path: PathBuf,
    /// Conditional compilation flag.
    pub condition: Option<String>,
}

// =========================================================================
// Session manager
// =========================================================================

/// Manages session loading and theory scheduling.
pub struct SessionManager {
    /// All known sessions.
    sessions: HashMap<String, SessionInfo>,
}

impl SessionManager {
    pub fn new() -> Self {
        SessionManager {
            sessions: HashMap::new(),
        }
    }

    /// Register a session.
    pub fn register(&mut self, info: SessionInfo) {
        self.sessions.insert(info.name.clone(), info);
    }

    /// Get a session by name.
    pub fn get(&self, name: &str) -> Option<&SessionInfo> {
        self.sessions.get(name)
    }

    /// Get theories in dependency order (topological sort).
    pub fn theories_in_order(&self, _session: &str) -> Vec<&TheoryInfo> {
        // TODO: Topological sort of theories by imports
        Vec::new()
    }
}

impl Default for SessionManager {
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
    fn test_session_manager() {
        let mut mgr = SessionManager::new();
        let info = SessionInfo {
            name: "Test".into(),
            parents: vec!["Pure".into()],
            theories: vec![],
            options: HashMap::new(),
        };
        mgr.register(info);
        assert!(mgr.get("Test").is_some());
        assert!(mgr.get("Nonexistent").is_none());
    }
}
