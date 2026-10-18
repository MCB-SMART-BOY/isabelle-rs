//! Search-only metadata and unverified tactic proposals for WASM plugins.
//!
//! The runtime does not yet execute tactics or reconstruct their results.
//! Serialization of a proposal never certifies a term or accepts a proof.
//! A legacy search handle is only an index into metadata for one invocation.
//! The serialized proposal types below are data definitions only: the current
//! runtime does not exchange them through the plugin's `apply_tactic` export.
//!
//! `env.host_lookup(ptr, len)` returns a positive legacy metadata handle or
//! `-1` for an unavailable name/invalid input. `env.host_fact_kind(handle)`
//! returns `-1` for missing/stale handles; otherwise 1 = transitional strict
//! closed, 2 = compat closed oracle-free, 3 = open oracle-free, 4 = unverified
//! closed, 5 = admitted. None of these codes means `TrustedTheorem`. The WASM
//! ABI does not yet expose proposition text or execute a tactic.

use serde::{Deserialize, Serialize};

// =========================================================================
// Serialized types (passed between host and plugin via JSON)
// =========================================================================

/// A proposed goal as seen by a plugin; not a certified proposition.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginGoal {
    /// Serialized assumptions.
    pub assumptions: Vec<PluginTerm>,
    /// Serialized conclusion.
    pub conclusion: PluginTerm,
}

/// A simplified display term; type and theory certificates are absent.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PluginTerm {
    /// A constant.
    Const { name: String },
    /// A free variable.
    Free { name: String },
    /// A bound variable (de Bruijn index).
    Bound(usize),
    /// Lambda abstraction.
    Abs { name: String, body: Box<PluginTerm> },
    /// Application.
    App { func: Box<PluginTerm>, arg: Box<PluginTerm> },
}

/// Unverified proposals returned by a plugin, not theorem proofs.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginResult {
    /// List of outcomes (each is a list of subgoals).
    pub outcomes: Vec<Vec<PluginGoal>>,
}

// =========================================================================
// Plugin ABI constants
// =========================================================================

/// Memory offset for input/output data.
pub const DATA_OFFSET: i32 = 1024;

/// Maximum data size (64KB - 1KB header).
pub const MAX_DATA_SIZE: usize = 64512;

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_plugin_goal_serde() {
        let goal = PluginGoal {
            assumptions: vec![],
            conclusion: PluginTerm::Const { name: "True".into() },
        };
        let json = serde_json::to_string(&goal).unwrap();
        let decoded: PluginGoal = serde_json::from_str(&json).unwrap();
        assert!(matches!(decoded.conclusion, PluginTerm::Const { .. }));
    }

    #[test]
    fn test_plugin_result_serde() {
        let result = PluginResult { outcomes: vec![vec![]] };
        let json = serde_json::to_string(&result).unwrap();
        let decoded: PluginResult = serde_json::from_str(&json).unwrap();
        assert_eq!(decoded.outcomes.len(), 1);
    }
}
