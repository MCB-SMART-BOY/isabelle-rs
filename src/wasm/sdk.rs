//! Plugin SDK — types and macros for writing Isabelle-rs WASM plugins.
//!
//! Plugin authors use these types to write tactics in Rust that
//! compile to .wasm and run in the Isabelle-rs sandbox.
//!
//! ## Example plugin
//!
//! ```rust,ignore
//! use isabelle_wasm_sdk::*;
//!
//! #[isabelle_plugin]
//! pub fn my_auto(goal: &Goal, ctx: &mut PluginContext) -> Vec<Vec<Goal>> {
//!     // Try assumption first
//!     if let Some(result) = try_assumption(goal) {
//!         return result;
//!     }
//!     // Try each named theorem
//!     for (name, thm) in &ctx.theorems() {
//!         if let Some(result) = try_resolve(goal, thm) {
//!             return result;
//!         }
//!     }
//!     vec![] // failed
//! }
//! ```

use serde::{Deserialize, Serialize};

// =========================================================================
// Serialized types (passed between host and plugin via JSON)
// =========================================================================

/// A goal as seen by the plugin (serialized form).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginGoal {
    /// Serialized assumptions.
    pub assumptions: Vec<PluginTerm>,
    /// Serialized conclusion.
    pub conclusion: PluginTerm,
}

/// A term as seen by the plugin (simplified representation).
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
    App {
        func: Box<PluginTerm>,
        arg: Box<PluginTerm>,
    },
}

/// Result returned by the plugin.
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
            conclusion: PluginTerm::Const {
                name: "True".into(),
            },
        };
        let json = serde_json::to_string(&goal).unwrap();
        let decoded: PluginGoal = serde_json::from_str(&json).unwrap();
        assert!(matches!(decoded.conclusion, PluginTerm::Const { .. }));
    }

    #[test]
    fn test_plugin_result_serde() {
        let result = PluginResult {
            outcomes: vec![vec![]],
        };
        let json = serde_json::to_string(&result).unwrap();
        let decoded: PluginResult = serde_json::from_str(&json).unwrap();
        assert_eq!(decoded.outcomes.len(), 1);
    }
}
