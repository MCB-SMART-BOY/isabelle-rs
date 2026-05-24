//! WASM plugin system — sandboxed tactic execution.
//!
//! ## Architecture
//!
//! ```text
//! plugin.wasm → WasmRuntime → host functions → kernel LCF API
//!                  │
//!                  ├── memory (64KB isolated)
//!                  └── fuel (timeout via instruction counting)
//! ```
//!
//! ## Security model
//!
//! - Memory isolation: WASM linear memory, cannot access host memory
//! - Fuel metering: each instruction costs 1 fuel, hard limit enforced
//! - Whitelist: only 13 registered host functions callable
//! - No I/O: no filesystem, network, or environment access

use std::sync::Arc;

use crate::core::thm::Thm;

pub mod host;
pub mod runtime;
pub mod sdk;

// =========================================================================
// Plugin trait
// =========================================================================

/// A WASM plugin that can be loaded and executed.
///
/// Plugins are .wasm binaries that implement a specific ABI.
/// They communicate with the host via wasmtime host functions.
pub trait Plugin: Send + Sync {
    /// Plugin identifier.
    fn name(&self) -> &str;

    /// Plugin version string.
    fn version(&self) -> &str;

    /// Apply the plugin's tactic to a goal state.
    ///
    /// Returns a list of new goal states.
    /// Empty list = tactic failed.
    fn apply(&self, state: &Thm, thms: &[Arc<Thm>]) -> Vec<Thm>;
}

// =========================================================================
// PluginContext — restricted kernel access for plugins
// =========================================================================

/// Restricted view of the kernel available to plugins.
///
/// Plugins cannot create arbitrary theorems — they can only:
/// - Look up existing theorems by name
/// - Apply resolution (kernel-mediated)
/// - Access the goal's assumptions and conclusion
pub struct PluginContext {
    /// Named theorems available to the plugin.
    pub named_theorems: Vec<(String, Arc<Thm>)>,
}

impl PluginContext {
    pub fn new() -> Self {
        PluginContext {
            named_theorems: Vec::new(),
        }
    }

    /// Look up a theorem by name.
    pub fn lookup(&self, name: &str) -> Option<&Arc<Thm>> {
        self.named_theorems
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, thm)| thm)
    }
}

impl Default for PluginContext {
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
    fn test_plugin_context_empty() {
        let ctx = PluginContext::new();
        assert!(ctx.lookup("nonexistent").is_none());
    }

    #[test]
    fn test_plugin_context_lookup() {
        let mut ctx = PluginContext::new();
        let a_cterm = crate::core::thm::CTerm::certify(crate::core::term::Term::const_(
            "A",
            crate::core::types::Typ::base("prop"),
        ));
        let thm = Arc::new(crate::core::thm::ThmKernel::trivial(a_cterm).unwrap());
        ctx.named_theorems
            .push(("trivial".into(), Arc::clone(&thm)));
        assert!(ctx.lookup("trivial").is_some());
        assert!(ctx.lookup("other").is_none());
    }
}
