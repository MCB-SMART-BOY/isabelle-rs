//! WASM plugin interface for legacy search and proposed tactic results.
//!
//! Wasmtime execution uses a fuel budget, but this runtime sets no explicit
//! Store memory limit or wall-clock deadline. It is not a complete resource
//! sandbox. No plugin result is a trusted theorem; tactic execution and proof
//! reconstruction are not implemented.

use std::sync::Arc;

use self::host::LegacySearchFact;
use crate::core::thm::Thm;

pub mod host;
pub mod runtime;
pub mod sdk;

// =========================================================================
// Plugin trait
// =========================================================================

/// A WASM plugin that can be loaded and queried.
///
/// The legacy tactic API is not an acceptance path. `apply` currently returns
/// no results; future proposals must be reconstructed by the trusted kernel.
pub trait Plugin: Send + Sync {
    fn name(&self) -> &str;
    fn version(&self) -> &str;
    fn apply(&self, state: &Thm, thms: &[Arc<Thm>]) -> Vec<Thm>;
}

// =========================================================================
// PluginContext — legacy search view
// =========================================================================

/// Read-only legacy search metadata available to a plugin.
///
/// Lookup does not supply a theorem object or certify its proposition.
pub struct PluginContext {
    named_facts: Vec<(String, Arc<LegacySearchFact>)>,
}

impl PluginContext {
    pub fn new() -> Self {
        Self { named_facts: Vec::new() }
    }

    /// Index a legacy fact for search, discarding its proof object.
    pub fn index_legacy(&mut self, name: String, theorem: &Thm) {
        self.named_facts.push((name, Arc::new(LegacySearchFact::from_legacy(theorem))));
    }

    /// Look up shared search metadata by name; never returns a theorem.
    pub fn lookup(&self, name: &str) -> Option<&Arc<LegacySearchFact>> {
        self.named_facts.iter().find(|(key, _)| key == name).map(|(_, fact)| fact)
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
    fn plugin_context_lookup_returns_legacy_metadata() {
        let mut ctx = PluginContext::new();
        let a_cterm = crate::core::thm::CTerm::certify(crate::core::term::Term::const_(
            "A",
            crate::core::types::Typ::base("prop"),
        ));
        let theorem = crate::core::thm::ThmKernel::admit(a_cterm, "test");
        ctx.index_legacy("A".into(), &theorem);
        assert_eq!(ctx.lookup("A").unwrap().kind(), host::LegacyFactKind::Admitted);
        assert!(ctx.lookup("other").is_none());
    }
}
