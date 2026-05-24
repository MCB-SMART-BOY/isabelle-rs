//! Host functions — kernel API bridge for WASM plugins.
//!
//! These functions are registered with the wasmtime Linker and
//! provide the only way for plugins to interact with the kernel.
//!
//! ## Security
//!
//! This is the security boundary. Plugins can ONLY:
//! - Look up theorems by name (read-only)
//! - Print debug messages (tracing::debug)
//! - Call kernel inference rules via serialized IPC
//!
//! Plugins CANNOT:
//! - Access the filesystem, network, or environment
//! - Allocate host memory directly
//! - Create theorems without going through the kernel

use std::sync::Arc;

use crate::core::thm::Thm;

// =========================================================================
// Host function signatures
// =========================================================================

/// Host function identifiers (exported to WASM under "env" module).
pub const HOST_LOOKUP: &str = "host_lookup";
pub const HOST_DEBUG: &str = "host_debug";
pub const HOST_RESOLVE: &str = "host_resolve";
pub const HOST_UNIFY: &str = "host_unify";

/// Result of host_lookup: a theorem handle (index into a table).
pub type ThmHandle = u32;

/// A table of theorems shared between host and plugin.
///
/// The plugin refers to theorems by handle (index), never by pointer.
pub struct ThmTable {
    entries: Vec<Arc<Thm>>,
}

impl ThmTable {
    pub fn new() -> Self {
        ThmTable {
            entries: Vec::new(),
        }
    }

    /// Register a theorem and get its handle.
    pub fn register(&mut self, thm: Arc<Thm>) -> ThmHandle {
        let handle = self.entries.len() as ThmHandle;
        self.entries.push(thm);
        handle
    }

    /// Look up a theorem by handle.
    pub fn get(&self, handle: ThmHandle) -> Option<&Arc<Thm>> {
        self.entries.get(handle as usize)
    }
}

impl Default for ThmTable {
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
    use crate::core::term::Term;
    use crate::core::thm::{CTerm, ThmKernel};
    use crate::core::types::Typ;

    #[test]
    fn test_thm_table_register_and_get() {
        let mut table = ThmTable::new();
        let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
        let thm = Arc::new(ThmKernel::trivial(a).unwrap());

        let handle = table.register(Arc::clone(&thm));
        let retrieved = table.get(handle);
        assert!(retrieved.is_some());
    }

    #[test]
    fn test_thm_table_invalid_handle() {
        let table = ThmTable::new();
        assert!(table.get(999).is_none());
    }
}
