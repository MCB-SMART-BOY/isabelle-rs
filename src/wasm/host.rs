//! Host functions — search-only metadata bridge for WASM plugins.
//!
//! A legacy `core::Thm` is not a `kernel::TrustedTheorem`. Plugin handles
//! identify search snapshots only; they cannot be used to accept a proof.

use crate::core::thm::Thm;

/// Classification of a legacy search fact, not a trusted proof status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LegacyFactKind {
    TransitionalStrictClosed,
    CompatClosedOracleFree,
    OpenOracleFree,
    UnverifiedClosed,
    Admitted,
}

impl LegacyFactKind {
    /// Search classification ABI; all codes are legacy, never trusted proofs.
    pub fn abi_code(self) -> i32 {
        match self {
            Self::TransitionalStrictClosed => 1,
            Self::CompatClosedOracleFree => 2,
            Self::OpenOracleFree => 3,
            Self::UnverifiedClosed => 4,
            Self::Admitted => 5,
        }
    }
}

/// Search metadata copied from a legacy theorem; no proof token is retained.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LegacySearchFact {
    proposition: String,
    kind: LegacyFactKind,
}

impl LegacySearchFact {
    pub fn from_legacy(theorem: &Thm) -> Self {
        let kind = if theorem.is_admitted_theorem() {
            LegacyFactKind::Admitted
        } else if !theorem.is_closed() {
            LegacyFactKind::OpenOracleFree
        } else if theorem.is_strict_closed_proved() {
            LegacyFactKind::TransitionalStrictClosed
        } else if theorem.is_compat_theorem() {
            LegacyFactKind::CompatClosedOracleFree
        } else {
            LegacyFactKind::UnverifiedClosed
        };
        Self { proposition: format!("{:?}", theorem.prop().term()), kind }
    }

    pub fn proposition(&self) -> &str {
        &self.proposition
    }

    pub fn kind(&self) -> LegacyFactKind {
        self.kind
    }
}

// =========================================================================
// Host function signatures
// =========================================================================

/// Host lookup functions exported to WASM under "env".
pub const HOST_LOOKUP: &str = "host_lookup";
pub const HOST_FACT_KIND: &str = "host_fact_kind";
pub const HOST_DEBUG: &str = "host_debug";

/// Positive search handle returned by host_lookup; -1 means not found.
pub type ThmHandle = i32;

/// Session-local search metadata. Handles are never reused, including after
/// `clear`, so a previous plugin invocation cannot resurrect an old fact.
pub struct ThmTable {
    entries: std::collections::HashMap<ThmHandle, std::sync::Arc<LegacySearchFact>>,
    next_handle: ThmHandle,
}

impl ThmTable {
    pub fn new() -> Self {
        Self { entries: std::collections::HashMap::new(), next_handle: 1 }
    }

    /// Register search metadata; fail closed if the positive handle space is full.
    pub fn register(&mut self, fact: std::sync::Arc<LegacySearchFact>) -> Option<ThmHandle> {
        let next = self.next_handle.checked_add(1)?;
        let handle = self.next_handle;
        self.entries.insert(handle, fact);
        self.next_handle = next;
        Some(handle)
    }

    /// Clear invocation metadata without recycling old handles.
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    /// Unknown, stale, zero and negative handles have no result.
    pub fn get(&self, handle: ThmHandle) -> Option<&LegacySearchFact> {
        self.entries.get(&handle).map(std::sync::Arc::as_ref)
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
    use crate::core::{
        term::Term,
        thm::{CTerm, ThmKernel},
        types::Typ,
    };

    #[test]
    fn thm_table_legacy_fact_is_search_only() {
        let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
        let theorem = ThmKernel::trivial(a).unwrap();
        let fact = std::sync::Arc::new(LegacySearchFact::from_legacy(&theorem));
        let mut table = ThmTable::new();
        let handle = table.register(fact.clone()).unwrap();
        assert_eq!(table.get(handle), Some(fact.as_ref()));
        assert_ne!(fact.kind(), LegacyFactKind::Admitted);
        assert!(table.get(0).is_none());
        assert!(table.get(-1).is_none());
        assert!(table.get(handle + 1).is_none());
        assert!(ThmTable::new().get(handle).is_none());
        table.clear();
        assert!(table.get(handle).is_none());
        assert_ne!(table.register(fact).unwrap(), handle);
    }

    #[test]
    fn thm_table_admitted_fact_remains_admitted() {
        let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
        let admitted = ThmKernel::admit(a, "plugin-search");
        let fact = LegacySearchFact::from_legacy(&admitted);
        assert_eq!(fact.kind(), LegacyFactKind::Admitted);
    }
}
