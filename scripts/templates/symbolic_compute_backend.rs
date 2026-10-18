// Classification: design-only standalone template; not production code.
#![allow(dead_code)]

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PackedTrustClass {
    TransitionalStrictClosed,
    Open,
    Compat,
    Admitted,
    SearchOnly,
}

#[derive(Clone, Debug, Default)]
pub struct PackedTermArena {
    pub tags: Vec<u32>,
    pub ty_ids: Vec<u32>,
    pub symbol_ids: Vec<u32>,
    pub child_start: Vec<u32>,
    pub child_len: Vec<u32>,
    pub children: Vec<u32>,
    pub root_ids: Vec<u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PackedFact {
    pub fact_id: u32,
    pub prop_root: u32,
    pub fingerprint_id: u32,
    pub trust_class: PackedTrustClass,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PackedRewriteRule {
    pub rule_id: u32,
    pub lhs_root: u32,
    pub rhs_root: u32,
    pub fingerprint_id: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TermFingerprint {
    pub head_symbol: u32,
    pub result_ty: u32,
    pub arity: u16,
    pub depth_bucket: u16,
    pub symbol_hash: u64,
    pub type_hash: u64,
    pub subterm_hash: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FactCandidate {
    pub fact_id: u32,
    pub score: u32,
    pub reason_bits: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RewriteCandidate {
    pub rule_id: u32,
    pub subterm_path_id: u32,
    pub score: u32,
    pub reason_bits: u32,
}

/// Candidate generation only. Implementations must never construct theorems.
pub trait SymbolicComputeBackend {
    fn fingerprint_terms(&self, arena: &PackedTermArena) -> Vec<TermFingerprint>;

    fn prefilter_facts(
        &self,
        goal: &TermFingerprint,
        facts: &[PackedFact],
        fingerprints: &[TermFingerprint],
        limit: usize,
    ) -> Vec<FactCandidate>;

    fn prefilter_rewrites(
        &self,
        subterms: &[TermFingerprint],
        rules: &[PackedRewriteRule],
        fingerprints: &[TermFingerprint],
        limit_per_subterm: usize,
    ) -> Vec<RewriteCandidate>;
}
