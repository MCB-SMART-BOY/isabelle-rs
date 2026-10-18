use std::{
    fmt,
    sync::atomic::{AtomicU64, Ordering},
};

use sha2::{Digest, Sha256};

use super::logic::LogicBasisId;
use super::{KernelError, Name};

// Canonical identities have separately versioned domains. Every tag and field
// below is part of the persisted identity contract. Any byte-level encoding
// change MUST use new `/vN` domains rather than silently changing existing IDs.
// Variant tags are explicit and append-only within one schema version.
pub(crate) const SIGNATURE_DOMAIN: &[u8] = b"isabelle-rs/signature/v4";
pub(crate) const THEORY_DOMAIN: &[u8] = b"isabelle-rs/theory/v4";

// Monotone process-local identity only for unsealable proof scopes.
static NEXT_LOCAL_TYPE_SCOPE: AtomicU64 = AtomicU64::new(0);

/// Content identity of a checked strict-kernel signature.
///
/// The digest constructor is private to the strict kernel. Callers obtain an ID
/// only from a validated [`super::Signature`].
///
/// ```compile_fail
/// use isabelle_kernel::SignatureId;
/// let _forged = SignatureId([0; 32]);
/// ```
///
/// IDs are deliberately not deserializable as trusted values.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SignatureId([u8; 32]);

impl SignatureId {
    pub fn to_bytes(self) -> [u8; 32] {
        self.0
    }

    pub(crate) fn from_digest(digest: [u8; 32]) -> Self {
        Self(digest)
    }

    pub(crate) fn write_canonical(self, encoder: &mut CanonicalEncoder) {
        encoder.write_fixed_bytes(&self.0);
    }
}

/// Ancestry-sensitive identity of an immutable strict-kernel theory snapshot.
///
/// Unlike [`SignatureId`], this commits to the parent theory and extension
/// history. The raw digest constructor is private to the strict kernel.
///
/// ```compile_fail
/// use isabelle_kernel::TheoryId;
/// let _forged = TheoryId([0; 32]);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TheoryId([u8; 32]);

impl TheoryId {
    pub fn to_bytes(self) -> [u8; 32] {
        self.0
    }

    pub(crate) fn from_digest(digest: [u8; 32]) -> Self {
        Self(digest)
    }

    pub(crate) fn write_canonical(self, encoder: &mut CanonicalEncoder) {
        encoder.write_fixed_bytes(&self.0);
    }
}

/// Exact semantic world in which a strict term or theorem was certified.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContextStamp {
    theory: TheoryId,
    signature: SignatureId,
    logic_basis: Option<LogicBasisId>,
    local_type_scope: Option<u64>,
}

impl ContextStamp {
    pub fn theory(self) -> TheoryId {
        self.theory
    }

    pub fn signature(self) -> SignatureId {
        self.signature
    }

    pub fn logic_basis(self) -> Option<LogicBasisId> {
        self.logic_basis
    }

    /// A kernel-issued local fixed-type scope; `None` is the canonical theory owner.
    pub fn has_local_type_scope(self) -> bool {
        self.local_type_scope.is_some()
    }

    #[cfg(test)]
    pub(crate) fn local_type_scope(self) -> Option<u64> {
        self.local_type_scope
    }

    pub(crate) fn new(
        theory: TheoryId,
        signature: SignatureId,
        logic_basis: Option<LogicBasisId>,
    ) -> Self {
        Self { theory, signature, logic_basis, local_type_scope: None }
    }

    pub(crate) fn fresh_local_type_scope(mut self, name: &Name) -> Result<Self, KernelError> {
        let mut current = NEXT_LOCAL_TYPE_SCOPE.load(Ordering::Relaxed);
        loop {
            let scope = current
                .checked_add(1)
                .ok_or_else(|| KernelError::LocalTypeScopeExhausted { name: name.clone() })?;
            match NEXT_LOCAL_TYPE_SCOPE.compare_exchange_weak(
                current,
                scope,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    self.local_type_scope = Some(scope);
                    return Ok(self);
                },
                Err(observed) => current = observed,
            }
        }
    }

    pub(crate) fn write_canonical(self, encoder: &mut CanonicalEncoder) {
        encoder.write_bytes(b"isabelle-rs/context/v3");
        self.theory.write_canonical(encoder);
        self.signature.write_canonical(encoder);
        match self.logic_basis {
            Some(basis) => {
                encoder.write_u8(1);
                basis.write_canonical(encoder);
            },
            None => encoder.write_u8(0),
        }
        match self.local_type_scope {
            Some(scope) => {
                encoder.write_u8(1);
                encoder.write_u64(scope);
            },
            None => encoder.write_u8(0),
        }
    }
}

impl fmt::Debug for SignatureId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_digest(f, "SignatureId", &self.0)
    }
}

impl fmt::Debug for TheoryId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_digest(f, "TheoryId", &self.0)
    }
}

impl fmt::Debug for ContextStamp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ContextStamp")
            .field("theory", &self.theory)
            .field("signature", &self.signature)
            .field("logic_basis", &self.logic_basis)
            .field("local_type_scope", &self.local_type_scope)
            .finish()
    }
}

fn write_digest(f: &mut fmt::Formatter<'_>, label: &str, digest: &[u8; 32]) -> fmt::Result {
    write!(f, "{label}(")?;
    for byte in digest {
        write!(f, "{byte:02x}")?;
    }
    write!(f, ")")
}

/// Versioned, allocation-free canonical encoder for context identities.
pub(crate) struct CanonicalEncoder {
    hasher: Sha256,
}

impl CanonicalEncoder {
    pub(crate) fn new(domain: &[u8]) -> Self {
        let mut encoder = Self { hasher: Sha256::new() };
        encoder.write_bytes(domain);
        encoder
    }

    pub(crate) fn write_u8(&mut self, value: u8) {
        self.hasher.update([value]);
    }

    pub(crate) fn write_u64(&mut self, value: u64) {
        self.hasher.update(value.to_be_bytes());
    }

    pub(crate) fn write_fixed_bytes(&mut self, value: &[u8]) {
        self.hasher.update(value);
    }

    pub(crate) fn write_bytes(&mut self, value: &[u8]) {
        self.write_u64(value.len() as u64);
        self.write_fixed_bytes(value);
    }

    pub(crate) fn write_name(&mut self, name: &Name) {
        self.write_bytes(name.as_str().as_bytes());
    }

    pub(crate) fn finish(self) -> [u8; 32] {
        self.hasher.finalize().into()
    }
}
