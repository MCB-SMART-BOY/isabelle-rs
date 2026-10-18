use std::{collections::BTreeMap, sync::Arc};

use super::{
    KernelError, Name, Ty,
    identity::{CanonicalEncoder, SIGNATURE_DOMAIN, SignatureId},
};

/// Immutable theory-level signature for strict certification.
///
/// `SignatureId` is a content identity: equal canonical declaration sets have
/// the same ID regardless of construction order. Extensions return a new value;
/// the parent remains unchanged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    id: SignatureId,
    consts: Arc<BTreeMap<Name, Ty>>,
}

impl Signature {
    pub fn new() -> Self {
        Self::from_map(BTreeMap::new())
    }

    pub fn id(&self) -> SignatureId {
        self.id
    }

    pub fn extend_const(&self, name: impl Into<Name>, ty: Ty) -> Result<Self, KernelError> {
        let name = name.into();
        if self.consts.contains_key(&name) {
            return Err(KernelError::DuplicateDeclaration { name });
        }

        let mut consts = (*self.consts).clone();
        consts.insert(name, ty);
        Ok(Self::from_map(consts))
    }

    /// Rebuild a signature from an untrusted wire payload.
    ///
    /// The claimed digest is never trusted: declarations are canonicalized,
    /// duplicates are rejected, and the ID is recomputed before comparison.
    pub fn from_untrusted_snapshot(
        claimed_digest: [u8; 32],
        declarations: Vec<(Name, Ty)>,
    ) -> Result<Self, KernelError> {
        let mut consts = BTreeMap::new();
        for (name, ty) in declarations {
            if consts.insert(name.clone(), ty).is_some() {
                return Err(KernelError::DuplicateDeclaration { name });
            }
        }

        let signature = Self::from_map(consts);
        if signature.id.to_bytes() != claimed_digest {
            return Err(KernelError::SignatureDigestMismatch);
        }
        Ok(signature)
    }

    pub fn const_type(&self, name: &Name) -> Option<&Ty> {
        self.consts.get(name)
    }

    pub fn len(&self) -> usize {
        self.consts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.consts.is_empty()
    }

    fn from_map(consts: BTreeMap<Name, Ty>) -> Self {
        let id = compute_signature_id(&consts);
        Self { id, consts: Arc::new(consts) }
    }
}

impl Default for Signature {
    fn default() -> Self {
        Self::new()
    }
}

fn compute_signature_id(consts: &BTreeMap<Name, Ty>) -> SignatureId {
    let mut encoder = CanonicalEncoder::new(SIGNATURE_DOMAIN);
    encoder.write_u64(consts.len() as u64);
    for (name, ty) in consts {
        encoder.write_u8(0); // constant declaration, signature schema v1
        encoder.write_name(name);
        ty.write_canonical(&mut encoder);
    }
    SignatureId::from_digest(encoder.finish())
}
