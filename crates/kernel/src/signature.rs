use std::{collections::BTreeMap, sync::Arc};

use super::{
    KernelError, Name, Ty,
    identity::{CanonicalEncoder, SIGNATURE_DOMAIN, SignatureId},
    logic::PolyType,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ConstScheme {
    Monomorphic(Ty),
    Polymorphic(PolyType),
}

/// Immutable theory-level signature for strict certification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    id: SignatureId,
    consts: Arc<BTreeMap<Name, ConstScheme>>,
}

impl Signature {
    pub fn new() -> Self {
        Self::from_map(BTreeMap::new())
    }

    pub fn id(&self) -> SignatureId { self.id }

    pub fn extend_const(&self, name: impl Into<Name>, ty: Ty) -> Result<Self, KernelError> {
        let name = name.into();
        if self.consts.contains_key(&name) {
            return Err(KernelError::DuplicateDeclaration { name });
        }
        let mut consts = (*self.consts).clone();
        consts.insert(name, ConstScheme::Monomorphic(ty));
        Ok(Self::from_map(consts))
    }

    pub fn extend_const_scheme(&self, name: impl Into<Name>, scheme: PolyType) -> Result<Self, KernelError> {
        let name = name.into();
        if self.consts.contains_key(&name) {
            return Err(KernelError::DuplicateDeclaration { name });
        }
        let mut consts = (*self.consts).clone();
        consts.insert(name, ConstScheme::Polymorphic(scheme));
        Ok(Self::from_map(consts))
    }

    pub fn get_const(&self, name: &Name) -> Option<&ConstScheme> { self.consts.get(name) }

    pub fn const_type(&self, name: &Name) -> Option<&Ty> {
        match self.consts.get(name) {
            Some(ConstScheme::Monomorphic(ty)) => Some(ty),
            _ => None,
        }
    }

    pub fn from_untrusted_snapshot(
        claimed_digest: [u8; 32],
        declarations: Vec<(Name, Ty)>,
    ) -> Result<Self, KernelError> {
        let mut consts = BTreeMap::new();
        for (name, ty) in declarations {
            if consts.insert(name.clone(), ConstScheme::Monomorphic(ty)).is_some() {
                return Err(KernelError::DuplicateDeclaration { name });
            }
        }
        let signature = Self::from_map(consts);
        if signature.id.to_bytes() != claimed_digest {
            return Err(KernelError::SignatureDigestMismatch);
        }
        Ok(signature)
    }

    pub fn len(&self) -> usize { self.consts.len() }
    pub fn is_empty(&self) -> bool { self.consts.is_empty() }

    fn from_map(consts: BTreeMap<Name, ConstScheme>) -> Self {
        let id = compute_signature_id(&consts);
        Self { id, consts: Arc::new(consts) }
    }
}

impl Default for Signature {
    fn default() -> Self { Self::new() }
}

fn compute_signature_id(consts: &BTreeMap<Name, ConstScheme>) -> SignatureId {
    let mut encoder = CanonicalEncoder::new(SIGNATURE_DOMAIN);
    encoder.write_u64(consts.len() as u64);
    for (name, scheme) in consts {
        encoder.write_u8(0);
        encoder.write_name(name);
        match scheme {
            ConstScheme::Monomorphic(ty) => {
                encoder.write_u8(0);
                ty.write_canonical(&mut encoder);
            },
            ConstScheme::Polymorphic(scheme) => {
                encoder.write_u8(1);
                scheme.write_canonical(&mut encoder);
            },
        }
    }
    SignatureId::from_digest(encoder.finish())
}
