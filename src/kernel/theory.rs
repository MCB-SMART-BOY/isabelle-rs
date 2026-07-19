use std::{collections::HashMap, fmt, sync::Arc};

use super::{
    KernelError, Name, Signature, TrustedTheorem, Ty,
    identity::{CanonicalEncoder, ContextStamp, THEORY_DOMAIN, TheoryId},
};

/// Immutable ancestry-sensitive theory context used by strict certification.
#[derive(Clone)]
pub struct TheorySnapshot {
    inner: Arc<TheoryNode>,
}

struct TheoryNode {
    id: TheoryId,
    parent: Option<TheorySnapshot>,
    signature: Signature,
}

enum TheoryExtension {
    Root { name: Name },
    BeginChild { name: Name },
    DeclareConst { name: Name, ty: Ty },
}

impl TheorySnapshot {
    pub fn root(name: impl Into<Name>, signature: Signature) -> Self {
        Self::build(None, signature, TheoryExtension::Root { name: name.into() })
    }

    pub fn begin_child(&self, name: impl Into<Name>) -> Self {
        Self::build(
            Some(self.clone()),
            self.signature().clone(),
            TheoryExtension::BeginChild { name: name.into() },
        )
    }

    pub fn extend_const(&self, name: impl Into<Name>, ty: Ty) -> Result<Self, KernelError> {
        let name = name.into();
        let signature = self.signature().extend_const(name.clone(), ty.clone())?;
        Ok(Self::build(Some(self.clone()), signature, TheoryExtension::DeclareConst { name, ty }))
    }

    pub fn id(&self) -> TheoryId {
        self.inner.id
    }

    pub fn signature(&self) -> &Signature {
        &self.inner.signature
    }

    pub fn stamp(&self) -> ContextStamp {
        ContextStamp::new(self.id(), self.signature().id())
    }

    pub fn parent(&self) -> Option<&TheorySnapshot> {
        self.inner.parent.as_ref()
    }

    pub fn is_ancestor_of(&self, descendant: &TheorySnapshot) -> bool {
        let mut current = Some(descendant);
        while let Some(theory) = current {
            if theory.id() == self.id() {
                return true;
            }
            current = theory.parent();
        }
        false
    }

    fn build(
        parent: Option<TheorySnapshot>,
        signature: Signature,
        extension: TheoryExtension,
    ) -> Self {
        let id = compute_theory_id(parent.as_ref().map(TheorySnapshot::id), &extension, &signature);
        Self { inner: Arc::new(TheoryNode { id, parent, signature }) }
    }
}

impl fmt::Debug for TheorySnapshot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TheorySnapshot")
            .field("id", &self.id())
            .field("parent", &self.parent().map(TheorySnapshot::id))
            .field("signature", &self.signature().id())
            .finish()
    }
}

fn compute_theory_id(
    parent: Option<TheoryId>,
    extension: &TheoryExtension,
    signature: &Signature,
) -> TheoryId {
    let mut encoder = CanonicalEncoder::new(THEORY_DOMAIN);
    match parent {
        Some(parent) => {
            encoder.write_u8(1);
            parent.write_canonical(&mut encoder);
        },
        None => encoder.write_u8(0),
    }
    extension.write_canonical(&mut encoder);
    signature.id().write_canonical(&mut encoder);
    TheoryId::from_digest(encoder.finish())
}

impl TheoryExtension {
    fn write_canonical(&self, encoder: &mut CanonicalEncoder) {
        match self {
            TheoryExtension::Root { name } => {
                encoder.write_u8(0);
                encoder.write_name(name);
            },
            TheoryExtension::BeginChild { name } => {
                encoder.write_u8(1);
                encoder.write_name(name);
            },
            TheoryExtension::DeclareConst { name, ty } => {
                encoder.write_u8(2);
                encoder.write_name(name);
                ty.write_canonical(encoder);
            },
        }
    }
}

/// Transitional context-agnostic storage: theorem values carry stamps, but
/// this table selects no owning snapshot and is not the acceptance API.
#[derive(Clone, Debug, Default)]
pub struct TrustedTheory {
    theorems: HashMap<Name, TrustedTheorem>,
}

impl TrustedTheory {
    pub fn new() -> Self {
        Self::default()
    }

    pub(in crate::kernel) fn add(&mut self, name: impl Into<Name>, theorem: TrustedTheorem) {
        self.theorems.insert(name.into(), theorem);
    }

    pub fn get(&self, name: &Name) -> Option<&TrustedTheorem> {
        self.theorems.get(name)
    }

    pub fn len(&self) -> usize {
        self.theorems.len()
    }

    pub fn is_empty(&self) -> bool {
        self.theorems.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extension_kind_contributes_to_theory_identity() {
        let signature = Signature::new();
        let name = Name::from("SamePayload");
        let root =
            compute_theory_id(None, &TheoryExtension::Root { name: name.clone() }, &signature);
        let child = compute_theory_id(None, &TheoryExtension::BeginChild { name }, &signature);

        assert_ne!(root, child);
    }
}
