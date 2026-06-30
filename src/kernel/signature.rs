use std::collections::HashMap;

use super::{Name, Ty};

/// Theory-level signature for strict certification.
#[derive(Clone, Debug, Default)]
pub struct Signature {
    consts: HashMap<Name, Ty>,
}

impl Signature {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn declare_const(&mut self, name: impl Into<Name>, ty: Ty) {
        self.consts.insert(name.into(), ty);
    }

    pub fn const_type(&self, name: &Name) -> Option<&Ty> {
        self.consts.get(name)
    }
}
