use std::collections::HashMap;

use super::{Name, TrustedTheorem};

#[derive(Clone, Debug, Default)]
pub struct TrustedTheory {
    theorems: HashMap<Name, TrustedTheorem>,
}

impl TrustedTheory {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, name: impl Into<Name>, theorem: TrustedTheorem) {
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
