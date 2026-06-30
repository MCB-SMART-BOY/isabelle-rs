use std::convert::TryFrom;

use super::{CProp, KernelError, KernelThm, TrustedTheorem};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SearchFact {
    Kernel(KernelThm),
    Admitted { prop: CProp, reason: String },
    Compat { prop: CProp, note: String },
}

impl From<KernelThm> for SearchFact {
    fn from(value: KernelThm) -> Self {
        SearchFact::Kernel(value)
    }
}

impl TryFrom<SearchFact> for TrustedTheorem {
    type Error = KernelError;

    fn try_from(_: SearchFact) -> Result<Self, Self::Error> {
        Err(KernelError::SearchFactNotTrusted)
    }
}

#[derive(Clone, Debug, Default)]
pub struct SearchFactDb {
    facts: Vec<SearchFact>,
}

impl SearchFactDb {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, fact: SearchFact) {
        self.facts.push(fact);
    }

    pub fn len(&self) -> usize {
        self.facts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }
}
