use super::{CProp, KernelThm};

/// Search-only fact representation.
///
/// Even the strict-kernel variant retains only a proposition. Moving a theorem
/// into this type erases its proof, so search storage cannot return a candidate
/// for trusted acceptance.
///
/// ```compile_fail
/// use isabelle_rs::kernel::{SearchFact, TrustedTheorem};
/// fn cannot_promote(fact: SearchFact) {
///     let _: TrustedTheorem = fact.try_into().unwrap();
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SearchFact {
    Kernel { prop: CProp },
    Admitted { prop: CProp, reason: String },
    Compat { prop: CProp, note: String },
}

impl From<KernelThm> for SearchFact {
    fn from(value: KernelThm) -> Self {
        SearchFact::Kernel { prop: value.prop().clone() }
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
