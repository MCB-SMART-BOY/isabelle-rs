//! Isar proof context — the full local reasoning environment.
//!
//! Corresponds to `src/Pure/Isar/proof_context.ML`.
//!
//! The Isar proof context extends the core `ProofContext` with:
//! - **Cases**: named case splits (for `case` / `cases`)
//! - **Facts**: locally named theorems (for `note`, `using`, `with`)
//! - **Bindings**: term and type variable bindings
//! - **Syntax**: local syntax extensions

use std::collections::HashMap;
use std::sync::Arc;

use crate::core::term::Term;
use crate::core::theory::{ProofContext as CoreProofContext, Theory};
use crate::core::thm::Thm;
use crate::core::types::Symbol;
use crate::core::types::Typ;

// =========================================================================
// Case — a proof case from case analysis
// =========================================================================

/// A named case for structured case analysis.
#[derive(Clone, Debug)]
pub struct Case {
    /// Case name (e.g., `Nil`, `Cons`).
    pub name: String,
    /// Fixed variables introduced by this case.
    pub fixes: Vec<(String, Typ)>,
    /// Assumptions introduced by this case.
    pub assumes: Vec<Term>,
    /// Sub-cases (for nested case analysis).
    pub binds: Vec<(String, Term)>,
}

// =========================================================================
// Local facts
// =========================================================================

/// Locally known facts (from `note`, `using`, `have`).
#[derive(Clone, Debug)]
pub struct LocalFacts {
    facts: HashMap<String, Vec<Arc<Thm>>>,
}

impl LocalFacts {
    pub fn new() -> Self {
        LocalFacts {
            facts: HashMap::new(),
        }
    }

    pub fn add(&mut self, name: &str, thms: Vec<Arc<Thm>>) {
        self.facts.insert(name.to_string(), thms);
    }

    pub fn get(&self, name: &str) -> Option<&[Arc<Thm>]> {
        self.facts.get(name).map(|v| v.as_slice())
    }
}

/// A snapshot of the context state for save/restore.
#[derive(Clone, Debug)]
pub struct ContextSnapshot {
    pub fixes_len: usize,
    pub assumptions_len: usize,
    pub facts_count: usize,
    pub chained_len: usize,
    pub let_bindings_len: usize,
}

// =========================================================================
// Isar Proof Context
// =========================================================================

/// The Isar proof context extends the core proof context with
/// Isar-specific features like cases, local facts, syntax, and let bindings.
#[derive(Clone, Debug)]
pub struct IsarContext {
    /// The underlying core proof context.
    pub core: CoreProofContext,
    /// Open cases (for `case` command).
    cases: Vec<Case>,
    /// Local facts (for `note`, `using`, `with`).
    facts: LocalFacts,
    /// Chained facts (for `using thm1 thm2`).
    chained: Vec<Arc<Thm>>,
    /// Let bindings: name → term (for `let x = t`).
    let_bindings: Vec<(String, Term)>,
    /// Type variable bindings: name → Typ (for `let 'a = τ`).
    type_bindings: Vec<(String, Typ)>,
    /// Context stack for save/restore (backtracking).
    stack: Vec<ContextSnapshot>,
}

impl IsarContext {
    /// Create a new Isar context from a theory.
    pub fn init(theory: &Arc<Theory>) -> Self {
        IsarContext {
            core: CoreProofContext::init(theory),
            cases: Vec::new(),
            facts: LocalFacts::new(),
            chained: Vec::new(),
            let_bindings: Vec::new(),
            type_bindings: Vec::new(),
            stack: Vec::new(),
        }
    }

    // =================================================================
    // Cases
    // =================================================================

    /// Add a case to the context.
    pub fn add_case(&mut self, case: Case) {
        self.cases.push(case);
    }

    /// Look up a case by name.
    pub fn find_case(&self, name: &str) -> Option<&Case> {
        self.cases.iter().find(|c| c.name == name)
    }

    // =================================================================
    // Local facts
    // =================================================================

    /// Note a fact: `note name = thms`.
    pub fn note(&mut self, name: &str, thms: Vec<Arc<Thm>>) {
        self.facts.add(name, thms);
    }

    /// Get local facts by name.
    pub fn get_fact(&self, name: &str) -> Option<&[Arc<Thm>]> {
        self.facts.get(name)
    }

    /// Chain facts: `using thms`.
    pub fn using(&mut self, thms: Vec<Arc<Thm>>) {
        self.chained = thms;
    }

    /// Append theorem facts to the chain (for calculational reasoning).
    pub fn chain_facts(&mut self, thms: Vec<crate::core::thm::Thm>) {
        let arcs: Vec<Arc<crate::core::thm::Thm>> = thms.into_iter().map(Arc::new).collect();
        self.chained.extend(arcs);
    }

    /// `with` = `using` + `from` (chain + make available as assumptions)
    pub fn with(&mut self, thms: Vec<Arc<Thm>>) {
        self.chained = thms;
    }

    /// Let binding: `let x = t`.
    pub fn let_bind(&mut self, name: &str, term: Term) {
        self.let_bindings.push((name.to_string(), term));
    }

    /// Look up a let binding by name.
    pub fn get_let_binding(&self, name: &str) -> Option<&Term> {
        self.let_bindings.iter().rev().find(|(n, _)| n == name).map(|(_, t)| t)
    }

    /// Type variable binding: `let 'a = τ`.
    pub fn type_bind(&mut self, name: &str, typ: Typ) {
        self.type_bindings.push((name.to_string(), typ));
    }

    /// Save current context state (for backtracking).
    pub fn save(&mut self) {
        let snap = ContextSnapshot {
            fixes_len: self.core.fixes().len(),
            assumptions_len: self.core.assumptions().len(),
            facts_count: self.facts.facts.len(),
            chained_len: self.chained.len(),
            let_bindings_len: self.let_bindings.len(),
        };
        self.stack.push(snap);
    }

    /// Restore context to the last saved state.
    pub fn restore(&mut self) {
        if let Some(snap) = self.stack.pop() {
            self.core.restore_to(snap.fixes_len, snap.assumptions_len);
            self.chained.truncate(snap.chained_len);
            self.let_bindings.truncate(snap.let_bindings_len);
        }
    }

    /// Get chained facts (consumed by the next method).
    pub fn take_chained(&mut self) -> Vec<Arc<Thm>> {
        std::mem::take(&mut self.chained)
    }

    // =================================================================
    // Fix / Assume (delegate to core)
    // =================================================================

    /// Fix a variable: `fix x :: τ`.
    pub fn fix(&mut self, name: &str, typ: Typ) {
        self.core.fix(name, typ);
    }

    /// Assume a proposition: `assume "A"`.
    pub fn assume(&mut self, prop: Term) {
        self.core.assume(prop);
    }

    // =================================================================
    // Accessors
    // =================================================================

    pub fn theory(&self) -> &Arc<Theory> {
        self.core.theory()
    }

    pub fn fixes(&self) -> &[(Symbol, Typ)] {
        self.core.fixes()
    }

    pub fn assumptions(&self) -> &[Term] {
        self.core.assumptions()
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::theory::Theory;
    use crate::core::thm::{CTerm, ThmKernel};
    use crate::core::types::Typ;

    fn init_context() -> IsarContext {
        let pure = Theory::pure();
        IsarContext::init(&pure)
    }

    #[test]
    fn test_fix_assume() {
        let mut ctx = init_context();
        ctx.fix("x", Typ::base("nat"));
        ctx.assume(Term::const_("Px", Typ::base("prop")));

        assert_eq!(ctx.fixes().len(), 1);
        assert_eq!(ctx.fixes()[0].0.as_ref(), "x");
        assert_eq!(ctx.assumptions().len(), 1);
    }

    #[test]
    fn test_local_facts() {
        let mut ctx = init_context();
        let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
        let thm = Arc::new(ThmKernel::trivial(a).unwrap());

        ctx.note("my_fact", vec![Arc::clone(&thm)]);
        assert!(ctx.get_fact("my_fact").is_some());
        assert_eq!(ctx.get_fact("my_fact").unwrap().len(), 1);
    }

    #[test]
    fn test_chaining() {
        let mut ctx = init_context();
        let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
        let thm = Arc::new(ThmKernel::trivial(a).unwrap());

        ctx.using(vec![Arc::clone(&thm)]);
        let chained = ctx.take_chained();
        assert_eq!(chained.len(), 1);
        assert!(ctx.take_chained().is_empty()); // consumed
    }

    #[test]
    fn test_cases() {
        let mut ctx = init_context();
        let case = Case {
            name: "Nil".into(),
            fixes: vec![],
            assumes: vec![Term::const_("list_empty", Typ::base("prop"))],
            binds: vec![],
        };
        ctx.add_case(case);
        assert!(ctx.find_case("Nil").is_some());
        assert!(ctx.find_case("Cons").is_none());
    }
}
