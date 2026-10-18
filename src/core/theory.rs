//! Theory management — the top-level container.
//!
//! Corresponds to `src/Pure/theory.ML`.
//!
//! ## Isabelle's Theory Philosophy
//!
//! In Isabelle, a **theory** is a self-contained world of:
//! - A **signature** (declared types and constants with their most-general types)
//! - A set of **axioms** (named propositions that are accepted as true)
//! - A collection of **theorems** (proved from axioms via the trusted kernel)
//! - Parent theories (inheritance via `imports`)
//!
//! Theories are **immutable** once built. Extending a theory creates a new theory.
//! This ensures that reasoning in theory `T1` cannot be invalidated by changes in `T2`.
//!
//! ## The Pure Theory
//!
//! Isabelle always starts with theory `Pure`, which declares:
//! - The type `prop` (type of propositions)
//! - The three meta-logic constants: `Pure.all`, `Pure.imp`, `Pure.eq`
//! - No axioms — Pure has no axioms; soundness comes from the inference rules alone
//!
//! All other theories (HOL, FOL, ZF) are built on top of Pure.

use std::{
    collections::{HashMap, HashSet},
    sync::{Arc, OnceLock},
};

use super::{
    sign::{Signature, SignatureMergeError, TypeDeclarationError},
    term::Term,
    thm::Thm,
    types::{Symbol, Typ},
};

// =========================================================================
// Theory
// =========================================================================

/// A named constant with its defining term (for definitions).
#[derive(Clone, Debug)]
pub struct Definition {
    pub name: Symbol,
    pub term: Arc<Term>, // the definiens (right-hand side)
}

/// User-fixable parent graph or inherited declaration conflict.
#[derive(Clone, Debug, thiserror::Error)]
pub enum TheoryMergeError {
    /// Only the fixed Pure bootstrap may have no parents.
    #[error("theory `{name}` requires at least one imported theory")]
    MissingParents { name: Symbol },
    /// Independently constructed theories cannot claim one imported name.
    #[error("distinct imported theories claim the name `{name}`")]
    IdentityConflict { name: Symbol },
    /// Two imported declarations do not have the same origin.
    #[error(transparent)]
    Signature(#[from] SignatureMergeError),
    /// Named facts or definitions from separate branches conflict.
    #[error("conflicting imported {namespace} `{name}`")]
    ItemConflict { namespace: &'static str, name: Symbol },
}

/// A theory: a name, a signature, axioms, and theorems.
///
/// Theories form a DAG via `imports`. The root is always theory `Pure`.
#[derive(Clone, Debug)]
pub struct Theory {
    /// Theory name (e.g., "Pure", "HOL", "MyTheory").
    name: Symbol,
    /// Parent theories (the `imports` chain).
    parents: Vec<Arc<Theory>>,
    /// The theory's signature.
    signature: Signature,
    /// Named axioms (unproved; accepted as true).
    axioms: HashMap<Symbol, Arc<Term>>,
    /// Named definitions (constants introduced by definition).
    definitions: HashMap<Symbol, Definition>,
    /// Named theorems (proved via the kernel).
    theorems: HashMap<Symbol, Arc<Thm>>,
}

impl Theory {
    // =================================================================
    // Construction
    // =================================================================

    /// Create the root Pure theory.
    ///
    /// This is the minimal bootstrap theory: no parents, no axioms,
    /// only the Pure signature with the three meta-logic constants.
    pub fn pure() -> Arc<Theory> {
        // One immutable bootstrap identity allows independent registries to share Pure ancestry.
        static PURE: OnceLock<Arc<Theory>> = OnceLock::new();
        Arc::clone(PURE.get_or_init(|| {
            Arc::new(Theory {
                name: Arc::from("Pure"),
                parents: Vec::new(),
                signature: Signature::pure(),
                axioms: HashMap::new(),
                definitions: HashMap::new(),
                theorems: HashMap::new(),
            })
        }))
    }

    /// Create a new theory extending existing theories.
    ///
    /// The new theory inherits all declarations and theorems from its parents.
    pub fn begin(
        name: impl Into<Symbol>,
        parents: Vec<Arc<Theory>>,
    ) -> Result<Theory, TheoryMergeError> {
        let name = name.into();
        let parents = canonicalize_parents(&name, parents)?;
        let mut signature = parents[0].signature.extend();
        for parent in &parents[1..] {
            signature.merge(&parent.signature)?;
        }
        validate_imported_items(&parents)?;
        Ok(Theory {
            name,
            parents,
            signature,
            axioms: HashMap::new(),
            definitions: HashMap::new(),
            theorems: HashMap::new(),
        })
    }

    // =================================================================
    // Accessors
    // =================================================================

    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn signature(&self) -> &Signature {
        &self.signature
    }
    pub fn parents(&self) -> &[Arc<Theory>] {
        &self.parents
    }

    /// Look up a constant's type in this theory (including ancestor theories).
    pub fn const_type(&self, name: &str) -> Option<&Typ> {
        if let Some(typ) = self.signature.const_type(name) {
            return Some(typ);
        }
        for parent in &self.parents {
            if let Some(typ) = parent.const_type(name) {
                return Some(typ);
            }
        }
        None
    }

    /// Check if a constant is declared in this theory.
    pub fn is_declared(&self, name: &str) -> bool {
        self.signature.is_declared(name) || self.parents.iter().any(|p| p.is_declared(name))
    }

    // =================================================================
    // Extension (building theories incrementally)
    // =================================================================

    /// Add an axiom to the theory.
    ///
    /// An axiom is a proposition accepted as true without proof.
    /// In Isabelle, axioms are rare — most things are proved or defined.
    pub fn add_axiom(&mut self, name: impl Into<Symbol>, prop: Term) {
        self.axioms.insert(name.into(), Arc::new(prop));
    }

    /// Add a definition.
    ///
    /// A definition introduces a new constant as shorthand for an existing term.
    /// E.g., `definition "foo == bar"` declares `foo` and defines it as `bar`.
    pub fn add_definition(&mut self, def: Definition) {
        self.definitions.insert(Arc::clone(&def.name), def);
    }

    /// Add a proved theorem to the theory.
    ///
    /// The theorem must be strict-kernel constructed, closed, oracle-free, and
    /// its propositions must be built from constants declared in this theory.
    pub fn add_theorem(&mut self, name: impl Into<Symbol>, thm: Thm) {
        assert!(
            thm.is_strict_closed_proved(),
            "stored theorems must be strict closed proved theorems"
        );
        self.theorems.insert(name.into(), Arc::new(thm));
    }

    /// Declare a new constant in the signature.
    pub fn declare_const(&mut self, name: impl Into<Symbol>, typ: Typ) {
        self.signature.declare(name, typ);
    }

    /// Declare a fresh type constructor without shadowing a parent type.
    pub fn declare_type(&mut self, name: &str, arity: usize) -> Result<(), TypeDeclarationError> {
        self.signature.declare_type(name, arity)
    }

    // =================================================================
    // Lookup
    // =================================================================

    pub fn lookup_theorem(&self, name: &str) -> Option<&Arc<Thm>> {
        if let Some(thm) = self.theorems.get(name) {
            return Some(thm);
        }
        for parent in &self.parents {
            if let Some(thm) = parent.lookup_theorem(name) {
                return Some(thm);
            }
        }
        None
    }

    /// Collect each inherited axiom name once, including shared diamond ancestors.
    pub fn all_axiom_names(&self) -> Vec<&str> {
        self.collect_names(|theory| theory.axioms.keys())
    }

    /// Collect each inherited theorem name once, including shared diamond ancestors.
    pub fn all_theorem_names(&self) -> Vec<&str> {
        self.collect_names(|theory| theory.theorems.keys())
    }

    fn collect_names<'a, V: 'a>(
        &'a self,
        names: impl Fn(&'a Theory) -> std::collections::hash_map::Keys<'a, Symbol, V>,
    ) -> Vec<&'a str> {
        let mut collected = std::collections::BTreeSet::new();
        let mut visited = HashSet::new();
        let mut pending = vec![self];
        while let Some(theory) = pending.pop() {
            if visited.insert(std::ptr::from_ref(theory)) {
                collected.extend(names(theory).map(AsRef::as_ref));
                pending.extend(theory.parents.iter().map(Arc::as_ref));
            }
        }
        collected.into_iter().collect()
    }
}

fn canonicalize_parents(
    name: &Symbol,
    mut parents: Vec<Arc<Theory>>,
) -> Result<Vec<Arc<Theory>>, TheoryMergeError> {
    if parents.is_empty() {
        return Err(TheoryMergeError::MissingParents { name: Arc::clone(name) });
    }
    let mut identities = HashMap::new();
    let mut covered = HashSet::new();
    let mut pending: Vec<_> = parents.iter().map(|parent| (parent.as_ref(), false)).collect();
    while let Some((theory, is_ancestor)) = pending.pop() {
        let identity = std::ptr::from_ref(theory);
        if is_ancestor {
            covered.insert(identity);
        }
        if let Some(previous) = identities.insert(&theory.name, identity) {
            if previous != identity {
                return Err(TheoryMergeError::IdentityConflict { name: Arc::clone(&theory.name) });
            }
            continue;
        }
        if &theory.name == name {
            return Err(TheoryMergeError::IdentityConflict { name: Arc::clone(name) });
        }
        pending.extend(theory.parents.iter().map(|parent| (parent.as_ref(), true)));
    }
    let mut seen = HashSet::new();
    parents.retain(|parent| {
        let identity = Arc::as_ptr(parent);
        !covered.contains(&identity) && seen.insert(identity)
    });
    Ok(parents)
}

fn validate_imported_items(parents: &[Arc<Theory>]) -> Result<(), TheoryMergeError> {
    let mut visited = HashSet::new();
    let mut pending: Vec<_> = parents.iter().map(Arc::as_ref).collect();
    let mut axioms = HashMap::new();
    let mut definitions = HashMap::new();
    let mut theorems = HashMap::new();
    while let Some(theory) = pending.pop() {
        if !visited.insert(std::ptr::from_ref(theory)) {
            continue;
        }
        validate_item_origins(&mut axioms, theory.axioms.iter(), "axiom")?;
        validate_item_origins(
            &mut definitions,
            theory.definitions.iter().map(|(name, definition)| (name, &definition.term)),
            "definition",
        )?;
        validate_item_origins(&mut theorems, theory.theorems.iter(), "theorem")?;
        pending.extend(theory.parents.iter().map(Arc::as_ref));
    }
    Ok(())
}

fn validate_item_origins<'a, T: 'a>(
    known: &mut HashMap<&'a Symbol, *const T>,
    incoming: impl Iterator<Item = (&'a Symbol, &'a Arc<T>)>,
    namespace: &'static str,
) -> Result<(), TheoryMergeError> {
    for (name, item) in incoming {
        if let Some(previous) = known.insert(name, Arc::as_ptr(item))
            && previous != Arc::as_ptr(item)
        {
            return Err(TheoryMergeError::ItemConflict { namespace, name: Arc::clone(name) });
        }
    }
    Ok(())
}

// =========================================================================
// Proof Context — local proof state
// =========================================================================

/// A proof context: local fixed variables and assumptions.
///
/// Corresponds to `Proof.context` in `src/Pure/context.ML`.
///
/// Why this is separate from Theory:
/// - Theory: global, immutable, shared
/// - Context: local, grows with `fix` and `assume`, shrinks with `discharge`
#[derive(Clone, Debug)]
pub struct ProofContext {
    /// The theory this context belongs to.
    theory: Arc<Theory>,
    /// Locally fixed term variables: name → (typ, is_free).
    fixes: Vec<(Symbol, Typ)>,
    /// Local assumptions (hypotheses).
    assumptions: Vec<Term>,
}

impl ProofContext {
    /// Create a new proof context from a theory.
    pub fn init(theory: &Arc<Theory>) -> Self {
        ProofContext { theory: Arc::clone(theory), fixes: Vec::new(), assumptions: Vec::new() }
    }

    pub fn theory(&self) -> &Arc<Theory> {
        &self.theory
    }

    /// Fix a variable: add it to the local context.
    /// Corresponds to `fix x :: τ` in Isar.
    pub fn fix(&mut self, name: impl Into<Symbol>, typ: Typ) {
        self.fixes.push((name.into(), typ));
    }

    /// Assume a proposition.
    /// Corresponds to `assume "A"` in Isar.
    pub fn assume(&mut self, prop: Term) {
        self.assumptions.push(prop);
    }

    pub fn fixes(&self) -> &[(Symbol, Typ)] {
        &self.fixes
    }
    pub fn assumptions(&self) -> &[Term] {
        &self.assumptions
    }

    /// Restore context to a previous state (for backtracking).
    pub(crate) fn restore_to(&mut self, fixes_len: usize, assumptions_len: usize) {
        self.fixes.truncate(fixes_len);
        self.assumptions.truncate(assumptions_len);
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::{
        super::thm::{CTerm, ThmKernel},
        super::types::TypeEnv,
        *,
    };

    #[test]
    fn test_pure_theory() {
        let pure = Theory::pure();
        assert_eq!(pure.name(), "Pure");
        assert!(pure.parents().is_empty());
        assert!(pure.is_declared("Pure.imp"));
        assert!(pure.is_declared("Pure.all"));
        assert!(pure.is_declared("Pure.eq"));
        assert!(!pure.is_declared("HOL.eq"));
    }

    #[test]
    fn test_theory_extension() {
        let pure = Theory::pure();
        let mut my_theory = Theory::begin("MyTheory", vec![Arc::clone(&pure)]).unwrap();
        my_theory.declare_const("MyTheory.foo", Typ::base("prop"));

        assert!(my_theory.is_declared("Pure.imp")); // inherited
        assert!(my_theory.is_declared("MyTheory.foo")); // own
    }

    #[test]
    fn test_add_theorem() {
        let pure = Theory::pure();
        let mut my_theory = Theory::begin("MyTheory", vec![Arc::clone(&pure)]).unwrap();

        // Prove A ==> A in this theory through the strict kernel boundary.
        let mut env = TypeEnv::new();
        let prop_t = Typ::base("prop");
        env.declare_const("A", prop_t.clone());
        let a = CTerm::certify_checked(Term::const_("A", prop_t), &env).unwrap();
        let thm = ThmKernel::trivial(a).unwrap();
        assert!(thm.is_strict_closed_proved());

        my_theory.add_theorem("trivial", thm);
        assert!(my_theory.lookup_theorem("trivial").is_some());
    }

    #[test]
    fn test_proof_context() {
        let pure = Theory::pure();
        let mut ctx = ProofContext::init(&pure);

        ctx.fix("x", Typ::base("nat"));
        assert_eq!(ctx.fixes().len(), 1);
        assert_eq!(ctx.fixes()[0].0.as_ref(), "x");

        ctx.assume(Term::const_("P", Typ::base("prop")));
        assert_eq!(ctx.assumptions().len(), 1);
    }
}
