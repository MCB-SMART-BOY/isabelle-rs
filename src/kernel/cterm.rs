use super::{KernelError, Name, Term, Ty};

/// Strict certified term.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CTerm {
    term: Term,
}

/// An entry in a schematic instantiation substitution.
///
/// Maps a target schematic variable `Var(name, index, var_ty)` to a
/// certified replacement `CTerm`. The replacement must pass strict
/// certification (constants declared in `Signature`, no dummy types,
/// no `Bound` variables).
///
/// # Trust boundary
///
/// `InstEntry` enforces that `instantiate` replacements enter the
/// kernel through the `CTerm` certification boundary, not as bare
/// `Term` values. This prevents uncertified terms from being
/// injected into theorems.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstEntry {
    /// Name of the schematic variable to replace.
    name: Name,
    /// De Bruijn-style index of the schematic variable.
    index: usize,
    /// Type of the schematic variable (must match `replacement.ty()`).
    var_ty: Ty,
    /// The certified replacement term.
    replacement: CTerm,
}

impl InstEntry {
    /// Construct a new substitution entry.
    ///
    /// The caller is responsible for ensuring `replacement.ty() == var_ty`.
    /// `KernelRules::instantiate` performs a runtime type check.
    pub fn new(name: impl Into<Name>, index: usize, var_ty: Ty, replacement: CTerm) -> Self {
        InstEntry { name: name.into(), index, var_ty, replacement }
    }

    /// Name of the schematic variable to replace.
    pub fn name(&self) -> &Name {
        &self.name
    }

    /// De Bruijn-style index of the schematic variable.
    pub fn index(&self) -> usize {
        self.index
    }

    /// Type of the schematic variable (must match `replacement.ty()`).
    pub fn var_ty(&self) -> &Ty {
        &self.var_ty
    }

    /// The certified replacement term.
    pub fn replacement(&self) -> &CTerm {
        &self.replacement
    }
}

impl CTerm {
    /// Internal constructor. Only for use within `src/kernel/` when the
    /// term has already passed through `ProofContext::certify_term` or
    /// `ProofContext::certify_raw` and is known to be well-formed.
    ///
    /// This is deliberately scoped to `crate::kernel`, not the whole crate:
    /// legacy `core`/Isar/HOL/tooling code must enter through strict
    /// certification instead of wrapping typed terms directly.
    pub(in crate::kernel) fn new(term: Term) -> Self {
        CTerm { term }
    }

    /// Wrap a term that originates from an already-certified `CProp` or
    /// `KernelThm` proposition. The term is certified-by-origin: it is a
    /// subterm extracted from a proposition that already passed
    /// `ProofContext` certification.
    ///
    /// # Contract (caller MUST guarantee)
    ///
    /// 1. The term was extracted from a certified `CProp` / `KernelThm`.
    /// 2. The term contains no `Ty::Dummy`.
    /// 3. The term contains no unbound de Bruijn indices.
    /// 4. The term's constants are declared in the active `Signature`.
    ///
    /// This constructor is `pub(in crate::kernel)` — only `src/kernel/` modules
    /// can call it. External code and upper-layer modules MUST use
    /// `ProofContext::certify_term` instead.
    pub(in crate::kernel) fn from_certified_subterm(term: Term) -> Self {
        CTerm { term }
    }

    pub fn term(&self) -> &Term {
        &self.term
    }

    pub fn ty(&self) -> Ty {
        self.term.ty()
    }
}

/// Strict certified proposition.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CProp {
    term: Term,
}

impl CProp {
    pub(in crate::kernel) fn new(term: Term) -> Result<Self, KernelError> {
        if !term.ty().is_prop() {
            return Err(KernelError::NotProposition(term.ty().clone()));
        }
        Ok(CProp { term })
    }

    pub(in crate::kernel) fn from_checked_term(term: Term) -> Self {
        debug_assert!(term.ty().is_prop());
        CProp { term }
    }

    pub fn term(&self) -> &Term {
        &self.term
    }
}
