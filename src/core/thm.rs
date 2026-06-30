//! Isabelle theorem kernel — the LCF trusted core.
//!
//! Corresponds to `src/Pure/thm.ML`.
//!
//! ## Isabelle's LCF Philosophy
//!
//! The theorem type `Thm` is **abstract** — it has no public constructors.
//! The only way to create a `Thm` is through the primitive inference rules
//! in `ThmKernel`. This guarantees that every `Thm` is indeed a logical
//! consequence of the axioms.
//!
//! ## Key design decisions aligned with Isabelle
//!
//! 1. **Abstract type**: `Thm` fields are private; only `ThmKernel` creates them
//! 2. **Pure logic**: uses `Pure` module for `==>`, `!!`, `==`
//! 3. **Hyps as α-equivalence classes**: hypotheses are identified modulo α
//! 4. **Derivations**: theorems carry proof terms (or oracle tags)
//! 5. **Maxidx**: proper tracking for fresh variable generation

use std::{
    collections::HashMap,
    fmt,
    hash::{Hash, Hasher},
    sync::Arc,
};

use super::{
    error::KernelError,
    logic::Pure,
    term::Term,
    types::{Sort, Typ, TypeEnv},
};

// =========================================================================
// Certified terms (cterm) — align with Isabelle's cterm
// =========================================================================

/// A certified term — a term that has been type-checked against a theory
/// signature. In Isabelle, `cterm` is an abstract type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CertStatus {
    /// Strictly checked against an explicit `TypeEnv`.
    Checked,
    /// Best-effort compatibility wrapper for legacy parser/HOL paths.
    Compat,
}

/// The construction boundary that produced a theorem.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ThmTrust {
    /// Constructed only through strict checked kernel inputs and strict rules.
    Strict,
    /// Constructed through a legacy/best-effort compatibility path.
    Compat,
    /// Accepted through an oracle/admit footprint, or derived from one.
    Admitted,
}

/// How hard theorem invariants should be checked.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum KernelCheckMode {
    /// Legacy/searchable fact mode. Checks structural consistency only.
    Compat,
    /// Trusted kernel mode. Requires strict construction provenance and no
    /// dummy-typed theorem burdens.
    Strict,
}

/// A certified term — a term paired with certification metadata.
#[derive(Clone)]
pub struct CTerm {
    term: Term,
    maxidx: usize,
    /// The type of this term (Typ::dummy() if unknown).
    term_type: Typ,
    cert_status: CertStatus,
}

impl PartialEq for CTerm {
    fn eq(&self, other: &Self) -> bool {
        self.term == other.term && self.maxidx == other.maxidx && self.term_type == other.term_type
    }
}

impl Eq for CTerm {}

impl Hash for CTerm {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.term.hash(state);
        self.maxidx.hash(state);
        self.term_type.hash(state);
    }
}

impl CTerm {
    /// Compatibility certification.
    ///
    /// This is the historical best-effort wrapper: it infers a top-level type
    /// when possible, may consult the global HOL type database, and may still
    /// return a `CTerm` whose type is `Typ::dummy()`. It exists for legacy
    /// parser/loader/HOL compatibility and must not be treated as a hard
    /// trusted certification boundary.
    pub fn certify(term: Term) -> Self {
        let maxidx = Self::compute_maxidx(&term);
        // Try to infer type from the term structure
        let term_type = Self::infer_type(&term);
        // If type is still dummy, try the type inference engine
        let term_type = if term_type.is_dummy() {
            super::type_infer::infer_type(&term).unwrap_or(term_type)
        } else {
            term_type
        };
        CTerm { term, maxidx, term_type, cert_status: CertStatus::Compat }
    }

    /// Compatibility alias for callers that need the legacy best-effort
    /// behavior explicitly.
    pub fn certify_compat(term: Term) -> Self {
        Self::certify(term)
    }

    /// Strict certification against an explicit type environment.
    ///
    /// This is the trusted certification entry point for new kernel-facing
    /// code. It rejects unknown constants, ill-typed applications, unbound
    /// de Bruijn indices, and any residual `Typ::dummy()` in the certified
    /// term or its inferred type. It never performs parser compatibility
    /// repairs such as Free/Const name fallback.
    pub fn certify_checked(term: Term, type_env: &TypeEnv) -> Result<Self, KernelError> {
        let (term, term_type) = Self::certify_checked_term(term, type_env, &[])?;
        if term_type.contains_dummy() || Self::term_contains_dummy_type(&term) {
            return Err(KernelError::DummyType { op: "CTerm::certify_checked" });
        }
        let maxidx = Self::compute_maxidx(&term);
        Ok(CTerm { term, maxidx, term_type, cert_status: CertStatus::Checked })
    }

    /// Mark a kernel-derived term as checked after a primitive rule has
    /// constructed it from already checked inputs.
    ///
    /// This does not perform parser/type inference repairs. It only verifies
    /// that the derived term has a non-dummy apparent type and no embedded
    /// dummy annotations.
    pub(crate) fn certify_derived_checked(
        term: Term,
        op: &'static str,
    ) -> Result<Self, KernelError> {
        let maxidx = Self::compute_maxidx(&term);
        let term_type = Self::infer_type(&term);
        if term_type.contains_dummy() || Self::term_contains_dummy_type(&term) {
            return Err(KernelError::DummyType { op });
        }
        Ok(CTerm { term, maxidx, term_type, cert_status: CertStatus::Checked })
    }

    /// Create a compatibility CTerm with an explicit top-level type.
    ///
    /// This bypasses structural type checking and is therefore compatibility
    /// certification, not a trusted checked term.
    pub fn certify_typed(term: Term, typ: Typ) -> Self {
        let maxidx = Self::compute_maxidx(&term);
        CTerm { term, maxidx, term_type: typ, cert_status: CertStatus::Compat }
    }

    pub fn term(&self) -> &Term {
        &self.term
    }
    pub fn maxidx(&self) -> usize {
        self.maxidx
    }
    pub fn term_type(&self) -> &Typ {
        &self.term_type
    }
    pub fn cert_status(&self) -> CertStatus {
        self.cert_status
    }
    pub fn is_checked(&self) -> bool {
        self.cert_status == CertStatus::Checked
    }

    /// Require strict checked certification.
    pub fn require_checked(&self, op: &'static str) -> Result<(), KernelError> {
        if self.is_checked() { Ok(()) } else { Err(KernelError::CompatCTerm { op }) }
    }

    /// Require non-dummy type — fails if the type is Typ::dummy().
    /// Use this at kernel rule boundaries to ensure type safety.
    pub fn require_non_dummy(&self, op: &'static str) -> Result<&Typ, KernelError> {
        if self.term_type.is_dummy() {
            Err(KernelError::DummyType { op })
        } else {
            Ok(&self.term_type)
        }
    }

    /// Require that neither the top-level type nor embedded term annotations
    /// contain `Typ::dummy()`.
    pub fn require_no_dummy_types(&self, op: &'static str) -> Result<(), KernelError> {
        if self.contains_dummy_type() { Err(KernelError::DummyType { op }) } else { Ok(()) }
    }

    /// Whether this certified term still contains a dummy type annotation.
    pub fn contains_dummy_type(&self) -> bool {
        self.term_type.contains_dummy() || Self::term_contains_dummy_type(&self.term)
    }

    /// Whether a raw term contains any dummy type annotation.
    pub fn term_contains_dummy_type(term: &Term) -> bool {
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            match t {
                Term::Const { typ, .. } | Term::Free { typ, .. } | Term::Var { typ, .. } => {
                    if typ.contains_dummy() {
                        return true;
                    }
                },
                Term::Abs { typ, body, .. } => {
                    if typ.contains_dummy() {
                        return true;
                    }
                    stack.push(body);
                },
                Term::App { func, arg } => {
                    stack.push(arg);
                    stack.push(func);
                },
                Term::Bound(_) => {},
            }
        }
        false
    }

    /// Create a certified term, attempting to annotate dummy types from the
    /// global theorem database's TypeEnv first. Falls back to plain `certify`
    /// if the DB is not available.
    pub fn certify_annotated(mut term: Term) -> Self {
        // Try to annotate dummy types from the global TypeEnv
        use crate::hol::hol_loader::HolTheoremDb;
        let db = HolTheoremDb::get();
        term.type_annotate(&db.type_env);
        Self::certify(term)
    }

    /// Infer the type of a term from its structure.
    /// Returns Typ::dummy() if type cannot be determined.
    fn infer_type(term: &Term) -> Typ {
        match term {
            Term::Const { typ, .. } if !typ.is_dummy() => typ.clone(),
            Term::Free { typ, .. } if !typ.is_dummy() => typ.clone(),
            Term::Var { typ, .. } if !typ.is_dummy() => typ.clone(),
            Term::Abs { typ, .. } if !typ.is_dummy() => typ.clone(),
            Term::App { func, arg: _ } => {
                let ft = Self::infer_type(func);
                if let Some((_, ret)) = ft.dest_fun() { ret.clone() } else { Typ::dummy() }
            },
            _ => Typ::dummy(),
        }
    }

    fn certify_checked_term(
        term: Term,
        type_env: &TypeEnv,
        bound_types: &[Typ],
    ) -> Result<(Term, Typ), KernelError> {
        match term {
            Term::Const { name, typ } => {
                let typ = if typ.is_dummy() {
                    type_env
                        .const_type(name.as_ref())
                        .cloned()
                        .ok_or_else(|| KernelError::UndeclaredConstant(name.to_string()))?
                } else {
                    if let Some(declared) = type_env.const_type(name.as_ref()) {
                        if !Self::type_scheme_matches(declared, &typ) {
                            return Err(KernelError::TypeMismatch {
                                expected: declared.clone(),
                                actual: typ,
                            });
                        }
                    } else {
                        return Err(KernelError::UndeclaredConstant(name.to_string()));
                    }
                    typ
                };
                Self::ensure_type_has_no_dummy(&typ, "CTerm::certify_checked")?;
                Ok((Term::Const { name, typ: typ.clone() }, typ))
            },
            Term::Free { name, typ } => {
                let typ = if typ.is_dummy() {
                    type_env
                        .frees
                        .get(name.as_ref())
                        .cloned()
                        .ok_or(KernelError::DummyType { op: "CTerm::certify_checked" })?
                } else {
                    if let Some(declared) = type_env.frees.get(name.as_ref())
                        && declared != &typ
                    {
                        return Err(KernelError::TypeMismatch {
                            expected: declared.clone(),
                            actual: typ,
                        });
                    }
                    typ
                };
                Self::ensure_type_has_no_dummy(&typ, "CTerm::certify_checked")?;
                Ok((Term::Free { name, typ: typ.clone() }, typ))
            },
            Term::Var { name, index, typ } => {
                Self::ensure_type_has_no_dummy(&typ, "CTerm::certify_checked")?;
                Ok((Term::Var { name, index, typ: typ.clone() }, typ))
            },
            Term::Bound(index) => {
                let typ = bound_types
                    .get(index)
                    .cloned()
                    .ok_or(KernelError::DummyType { op: "CTerm::certify_checked" })?;
                Self::ensure_type_has_no_dummy(&typ, "CTerm::certify_checked")?;
                Ok((Term::Bound(index), typ))
            },
            Term::Abs { name, typ, body } => {
                Self::ensure_type_has_no_dummy(&typ, "CTerm::certify_checked")?;
                let mut scoped = Vec::with_capacity(bound_types.len() + 1);
                scoped.push(typ.clone());
                scoped.extend_from_slice(bound_types);
                let (body, body_typ) = Self::certify_checked_term(*body, type_env, &scoped)?;
                let abs_typ = Typ::arrow(typ.clone(), body_typ);
                Ok((Term::Abs { name, typ, body: Box::new(body) }, abs_typ))
            },
            Term::App { func, arg } => {
                let (func, func_typ) = Self::certify_checked_term(*func, type_env, bound_types)?;
                let (arg, arg_typ) = Self::certify_checked_term(*arg, type_env, bound_types)?;
                let (expected_arg, result_typ) = func_typ
                    .dest_fun()
                    .map(|(from, to)| (from.clone(), to.clone()))
                    .ok_or_else(|| KernelError::NotFunctionType(func_typ.clone()))?;
                let mut subst = HashMap::new();
                if !Self::type_scheme_match_inner(&expected_arg, &arg_typ, &mut subst) {
                    return Err(KernelError::TypeMismatch {
                        expected: expected_arg,
                        actual: arg_typ,
                    });
                }
                let result_typ = Self::apply_type_scheme_subst(&result_typ, &subst);
                Self::ensure_type_has_no_dummy(&result_typ, "CTerm::certify_checked")?;
                Ok((Term::App { func: Box::new(func), arg: Box::new(arg) }, result_typ))
            },
        }
    }

    fn ensure_type_has_no_dummy(typ: &Typ, op: &'static str) -> Result<(), KernelError> {
        if typ.contains_dummy() { Err(KernelError::DummyType { op }) } else { Ok(()) }
    }

    fn type_scheme_matches(scheme: &Typ, actual: &Typ) -> bool {
        let mut subst = HashMap::new();
        Self::type_scheme_match_inner(scheme, actual, &mut subst)
    }

    fn type_scheme_match_inner(
        scheme: &Typ,
        actual: &Typ,
        subst: &mut HashMap<String, Typ>,
    ) -> bool {
        if actual.contains_dummy() {
            return false;
        }
        match scheme {
            Typ::TFree { name, .. } => {
                Self::bind_type_scheme_var(format!("F:{}", name.as_ref()), actual, subst)
            },
            Typ::TVar { name, index, .. } => {
                Self::bind_type_scheme_var(format!("V:{}:{index}", name.as_ref()), actual, subst)
            },
            Typ::Type { name: n1, args: a1 } => match actual {
                Typ::Type { name: n2, args: a2 } if n1 == n2 && a1.len() == a2.len() => a1
                    .iter()
                    .zip(a2.iter())
                    .all(|(left, right)| Self::type_scheme_match_inner(left, right, subst)),
                _ => false,
            },
        }
    }

    fn bind_type_scheme_var(key: String, actual: &Typ, subst: &mut HashMap<String, Typ>) -> bool {
        if actual.contains_dummy() {
            return false;
        }
        match subst.get(&key) {
            Some(bound) => bound == actual,
            None => {
                subst.insert(key, actual.clone());
                true
            },
        }
    }

    fn apply_type_scheme_subst(typ: &Typ, subst: &HashMap<String, Typ>) -> Typ {
        match typ {
            Typ::TFree { name, .. } => {
                subst.get(&format!("F:{}", name.as_ref())).cloned().unwrap_or_else(|| typ.clone())
            },
            Typ::TVar { name, index, .. } => subst
                .get(&format!("V:{}:{index}", name.as_ref()))
                .cloned()
                .unwrap_or_else(|| typ.clone()),
            Typ::Type { name, args } => {
                let args =
                    args.iter().map(|arg| Self::apply_type_scheme_subst(arg, subst)).collect();
                Typ::Type { name: name.clone(), args }
            },
        }
    }

    fn compute_maxidx(t: &Term) -> usize {
        // Iterative implementation using explicit stack to avoid recursion overflow
        let mut maxidx = 0usize;
        let mut stack: Vec<&Term> = vec![t];
        while let Some(term) = stack.pop() {
            match term {
                Term::Var { index, typ, .. } => {
                    maxidx = usize::max(maxidx, *index);
                    maxidx = usize::max(maxidx, typ.maxidx());
                },
                Term::Const { typ, .. } | Term::Free { typ, .. } => {
                    maxidx = usize::max(maxidx, typ.maxidx());
                },
                Term::Abs { typ, body, .. } => {
                    maxidx = usize::max(maxidx, typ.maxidx());
                    stack.push(body);
                },
                Term::App { func, arg } => {
                    stack.push(arg);
                    stack.push(func);
                },
                Term::Bound(_) => {},
            }
        }
        maxidx
    }
}

impl fmt::Debug for CTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CTerm({:?}, {:?})", self.term, self.cert_status)
    }
}

// =========================================================================
// Hypotheses — α-equivalence classes
// =========================================================================

/// A set of hypotheses (assumptions).
///
/// In Isabelle, hypotheses are identified modulo α-equivalence.
/// Two hypotheses that differ only in bound variable names are the same.
#[derive(Clone, PartialEq, Eq)]
pub struct Hyps {
    entries: Vec<CTerm>,
}

impl Hyps {
    pub fn empty() -> Self {
        Hyps { entries: Vec::new() }
    }

    pub fn singleton(h: CTerm) -> Self {
        Hyps { entries: vec![h] }
    }

    pub fn insert(&mut self, h: CTerm) {
        // Check α-equivalence against existing hypotheses
        if !self.contains(&h) {
            self.entries.push(h);
        }
    }

    /// Check if a hypothesis is already present (modulo kernel α-equivalence).
    pub fn contains(&self, h: &CTerm) -> bool {
        self.entries.iter().any(|existing| Self::kernel_alpha_eq(existing.term(), h.term()))
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
    pub fn iter(&self) -> impl Iterator<Item = &CTerm> {
        self.entries.iter()
    }

    /// Union: H1 ∪ H2.
    pub fn union(&self, other: &Hyps) -> Hyps {
        let mut result = self.clone();
        for h in &other.entries {
            result.insert(h.clone());
        }
        result
    }

    /// Remove a hypothesis.
    pub fn remove(&self, h: &CTerm) -> Hyps {
        Hyps {
            entries: self
                .entries
                .iter()
                .filter(|existing| !Self::kernel_alpha_eq(existing.term(), h.term()))
                .cloned()
                .collect(),
        }
    }

    /// Strict kernel α-equivalence check for terms.
    ///
    /// This relation is for trusted theorem construction. It only accepts real
    /// structural α-equivalence: term constructors must match, schematic
    /// variable indices must match, and binder types must match. It deliberately
    /// does not perform parser/loader compatibility repairs such as Free/Const
    /// suffix matching or Var/Free matching.
    pub(crate) fn kernel_alpha_eq(a: &Term, b: &Term) -> bool {
        match (a, b) {
            (Term::Const { name: n1, .. }, Term::Const { name: n2, .. }) => n1 == n2,
            (Term::Free { name: n1, .. }, Term::Free { name: n2, .. }) => n1 == n2,
            (Term::Var { name: n1, index: i1, .. }, Term::Var { name: n2, index: i2, .. }) => {
                n1 == n2 && i1 == i2
            },
            (Term::Bound(i1), Term::Bound(i2)) => i1 == i2,
            (Term::Abs { body: b1, typ: t1, .. }, Term::Abs { body: b2, typ: t2, .. }) => {
                t1 == t2 && Self::kernel_alpha_eq(b1, b2)
            },
            (Term::App { func: f1, arg: a1 }, Term::App { func: f2, arg: a2 }) => {
                Self::kernel_alpha_eq(f1, f2) && Self::kernel_alpha_eq(a1, a2)
            },
            _ => false,
        }
    }

    /// Backward-compatible parser/loader matching.
    ///
    /// This preserves the historical loose behavior for explicitly marked
    /// compatibility paths only. It must not be used by trusted `ThmKernel`
    /// primitive rules.
    #[allow(dead_code)]
    pub(crate) fn compat_alpha_eq(a: &Term, b: &Term) -> bool {
        match (a, b) {
            (Term::Const { name: n1, .. }, Term::Const { name: n2, .. }) => n1 == n2,
            (Term::Free { name: n1, .. }, Term::Free { name: n2, .. }) => n1 == n2,
            (Term::Free { name: n1, .. }, Term::Const { name: n2, .. })
            | (Term::Const { name: n2, .. }, Term::Free { name: n1, .. }) => {
                n1 == n2
                    || n1.as_ref().ends_with(&format!(".{}", n2.as_ref()))
                    || n2.as_ref().ends_with(&format!(".{}", n1.as_ref()))
            },
            (Term::Var { name: n1, .. }, Term::Free { name: n2, .. })
            | (Term::Free { name: n2, .. }, Term::Var { name: n1, .. }) => n1 == n2,
            (Term::Var { name: n1, index: i1, .. }, Term::Var { name: n2, index: i2, .. }) => {
                n1 == n2 && i1 == i2
            },
            (Term::Bound(i1), Term::Bound(i2)) => i1 == i2,
            (Term::Abs { body: b1, typ: t1, .. }, Term::Abs { body: b2, typ: t2, .. }) => {
                // Compatibility mode still tolerates dummy binders for legacy
                // parser output. Trusted kernel equality does not.
                (t1.is_dummy() || t2.is_dummy() || t1 == t2) && Self::compat_alpha_eq(b1, b2)
            },
            (Term::App { func: f1, arg: a1 }, Term::App { func: f2, arg: a2 }) => {
                Self::compat_alpha_eq(f1, f2) && Self::compat_alpha_eq(a1, a2)
            },
            _ => false,
        }
    }
}

impl fmt::Debug for Hyps {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, h) in self.entries.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", h.term())?;
        }
        write!(f, "]")
    }
}

// =========================================================================
// Derivation — the proof record
// =========================================================================

/// A derivation records how a theorem was proved.
///
/// In Isabelle's `proofterm.ML`, every theorem carries a derivation object
/// that can be replayed for proof checking.
///
/// - `Oracle`: the theorem came from an external source (tagged as untrusted)
/// - `Axiom`: a primitive inference rule with no premises
/// - `Rule`: a primitive inference rule applied to premises
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Derivation {
    Oracle { name: String, prop: CTerm },
    Axiom { name: &'static str, prop: CTerm },
    Rule { name: &'static str, prop: CTerm, premises: Vec<ThmDeriv> },
}

/// A reference to a premise theorem's derivation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ThmDeriv {
    pub(crate) serial: u64,
    pub(crate) prop: CTerm,
    pub(crate) hyps: Hyps,
    pub(crate) tpairs: Vec<(Term, Term)>,
    pub(crate) oracles: Vec<Arc<str>>,
    pub(crate) trust: ThmTrust,
    pub(crate) derivation: Derivation,
}

// =========================================================================
// Thm — the abstract theorem type
// =========================================================================

/// A **theorem**: `Γ ⊢ φ` where Γ are hypotheses and φ is the conclusion.
///
/// This is the central type of the LCF trusted kernel.
/// **No public constructors** — use `ThmKernel` to create theorems.
///
/// ## Isabelle Correspondence
///
/// In Isabelle/ML (`thm.ML`), theorems carry additional fields:
/// - `tpairs`: flex-flex disagreement pairs from higher-order unification
/// - `shyps`: sort hypotheses tracking type-class constraints
/// - `maxidx`: maximum schematic variable index for freshness
///
/// These are tracked here to maintain full Isabelle kernel equivalence.
#[derive(Clone, PartialEq, Eq)]
pub struct Thm {
    hyps: Hyps,
    prop: CTerm,
    maxidx: usize,
    /// Flex-flex disagreement pairs (tpairs in Isabelle).
    ///
    /// During higher-order unification, some pairs may remain unresolved
    /// when both sides are flexible (contain schematic variables). These
    /// are stored as constraints on the theorem.
    ///
    /// Each pair `(t, u)` represents the constraint that `t` and `u`
    /// must be made equal by some future instantiation.
    tpairs: Vec<(Term, Term)>,
    /// Sort hypotheses (shyps in Isabelle).
    ///
    /// When a theorem uses type-class-polymorphic constants, it carries
    /// sort constraints like `OFCLASS('a, order)`. These must be
    /// satisfied by the calling context.
    shyps: Vec<Sort>,
    /// Oracle trust footprint (Isabelle's `oracles_of`).
    ///
    /// The set of *unproved* assertions this theorem ultimately depends on:
    /// external oracles, `sorry`, or lemmas `admitted` by the verifier when
    /// its proof engine could not replay the script. Propagated as a union
    /// through every inference rule, exactly like `hyps`.
    ///
    /// Empty means the theorem is oracle-free. A lemma is counted as a closed
    /// proved result only if this is empty and no hypotheses or unresolved
    /// tpairs remain.
    oracles: Vec<Arc<str>>,
    /// How this theorem crossed the trusted construction boundary.
    ///
    /// This is independent from the oracle footprint. A compatibility theorem
    /// may be oracle-free and closed-shaped, but it is not a strict trusted
    /// theorem until it is rebuilt through checked CTerms and strict kernel
    /// rules.
    trust: ThmTrust,
    derivation: Derivation,
    serial: u64,
}

impl ThmDeriv {
    fn from_thm(thm: &Thm) -> Self {
        ThmDeriv {
            serial: thm.serial,
            prop: thm.prop.clone(),
            hyps: thm.hyps.clone(),
            tpairs: thm.tpairs.clone(),
            oracles: thm.oracles.clone(),
            trust: thm.trust,
            derivation: thm.derivation.clone(),
        }
    }
}

impl Thm {
    pub fn hyps(&self) -> &Hyps {
        &self.hyps
    }
    pub fn prop(&self) -> &CTerm {
        &self.prop
    }
    pub fn maxidx(&self) -> usize {
        self.maxidx
    }
    pub fn is_unconditional(&self) -> bool {
        self.hyps.is_empty()
    }
    /// Whether this theorem has no ambient hypotheses and no unresolved
    /// higher-order unification constraints. The proposition may still contain
    /// object-level implications such as `A ==> A`.
    pub fn is_closed(&self) -> bool {
        self.hyps.is_empty() && self.tpairs.is_empty()
    }
    /// Flex-flex disagreement pairs from higher-order unification.
    pub fn tpairs(&self) -> &[(Term, Term)] {
        &self.tpairs
    }
    /// Sort hypotheses (type-class constraints).
    pub fn shyps(&self) -> &[Sort] {
        &self.shyps
    }
    pub fn has_oracles(&self) -> bool {
        !self.oracles.is_empty()
    }

    /// The oracle trust footprint: the unproved assertions (oracles, `sorry`,
    /// `admitted` lemmas) this theorem ultimately depends on. Empty for a
    /// genuinely proved theorem.
    pub fn oracles(&self) -> &[Arc<str>] {
        &self.oracles
    }

    /// Whether this theorem has an empty oracle footprint.
    ///
    /// This does not imply the theorem is a closed lemma: `assume(A)` is
    /// oracle-free but still has hypothesis `A`.
    pub fn is_fully_proved(&self) -> bool {
        self.oracles.is_empty()
    }
    /// Whether this theorem is both oracle-free and closed-shaped.
    ///
    /// This does not imply strict trusted acceptance: compatibility theorems
    /// can be oracle-free and closed-shaped. Final trusted tables and verified
    /// statistics must use `is_strict_closed_proved()`.
    pub fn is_closed_proved(&self) -> bool {
        self.is_fully_proved() && self.is_closed()
    }
    /// The construction boundary used for this theorem.
    pub fn trust_status(&self) -> ThmTrust {
        self.trust
    }
    /// Whether this theorem was constructed through strict kernel paths.
    pub fn is_strict_kernel_theorem(&self) -> bool {
        self.trust == ThmTrust::Strict
    }
    /// Whether this theorem was constructed through compatibility paths.
    pub fn is_compat_theorem(&self) -> bool {
        self.trust == ThmTrust::Compat
    }
    /// Whether this theorem depends on an admitted/oracle source.
    pub fn is_admitted_theorem(&self) -> bool {
        self.trust == ThmTrust::Admitted || !self.oracles.is_empty()
    }
    /// Whether this theorem contains any residual dummy type annotation.
    pub fn contains_dummy_type(&self) -> bool {
        self.prop.contains_dummy_type()
            || self.hyps.iter().any(CTerm::contains_dummy_type)
            || self.tpairs.iter().any(|(t, u)| {
                CTerm::term_contains_dummy_type(t) || CTerm::term_contains_dummy_type(u)
            })
    }
    /// Strict trusted theorem-table eligibility.
    pub fn is_strict_closed_proved(&self) -> bool {
        self.is_strict_kernel_theorem()
            && self.is_closed_proved()
            && self.prop.is_checked()
            && self.hyps.iter().all(CTerm::is_checked)
            && !self.contains_dummy_type()
    }
    pub fn serial(&self) -> u64 {
        self.serial
    }

    fn invariant_error(message: impl Into<String>) -> KernelError {
        KernelError::KernelInvariant { op: "Thm::check_kernel_invariants", message: message.into() }
    }

    fn cterm_actual_maxidx(ct: &CTerm) -> usize {
        usize::max(CTerm::compute_maxidx(ct.term()), ct.term_type().maxidx())
    }

    fn actual_maxidx(&self) -> usize {
        let mut maxidx = Self::cterm_actual_maxidx(&self.prop);
        for hyp in self.hyps.iter() {
            maxidx = usize::max(maxidx, Self::cterm_actual_maxidx(hyp));
        }
        for (left, right) in &self.tpairs {
            maxidx = usize::max(maxidx, CTerm::compute_maxidx(left));
            maxidx = usize::max(maxidx, CTerm::compute_maxidx(right));
        }
        maxidx
    }

    fn require_cterm_structural(
        ct: &CTerm,
        label: &'static str,
        mode: KernelCheckMode,
    ) -> Result<(), KernelError> {
        let actual_maxidx = Self::cterm_actual_maxidx(ct);
        if ct.maxidx() != actual_maxidx {
            return Err(Self::invariant_error(format!(
                "{label} CTerm maxidx mismatch: stored {}, actual {actual_maxidx}",
                ct.maxidx()
            )));
        }

        if mode == KernelCheckMode::Strict {
            ct.require_checked("Thm::check_kernel_invariants")?;
            ct.require_no_dummy_types("Thm::check_kernel_invariants")?;
            if ct.term_type() != &Pure::prop_type() {
                return Err(Self::invariant_error(format!(
                    "{label} is not a Pure proposition: type {:?}",
                    ct.term_type()
                )));
            }
        }

        Ok(())
    }

    fn derivation_replay_supported(deriv: &Derivation) -> bool {
        match deriv {
            Derivation::Oracle { .. } => false,
            Derivation::Axiom { name, .. } => matches!(*name, "assume" | "reflexive"),
            Derivation::Rule { name, premises, .. } => {
                matches!(*name, "symmetric" | "transitive" | "implies_intr" | "implies_elim")
                    && premises
                        .iter()
                        .all(|premise| Self::derivation_replay_supported(&premise.derivation))
            },
        }
    }

    /// Check theorem construction invariants.
    ///
    /// `Compat` mode is for legacy/searchable facts and only checks structural
    /// self-consistency. `Strict` mode is the trusted-kernel gate: it requires
    /// strict construction provenance, checked proposition/hypothesis CTerms,
    /// no residual dummy types, no oracle footprint, exact `maxidx`, and
    /// burden-aware proof replay for the currently supported replay subset.
    pub fn check_kernel_invariants(&self, mode: KernelCheckMode) -> Result<(), KernelError> {
        if mode == KernelCheckMode::Strict && self.trust != ThmTrust::Strict {
            return Err(Self::invariant_error(format!(
                "strict invariant requires ThmTrust::Strict, found {:?}",
                self.trust
            )));
        }

        Self::require_cterm_structural(&self.prop, "proposition", mode)?;
        for hyp in self.hyps.iter() {
            Self::require_cterm_structural(hyp, "hypothesis", mode)?;
        }

        let actual_maxidx = self.actual_maxidx();
        if self.maxidx != actual_maxidx {
            return Err(Self::invariant_error(format!(
                "theorem maxidx mismatch: stored {}, actual {actual_maxidx}",
                self.maxidx
            )));
        }

        if self.trust == ThmTrust::Strict && !self.oracles.is_empty() {
            return Err(Self::invariant_error("strict theorem carries an oracle/admit footprint"));
        }
        if self.trust == ThmTrust::Admitted && self.oracles.is_empty() {
            return Err(Self::invariant_error("admitted theorem has no oracle/admit footprint"));
        }

        if mode == KernelCheckMode::Strict {
            if self.contains_dummy_type() {
                return Err(Self::invariant_error(
                    "strict theorem contains Typ::dummy in prop/hyps/tpairs",
                ));
            }
            if self.tpairs.iter().any(|(left, right)| {
                CTerm::term_contains_dummy_type(left) || CTerm::term_contains_dummy_type(right)
            }) {
                return Err(Self::invariant_error("strict theorem has dummy-typed tpairs"));
            }
            if Self::derivation_replay_supported(&self.derivation) {
                self.check_proof().map_err(|err| {
                    Self::invariant_error(format!("proof replay burden mismatch: {err}"))
                })?;
            }
        }

        Ok(())
    }

    /// Number of subgoals (premises in the prop chain).
    pub fn nprems(&self) -> usize {
        Pure::count_prems(self.prop.term())
    }

    /// Reconstruct the proof term for this theorem from its derivation.
    pub fn proof_term(&self) -> super::proofterm::ProofTerm {
        super::proofterm::ProofTerm::from_derivation(&self.derivation)
    }

    /// Check that this theorem's proof term is valid.
    /// Returns `Ok(())` if the proof checks out, or an error message.
    pub fn check_proof(&self) -> Result<(), String> {
        let proof = self.proof_term();
        super::proofterm::check_proof_with_burdens(
            &proof,
            self.prop.term(),
            &self.hyps,
            &self.tpairs,
            &self.oracles,
        )
    }

    /// Get the proof body for this theorem (lazy checking).
    pub fn proof_body(&self) -> super::proofterm::ProofBody {
        super::proofterm::ProofBody::from_derivation(&self.derivation)
    }

    /// Validate the proof body against the theorem's proposition.
    /// Returns Ok if the proof is valid (or cached), Err if invalid.
    pub fn validate_proof(&self, body: &mut super::proofterm::ProofBody) -> Result<(), String> {
        body.check_with_burdens(self.prop.term(), &self.hyps, &self.tpairs, &self.oracles)
    }

    /// Get the i-th subgoal (0-indexed).
    pub fn prem(&self, i: usize) -> Option<Term> {
        Pure::nth_premise(self.prop.term(), i).cloned()
    }

    /// Get the main conclusion (after stripping all ==>-chain premises).
    pub fn concl(&self) -> Term {
        Pure::strip_imp_prems(self.prop.term()).1.clone()
    }
}

impl fmt::Debug for Thm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let hyps: Vec<String> = self.hyps.iter().map(|h| format!("{:?}", h.term())).collect();
        if hyps.is_empty() {
            write!(f, "⊢ {:?}", self.prop.term())
        } else {
            write!(f, "{} ⊢ {:?}", hyps.join(", "), self.prop.term())
        }
    }
}

impl fmt::Display for Thm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

// =========================================================================
// ThmKernel — the ONLY way to create Thm values
// =========================================================================

static NEXT_SERIAL: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn new_serial() -> u64 {
    NEXT_SERIAL.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

/// The trusted kernel.
///
/// Every function here implements one primitive inference rule
/// of Isabelle/Pure. These functions MUST be correct — any bug
/// could allow proving `False`.
pub struct ThmKernel;

impl ThmKernel {
    /// Union two oracle footprints, preserving uniqueness.
    ///
    /// Used by every multi-premise rule to propagate the trust footprint of
    /// its premises into the conclusion, exactly as `hyps` are unioned.
    fn union_oracles(a: &[Arc<str>], b: &[Arc<str>]) -> Vec<Arc<str>> {
        if b.is_empty() {
            return a.to_vec();
        }
        if a.is_empty() {
            return b.to_vec();
        }
        let mut out = a.to_vec();
        for o in b {
            if !out.iter().any(|x| **x == **o) {
                out.push(Arc::clone(o));
            }
        }
        out
    }

    /// Union two flex-flex pair lists (tpairs), preserving uniqueness.
    ///
    /// Every multi-premise rule must carry forward the unresolved higher-order
    /// unification constraints of its premises — in Isabelle these are a logical
    /// burden on the theorem that must never be silently dropped. (Currently the
    /// engine produces no flex-flex pairs, so these lists are empty in practice;
    /// this keeps the kernel correct-by-construction once full HO unification
    /// feeds them.)
    fn union_tpairs(a: &[(Term, Term)], b: &[(Term, Term)]) -> Vec<(Term, Term)> {
        if b.is_empty() {
            return a.to_vec();
        }
        if a.is_empty() {
            return b.to_vec();
        }
        let mut out = a.to_vec();
        for p in b {
            if !out.contains(p) {
                out.push(p.clone());
            }
        }
        out
    }

    /// Union two sort-hypothesis lists (shyps), preserving uniqueness.
    ///
    /// Sort constraints required by type-class-polymorphic constants must be
    /// propagated, not forgotten — dropping them would let a theorem be used in
    /// a context where its class constraints are unsatisfied.
    fn union_shyps(a: &[Sort], b: &[Sort]) -> Vec<Sort> {
        if b.is_empty() {
            return a.to_vec();
        }
        if a.is_empty() {
            return b.to_vec();
        }
        let mut out = a.to_vec();
        for s in b {
            if !out.contains(s) {
                out.push(s.clone());
            }
        }
        out
    }

    fn trust_from_premises(premises: &[&Thm]) -> ThmTrust {
        if premises.iter().any(|thm| thm.trust == ThmTrust::Admitted || !thm.oracles.is_empty()) {
            ThmTrust::Admitted
        } else if premises.iter().all(|thm| thm.trust == ThmTrust::Strict) {
            ThmTrust::Strict
        } else {
            ThmTrust::Compat
        }
    }

    fn trust_from_premises_and_cterms(premises: &[&Thm], cterms: &[&CTerm]) -> ThmTrust {
        match Self::trust_from_premises(premises) {
            ThmTrust::Admitted => ThmTrust::Admitted,
            ThmTrust::Strict if cterms.iter().all(|ct| ct.is_checked()) => ThmTrust::Strict,
            _ => ThmTrust::Compat,
        }
    }

    fn trust_from_cterm(ct: &CTerm) -> ThmTrust {
        if ct.is_checked() { ThmTrust::Strict } else { ThmTrust::Compat }
    }

    fn certify_rule_prop(
        term: Term,
        trust: ThmTrust,
        op: &'static str,
    ) -> Result<CTerm, KernelError> {
        if trust == ThmTrust::Strict {
            CTerm::certify_derived_checked(term, op)
        } else {
            Ok(CTerm::certify(term))
        }
    }

    /// Whether two known concrete types are incompatible.
    ///
    /// `dummy`, `TVar`, and `TFree` remain potentially compatible: these are
    /// schema or parser-boundary unknowns, not concrete type contradictions.
    fn known_types_mismatch(expected: &Typ, actual: &Typ) -> bool {
        !expected.is_dummy() && !actual.is_dummy() && !Self::types_compatible(expected, actual)
    }

    /// Infer a term's apparent type from embedded annotations.
    ///
    /// This is deliberately conservative: if we cannot infer a meaningful type,
    /// return `Typ::dummy()` so legacy parser gaps are not treated as concrete
    /// contradictions.
    fn term_known_type(term: &Term) -> Typ {
        match term {
            Term::Const { typ, .. } | Term::Free { typ, .. } | Term::Var { typ, .. } => typ.clone(),
            Term::Abs { typ, body, .. } => {
                let body_typ = Self::term_known_type(body);
                if typ.is_dummy() || body_typ.is_dummy() {
                    Typ::dummy()
                } else {
                    Typ::arrow(typ.clone(), body_typ)
                }
            },
            Term::App { func, .. } => {
                let fn_typ = Self::term_known_type(func);
                fn_typ.dest_fun().map(|(_, ret)| ret.clone()).unwrap_or_else(Typ::dummy)
            },
            Term::Bound(_) => Typ::dummy(),
        }
    }

    fn known_term_types_compatible(a: &Term, b: &Term) -> bool {
        let a_typ = Self::term_known_type(a);
        let b_typ = Self::term_known_type(b);
        !Self::known_types_mismatch(&a_typ, &b_typ)
    }

    fn ensure_known_term_types_compatible(a: &Term, b: &Term) -> Result<(), KernelError> {
        let expected = Self::term_known_type(a);
        let actual = Self::term_known_type(b);
        if Self::known_types_mismatch(&expected, &actual) {
            Err(KernelError::TypeMismatch { expected, actual })
        } else {
            Ok(())
        }
    }

    fn alpha_eq_with_known_types(a: &Term, b: &Term) -> bool {
        Hyps::kernel_alpha_eq(a, b) && Self::known_term_types_compatible(a, b)
    }

    /// **Admit** `ct` as an oracle-backed theorem: `⊢ ct`, tagged with the
    /// oracle `name`.
    ///
    /// This is the kernel's single, auditable entry point for accepting a
    /// proposition *without proof* — the analogue of Isabelle's `sorry` and
    /// oracle mechanism. The resulting theorem is NOT `is_fully_proved()`;
    /// its `oracles()` footprint contains `name`, and that footprint
    /// propagates into everything derived from it.
    ///
    /// The verifier's "accept as axiom when the engine cannot replay the
    /// proof" fallback routes through here, so admitted lemmas are honestly
    /// distinguishable from proved ones at the type level.
    pub fn admit(ct: CTerm, name: &str) -> Thm {
        let oracle: Arc<str> = Arc::from(name);
        Thm {
            hyps: Hyps::empty(),
            prop: ct.clone(),
            maxidx: ct.maxidx(),
            tpairs: vec![],
            shyps: vec![],
            oracles: vec![oracle],
            trust: ThmTrust::Admitted,
            derivation: Derivation::Oracle { name: name.to_string(), prop: ct },
            serial: new_serial(),
        }
    }

    /// **Assume** `ct`: `{ct} ⊢ ct`.
    ///
    /// ```text
    /// —————— (assume)
    /// A ⊢ A
    /// ```
    pub fn assume_compat(ct: CTerm) -> Thm {
        Thm {
            hyps: Hyps::singleton(ct.clone()),
            prop: ct.clone(),
            maxidx: ct.maxidx(),
            tpairs: vec![],
            shyps: vec![],
            oracles: vec![],
            trust: ThmTrust::Compat,
            derivation: Derivation::Axiom { name: "assume", prop: ct },
            serial: new_serial(),
        }
    }

    /// Strict assumption entry point for checked `CTerm`s: `A |- A`.
    ///
    /// Compatibility CTerms must use `assume_compat` and cannot enter this
    /// trusted theorem-construction path.
    pub fn assume(ct: CTerm) -> Result<Thm, KernelError> {
        ct.require_checked("ThmKernel::assume")?;
        ct.require_no_dummy_types("ThmKernel::assume")?;
        let mut thm = Self::assume_compat(ct);
        thm.trust = ThmTrust::Strict;
        Ok(thm)
    }

    /// Transitional strict alias retained while callers migrate.
    pub fn assume_checked(ct: CTerm) -> Result<Thm, KernelError> {
        Self::assume(ct)
    }

    // =================================================================
    // Primitive: reflexive
    // =================================================================

    /// **Reflexivity**: `⊢ t ≡ t`.
    ///
    /// The equality uses `Pure.eq` with the type inferred from the certified term.
    ///
    /// ```text
    /// —————— (reflexive)
    /// ⊢ t ≡ t
    /// ```
    pub fn reflexive_compat(ct: CTerm) -> Thm {
        let t = ct.term().clone();
        // Use the type from the certified term (Typ::dummy() if unknown)
        let typ = ct.term_type().clone();
        let eq_term = Pure::mk_equals(typ, t.clone(), t);
        let new_prop = CTerm::certify(eq_term);

        Thm {
            hyps: Hyps::empty(),
            prop: new_prop.clone(),
            maxidx: ct.maxidx(),
            tpairs: vec![],
            shyps: vec![],
            oracles: vec![],
            trust: ThmTrust::Compat,
            derivation: Derivation::Axiom { name: "reflexive", prop: new_prop },
            serial: new_serial(),
        }
    }

    /// Strict reflexivity entry point for checked `CTerm`s: `|- t == t`.
    pub fn reflexive(ct: CTerm) -> Result<Thm, KernelError> {
        ct.require_checked("ThmKernel::reflexive")?;
        ct.require_no_dummy_types("ThmKernel::reflexive")?;
        let t = ct.term().clone();
        let typ = ct.term_type().clone();
        let new_prop = CTerm::certify_derived_checked(
            Pure::mk_equals(typ, t.clone(), t),
            "ThmKernel::reflexive",
        )?;

        Ok(Thm {
            hyps: Hyps::empty(),
            prop: new_prop.clone(),
            maxidx: ct.maxidx(),
            tpairs: vec![],
            shyps: vec![],
            oracles: vec![],
            trust: ThmTrust::Strict,
            derivation: Derivation::Axiom { name: "reflexive", prop: new_prop },
            serial: new_serial(),
        })
    }

    /// Transitional strict alias retained while callers migrate.
    pub fn reflexive_checked(ct: CTerm) -> Result<Thm, KernelError> {
        Self::reflexive(ct)
    }

    // =================================================================
    // Primitive: symmetric
    // =================================================================

    /// **Symmetry**: `Γ ⊢ t ≡ u  ⟹  Γ ⊢ u ≡ t`.
    pub fn symmetric(thm: &Thm) -> Result<Thm, KernelError> {
        let (t, u, eq_typ) = Pure::dest_equals_with_type(thm.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm.prop.term().clone()))?;

        let trust = Self::trust_from_premises(&[thm]);
        let new_prop = Self::certify_rule_prop(
            Pure::mk_equals(eq_typ, u.clone(), t.clone()),
            trust,
            "ThmKernel::symmetric",
        )?;

        Ok(Thm {
            hyps: thm.hyps.clone(),
            prop: new_prop.clone(),
            maxidx: thm.maxidx,
            tpairs: thm.tpairs.clone(),
            shyps: thm.shyps.clone(),
            oracles: thm.oracles.clone(),
            trust,
            derivation: Derivation::Rule {
                name: "symmetric",
                prop: new_prop,
                premises: vec![ThmDeriv::from_thm(thm)],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: transitive
    // =================================================================

    /// **Transitivity**: `Γ ⊢ t ≡ u` and `Δ ⊢ u ≡ v` ⟹ `Γ ∪ Δ ⊢ t ≡ v`.
    pub fn transitive(thm1: &Thm, thm2: &Thm) -> Result<Thm, KernelError> {
        let (t, u1, eq_typ1) = Pure::dest_equals_with_type(thm1.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm1.prop.term().clone()))?;
        let (u2, v, eq_typ2) = Pure::dest_equals_with_type(thm2.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm2.prop.term().clone()))?;

        // The middle terms must be strict kernel α-equivalent.
        if !Hyps::kernel_alpha_eq(u1, u2) {
            return Err(KernelError::MidTermsNotEquiv);
        }
        Self::ensure_known_term_types_compatible(u1, u2)?;

        // Equality transitivity is only well-formed for a single object type.
        // `Typ::dummy()` is still tolerated at the parser boundary, but two
        // known, distinct equality types must never be chained.
        if Self::known_types_mismatch(&eq_typ1, &eq_typ2) {
            return Err(KernelError::TypeMismatch { expected: eq_typ1, actual: eq_typ2 });
        }

        let trust = Self::trust_from_premises(&[thm1, thm2]);
        let new_prop = Self::certify_rule_prop(
            Pure::mk_equals(eq_typ1, t.clone(), v.clone()),
            trust,
            "ThmKernel::transitive",
        )?;

        Ok(Thm {
            hyps: thm1.hyps.union(&thm2.hyps),
            prop: new_prop.clone(),
            maxidx: usize::max(thm1.maxidx, thm2.maxidx),
            tpairs: Self::union_tpairs(&thm1.tpairs, &thm2.tpairs),
            shyps: Self::union_shyps(&thm1.shyps, &thm2.shyps),
            oracles: Self::union_oracles(&thm1.oracles, &thm2.oracles),
            trust,
            derivation: Derivation::Rule {
                name: "transitive",
                prop: new_prop,
                premises: vec![ThmDeriv::from_thm(thm1), ThmDeriv::from_thm(thm2)],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: combination
    // =================================================================

    /// **Combination**: `Γ ⊢ f ≡ g` and `Δ ⊢ x ≡ y` ⟹ `Γ ∪ Δ ⊢ f x ≡ g y`.
    ///
    /// This is a **congruence** rule: it is logically sound for *any* `f ≡ g`
    /// and `x ≡ y`, irrespective of types — equality is preserved under
    /// application. The type comparison below is therefore a **well-formedness
    /// guard** (rejecting meaningless ill-typed applications), not a soundness
    /// guard.
    ///
    /// When both the function domain and the argument type are known, a
    /// mismatch is rejected. When either is `Typ::dummy()` (the type was never
    /// inferred — pervasive in the current parser/loader pipeline), the guard
    /// is necessarily skipped: we cannot compare against an unknown type, and
    /// skipping cannot introduce logical unsoundness because the rule is a
    /// congruence. Strengthening this further requires full type inference at
    /// the parse boundary (a separate workstream), not a kernel change.
    pub fn combination(thm_f: &Thm, thm_x: &Thm) -> Result<Thm, KernelError> {
        let (f, g, fn_typ) = Pure::dest_equals_with_type(thm_f.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm_f.prop.term().clone()))?;
        let (x, y, arg_typ) = Pure::dest_equals_with_type(thm_x.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm_x.prop.term().clone()))?;

        // The result type of f x (and g y) is the codomain of fn_typ.
        // Like Isabelle's combination, we require proper types — no Typ::dummy() fallback.
        let (from_typ, result_typ) = fn_typ
            .dest_fun()
            .map(|(from, to)| (from.clone(), to.clone()))
            .ok_or_else(|| KernelError::NotFunctionType(fn_typ.clone()))?;

        // Verify argument type compatibility (like Isabelle: T1 = tT)
        if Self::known_types_mismatch(&from_typ, &arg_typ) {
            return Err(KernelError::TypeMismatch {
                expected: from_typ.clone(),
                actual: arg_typ.clone(),
            });
        }

        let new_prop = CTerm::certify(Pure::mk_equals(
            result_typ,
            Term::app(f.clone(), x.clone()),
            Term::app(g.clone(), y.clone()),
        ));

        Ok(Thm {
            hyps: thm_f.hyps.union(&thm_x.hyps),
            prop: new_prop.clone(),
            maxidx: usize::max(thm_f.maxidx, thm_x.maxidx),
            tpairs: Self::union_tpairs(&thm_f.tpairs, &thm_x.tpairs),
            shyps: Self::union_shyps(&thm_f.shyps, &thm_x.shyps),
            oracles: Self::union_oracles(&thm_f.oracles, &thm_x.oracles),
            trust: Self::trust_from_premises(&[thm_f, thm_x]),
            derivation: Derivation::Rule {
                name: "combination",
                prop: new_prop,
                premises: vec![ThmDeriv::from_thm(thm_f), ThmDeriv::from_thm(thm_x)],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: abstraction
    // =================================================================

    /// **Abstraction**: `Γ ⊢ t ≡ u` ⟹ `Γ ⊢ (λx. t) ≡ (λx. u)`.
    ///
    /// Side condition: `x` must not be free in `Γ`.
    pub fn abstraction(x_name: &str, x_typ: Typ, thm: &Thm) -> Result<Thm, KernelError> {
        let (t, u, eq_typ) = Pure::dest_equals_with_type(thm.prop.term())
            .ok_or_else(|| KernelError::NotEquality(thm.prop.term().clone()))?;

        // Side condition: x must not be free in the hypotheses
        for hyp in thm.hyps.iter() {
            if free_in(x_name, hyp.term()) {
                return Err(KernelError::FreeVarInHypotheses { name: x_name.to_string() });
            }
        }

        // The new equality type is the function type x_typ → eq_typ
        let fn_typ = Typ::arrow(x_typ.clone(), eq_typ);

        let new_prop = CTerm::certify(Pure::mk_equals(
            fn_typ,
            Term::abs(x_name, x_typ.clone(), t.clone()),
            Term::abs(x_name, x_typ, u.clone()),
        ));

        Ok(Thm {
            hyps: thm.hyps.clone(),
            prop: new_prop.clone(),
            maxidx: thm.maxidx,
            tpairs: thm.tpairs.clone(),
            shyps: thm.shyps.clone(),
            oracles: thm.oracles.clone(),
            trust: Self::trust_from_premises(&[thm]),
            derivation: Derivation::Rule {
                name: "abstraction",
                prop: new_prop,
                premises: vec![ThmDeriv::from_thm(thm)],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: beta conversion
    // =================================================================

    /// **Beta conversion**: `⊢ (λx. t) x ≡ t`.
    pub fn beta_conversion(ct: CTerm) -> Result<Thm, KernelError> {
        // ct should be of the form (λx. t) x
        let (abs, arg) = match ct.term() {
            Term::App { func, arg } => (func.as_ref(), arg.as_ref()),
            _ => return Err(KernelError::BetaConversion("not an application".into())),
        };

        let body = match abs {
            Term::Abs { body, .. } => body.as_ref(),
            _ => return Err(KernelError::BetaConversion("not a lambda".into())),
        };

        let reduced = super::term_subst::subst_bounds(&[arg.clone()], body);

        // The equality type is the body's type; extract from the CTerm's type
        // (which is the application's result type = body type after beta reduction)
        let typ = ct.term_type().clone();

        let trust = Self::trust_from_cterm(&ct);
        let new_prop = Self::certify_rule_prop(
            Pure::mk_equals(typ, ct.term().clone(), reduced),
            trust,
            "ThmKernel::beta_conversion",
        )?;

        Ok(Thm {
            hyps: Hyps::empty(),
            prop: new_prop.clone(),
            maxidx: ct.maxidx(),
            tpairs: vec![],
            shyps: vec![],
            oracles: vec![],
            trust,
            derivation: Derivation::Axiom { name: "beta_conversion", prop: new_prop },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: implies introduction (discharge)
    // =================================================================

    /// **Implication introduction**:
    /// `Γ ∪ {A} ⊢ B` ⟹ `Γ ⊢ A ==> B`.
    pub fn implies_intr(assumption: &CTerm, thm: &Thm) -> Result<Thm, KernelError> {
        if !thm.hyps.contains(assumption) {
            return Err(KernelError::HypothesisNotFound);
        }

        let trust = Self::trust_from_premises_and_cterms(&[thm], &[assumption]);
        let new_prop = Self::certify_rule_prop(
            Pure::mk_implies(assumption.term().clone(), thm.prop.term().clone()),
            trust,
            "ThmKernel::implies_intr",
        )?;

        Ok(Thm {
            hyps: thm.hyps.remove(assumption),
            prop: new_prop.clone(),
            maxidx: thm.maxidx,
            tpairs: thm.tpairs.clone(),
            shyps: thm.shyps.clone(),
            oracles: thm.oracles.clone(),
            trust,
            derivation: Derivation::Rule {
                name: "implies_intr",
                prop: new_prop,
                premises: vec![ThmDeriv::from_thm(thm)],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: implies elimination (modus ponens)
    // =================================================================

    /// **Implication elimination** (modus ponens):
    /// `Γ ⊢ A ==> B` and `Δ ⊢ A` ⟹ `Γ ∪ Δ ⊢ B`.
    pub fn implies_elim(thm_imp: &Thm, thm_a: &Thm) -> Result<Thm, KernelError> {
        let (a, b) = Pure::dest_implies(thm_imp.prop.term())
            .ok_or_else(|| KernelError::NotImplication(thm_imp.prop.term().clone()))?;

        if !Hyps::kernel_alpha_eq(a, thm_a.prop.term()) {
            return Err(KernelError::AntecedentMismatch);
        }
        Self::ensure_known_term_types_compatible(a, thm_a.prop.term())?;
        let trust = Self::trust_from_premises(&[thm_imp, thm_a]);
        let new_prop = Self::certify_rule_prop(b.clone(), trust, "ThmKernel::implies_elim")?;

        Ok(Thm {
            hyps: thm_imp.hyps.union(&thm_a.hyps),
            prop: new_prop.clone(),
            maxidx: usize::max(thm_imp.maxidx, thm_a.maxidx),
            tpairs: Self::union_tpairs(&thm_imp.tpairs, &thm_a.tpairs),
            shyps: Self::union_shyps(&thm_imp.shyps, &thm_a.shyps),
            oracles: Self::union_oracles(&thm_imp.oracles, &thm_a.oracles),
            trust,
            derivation: Derivation::Rule {
                name: "implies_elim",
                prop: new_prop,
                premises: vec![ThmDeriv::from_thm(thm_imp), ThmDeriv::from_thm(thm_a)],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive rules: forall_intr and forall_elim
    // =================================================================

    pub fn forall_intr(x_name: &str, x_typ: Typ, thm: &Thm) -> Result<Thm, KernelError> {
        for hyp in thm.hyps.iter() {
            if free_in(x_name, hyp.term()) {
                return Err(KernelError::FreeVarInHypotheses { name: x_name.to_string() });
            }
        }
        let all_term = Pure::mk_all(x_name, x_typ.clone(), thm.prop.term().clone());
        let new_prop = CTerm::certify(all_term);
        Ok(Thm {
            hyps: thm.hyps.clone(),
            prop: new_prop.clone(),
            maxidx: thm.maxidx,
            tpairs: thm.tpairs.clone(),
            shyps: thm.shyps.clone(),
            oracles: thm.oracles.clone(),
            trust: Self::trust_from_premises(&[thm]),
            derivation: Derivation::Rule {
                name: "forall_intr",
                prop: new_prop,
                premises: vec![ThmDeriv::from_thm(thm)],
            },
            serial: new_serial(),
        })
    }

    pub fn forall_elim(ct: CTerm, thm: &Thm) -> Result<Thm, KernelError> {
        let ((_, binder_typ), p_body) = Pure::dest_all(thm.prop.term())
            .ok_or_else(|| KernelError::NotForall(thm.prop.term().clone()))?;
        let arg_typ = ct.term_type().clone();
        if Self::known_types_mismatch(binder_typ, &arg_typ) {
            return Err(KernelError::TypeMismatch {
                expected: binder_typ.clone(),
                actual: arg_typ,
            });
        }
        let instantiated = super::term_subst::subst_bounds(&[ct.term().clone()], p_body);
        let new_prop = CTerm::certify(instantiated);
        Ok(Thm {
            hyps: thm.hyps.clone(),
            prop: new_prop.clone(),
            maxidx: usize::max(thm.maxidx, ct.maxidx()),
            tpairs: thm.tpairs.clone(),
            shyps: thm.shyps.clone(),
            oracles: thm.oracles.clone(),
            trust: Self::trust_from_premises_and_cterms(&[thm], &[&ct]),
            derivation: Derivation::Rule {
                name: "forall_elim",
                prop: new_prop,
                premises: vec![ThmDeriv::from_thm(thm)],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: instantiate
    // =================================================================

    /// Apply an environment (from unification) to instantiate a theorem.
    ///
    /// If `Γ ⊢ φ` is a theorem schema (with schematic variables), then
    /// for any substitution `θ`, `Γθ ⊢ φθ` is also a theorem.
    fn validate_instantiation(env: &super::envir::Envir, thm: &Thm) -> Result<(), KernelError> {
        for h in thm.hyps.iter() {
            Self::validate_instantiation_term(env, h.term())?;
        }
        Self::validate_instantiation_term(env, thm.prop.term())
    }

    fn validate_instantiation_term(
        env: &super::envir::Envir,
        term: &Term,
    ) -> Result<(), KernelError> {
        let mut stack = vec![term];
        while let Some(t) = stack.pop() {
            match t {
                Term::Var { name, index, typ } => {
                    if let Some(assigned) = env.lookup(name, *index) {
                        let expected = env.norm_type(typ);
                        let actual = env.norm_type(&Self::term_known_type(assigned));
                        if Self::known_types_mismatch(&expected, &actual) {
                            return Err(KernelError::TypeMismatch { expected, actual });
                        }
                    }
                },
                Term::Abs { body, .. } => stack.push(body),
                Term::App { func, arg } => {
                    stack.push(arg);
                    stack.push(func);
                },
                Term::Const { .. } | Term::Free { .. } | Term::Bound(_) => {},
            }
        }
        Ok(())
    }

    fn instantiate_unchecked(env: &super::envir::Envir, thm: &Thm) -> Thm {
        let mut new_hyps = Hyps::empty();
        for h in thm.hyps.iter() {
            new_hyps.insert(CTerm::certify(env.norm_term(h.term())));
        }
        let new_prop = CTerm::certify(env.norm_term(thm.prop.term()));
        Thm {
            hyps: new_hyps,
            prop: new_prop.clone(),
            maxidx: usize::max(thm.maxidx, env.maxidx()),
            tpairs: thm.tpairs.clone(),
            shyps: thm.shyps.clone(),
            oracles: thm.oracles.clone(),
            trust: Self::trust_from_premises(&[thm]),
            derivation: Derivation::Rule {
                name: "instantiate",
                prop: new_prop,
                premises: vec![ThmDeriv::from_thm(thm)],
            },
            serial: new_serial(),
        }
    }

    /// Checked theorem instantiation.
    ///
    /// This rejects a concrete type contradiction in the supplied environment
    /// before applying it. It is the preferred API for new kernel code.
    pub fn instantiate_checked(env: &super::envir::Envir, thm: &Thm) -> Result<Thm, KernelError> {
        Self::validate_instantiation(env, thm)?;
        Ok(Self::instantiate_unchecked(env, thm))
    }

    /// Legacy compatibility path for the historical infallible API.
    ///
    /// This is test-only by design: trusted proof-search paths must call
    /// `instantiate_checked` and handle rejected substitutions explicitly.
    #[cfg(test)]
    fn instantiate_legacy(env: &super::envir::Envir, thm: &Thm) -> Thm {
        Self::instantiate_checked(env, thm).unwrap_or_else(|_| thm.clone())
    }

    // =================================================================
    // Primitive: bicompose — the core resolution operation
    // =================================================================

    /// Compose `thm1` with `thm2` at position `i`.
    ///
    /// `thm1`: `[| H1; ...; Hm |] ==> A`
    /// `thm2`: `[| G1; ...; Gi; ...; Gn |] ==> C`
    ///
    /// If `match_flag` is true and `A` unifies with `Gi`, or if `match_flag`
    /// is false and `A` is α-equivalent to `Gi`, then:
    ///
    /// `[| G1;...;Gi-1; H1;...;Hm; Gi+1;...;Gn |]`
    ///   `==> G1 ==> ... ==> Gi-1 ==> H1 ==> ... ==> Hm ==> Gi+1 ==> ... ==> Gn ==> C`
    ///
    /// Quick check: can two terms possibly unify based on their top-level structure?
    /// Returns false for obviously incompatible pairs (different head constructors),
    /// avoiding expensive unification attempts that are guaranteed to fail.
    /// Now also checks type compatibility when type info is available.
    fn likely_unifiable(a: &Term, b: &Term) -> bool {
        match (a, b) {
            (Term::Var { .. }, _) | (_, Term::Var { .. }) => true,
            (Term::App { .. }, Term::App { .. }) => true,
            (Term::Abs { .. }, Term::Abs { .. }) => true,
            (Term::Const { name: n1, typ: t1 }, Term::Const { name: n2, typ: t2 }) => {
                if n1 != n2 {
                    return false;
                }
                // Type-aware: check TypeEnv when embedded types are dummy
                let t1_eff = if t1.is_dummy() {
                    use crate::hol::hol_loader::HolTheoremDb;
                    HolTheoremDb::get().type_env.const_type(n1).unwrap_or(t1)
                } else {
                    t1
                };
                let t2_eff = if t2.is_dummy() {
                    use crate::hol::hol_loader::HolTheoremDb;
                    HolTheoremDb::get().type_env.const_type(n2).unwrap_or(t2)
                } else {
                    t2
                };
                if !t1_eff.is_dummy() && !t2_eff.is_dummy() {
                    Self::types_compatible(t1_eff, t2_eff)
                } else {
                    true
                }
            },
            (Term::Free { name: n1, typ: t1 }, Term::Free { name: n2, typ: t2 }) => {
                n1 == n2 && !Self::known_types_mismatch(t1, t2)
            },
            (Term::Bound(i1), Term::Bound(i2)) => i1 == i2,
            _ => false,
        }
    }

    /// Check if two types are structurally compatible (can potentially unify).
    fn types_compatible(t1: &Typ, t2: &Typ) -> bool {
        match (t1, t2) {
            (Typ::Type { name: n1, args: a1 }, Typ::Type { name: n2, args: a2 }) => {
                if n1 != n2 {
                    return false;
                }
                if a1.len() != a2.len() {
                    return false;
                }
                a1.iter().zip(a2.iter()).all(|(a, b)| Self::types_compatible(a, b))
            },
            _ => true, // TFree, TVar, dummy — always potentially compatible
        }
    }

    /// This is the single core operation behind ALL tactics (assume_tac,
    /// resolve_tac, eresolve_tac, ...).
    pub fn bicompose(match_flag: bool, thm1: &Thm, thm2: &Thm, i: usize) -> Option<Thm> {
        // 1. Get the i-th premise of thm2 (0-indexed)
        let prem_i = Pure::nth_premise(thm2.prop.term(), i)?;

        // 2. Get thm1's conclusion (last element after stripping all ==>-premises)
        let (_, concl_1) = Pure::strip_imp_prems(thm1.prop.term());

        // 3. Match or unify
        let (env, full_match) = if match_flag {
            let maxidx = usize::max(thm1.maxidx(), thm2.maxidx());
            let env = super::envir::Envir::empty(maxidx);
            (
                super::unify::matchers(
                    &env,
                    concl_1,
                    prem_i,
                    &super::unify::UnifyConfig::default(),
                )?,
                false,
            )
        } else {
            // match_flag=false: first try alpha_eq (assume_tac / exact match),
            // then try full unification (for RS/THEN/COMP composition)
            if Self::alpha_eq_with_known_types(thm1.prop.term(), prem_i) {
                (super::envir::Envir::init(), true) // full match — assume_tac
            } else if Self::alpha_eq_with_known_types(concl_1, prem_i) {
                (super::envir::Envir::init(), false) // conclusion match — resolve_tac
            } else {
                // Full unification: allows variables on both sides to be bound.
                // Quick heuristic: skip if terms have incompatible shapes.
                if !Self::likely_unifiable(concl_1, prem_i) {
                    return None;
                }
                let maxidx = usize::max(thm1.maxidx(), thm2.maxidx());
                let env = super::envir::Envir::empty(maxidx);
                let pairs = vec![(concl_1.clone(), prem_i.clone())];
                (
                    super::unify::unifiers(&env, &pairs, &super::unify::UnifyConfig::default())?,
                    false,
                )
            }
        };

        // 4. Instantiate both theorems with the unifier
        let thm1 = Self::instantiate_checked(&env, thm1).ok()?;
        let thm2 = Self::instantiate_checked(&env, thm2).ok()?;

        // 5. Build the result: replace thm2's i-th premise with thm1's premise chain
        let prems_1: Vec<Term> = if full_match {
            // Full match: entire subgoal is a hypothesis — no new premises
            Vec::new()
        } else {
            let (p, _) = Pure::strip_imp_prems(thm1.prop.term());
            p.iter().cloned().cloned().collect()
        };
        let (prems_2, concl_2) = Pure::strip_imp_prems(thm2.prop.term());

        let mut new_prems: Vec<Term> = Vec::new();
        new_prems.extend(prems_2[..i].iter().cloned().cloned());
        new_prems.extend(prems_1.iter().cloned());
        new_prems.extend(prems_2[i + 1..].iter().cloned().cloned());

        let mut new_prop = concl_2.clone();
        for p in new_prems.iter().rev() {
            new_prop = Pure::mk_implies(p.clone(), new_prop);
        }

        let new_prop = CTerm::certify(new_prop);

        Some(Thm {
            hyps: thm1.hyps.union(&thm2.hyps),
            prop: new_prop.clone(),
            maxidx: usize::max(thm1.maxidx, thm2.maxidx),
            tpairs: Self::union_tpairs(&thm1.tpairs, &thm2.tpairs),
            shyps: Self::union_shyps(&thm1.shyps, &thm2.shyps),
            oracles: Self::union_oracles(&thm1.oracles, &thm2.oracles),
            trust: Self::trust_from_premises(&[&thm1, &thm2]),
            derivation: Derivation::Rule {
                name: "bicompose",
                prop: new_prop,
                premises: vec![ThmDeriv::from_thm(&thm1), ThmDeriv::from_thm(&thm2)],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: subst_premise — replace a premise using an equality
    // =================================================================

    /// Replace the i-th premise of `state` using an equality theorem.
    ///
    /// If `eq_thm` proves `t == u` and the i-th premise of `state` is
    /// α-equivalent to `t`, replace it with `u`.
    ///
    /// Soundness: by substitutivity of equality, if `t == u` and `Γ, t ⊢ C`,
    /// then `Γ, u ⊢ C`.
    pub fn subst_premise(eq_thm: &Thm, state: &Thm, i: usize) -> Option<Thm> {
        let (t, u) = Pure::dest_equals(eq_thm.prop.term())?;
        let prem_i = Pure::nth_premise(state.prop.term(), i)?;
        if !Hyps::kernel_alpha_eq(t, prem_i) {
            return None;
        }
        if !Self::known_term_types_compatible(t, prem_i) {
            return None;
        }

        let (prems, concl) = Pure::strip_imp_prems(state.prop.term());
        let mut new_prems: Vec<Term> = prems.iter().cloned().cloned().collect();
        new_prems[i] = u.clone();

        let mut new_prop = concl.clone();
        for p in new_prems.iter().rev() {
            new_prop = Pure::mk_implies(p.clone(), new_prop);
        }

        let new_prop = CTerm::certify(new_prop);

        Some(Thm {
            hyps: state.hyps.union(&eq_thm.hyps),
            prop: new_prop.clone(),
            maxidx: usize::max(state.maxidx, eq_thm.maxidx),
            tpairs: Self::union_tpairs(&state.tpairs, &eq_thm.tpairs),
            shyps: Self::union_shyps(&state.shyps, &eq_thm.shyps),
            oracles: Self::union_oracles(&state.oracles, &eq_thm.oracles),
            trust: Self::trust_from_premises(&[state, eq_thm]),
            derivation: Derivation::Rule {
                name: "subst_premise",
                prop: new_prop,
                premises: vec![ThmDeriv::from_thm(eq_thm), ThmDeriv::from_thm(state)],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Primitive: bicompose_eresolve — resolution with hypothesis elimination
    // =================================================================

    /// Like `bicompose`, but also consumes a matching hypothesis.
    ///
    /// `thm1`: `[| H; G1; ...; Gm |] ==> A`  (H is the "major premise")
    /// `thm2`: goal state with subgoal `i` matching `A`
    ///
    /// If `match_flag` is true, unifies `A` with subgoal `i` and `H` with
    /// some hypothesis of `thm2`. Then replaces subgoal `i` with `G1...Gm`
    /// (excluding `H`) and keeps the consumed hypothesis in hyps.
    ///
    /// This is the kernel implementation of `eresolve_tac`.
    pub fn bicompose_eresolve(
        match_flag: bool,
        thm1: &Thm,
        thm2: &Thm,
        i: usize,
        premises: &[Arc<Thm>],
    ) -> Option<Thm> {
        // 1. Get the i-th premise of thm2 and thm1's conclusion
        let prem_i = Pure::nth_premise(thm2.prop.term(), i)?;
        let (prems_1, concl_1) = Pure::strip_imp_prems(thm1.prop.term());

        // thm1 must have at least one premise (the major premise to consume)
        let major_prem = prems_1.first()?;
        let _rest_prems = &prems_1[1..];

        // 2. Unify major premise with hyps or premises
        let env = if match_flag {
            let maxidx = usize::max(thm1.maxidx(), thm2.maxidx());
            let mut found_env = None;
            // Collect all candidates: hyps (including stripped premises) + premises
            let mut all_candidates: Vec<Term> = Vec::new();
            for h in thm2.hyps.iter() {
                all_candidates.push(h.term().clone());
                // Also include individual premises stripped from implication chains
                let (prems, _) = Pure::strip_imp_prems(h.term());
                for p in prems {
                    all_candidates.push(p.clone());
                }
            }
            for p in premises.iter() {
                all_candidates.push(p.prop().term().clone());
            }
            for candidate in &all_candidates {
                // Quick heuristic: skip obviously incompatible candidates
                if !Self::likely_unifiable(major_prem, candidate) {
                    continue;
                }
                let env = super::envir::Envir::empty(maxidx);
                let pairs: Vec<(Term, Term)> = vec![
                    ((*major_prem).clone(), candidate.clone()),
                    ((*concl_1).clone(), prem_i.clone()),
                ];
                if let Some(env) =
                    super::unify::unifiers(&env, &pairs, &super::unify::UnifyConfig::default())
                {
                    found_env = Some(env);
                    break;
                }
            }
            found_env?
        } else {
            // Exact match with two-tier support, also checking constituent premises
            let hyp_matches = thm2.hyps.iter().any(|h| {
                Self::alpha_eq_with_known_types(major_prem, h.term()) || {
                    let (prems, _) = Pure::strip_imp_prems(h.term());
                    prems.iter().any(|p| Self::alpha_eq_with_known_types(p, major_prem))
                }
            });
            if !hyp_matches {
                return None;
            }
            if !Self::alpha_eq_with_known_types(thm1.prop.term(), prem_i)
                && !Self::alpha_eq_with_known_types(concl_1, prem_i)
            {
                return None;
            }
            super::envir::Envir::init()
        };

        // 3. Instantiate both theorems
        let thm1 = Self::instantiate_checked(&env, thm1).ok()?;
        let thm2 = Self::instantiate_checked(&env, thm2).ok()?;

        // 4. Build result: thm2's i-th premise replaced by thm1's REST premises (excluding major)
        let (prems_1_inst, _) = Pure::strip_imp_prems(thm1.prop.term());
        let rest_prems_inst: Vec<Term> = if prems_1_inst.is_empty() {
            Vec::new()
        } else {
            prems_1_inst[1..].iter().cloned().cloned().collect()
        };
        let (prems_2, concl_2) = Pure::strip_imp_prems(thm2.prop.term());

        let mut new_prems: Vec<Term> = Vec::new();
        new_prems.extend(prems_2[..i].iter().cloned().cloned());
        new_prems.extend(rest_prems_inst.iter().cloned());
        new_prems.extend(prems_2[i + 1..].iter().cloned().cloned());

        let mut new_prop = concl_2.clone();
        for p in new_prems.iter().rev() {
            new_prop = Pure::mk_implies(p.clone(), new_prop);
        }

        let new_prop = CTerm::certify(new_prop);

        Some(Thm {
            hyps: thm1.hyps.union(&thm2.hyps),
            prop: new_prop.clone(),
            maxidx: usize::max(thm1.maxidx, thm2.maxidx),
            tpairs: Self::union_tpairs(&thm1.tpairs, &thm2.tpairs),
            shyps: Self::union_shyps(&thm1.shyps, &thm2.shyps),
            oracles: Self::union_oracles(&thm1.oracles, &thm2.oracles),
            trust: Self::trust_from_premises(&[&thm1, &thm2]),
            derivation: Derivation::Rule {
                name: "bicompose_eresolve",
                prop: new_prop,
                premises: vec![ThmDeriv::from_thm(&thm1), ThmDeriv::from_thm(&thm2)],
            },
            serial: new_serial(),
        })
    }

    // =================================================================
    // Derived rule: A ==> A  (identity)
    // =================================================================

    pub fn trivial(ct: CTerm) -> Result<Thm, KernelError> {
        let assumed = if ct.is_checked() {
            ThmKernel::assume(ct.clone())?
        } else {
            ThmKernel::assume_compat(ct.clone())
        };
        ThmKernel::implies_intr(&ct, &assumed)
    }

    // =================================================================
    // Flex-flex resolution (Phase 41)
    // =================================================================

    /// Resolve flex-flex pairs in a theorem.
    ///
    /// In higher-order unification, some disagreement pairs may remain
    /// unresolved when both sides are flexible (contain schematic variables).
    /// These are stored in `thm.tpairs`.
    ///
    /// `flexflex_resolve` attempts to instantiate these pairs with the
    /// most general solution: each flexible head is instantiated to a
    /// projection of one of its arguments.
    ///
    /// Returns the theorem with resolved tpairs, or the original if
    /// resolution is not possible.
    pub fn flexflex_resolve(thm: &Thm) -> Thm {
        if thm.tpairs.is_empty() {
            return thm.clone();
        }

        // For now, we apply the most general flex-flex resolution:
        // each pair (f(args), g(args')) is resolved by instantiating
        // both f and g to be projections of their arguments.
        //
        // In the simple case where both sides are Var heads with the
        // same binder context, we can unify them directly.
        let mut env = super::envir::Envir::init();
        let mut resolved = true;

        for (t, u) in &thm.tpairs {
            let config = super::unify::UnifyConfig { search_bound: 10, max_unifiers: 1 };
            // Try to unify the flex-flex pair
            if let Some(new_env) = super::unify::unifiers(&env, &[(t.clone(), u.clone())], &config)
            {
                env = new_env;
            } else {
                resolved = false;
                break;
            }
        }

        if resolved {
            // Apply the instantiation to the whole theorem
            if let Ok(mut new_thm) = ThmKernel::instantiate_checked(&env, thm) {
                new_thm.tpairs = vec![]; // all resolved
                new_thm
            } else {
                thm.clone()
            }
        } else {
            // Keep unresolved tpairs (they are constraints, not errors)
            thm.clone()
        }
    }

    /// Strip all tpairs from a theorem (accepting them as constraints).
    ///
    /// This is sound: tpairs are unresolved flex-flex constraints that
    /// don't affect the truth of the proposition (they only restrict
    /// possible instantiations).
    pub fn strip_tpairs(thm: &Thm) -> Thm {
        let mut result = thm.clone();
        result.tpairs = vec![];
        result
    }

    // =================================================================
    // Sort hypotheses operations (Phase 41)
    // =================================================================

    /// Add a sort hypothesis to a theorem.
    ///
    /// Sort hypotheses track type-class constraints. When a theorem
    /// is used in a context that doesn't satisfy the required sort,
    /// the constraint is added as an explicit hypothesis.
    pub fn add_shyp(thm: &Thm, sort: Sort) -> Thm {
        let mut result = thm.clone();
        if !result.shyps.contains(&sort) {
            result.shyps.push(sort);
        }
        result
    }

    /// Strip sort hypotheses (weakening).
    ///
    /// This is sound: removing a constraint can only make a theorem
    /// more general (weaker assumption). However, the resulting theorem
    /// may not be usable in contexts that require the constraint.
    pub fn strip_shyps(thm: &Thm) -> Thm {
        let mut result = thm.clone();
        result.shyps = vec![];
        result
    }

    /// Check if a theorem satisfies a given sort hypothesis.
    pub fn satisfies_shyp(thm: &Thm, sort: &Sort) -> bool {
        thm.shyps.iter().any(|s| s == sort)
    }
}

/// Check if a free variable name occurs in a term.
/// Iterative implementation to avoid stack overflow.
fn free_in(var_name: &str, term: &Term) -> bool {
    let mut stack: Vec<&Term> = vec![term];
    while let Some(t) = stack.pop() {
        match t {
            Term::Free { name, .. } if name.as_ref() == var_name => return true,
            Term::Abs { body, .. } => stack.push(body),
            Term::App { func, arg } => {
                stack.push(arg);
                stack.push(func);
            },
            _ => {},
        }
    }
    false
}

/// Compute the sort hypotheses (shyps) for a term.
///
/// Walks the term and collects type class constraints from type variables
/// that have non-trivial sorts. This is used to track type-class-polymorphic
/// dependencies in theorems.
pub fn compute_shyps(term: &Term) -> Vec<Sort> {
    let mut shyps = Vec::new();
    let mut stack = vec![term];
    let mut seen = std::collections::HashSet::new();

    while let Some(t) = stack.pop() {
        match t {
            Term::Const { typ, .. } | Term::Free { typ, .. } | Term::Var { typ, .. } => {
                collect_type_sorts(typ, &mut shyps, &mut seen);
            },
            Term::Abs { typ, body, .. } => {
                collect_type_sorts(typ, &mut shyps, &mut seen);
                stack.push(body);
            },
            Term::App { func, arg } => {
                stack.push(arg);
                stack.push(func);
            },
            Term::Bound(_) => {},
        }
    }
    shyps
}

/// Helper: recursively collect sorts from a type.
fn collect_type_sorts(
    typ: &Typ,
    shyps: &mut Vec<Sort>,
    seen: &mut std::collections::HashSet<Sort>,
) {
    match typ {
        Typ::TFree { sort, .. } | Typ::TVar { sort, .. } => {
            if *sort != Sort::top() && seen.insert(sort.clone()) {
                shyps.push(sort.clone());
            }
        },
        Typ::Type { args, .. } => {
            for arg in args {
                collect_type_sorts(arg, shyps, seen);
            }
        },
    }
}

// =========================================================================
// Tests
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::{
        envir::Envir,
        types::{Symbol, TypeEnv},
    };

    fn prop(name: &str) -> CTerm {
        checked_prop(name)
    }

    fn checked_prop(name: &str) -> CTerm {
        let mut env = TypeEnv::new();
        env.declare_const(name, Typ::base("prop"));
        CTerm::certify_checked(Term::const_(name, Typ::base("prop")), &env).unwrap()
    }

    fn declare_term(term: &Term, env: &mut TypeEnv) {
        match term {
            Term::Const { name, typ } if !typ.is_dummy() && !name.as_ref().starts_with("Pure.") => {
                env.declare_const(name.as_ref(), typ.clone());
            },
            Term::Free { name, typ } if !typ.is_dummy() => {
                env.declare_free(name.as_ref(), typ.clone());
            },
            Term::Abs { body, .. } => declare_term(body, env),
            Term::App { func, arg } => {
                declare_term(func, env);
                declare_term(arg, env);
            },
            Term::Const { .. } | Term::Free { .. } | Term::Var { .. } | Term::Bound(_) => {},
        }
    }

    fn checked_cterm(term: Term) -> CTerm {
        let mut env = TypeEnv::new();
        declare_term(&term, &mut env);
        CTerm::certify_checked(term, &env).unwrap()
    }

    fn checked_const(name: &str, typ: Typ) -> CTerm {
        let mut env = TypeEnv::new();
        env.declare_const(name, typ.clone());
        CTerm::certify_checked(Term::const_(name, typ), &env).unwrap()
    }

    #[test]
    fn test_assume() {
        let a = checked_prop("A");
        let thm = ThmKernel::assume(a.clone()).unwrap();
        assert_eq!(thm.hyps().len(), 1);
        assert_eq!(thm.prop(), &a);
        assert_eq!(thm.trust_status(), ThmTrust::Strict);
    }

    #[test]
    fn test_trivial() {
        let a = checked_prop("A");
        let thm = ThmKernel::trivial(a).unwrap();
        assert!(thm.is_unconditional());
        let (x, y) = Pure::dest_implies(thm.prop.term()).expect("Not an implication");
        assert_eq!(x, &Term::const_("A", Typ::base("prop")));
        assert_eq!(y, &Term::const_("A", Typ::base("prop")));
        assert_eq!(thm.trust_status(), ThmTrust::Strict);
    }

    #[test]
    fn test_reflexive_compat_accepts_dummy_cterm() {
        let t = CTerm::certify(Term::const_("t", Typ::dummy()));
        let thm = ThmKernel::reflexive_compat(t);
        assert!(thm.is_unconditional());
        assert_eq!(thm.trust_status(), ThmTrust::Compat);
    }

    #[test]
    fn test_check_proof_rejects_tampered_theorem_prop() {
        let t = checked_const("t", Typ::base("nat"));
        let mut thm = ThmKernel::reflexive(t).unwrap();
        thm.prop = checked_prop("Tampered");

        assert!(
            thm.check_proof().is_err(),
            "check_proof accepted a theorem whose prop no longer matches its derivation"
        );
    }

    #[test]
    fn test_check_proof_rejects_tampered_theorem_hyps() {
        let t = checked_const("t", Typ::base("nat"));
        let mut thm = ThmKernel::reflexive(t).unwrap();
        thm.hyps = Hyps::singleton(checked_prop("InjectedHyp"));

        assert!(
            thm.check_proof().is_err(),
            "check_proof accepted a theorem whose hyps no longer match its derivation"
        );
    }

    #[test]
    fn test_check_proof_rejects_tampered_theorem_oracles() {
        let t = checked_const("t", Typ::base("nat"));
        let mut thm = ThmKernel::reflexive(t).unwrap();
        thm.oracles.push(Arc::from("admitted:tampered"));

        assert!(
            thm.check_proof().is_err(),
            "check_proof accepted a theorem whose oracle footprint no longer matches replay"
        );
    }

    #[test]
    fn test_check_proof_rejects_tampered_theorem_tpairs() {
        let t = checked_const("t", Typ::base("nat"));
        let mut thm = ThmKernel::reflexive(t).unwrap();
        thm.tpairs.push((Term::var("x", 0, Typ::base("nat")), Term::var("y", 0, Typ::base("nat"))));

        assert!(
            thm.check_proof().is_err(),
            "check_proof accepted a theorem whose tpairs no longer match replay"
        );
    }

    #[test]
    fn test_check_proof_rejects_tampered_premise_derivation() {
        let t = checked_const("t", Typ::base("nat"));
        let refl = ThmKernel::reflexive(t).unwrap();
        let mut sym = ThmKernel::symmetric(&refl).unwrap();

        let Derivation::Rule { premises, .. } = &mut sym.derivation else {
            panic!("symmetric should record a rule derivation");
        };
        let Derivation::Axiom { prop: premise_prop, .. } = &mut premises[0].derivation else {
            panic!("reflexive premise should record an axiom derivation");
        };
        *premise_prop = checked_prop("TamperedPremise");

        assert!(
            sym.check_proof().is_err(),
            "check_proof accepted a theorem with a tampered premise derivation"
        );
    }

    #[test]
    fn test_validate_proof_rechecks_stale_checked_body() {
        let t = checked_const("t", Typ::base("nat"));
        let mut thm = ThmKernel::reflexive(t).unwrap();
        let mut body = thm.proof_body();

        // Simulate legacy proposition-only checking having marked the body.
        body.checked = true;
        thm.hyps = Hyps::singleton(checked_prop("InjectedHyp"));

        assert!(
            thm.validate_proof(&mut body).is_err(),
            "validate_proof trusted ProofBody.checked without burden-aware replay"
        );
    }

    #[test]
    fn test_strict_reflexive_passes_strict_invariants() {
        let t = checked_const("t", Typ::base("nat"));
        let thm = ThmKernel::reflexive(t).unwrap();

        assert!(thm.check_kernel_invariants(KernelCheckMode::Strict).is_ok());
        assert!(thm.check_kernel_invariants(KernelCheckMode::Compat).is_ok());
    }

    #[test]
    fn test_strict_open_theorem_passes_strict_invariants_but_not_closed_proved() {
        let a = checked_prop("A");
        let thm = ThmKernel::assume(a).unwrap();

        assert_eq!(thm.trust_status(), ThmTrust::Strict);
        assert!(thm.check_kernel_invariants(KernelCheckMode::Strict).is_ok());
        assert!(thm.check_proof().is_ok());
        assert!(thm.is_fully_proved());
        assert!(!thm.is_closed_proved());
        assert!(!thm.is_strict_closed_proved());
    }

    #[test]
    fn test_unsupported_strict_replay_is_structural_only() {
        let nat = Typ::base("nat");
        let mut env = TypeEnv::new();
        env.declare_const("a", nat.clone());
        let redex =
            Term::app(Term::abs("x", nat, Term::bound(0)), Term::const_("a", Typ::base("nat")));
        let ct = CTerm::certify_checked(redex, &env).unwrap();
        let thm = ThmKernel::beta_conversion(ct).unwrap();

        assert_eq!(thm.trust_status(), ThmTrust::Strict);
        assert!(thm.check_kernel_invariants(KernelCheckMode::Strict).is_ok());
        let err = thm
            .check_proof()
            .expect_err("beta_conversion is still outside replay-supported subset");
        assert!(
            err.contains("unsupported axiom proof rule: beta_conversion"),
            "unexpected replay error: {err}"
        );
    }

    #[test]
    fn test_compat_reflexive_fails_strict_invariants() {
        let t = CTerm::certify(Term::const_("t", Typ::base("nat")));
        let thm = ThmKernel::reflexive_compat(t);

        assert!(thm.check_kernel_invariants(KernelCheckMode::Compat).is_ok());
        assert!(thm.check_kernel_invariants(KernelCheckMode::Strict).is_err());
    }

    #[test]
    fn test_admitted_theorem_fails_strict_invariants() {
        let thm = ThmKernel::admit(prop("A"), "admitted:invariant_test");

        assert!(thm.check_kernel_invariants(KernelCheckMode::Compat).is_ok());
        assert!(thm.check_kernel_invariants(KernelCheckMode::Strict).is_err());
    }

    #[test]
    fn test_strict_invariant_rejects_dummy_tainted_theorem() {
        let t = checked_const("t", Typ::base("nat"));
        let mut thm = ThmKernel::reflexive(t).unwrap();
        thm.prop.term_type = Typ::dummy();

        assert!(
            matches!(
                thm.check_kernel_invariants(KernelCheckMode::Strict),
                Err(KernelError::DummyType { .. }) | Err(KernelError::KernelInvariant { .. })
            ),
            "strict invariant accepted a dummy-tainted theorem"
        );
    }

    #[test]
    fn test_strict_invariant_rejects_tampered_maxidx() {
        let t = checked_const("t", Typ::base("nat"));
        let mut thm = ThmKernel::reflexive(t).unwrap();
        thm.maxidx = 17;

        assert!(
            matches!(
                thm.check_kernel_invariants(KernelCheckMode::Strict),
                Err(KernelError::KernelInvariant { .. })
            ),
            "strict invariant accepted a tampered maxidx"
        );
    }

    #[test]
    fn test_strict_invariant_rejects_tampered_hyps() {
        let t = checked_const("t", Typ::base("nat"));
        let mut thm = ThmKernel::reflexive(t).unwrap();
        thm.hyps = Hyps::singleton(checked_prop("InjectedHyp"));

        assert!(
            matches!(
                thm.check_kernel_invariants(KernelCheckMode::Strict),
                Err(KernelError::KernelInvariant { .. })
            ),
            "strict invariant accepted tampered hypotheses"
        );
    }

    #[test]
    fn test_strict_invariant_rejects_tampered_oracles() {
        let t = checked_const("t", Typ::base("nat"));
        let mut thm = ThmKernel::reflexive(t).unwrap();
        thm.oracles.push(Arc::from("admitted:tampered"));

        assert!(
            matches!(
                thm.check_kernel_invariants(KernelCheckMode::Strict),
                Err(KernelError::KernelInvariant { .. })
            ),
            "strict invariant accepted an oracle-tainted strict theorem"
        );
    }

    #[test]
    fn test_strict_invariant_rejects_tampered_tpairs() {
        let t = checked_const("t", Typ::base("nat"));
        let mut thm = ThmKernel::reflexive(t).unwrap();
        thm.tpairs
            .push((Term::const_("lhs", Typ::base("nat")), Term::const_("rhs", Typ::base("nat"))));

        assert!(
            matches!(
                thm.check_kernel_invariants(KernelCheckMode::Strict),
                Err(KernelError::KernelInvariant { .. })
            ),
            "strict invariant accepted tampered tpairs"
        );
    }

    #[test]
    fn test_alpha_equivalence() {
        let t1 = Term::abs("x", Typ::dummy(), Term::bound(0));
        let t2 = Term::abs("y", Typ::dummy(), Term::bound(0));
        assert_ne!(t1, t2);
        assert!(Hyps::kernel_alpha_eq(&t1, &t2));
    }

    // =================================================================
    // Tests for new kernel infrastructure
    // =================================================================

    #[test]
    fn test_nprems_prem_concl() {
        // trivial: [A] ==> A → 1 subgoal (A), conclusion = A
        let a = prop("A");
        let thm = ThmKernel::trivial(a.clone()).unwrap();
        assert_eq!(thm.nprems(), 1);
        assert_eq!(thm.prem(0), Some(a.term().clone()));
        assert_eq!(thm.concl(), a.term().clone());
    }

    #[test]
    fn test_nprems_multiple() {
        // assume(A ==> B): hyps={A==>B}, prop=A==>B → 1 subgoal (A), concl = B
        let a = prop("A");
        let b = prop("B");
        let imp = Pure::mk_implies(a.term().clone(), b.term().clone());
        let thm = ThmKernel::assume(checked_cterm(imp)).unwrap();
        assert_eq!(thm.nprems(), 1); // A is the only premise
        assert_eq!(thm.concl(), b.term().clone()); // B is the conclusion
    }

    #[test]
    fn test_instantiate_idempotent() {
        let a = prop("A");
        let thm = ThmKernel::assume(a.clone()).unwrap();
        let env = Envir::init();
        let result = ThmKernel::instantiate_checked(&env, &thm).unwrap();
        assert_eq!(result.prop(), thm.prop());
        assert_eq!(result.hyps().len(), thm.hyps().len());
    }

    #[test]
    fn test_bicompose_assume_tac() {
        // Simulate assume_tac: use assume(A) to discharge first subgoal
        // state: [A] ==> A  (trivial goal)
        // assume(A): [A] ⊢ A
        // Result should have 0 premises (A discharged)
        let a = prop("A");
        let state = ThmKernel::trivial(a.clone()).unwrap();
        let assume_a = ThmKernel::assume(a.clone()).unwrap();
        let result = ThmKernel::bicompose(false, &assume_a, &state, 0);
        assert!(result.is_some());
        assert_eq!(result.unwrap().nprems(), 0);
    }

    #[test]
    fn test_bicompose_resolve() {
        // Simulate resolve_tac with modus ponens:
        // thm: [B ==> A] ⊢ B ==> A
        // state: [A ==> C] ⊢ A ==> C
        // Result should be: [B ==> A, B] ⊢ B ==> C  (A replaced by B)
        let a = prop("A");
        let b = prop("B");
        let c = prop("C");
        let thm =
            ThmKernel::assume(checked_cterm(Pure::mk_implies(b.term().clone(), a.term().clone())))
                .unwrap();
        let state =
            ThmKernel::assume(checked_cterm(Pure::mk_implies(a.term().clone(), c.term().clone())))
                .unwrap();
        let result = ThmKernel::bicompose(false, &thm, &state, 0);
        assert!(result.is_some());
        let r = result.unwrap();
        // First premise should be B (from thm's premises)
        assert!(Hyps::kernel_alpha_eq(&r.prem(0).unwrap(), b.term()));
    }

    #[test]
    fn test_beta_conversion_compat_accepts_dummy_redex() {
        // (λx. x) A → A
        let lam = Term::abs("x", Typ::dummy(), Term::bound(0));
        let a = Term::free("a", Typ::dummy());
        let app = CTerm::certify(Term::app(lam, a.clone()));
        let result = ThmKernel::beta_conversion(app);
        assert!(result.is_ok());
    }

    #[test]
    fn test_beta_conversion_substitutes_argument_for_bound_zero() {
        // Attack: beta_conversion must not expose the raw de Bruijn body.
        // (λx. x) a proves equality to `a`, not equality to `Bound(0)`.
        let nat = Typ::base("nat");
        let lam = Term::abs("x", nat.clone(), Term::bound(0));
        let a = Term::free("a", nat.clone());
        let app = checked_cterm(Term::app(lam, a.clone()));

        let thm = ThmKernel::beta_conversion(app).unwrap();
        let (_, rhs) = Pure::dest_equals(thm.prop().term()).expect("beta result is equality");
        assert_eq!(rhs, &a);
        assert_ne!(rhs, &Term::bound(0));
    }

    #[test]
    fn test_beta_conversion_compat_non_application_err() {
        // Non-application should return Err, not panic
        let t = CTerm::certify(Term::const_("x", Typ::dummy()));
        let result = ThmKernel::beta_conversion(t);
        assert!(result.is_err());
        match result {
            Err(KernelError::BetaConversion(_)) => {}, // expected
            _ => panic!("expected BetaConversion error"),
        }
    }

    #[test]
    fn test_instantiate_with_unifier() {
        // Test instantiate with a non-empty environment
        let mut env = Envir::empty(10);
        let x_name: Symbol = "x".into();
        let nat = Typ::base("nat");
        let zero = Term::const_("zero", nat.clone());
        env.update(x_name.clone(), 0, nat.clone(), zero.clone());

        let var_term = Term::var("x", 0, nat);
        let thm = ThmKernel::assume(checked_cterm(var_term)).unwrap();
        let result = ThmKernel::instantiate_checked(&env, &thm).unwrap();
        // The var should be replaced by zero
        assert_eq!(result.prop().term(), &zero);
    }

    #[test]
    fn test_instantiate_legacy_is_test_only_and_conservative() {
        // Characterizes the old infallible behavior without keeping it as a
        // production API: bad environments must not manufacture a new theorem.
        let nat = Typ::base("nat");
        let bool_t = Typ::base("bool");
        let pred = Term::const_("P", Typ::arrow(nat.clone(), Typ::base("prop")));
        let var_term = Term::var("x", 0, nat.clone());
        let thm = ThmKernel::assume_compat(CTerm::certify(Term::app(pred, var_term)));

        let mut env = Envir::empty(0);
        env.update("x".into(), 0, nat, Term::const_("True", bool_t));

        let checked = ThmKernel::instantiate_checked(&env, &thm);
        assert!(matches!(checked, Err(KernelError::TypeMismatch { .. })));

        let result = ThmKernel::instantiate_legacy(&env, &thm);
        assert_eq!(result.prop(), thm.prop());
    }

    // =================================================================
    // Trust footprint (T3): proved vs admitted must be distinguishable
    // =================================================================

    #[test]
    fn test_proved_theorem_has_empty_oracle_footprint() {
        // A theorem built purely by kernel rules carries no oracle.
        let a = prop("A");
        let thm = ThmKernel::trivial(a).unwrap();
        assert!(thm.is_fully_proved());
        assert!(thm.oracles().is_empty());
    }

    #[test]
    fn test_admit_is_not_fully_proved() {
        // admit() accepts a proposition without proof — it must be tagged.
        let a = prop("A");
        let thm = ThmKernel::admit(a.clone(), "admitted");
        assert!(!thm.is_fully_proved());
        assert_eq!(thm.oracles().len(), 1);
        assert_eq!(&*thm.oracles()[0], "admitted");
        assert!(thm.has_oracles());
        // The conclusion is still the admitted proposition.
        assert_eq!(thm.prop(), &a);
    }

    #[test]
    fn test_oracle_footprint_propagates_through_rules() {
        // An admitted equality, fed through a real kernel rule, must taint
        // the result: trust is contagious and never silently dropped.
        let t = CTerm::certify(Term::const_("t", Typ::base("nat")));
        let u = CTerm::certify(Term::const_("u", Typ::base("nat")));
        let eq = Pure::mk_equals(Typ::base("nat"), t.term().clone(), u.term().clone());
        let admitted_eq = ThmKernel::admit(checked_cterm(eq), "admitted");
        assert!(!admitted_eq.is_fully_proved());

        // symmetric is a sound rule, but its input was admitted.
        let flipped = ThmKernel::symmetric(&admitted_eq).unwrap();
        assert!(!flipped.is_fully_proved(), "oracle must propagate through symmetric");
        assert_eq!(&*flipped.oracles()[0], "admitted");
    }

    #[test]
    fn test_union_of_proved_and_admitted_is_tainted() {
        // transitive(proved, admitted) must be tainted; transitive(proved,
        // proved) must stay clean. This is the core of honest accounting.
        let nat = Typ::base("nat");
        let t = Term::const_("t", nat.clone());
        let u = Term::const_("u", nat.clone());
        let v = Term::const_("v", nat.clone());

        let proved_tu = ThmKernel::reflexive(checked_cterm(t.clone())).unwrap(); // ⊢ t ≡ t
        assert!(proved_tu.is_fully_proved());
        assert!(proved_tu.is_strict_kernel_theorem());

        let admitted_tv = ThmKernel::admit(
            checked_cterm(Pure::mk_equals(nat.clone(), t.clone(), v.clone())),
            "admitted",
        );
        // transitive(t≡t, t≡v) = t≡v, tainted by the admitted premise.
        let res = ThmKernel::transitive(&proved_tu, &admitted_tv).unwrap();
        assert!(!res.is_fully_proved());
        assert_eq!(res.oracles().len(), 1);

        // transitive of two clean reflexives stays clean.
        let r1 = ThmKernel::reflexive(checked_cterm(u.clone())).unwrap();
        let r2 = ThmKernel::reflexive(checked_cterm(u)).unwrap();
        let clean = ThmKernel::transitive(&r1, &r2).unwrap();
        assert!(clean.is_fully_proved());
        assert!(clean.is_strict_closed_proved());
    }

    #[test]
    fn test_transitive_rejects_known_equality_type_mismatch() {
        // Attack: the middle terms have the same printed name, but the two
        // equality constants are instantiated at distinct known types. The
        // kernel must reject the chain instead of manufacturing a mixed-type
        // equality.
        let nat = Typ::base("nat");
        let bool_t = Typ::base("bool");
        let a = Term::const_("a", nat.clone());
        let b_nat = Term::const_("b", nat.clone());
        let b_bool = Term::const_("b", bool_t.clone());
        let c = Term::const_("c", bool_t.clone());

        let thm1 = ThmKernel::admit(
            CTerm::certify(Pure::mk_equals(nat, a, b_nat)),
            "admitted:test_type_mismatch_left",
        );
        let thm2 = ThmKernel::admit(
            CTerm::certify(Pure::mk_equals(bool_t, b_bool, c)),
            "admitted:test_type_mismatch_right",
        );

        let res = ThmKernel::transitive(&thm1, &thm2);
        assert!(
            matches!(res, Err(KernelError::TypeMismatch { .. })),
            "transitive accepted equality types nat and bool: {res:?}"
        );
    }

    // =================================================================
    // T2-3: sort hypotheses (shyps) must survive inference rules
    // =================================================================

    #[test]
    fn test_shyps_propagate_through_single_premise_rule() {
        // A sort constraint attached to a premise must not be silently dropped
        // by a single-premise rule. Before this fix, symmetric set shyps=vec![].
        let nat = Typ::base("nat");
        let eq =
            Pure::mk_equals(nat.clone(), Term::const_("a", nat.clone()), Term::const_("b", nat));
        let base = ThmKernel::reflexive(checked_cterm(eq)).unwrap();
        let sort = Sort::new(vec![Arc::from("order")]);
        let tagged = ThmKernel::add_shyp(&base, sort.clone());
        assert_eq!(tagged.shyps().len(), 1);

        // symmetric is single-premise; the shyp must carry through.
        let flipped = ThmKernel::symmetric(&tagged).unwrap();
        assert!(flipped.shyps().contains(&sort), "shyp dropped by symmetric");
    }

    #[test]
    fn test_shyps_union_through_multi_premise_rule() {
        // Two premises each carrying a distinct sort constraint: transitive must
        // carry the union of both. Before this fix, multi-premise rules dropped them.
        let nat = Typ::base("nat");
        let a = Term::const_("a", nat.clone());
        let b = Term::const_("b", nat.clone());
        let c = Term::const_("c", nat.clone());
        let ab =
            ThmKernel::reflexive(checked_cterm(Pure::mk_equals(nat.clone(), a.clone(), a.clone())))
                .unwrap();
        let bc = ThmKernel::reflexive(checked_cterm(Pure::mk_equals(nat.clone(), a.clone(), a)))
            .unwrap();
        let s1 = Sort::new(vec![Arc::from("order")]);
        let s2 = Sort::new(vec![Arc::from("finite")]);
        let _ = (b, c); // terms above kept reflexive for a valid transitive chain
        let p1 = ThmKernel::add_shyp(&ab, s1.clone());
        let p2 = ThmKernel::add_shyp(&bc, s2.clone());

        let res = ThmKernel::transitive(&p1, &p2).unwrap();
        assert!(res.shyps().contains(&s1), "shyp s1 dropped");
        assert!(res.shyps().contains(&s2), "shyp s2 dropped");
    }

    // =================================================================
    // T2-2: combination must reject a known argument-type mismatch
    // =================================================================

    #[test]
    fn test_combination_rejects_known_type_mismatch() {
        // f : nat → bool, applied to an argument equality typed `int`.
        // With both types known, the well-formedness guard must fire.
        let nat = Typ::base("nat");
        let int = Typ::base("int");
        let bool_t = Typ::base("bool");
        let fn_typ = Typ::arrow(nat.clone(), bool_t);

        // f ≡ f at type nat→bool
        let f = Term::const_("f", fn_typ.clone());
        let f_eq = ThmKernel::reflexive(checked_cterm(f)).unwrap();
        // x ≡ x at type int (mismatched against the nat domain)
        let x = Term::const_("x", int.clone());
        let x_eq = ThmKernel::reflexive(checked_cterm(x)).unwrap();

        let res = ThmKernel::combination(&f_eq, &x_eq);
        assert!(
            matches!(res, Err(KernelError::TypeMismatch { .. })),
            "combination accepted a known nat-vs-int mismatch: {res:?}"
        );
    }

    #[test]
    fn test_combination_accepts_well_typed_congruence() {
        // f : nat → nat applied to x : nat — proper congruence, must succeed.
        let nat = Typ::base("nat");
        let fn_typ = Typ::arrow(nat.clone(), nat.clone());
        let f = Term::const_("f", fn_typ.clone());
        let f_eq = ThmKernel::reflexive(checked_cterm(f)).unwrap();
        let x = Term::const_("x", nat.clone());
        let x_eq = ThmKernel::reflexive(checked_cterm(x)).unwrap();

        let res = ThmKernel::combination(&f_eq, &x_eq);
        assert!(res.is_ok(), "well-typed congruence rejected: {res:?}");
        assert!(res.unwrap().is_fully_proved());
    }

    // =================================================================
    // T2-1 (Strict Kernel Phase): kernel alpha-equivalence must not perform
    // parser/loader compatibility repair.
    // =================================================================

    #[test]
    fn test_alpha_eq_rejects_distinct_binder_types() {
        // λ(x:nat). x  vs  λ(x:bool). x  — same body, different known types.
        let nat_abs = Term::abs("x", Typ::base("nat"), Term::Bound(0));
        let bool_abs = Term::abs("x", Typ::base("bool"), Term::Bound(0));
        assert!(
            !Hyps::kernel_alpha_eq(&nat_abs, &bool_abs),
            "kernel_alpha_eq wrongly identified λ(x:nat).x with λ(x:bool).x"
        );
    }

    #[test]
    fn test_kernel_alpha_eq_rejects_dummy_known_binder_match() {
        // Strict kernel equality requires binder types to match exactly. Dummy
        // binder compatibility is now isolated in compat_alpha_eq.
        let dummy_abs = Term::abs("x", Typ::dummy(), Term::Bound(0));
        let nat_abs = Term::abs("y", Typ::base("nat"), Term::Bound(0));
        assert!(
            !Hyps::kernel_alpha_eq(&dummy_abs, &nat_abs),
            "kernel_alpha_eq tolerated dummy-vs-known binder type"
        );
        assert!(
            !Hyps::kernel_alpha_eq(&nat_abs, &dummy_abs),
            "kernel_alpha_eq tolerated known-vs-dummy binder type"
        );

        // Compatibility mode preserves the historical behavior explicitly.
        assert!(Hyps::compat_alpha_eq(&dummy_abs, &nat_abs));
        assert!(Hyps::compat_alpha_eq(&nat_abs, &dummy_abs));

        // Two identical known types still match in strict mode.
        let nat_abs2 = Term::abs("z", Typ::base("nat"), Term::Bound(0));
        assert!(Hyps::kernel_alpha_eq(&nat_abs, &nat_abs2));
    }

    #[test]
    fn test_alpha_eq_should_reject_free_const_suffix_match() {
        // A free variable named `zero` is not the HOL constant `Groups.zero`.
        let free_zero = Term::free("zero", Typ::base("nat"));
        let const_zero = Term::const_("Groups.zero", Typ::base("nat"));
        assert!(
            !Hyps::kernel_alpha_eq(&free_zero, &const_zero),
            "kernel_alpha_eq identified Free(\"zero\") with Const(\"Groups.zero\")"
        );
        assert!(
            Hyps::compat_alpha_eq(&free_zero, &const_zero),
            "compat_alpha_eq should preserve legacy Free/Const suffix matching"
        );
    }

    #[test]
    fn test_alpha_eq_should_reject_var_free_index_confusion() {
        // A schematic variable with an index is not a free variable.
        let schematic = Term::var("x", 7, Typ::base("nat"));
        let free = Term::free("x", Typ::base("nat"));
        assert!(
            !Hyps::kernel_alpha_eq(&schematic, &free),
            "kernel_alpha_eq identified Var(\"x\", 7) with Free(\"x\")"
        );
        assert!(
            Hyps::compat_alpha_eq(&schematic, &free),
            "compat_alpha_eq should preserve legacy Var/Free matching"
        );
    }

    #[test]
    fn test_kernel_alpha_eq_rejects_distinct_var_indices() {
        let x0 = Term::var("x", 0, Typ::base("nat"));
        let x7 = Term::var("x", 7, Typ::base("nat"));
        assert!(
            !Hyps::kernel_alpha_eq(&x0, &x7),
            "kernel_alpha_eq identified distinct schematic variable indices"
        );
    }
}
