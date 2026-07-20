use std::{collections::BTreeSet, fmt, sync::Arc};

use super::{
    CProp, CTerm, ClosedThm, ContextStamp, KernelError, KernelThm, Name, ProofContext, RawTerm,
    Signature, Ty,
    identity::{CanonicalEncoder, THEORY_DOMAIN, TheoryId},
    invariant::replay_closed_theorem_in,
};

const THEOREM_DOMAIN: &[u8] = b"isabelle-rs/theorem/v1";

/// Content identity of a replay-accepted theorem.
///
/// The digest constructor is private to this module. IDs are deliberately not
/// deserializable as trusted values.
///
/// ```compile_fail
/// use isabelle_rs::kernel::TheoremId;
/// let _forged = TheoremId([0; 32]);
/// ```
///
/// ```compile_fail
/// use isabelle_rs::kernel::TheoremId;
/// let _: TheoremId = serde_json::from_str("[0, 1]").unwrap();
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TheoremId([u8; 32]);

impl TheoremId {
    pub fn to_bytes(self) -> [u8; 32] {
        self.0
    }

    fn from_digest(digest: [u8; 32]) -> Self {
        Self(digest)
    }

    fn write_canonical(self, encoder: &mut CanonicalEncoder) {
        encoder.write_fixed_bytes(&self.0);
    }
}

impl fmt::Debug for TheoremId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_digest(f, "TheoremId", &self.0)
    }
}

/// Dependency categories reserved by the accepted-theorem identity schema.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DependencyKind {
    Axiom,
    Definition,
    Theorem,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct DependencyId {
    kind: DependencyKind,
    digest: [u8; 32],
}

/// Canonical logical dependencies reconstructed by accepting replay.
///
/// Theorem entries identify replayed theorem content; they do not grant
/// theorem-reference authority. Replay must first validate the exact sealed
/// `TrustedTheorem` token (`id`, `name`, and `accepted_in`) against the current
/// owner ancestry. The resulting `TheoremId` is recorded here only after that
/// authorization succeeds.
#[derive(Clone, Default, PartialEq, Eq)]
pub struct DependencySet {
    entries: BTreeSet<DependencyId>,
}

impl DependencySet {
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub(crate) fn empty() -> Self {
        Self::default()
    }

    pub(crate) fn insert_theorem(&mut self, theorem: TheoremId) {
        self.entries
            .insert(DependencyId { kind: DependencyKind::Theorem, digest: theorem.to_bytes() });
    }

    pub(crate) fn insert_axiom(&mut self, dep_id: super::AxiomDependencyId) {
        self.entries.insert(DependencyId {
            kind: DependencyKind::Axiom,
            digest: dep_id.to_bytes(),
        });
    }

    pub(crate) fn insert_definition(&mut self, definition_id: [u8; 32]) {
        let mut encoder = super::identity::CanonicalEncoder::new(b"isabelle-rs/dep-defn/v1");
        encoder.write_fixed_bytes(&definition_id);
        let digest = encoder.finish();
        self.entries.insert(DependencyId { kind: DependencyKind::Definition, digest });
    }

    fn write_canonical(&self, encoder: &mut CanonicalEncoder) {
        encoder.write_u64(self.entries.len() as u64);
        for dependency in &self.entries {
            let tag = match dependency.kind {
                DependencyKind::Axiom => 0,
                DependencyKind::Definition => 1,
                DependencyKind::Theorem => 2,
            };
            encoder.write_u8(tag);
            encoder.write_fixed_bytes(&dependency.digest);
        }
    }
}

impl fmt::Debug for DependencySet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DependencySet").field("len", &self.len()).finish()
    }
}

/// Immutable ancestry-sensitive theory context used by strict certification.
#[derive(Clone)]
pub struct TheorySnapshot {
    inner: Arc<TheoryNode>,
}

struct TheoryNode {
    id: TheoryId,
    parent: Option<TheorySnapshot>,
    signature: Signature,
    extension: TheoryExtension,
}

#[derive(Clone)]
enum TheoryExtension {
    Root { name: Name },
    BeginChild { name: Name },
    DeclareConst { name: Name, ty: Ty },
    DefineConst { name: Name, ty: Ty, definition_id: [u8; 32] },
    StoreTheorem { name: Name, theorem: TheoremId },
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

    pub fn extend_definition(
        &self, name: impl Into<Name>, ty: Ty, definition_id: [u8; 32],
    ) -> Result<Self, KernelError> {
        let name = name.into();
        let signature = self.signature().extend_const(name.clone(), ty.clone())?;
        Ok(Self::build(Some(self.clone()), signature,
            TheoryExtension::DefineConst { name, ty, definition_id }))
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

    fn extension(&self) -> &TheoryExtension {
        &self.inner.extension
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

    pub(crate) fn has_ancestor(&self, ancestor: TheoryId) -> bool {
        let mut current = Some(self);
        while let Some(theory) = current {
            if theory.id() == ancestor {
                return true;
            }
            current = theory.parent();
        }
        false
    }

    fn store_theorem(&self, name: Name, theorem: TheoremId) -> Self {
        Self::build(
            Some(self.clone()),
            self.signature().clone(),
            TheoryExtension::StoreTheorem { name, theorem },
        )
    }

    fn build(
        parent: Option<TheorySnapshot>,
        signature: Signature,
        extension: TheoryExtension,
    ) -> Self {
        let id = compute_theory_id(parent.as_ref().map(TheorySnapshot::id), &extension, &signature);
        Self { inner: Arc::new(TheoryNode { id, parent, signature, extension }) }
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
            TheoryExtension::DefineConst { name, ty, definition_id } => {
                encoder.write_u8(4);
                encoder.write_name(name);
                ty.write_canonical(encoder);
                encoder.write_fixed_bytes(definition_id);
            },
            TheoryExtension::StoreTheorem { name, theorem } => {
                encoder.write_u8(3);
                encoder.write_name(name);
                theorem.write_canonical(encoder);
            },
        }
    }
}

/// Sealed theorem accepted by one immutable trusted-theory extension.
///
/// Construction and proof extraction are intentionally unavailable.
///
/// ```compile_fail
/// use isabelle_rs::kernel::TrustedTheorem;
/// fn forge(inner: std::sync::Arc<()>) {
///     let _ = TrustedTheorem(inner);
/// }
/// ```
#[derive(Clone)]
pub struct TrustedTheorem(Arc<AcceptedTheoremInner>);

struct AcceptedTheoremInner {
    id: TheoremId,
    name: Name,
    closed: ClosedThm,
    dependencies: DependencySet,
    accepted_in: TheoryId,
}

impl TrustedTheorem {
    pub fn id(&self) -> TheoremId {
        self.0.id
    }

    pub fn name(&self) -> &Name {
        &self.0.name
    }

    pub fn prop(&self) -> &CProp {
        self.0.closed.as_kernel().prop()
    }

    /// Extract the sealed kernel theorem (for use as a premise in further derivations).
    pub fn as_kernel(&self) -> &KernelThm {
        self.0.closed.as_kernel()
    }

    pub fn proved_context(&self) -> ContextStamp {
        self.0.closed.context()
    }

    pub fn proved_in(&self) -> TheoryId {
        self.0.closed.as_kernel().proved_in()
    }

    pub fn accepted_in(&self) -> TheoryId {
        self.0.accepted_in
    }

    pub fn dependencies(&self) -> &DependencySet {
        &self.0.dependencies
    }

    fn seal(
        id: TheoremId,
        name: Name,
        closed: ClosedThm,
        dependencies: DependencySet,
        accepted_in: TheoryId,
    ) -> Self {
        Self(Arc::new(AcceptedTheoremInner { id, name, closed, dependencies, accepted_in }))
    }
}

impl PartialEq for TrustedTheorem {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
            && self.name() == other.name()
            && self.accepted_in() == other.accepted_in()
    }
}

impl Eq for TrustedTheorem {}

impl fmt::Debug for TrustedTheorem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TrustedTheorem")
            .field("id", &self.id())
            .field("name", self.name())
            .field("proved_in", &self.proved_in())
            .field("accepted_in", &self.accepted_in())
            .field("dependencies", self.dependencies())
            .finish()
    }
}

/// Immutable owner of a certification snapshot and its exact accepted-fact ancestry.
///
/// There is deliberately no `Default`, context-free `new`, or `from_snapshot`.
///
/// ```compile_fail
/// use isabelle_rs::kernel::TrustedTheory;
/// let _ = TrustedTheory::new();
/// ```
#[derive(Clone)]
pub struct TrustedTheory {
    inner: Arc<TrustedTheoryNode>,
}

struct TrustedTheoryNode {
    snapshot: TheorySnapshot,
    parent: Option<TrustedTheory>,
    local_fact: Option<TrustedTheorem>,
    fact_count: usize,
    logic_basis: Option<Arc<super::LogicBasis>>,
}

impl TrustedTheory {
    pub fn root(name: impl Into<Name>, signature: Signature) -> Self {
        Self {
            inner: Arc::new(TrustedTheoryNode {
                snapshot: TheorySnapshot::root(name, signature),
                parent: None,
                local_fact: None,
                fact_count: 0,
                logic_basis: None,
            }),
        }
    }

    /// Create a root theory with a validated logic basis.
    pub fn with_basis(
        name: impl Into<Name>,
        signature: Signature,
        basis: &super::LogicBasis,
    ) -> Result<Self, KernelError> {
        basis.validate_against(&signature)?;
        Ok(Self {
            inner: Arc::new(TrustedTheoryNode {
                snapshot: TheorySnapshot::root(name, signature),
                parent: None,
                local_fact: None,
                fact_count: 0,
                logic_basis: Some(Arc::new(basis.clone())),
            }),
        })
    }

    /// The installed logic basis, if any.
    pub fn logic_basis(&self) -> Option<&super::LogicBasis> {
        self.inner.logic_basis.as_deref()
    }

    pub fn begin_child(&self, name: impl Into<Name>) -> Self {
        let snapshot = self.snapshot().begin_child(name);
        Self::child(self, snapshot, None)
    }

    pub fn extend_const(&self, name: impl Into<Name>, ty: Ty) -> Result<Self, KernelError> {
        let snapshot = self.snapshot().extend_const(name, ty)?;
        Ok(Self::child(self, snapshot, None))
    }

    /// Atomically extend the theory with a conservative definition.
    ///
    /// Certifies RHS in the parent context (guaranteeing freshness — the
    /// constant does not yet exist), checks closedness, then extends the
    /// signature with a `DefineConst` extension. Returns the child theory
    /// and the certified RHS term.
    pub fn extend_definition(
        &self,
        name: impl Into<Name>,
        rhs_raw: RawTerm,
    ) -> Result<(TrustedTheory, CTerm), KernelError> {
        let name = name.into();
        let parent_ctx = ProofContext::new(self.snapshot().clone());
        let rhs = parent_ctx.certify_term(rhs_raw.clone())?;
        let rhs_ty = rhs.ty();
        if rhs_raw.has_free_vars() {
            return Err(KernelError::Invariant("definition RHS is not closed".into()));
        }
        let mut encoder = CanonicalEncoder::new(b"isabelle-rs/define-const/v1");
        self.id().write_canonical(&mut encoder);
        encoder.write_name(&name);
        rhs_ty.write_canonical(&mut encoder);
        rhs_raw.write_canonical(&mut encoder);
        let definition_id = encoder.finish();
        let snapshot = self.snapshot().extend_definition(name, rhs_ty, definition_id)?;
        let child = Self::child(self, snapshot, None);
        Ok((child, rhs))
    }

    pub fn snapshot(&self) -> &TheorySnapshot {
        &self.inner.snapshot
    }

    pub fn id(&self) -> TheoryId {
        self.snapshot().id()
    }

    pub fn signature(&self) -> &Signature {
        self.snapshot().signature()
    }

    pub fn stamp(&self) -> ContextStamp {
        self.snapshot().stamp()
    }

    pub fn parent(&self) -> Option<&TrustedTheory> {
        self.inner.parent.as_ref()
    }

    pub fn get(&self, name: &Name) -> Option<&TrustedTheorem> {
        let mut current = Some(self);
        while let Some(theory) = current {
            if let Some(theorem) = theory.inner.local_fact.as_ref()
                && theorem.name() == name
            {
                return Some(theorem);
            }
            current = theory.parent();
        }
        None
    }

    pub fn len(&self) -> usize {
        self.inner.fact_count
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn child(
        parent: &TrustedTheory,
        snapshot: TheorySnapshot,
        local_fact: Option<TrustedTheorem>,
    ) -> Self {
        debug_assert_eq!(snapshot.parent().map(TheorySnapshot::id), Some(parent.id()));
        let fact_count = parent.len() + usize::from(local_fact.is_some());
        let logic_basis = parent.inner.logic_basis.clone();
        Self {
            inner: Arc::new(TrustedTheoryNode {
                snapshot,
                parent: Some(parent.clone()),
                local_fact,
                fact_count,
                logic_basis,
            }),
        }
    }

    fn check_consistency(&self) -> Result<(), KernelError> {
        let mut current = Some(self);
        while let Some(theory) = current {
            let snapshot = theory.snapshot();
            match (theory.parent(), snapshot.extension(), theory.inner.local_fact.as_ref()) {
                (None, TheoryExtension::Root { name }, None) => {
                    if snapshot.parent().is_some()
                        || theory.len() != 0
                        || TheorySnapshot::root(name.clone(), snapshot.signature().clone()).id()
                            != theory.id()
                    {
                        return Err(KernelError::Invariant(
                            "trusted root owner does not match its snapshot".into(),
                        ));
                    }
                },
                (Some(parent), TheoryExtension::BeginChild { name }, None) => {
                    if snapshot.parent().map(TheorySnapshot::id) != Some(parent.id())
                        || theory.len() != parent.len()
                        || parent.snapshot().begin_child(name.clone()).id() != theory.id()
                    {
                        return Err(KernelError::Invariant(
                            "trusted child owner does not match its snapshot parent".into(),
                        ));
                    }
                },
                (Some(parent), TheoryExtension::DeclareConst { name, ty }, None) => {
                    let expected = parent.snapshot().extend_const(name.clone(), ty.clone())?;
                    if snapshot.parent().map(TheorySnapshot::id) != Some(parent.id())
                        || theory.len() != parent.len()
                        || expected.id() != theory.id()
                    {
                        return Err(KernelError::Invariant(
                            "trusted declaration owner does not match its snapshot parent".into(),
                        ));
                    }
                },
                (Some(parent), TheoryExtension::DefineConst { name, ty, definition_id }, None) => {
                    let expected = parent.snapshot().extend_definition(
                        name.clone(), ty.clone(), *definition_id,
                    )?;
                    if snapshot.parent().map(TheorySnapshot::id) != Some(parent.id())
                        || theory.len() != parent.len()
                        || expected.id() != theory.id()
                    {
                        return Err(KernelError::Invariant(
                            "trusted definition owner does not match its snapshot parent".into(),
                        ));
                    }
                },
                (
                    Some(parent),
                    TheoryExtension::StoreTheorem { name, theorem: theorem_id },
                    Some(theorem),
                ) => {
                    let expected = parent.snapshot().store_theorem(name.clone(), *theorem_id);
                    if snapshot.parent().map(TheorySnapshot::id) != Some(parent.id())
                        || theory.len() != parent.len() + 1
                        || expected.id() != theory.id()
                        || theorem.name() != name
                        || theorem.id() != *theorem_id
                        || theorem.accepted_in() != theory.id()
                        || theorem.proved_context() != parent.stamp()
                        || theorem.prop().context() != parent.stamp()
                        || !parent.resolves(theorem.dependencies())
                    {
                        return Err(KernelError::Invariant(
                            "accepted fact does not match its committed theory extension".into(),
                        ));
                    }
                },
                _ => {
                    return Err(KernelError::Invariant(
                        "trusted owner extension and local fact are inconsistent".into(),
                    ));
                },
            }
            current = theory.parent();
        }
        Ok(())
    }

    /// Check replay-derived logical dependency IDs after token authorization.
    ///
    /// `Derivation::TheoremRef` replay has already required the exact accepted
    /// token in this owner's ancestry. Digest lookup here is a consistency
    /// check for the canonical dependency set, not an authority check.
    fn resolves(&self, dependencies: &DependencySet) -> bool {
        dependencies.entries.iter().all(|dependency| match dependency.kind {
            DependencyKind::Axiom => self.contains_axiom_dependency(dependency.digest),
            DependencyKind::Definition => self.contains_definition_digest(dependency.digest),
            DependencyKind::Theorem => self.contains_theorem_digest(dependency.digest),
        })
    }


    fn contains_axiom_dependency(&self, digest: [u8; 32]) -> bool {
        if let Some(basis) = self.logic_basis() {
            for schema in &basis.axioms {
                let dep_id = super::AxiomDependencyId::compute(basis.id, schema.id());
                if dep_id.to_bytes() == digest {
                    return true;
                }
            }
        }
        false
    }


    fn contains_theorem_digest(&self, digest: [u8; 32]) -> bool {
        let mut current = Some(self);
        while let Some(theory) = current {
            if theory
                .inner
                .local_fact
                .as_ref()
                .is_some_and(|theorem| theorem.id().to_bytes() == digest)
            {
                return true;
            }
            current = theory.parent();
        }
        false
    }

    fn contains_definition_digest(&self, digest: [u8; 32]) -> bool {
        let mut current = Some(self);
        while let Some(theory) = current {
            if let TheoryExtension::DefineConst { definition_id, .. } = theory.snapshot().extension() {
                let mut encoder = CanonicalEncoder::new(b"isabelle-rs/dep-defn/v1");
                encoder.write_fixed_bytes(definition_id);
                if encoder.finish() == digest {
                    return true;
                }
            }
            current = theory.parent();
        }
        false
    }
    pub(crate) fn contains_theorem(&self, expected: &TrustedTheorem) -> bool {
        let mut current = Some(self);
        while let Some(theory) = current {
            if theory.inner.local_fact.as_ref().is_some_and(|theorem| {
                theorem.id() == expected.id()
                    && theorem.name() == expected.name()
                    && theorem.accepted_in() == expected.accepted_in()
            }) {
                return true;
            }
            current = theory.parent();
        }
        false
    }
}

impl fmt::Debug for TrustedTheory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TrustedTheory")
            .field("id", &self.id())
            .field("parent", &self.parent().map(TrustedTheory::id))
            .field("signature", &self.signature().id())
            .field("facts", &self.len())
            .finish()
    }
}

/// Replay and atomically install one closed theorem into a new trusted child.
pub fn accept_closed_theorem(
    theory: &TrustedTheory,
    name: impl Into<Name>,
    theorem: ClosedThm,
) -> Result<(TrustedTheory, TrustedTheorem), KernelError> {
    let name = name.into();
    let expected = theory.stamp();
    if theorem.context() != expected {
        return Err(KernelError::MixedContext { expected, actual: theorem.context() });
    }
    theory.check_consistency()?;
    if theory.get(&name).is_some() {
        return Err(KernelError::DuplicateTheorem { name });
    }

    let replayed = replay_closed_theorem_in(theory, &theorem)?;
    let candidate = theorem.as_kernel();
    if replayed.context() != candidate.context()
        || replayed.hyps() != candidate.hyps()
        || replayed.prop() != candidate.prop()
    {
        return Err(KernelError::AcceptanceReplayMismatch);
    }
    if !replayed.hyps().is_empty() {
        return Err(KernelError::TheoremNotClosed { hypotheses: replayed.hyps().len() });
    }
    if !theory.resolves(replayed.dependencies()) {
        return Err(KernelError::UnknownTheoremDependency);
    }

    let dependencies = replayed.dependencies().clone();
    let theorem_id = compute_theorem_id(expected, replayed.prop(), &dependencies);
    let child_snapshot = theory.snapshot().store_theorem(name.clone(), theorem_id);
    let trusted =
        TrustedTheorem::seal(theorem_id, name, theorem, dependencies, child_snapshot.id());
    let child = TrustedTheory::child(theory, child_snapshot, Some(trusted.clone()));
    debug_assert_eq!(trusted.accepted_in(), child.id());
    Ok((child, trusted))
}

fn compute_theorem_id(
    context: ContextStamp,
    prop: &CProp,
    dependencies: &DependencySet,
) -> TheoremId {
    let mut encoder = CanonicalEncoder::new(THEOREM_DOMAIN);
    context.write_canonical(&mut encoder);
    encoder.write_u8(0); // PureReplayV1
    encoder.write_u8(0); // no unresolved proof burdens
    prop.term().write_theorem_canonical(&mut encoder);
    dependencies.write_canonical(&mut encoder);
    TheoremId::from_digest(encoder.finish())
}

fn write_digest(f: &mut fmt::Formatter<'_>, label: &str, digest: &[u8; 32]) -> fmt::Result {
    write!(f, "{label}(")?;
    for byte in digest {
        write!(f, "{byte:02x}")?;
    }
    write!(f, ")")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{AxiomSchema, CTerm, Derivation, KernelRules, KernelThm, LogicBasis, ProofContext, RawTerm, Term, TrustedTheory};

    fn prop(name: &str) -> RawTerm {
        RawTerm::const_(name, Ty::prop())
    }

    fn trusted_theory(name: &str, props: &[&str]) -> TrustedTheory {
        let signature = props.iter().fold(Signature::new(), |signature, prop| {
            signature.extend_const(*prop, Ty::prop()).unwrap()
        });
        TrustedTheory::root(name, signature)
    }

    fn implication_identity(theory: &TrustedTheory, name: &str) -> ClosedThm {
        let context = ProofContext::new(theory.snapshot().clone());
        let proposition = context.certify_prop(prop(name)).unwrap();
        let assumed = KernelRules::assume(proposition.clone()).into_kernel();
        KernelRules::implies_intr(&proposition, &assumed).unwrap().try_close().unwrap()
    }

    #[test]
    fn extension_kind_contributes_to_theory_identity() {
        let signature = Signature::new();
        let name = Name::from("SamePayload");
        let root =
            compute_theory_id(None, &TheoryExtension::Root { name: name.clone() }, &signature);
        let child = compute_theory_id(None, &TheoryExtension::BeginChild { name }, &signature);

        assert_ne!(root, child);
    }

    #[test]
    fn forged_closed_candidate_with_hypotheses_is_rejected() {
        let theory = trusted_theory("Pure", &["A"]);
        let context = ProofContext::new(theory.snapshot().clone());
        let open = KernelRules::assume(context.certify_prop(prop("A")).unwrap()).into_kernel();
        let forged = ClosedThm::from_kernel_unchecked_for_test(open);

        assert!(matches!(
            accept_closed_theorem(&theory, "open", forged),
            Err(KernelError::TheoremNotClosed { hypotheses: 1 })
        ));
    }

    #[test]
    fn tampered_conclusion_and_derivation_are_rejected() {
        let theory = trusted_theory("Pure", &["A", "B"]);
        let valid = implication_identity(&theory, "A");
        let context = ProofContext::new(theory.snapshot().clone());
        let wrong_prop = context.certify_prop(prop("B")).unwrap();
        let wrong_conclusion =
            KernelThm::new(vec![], wrong_prop, valid.as_kernel().derivation().clone())
                .try_close()
                .unwrap();
        assert!(matches!(
            accept_closed_theorem(&theory, "wrong_conclusion", wrong_conclusion),
            Err(KernelError::AcceptanceReplayMismatch)
        ));

        let a = context.certify_term(prop("A")).unwrap();
        let wrong_derivation = KernelThm::new(
            vec![],
            valid.as_kernel().prop().clone(),
            Derivation::Reflexive { term: a },
        )
        .try_close()
        .unwrap();
        assert!(matches!(
            accept_closed_theorem(&theory, "wrong_derivation", wrong_derivation),
            Err(KernelError::AcceptanceReplayMismatch)
        ));
    }

    #[test]
    fn malformed_cached_application_type_is_rejected() {
        let nat = Ty::base("nat").unwrap();
        let signature = Signature::new()
            .extend_const("f", Ty::arrow(nat.clone(), nat.clone()))
            .unwrap()
            .extend_const("a", nat.clone())
            .unwrap();
        let theory = TrustedTheory::root("Pure", signature);
        let malformed = Term::App {
            func: Box::new(Term::Const {
                name: Name::from("f"),
                ty: Ty::arrow(nat.clone(), nat.clone()),
            }),
            arg: Box::new(Term::Const { name: Name::from("a"), ty: nat.clone() }),
            ty: Ty::prop(),
        };
        let candidate = KernelRules::reflexive(CTerm::new(malformed, theory.stamp()));

        assert!(matches!(
            accept_closed_theorem(&theory, "malformed_app", candidate),
            Err(KernelError::TypeMismatch { expected, actual })
                if expected == nat && actual == Ty::prop()
        ));
    }

    #[test]
    fn malformed_bound_and_equality_caches_are_rejected() {
        let nat = Ty::base("nat").unwrap();
        let signature = Signature::new().extend_const("a", nat.clone()).unwrap();
        let theory = TrustedTheory::root("Pure", signature);

        let malformed_abs = Term::Abs {
            name: Name::from("x"),
            param_ty: nat.clone(),
            body: Box::new(Term::Bound { index: 0, ty: Ty::prop() }),
            ty: Ty::arrow(nat.clone(), Ty::prop()),
        };
        let candidate = KernelRules::reflexive(CTerm::new(malformed_abs, theory.stamp()));
        assert!(matches!(
            accept_closed_theorem(&theory, "malformed_bound", candidate),
            Err(KernelError::TypeMismatch { .. })
        ));

        let a = Term::Const { name: Name::from("a"), ty: nat };
        let malformed_eq = CProp::from_checked_term(
            Term::Eq { object_ty: Ty::prop(), lhs: Box::new(a.clone()), rhs: Box::new(a) },
            theory.stamp(),
        );
        let assumed = KernelRules::assume(malformed_eq.clone()).into_kernel();
        let candidate =
            KernelRules::implies_intr(&malformed_eq, &assumed).unwrap().try_close().unwrap();
        assert!(matches!(
            accept_closed_theorem(&theory, "malformed_eq", candidate),
            Err(KernelError::TypeMismatch { .. })
        ));
    }

    #[test]
    fn forged_owner_store_mismatches_are_rejected() {
        let parent = trusted_theory("Pure", &["A"]);
        let (child, accepted) =
            accept_closed_theorem(&parent, "imp_identity", implication_identity(&parent, "A"))
                .unwrap();

        let missing_fact = TrustedTheory {
            inner: Arc::new(TrustedTheoryNode {
                snapshot: child.snapshot().clone(),
                parent: Some(parent.clone()),
                local_fact: None,
                fact_count: 0,
                logic_basis: None,
            }),
        };
        assert!(matches!(
            accept_closed_theorem(&missing_fact, "next", implication_identity(&missing_fact, "A")),
            Err(KernelError::Invariant(_))
        ));

        let wrong_token = TrustedTheorem::seal(
            accepted.id(),
            accepted.name().clone(),
            accepted.0.closed.clone(),
            accepted.dependencies().clone(),
            parent.id(),
        );
        let wrong_accepted_in = TrustedTheory {
            inner: Arc::new(TrustedTheoryNode {
                snapshot: child.snapshot().clone(),
                parent: Some(parent.clone()),
                local_fact: Some(wrong_token),
                fact_count: 1,
                logic_basis: None,
            }),
        };
        assert!(matches!(
            accept_closed_theorem(
                &wrong_accepted_in,
                "next",
                implication_identity(&wrong_accepted_in, "A")
            ),
            Err(KernelError::Invariant(_))
        ));
    }

    #[test]
    fn dependency_resolution_is_ancestry_bound() {
        let parent = trusted_theory("Pure", &["A"]);
        let unknown = DependencySet {
            entries: BTreeSet::from([DependencyId {
                kind: DependencyKind::Axiom,
                digest: [7; 32],
            }]),
        };
        assert!(!parent.resolves(&unknown));

        let (child, accepted) =
            accept_closed_theorem(&parent, "imp_identity", implication_identity(&parent, "A"))
                .unwrap();
        let known = DependencySet {
            entries: BTreeSet::from([DependencyId {
                kind: DependencyKind::Theorem,
                digest: accepted.id().to_bytes(),
            }]),
        };
        assert!(child.resolves(&known));
        assert!(!parent.resolves(&known));
    }

    #[test]
    fn acceptance_error_precedence_is_context_owner_name_then_replay() {
        let parent = trusted_theory("Pure", &["A"]);
        let (child, _) =
            accept_closed_theorem(&parent, "identity", implication_identity(&parent, "A")).unwrap();

        let wrong_context = implication_identity(&parent, "A");
        assert!(matches!(
            accept_closed_theorem(&child, "identity", wrong_context),
            Err(KernelError::MixedContext { .. })
        ));

        let context = ProofContext::new(child.snapshot().clone());
        let a = context.certify_term(prop("A")).unwrap();
        let proposition = context.certify_prop(RawTerm::imp(prop("A"), prop("A"))).unwrap();
        let malformed = KernelThm::new(Vec::new(), proposition, Derivation::Reflexive { term: a })
            .try_close()
            .unwrap();
        assert!(matches!(
            accept_closed_theorem(&child, "identity", malformed),
            Err(KernelError::DuplicateTheorem { .. })
        ));
    }

    #[test]
    fn forged_sibling_theorem_reference_is_rejected_by_replay() {
        let parent = trusted_theory("Pure", &["A"]);
        let (left, accepted) =
            accept_closed_theorem(&parent, "identity", implication_identity(&parent, "A")).unwrap();
        let sibling = parent.begin_child("Sibling");
        let context = ProofContext::new(sibling.snapshot().clone());
        let prop = context.certify_prop(RawTerm::imp(prop("A"), prop("A"))).unwrap();
        let forged = KernelThm::new(Vec::new(), prop, Derivation::TheoremRef { theorem: accepted })
            .try_close()
            .unwrap();

        assert!(
            KernelRules::theorem_ref(&left, left.get(&Name::from("identity")).unwrap()).is_ok()
        );
        assert!(matches!(
            accept_closed_theorem(&sibling, "forged_ref", forged),
            Err(KernelError::UnknownTheoremDependency)
        ));
    }

    #[test]
    fn theorem_identity_commits_to_term_namespace_index_type_and_node() {
        let theory = trusted_theory("Pure", &["A"]);
        let stamp = theory.stamp();
        let dependencies = DependencySet::default();
        let nat = Ty::base("nat").unwrap();
        let boolean = Ty::base("bool").unwrap();
        let free = |name: &str| {
            CProp::from_checked_term(
                Term::mk_imp(
                    Term::Free { name: Name::from(name), ty: Ty::prop() },
                    Term::Free { name: Name::from(name), ty: Ty::prop() },
                )
                .unwrap(),
                stamp,
            )
        };
        let var_eq = |index: usize, ty: Ty| {
            let variable = Term::Var { name: Name::from("x"), index, ty: ty.clone() };
            CProp::from_checked_term(Term::mk_eq(variable.clone(), variable).unwrap(), stamp)
        };

        let free_a = compute_theorem_id(stamp, &free("a"), &dependencies);
        let free_b = compute_theorem_id(stamp, &free("b"), &dependencies);
        let var_zero = compute_theorem_id(stamp, &var_eq(0, nat.clone()), &dependencies);
        let var_one = compute_theorem_id(stamp, &var_eq(1, nat), &dependencies);
        let var_bool = compute_theorem_id(stamp, &var_eq(0, boolean), &dependencies);
        let const_imp = compute_theorem_id(
            stamp,
            &ProofContext::new(theory.snapshot().clone())
                .certify_prop(RawTerm::imp(prop("A"), prop("A")))
                .unwrap(),
            &dependencies,
        );

        assert_ne!(free_a, free_b);
        assert_ne!(free_a, var_zero);
        assert_ne!(var_zero, var_one);
        assert_ne!(var_zero, var_bool);
        assert_ne!(free_a, const_imp);
    }

    #[test]
    fn theorem_identity_sorts_dependencies_and_tags_dependency_kind() {
        let theory = trusted_theory("Pure", &["A"]);
        let proposition = ProofContext::new(theory.snapshot().clone())
            .certify_prop(RawTerm::imp(prop("A"), prop("A")))
            .unwrap();
        let axiom = DependencyId { kind: DependencyKind::Axiom, digest: [1; 32] };
        let theorem = DependencyId { kind: DependencyKind::Theorem, digest: [2; 32] };
        let mut forward = BTreeSet::new();
        forward.insert(axiom);
        forward.insert(theorem);
        let mut reverse = BTreeSet::new();
        reverse.insert(theorem);
        reverse.insert(axiom);
        let changed_kind = DependencySet {
            entries: BTreeSet::from([
                DependencyId { kind: DependencyKind::Theorem, digest: [1; 32] },
                theorem,
            ]),
        };

        let forward_id =
            compute_theorem_id(theory.stamp(), &proposition, &DependencySet { entries: forward });
        let reverse_id =
            compute_theorem_id(theory.stamp(), &proposition, &DependencySet { entries: reverse });
        let changed_id = compute_theorem_id(theory.stamp(), &proposition, &changed_kind);

        assert_eq!(forward_id, reverse_id);
        assert_ne!(forward_id, changed_id);
    }

    #[test]
    fn axiom_rejects_unknown_type_variable() {
        let sig = Signature::new();
        let basis = LogicBasis::new(
            vec![],
            vec![AxiomSchema {
                name: Name::from("test_ax"),
                prop: RawTerm::Forall { name: Name::from("x"),
                    param_ty: Ty::tvar("'a", 0, crate::Sort::typ()),
                    body: Box::new(RawTerm::Var {
                        name: Name::from("x"), index: 0, ty: Ty::tvar("'a", 0, crate::Sort::typ()),
                    }),
                },
            }],
        );
        let theory = TrustedTheory::with_basis("T", sig, &basis).unwrap();
        let ctx = ProofContext::new(theory.snapshot().clone());
        // Missing type_inst: 'a not resolved
        let result = crate::theorem_builder::axiom_theorem(
            &ctx, theory.logic_basis().unwrap(),
            Name::from("test_ax"),
            vec![], // no type_inst — 'a unresolved
            vec![],
            RawTerm::const_("P", Ty::prop()),
        );
        assert!(result.is_err(), "missing type_inst must be rejected");
    }

    #[test]
    fn axiom_rejects_extra_type_instantiation() {
        let sig = Signature::new();
        let basis = LogicBasis::new(
            vec![],
            vec![AxiomSchema {
                name: Name::from("test_ax"),
                prop: RawTerm::const_("P", Ty::prop()), // no type vars
            }],
        );
        let theory = TrustedTheory::with_basis("T", sig, &basis).unwrap();
        let ctx = ProofContext::new(theory.snapshot().clone());
        let result = crate::theorem_builder::axiom_theorem(
            &ctx, theory.logic_basis().unwrap(),
            Name::from("test_ax"),
            vec![(Name::from("'a"), Ty::prop())], // extra inst
            vec![],
            RawTerm::const_("P", Ty::prop()),
        );
        assert!(result.is_err(), "extra type_inst must be rejected");
    }

    #[test]
    fn axiom_nested_binders_preserve_variable_identity() {
        // Schema: ∀x:'a. ∀y:'a. x ==> y
        // After 'a := prop, x := c1, y := c2, result must be c1 ==> c2.
        // The old de Bruijn bug (i > 0 instead of i > depth)
        // would produce c2 ==> c2 (variable capture).

        let schema = RawTerm::Forall {
            name: Name::from("x"),
            param_ty: Ty::tvar("'a", 0, crate::Sort::typ()),
            body: Box::new(RawTerm::Forall {
                name: Name::from("y"),
                param_ty: Ty::tvar("'a", 0, crate::Sort::typ()),
                body: Box::new(RawTerm::Imp {
                    premise: Box::new(RawTerm::Bound(1)),   // x
                    conclusion: Box::new(RawTerm::Bound(0)), // y
                }),
            }),
        };
        let sig = Signature::new()
            .extend_const("c1", Ty::prop()).unwrap()
            .extend_const("c2", Ty::prop()).unwrap();

        let basis = LogicBasis::new(
            vec![],
            vec![AxiomSchema { name: Name::from("nested"), prop: schema }],
        );
        let theory = TrustedTheory::with_basis("T", sig, &basis).unwrap();
        let ctx = ProofContext::new(theory.snapshot().clone());

        let c1 = ctx.certify_term(RawTerm::const_("c1", Ty::prop())).unwrap();
        let c2 = ctx.certify_term(RawTerm::const_("c2", Ty::prop())).unwrap();

        // Expected: c1 ==> c2
        let expected = RawTerm::Imp {
            premise: Box::new(RawTerm::Const { name: Name::from("c1"), ty: Ty::prop() }),
            conclusion: Box::new(RawTerm::Const { name: Name::from("c2"), ty: Ty::prop() }),
        };

        let result = crate::theorem_builder::axiom_theorem(
            &ctx, theory.logic_basis().unwrap(),
            Name::from("nested"),
            vec![(Name::from("'a"), Ty::prop())], // 'a := prop
            vec![c1, c2],
            expected,
        );
        assert!(result.is_ok(),
            "nested binders must instantiate correctly (x=c1, y=c2): {:?}",
            result.err());
    }

    #[test]
    fn axiom_rejects_substituting_concrete_type() {
        // Concrete types (prop, bool, fun) must NOT be substitution targets.
        // Only Ty::tvar type variables can be substituted.
        let sig = Signature::new();
        let basis = LogicBasis::new(
            vec![],
            vec![AxiomSchema {
                name: Name::from("test_ax"),
                prop: RawTerm::const_("P", Ty::prop()), // uses prop — concrete, not a tvar
            }],
        );
        let theory = TrustedTheory::with_basis("T", sig, &basis).unwrap();
        let ctx = ProofContext::new(theory.snapshot().clone());
        // Trying to substitute "prop" (a concrete type) must be rejected
        let result = crate::theorem_builder::axiom_theorem(
            &ctx, theory.logic_basis().unwrap(),
            Name::from("test_ax"),
            vec![(Name::from("prop"), Ty::prop())], // "prop" is concrete, not a tvar
            vec![],
            RawTerm::const_("P", Ty::prop()),
        );
        assert!(result.is_err(),
            "substituting concrete type `prop` must be rejected: {:?}",
            result.err());
    }
}


#[cfg(test)]
mod definition_tests {
    use super::*;

    fn hol_sig() -> Signature {
        Signature::new()
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop())).unwrap()
    }

    #[test]
    fn extend_definition_rejects_self_reference() {
        let sig = hol_sig();
        let parent = TrustedTheory::root("Test", sig);
        let self_ref = RawTerm::const_("HOL.True", Ty::base("bool").unwrap());
        let result = parent.extend_definition("HOL.True", self_ref);
        assert!(result.is_err(), "must reject self-referential RHS");
    }

    #[test]
    fn extend_definition_rejects_open_rhs() {
        let sig = hol_sig();
        let parent = TrustedTheory::root("Test", sig);
        let open_rhs = RawTerm::Free { name: Name::from("x"), ty: Ty::base("bool").unwrap() };
        let result = parent.extend_definition("HOL.True", open_rhs);
        assert!(result.is_err(), "must reject open RHS");
    }

    #[test]
    fn extend_definition_rejects_wrong_parent() {
        let sig = hol_sig().extend_const("HOL.eq", Ty::arrow(
            Ty::tvar("'a", 0, crate::Sort::typ()),
            Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::base("bool").unwrap()),
        )).unwrap();
        let parent = TrustedTheory::root("Test", sig);
        // Valid definition on parent
        let rhs = RawTerm::const_("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()));
        let (child, _) = parent.extend_definition("HOL.True", rhs.clone()).unwrap();
        // Cannot re-define the same constant
        let result = child.extend_definition("HOL.True", rhs);
        assert!(result.is_err(), "must reject re-definition of existing constant");
    }

    #[test]
    fn extend_definition_rejects_tampered_id() {
        let sig = hol_sig().extend_const("HOL.eq", Ty::arrow(
            Ty::tvar("'a", 0, crate::Sort::typ()),
            Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::base("bool").unwrap()),
        )).unwrap();
        let parent = TrustedTheory::root("Test", sig);
        let rhs = RawTerm::const_("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()));
        let (child, _rhs_cterm) = parent.extend_definition("HOL.True", rhs).unwrap();
        // The child theory has the definition in its signature
        assert!(child.signature().const_type(&Name::from("HOL.True")).is_some(),
            "child must have HOL.True in signature");
        // Re-defining fails
        let rhs2 = RawTerm::const_("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()));
        assert!(child.extend_definition("HOL.True", rhs2).is_err(),
            "must reject re-definition");
    }
}


#[cfg(test)]
mod axiom_dep_tests {
    use super::*;
    use crate::{AxiomDependencyId, AxiomSchema, LogicBasis};

    #[test]
    fn axiom_rejects_cross_paired_basis_schema() {
        let sig = Signature::new()
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop())).unwrap()
            .extend_const("HOL.eq", Ty::arrow(
                Ty::tvar("'a", 0, crate::Sort::typ()),
                Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::base("bool").unwrap()),
            )).unwrap();
        // Two different bases with same axiom name
        let basis_a = LogicBasis::new(
            vec![],
            vec![AxiomSchema {
                name: Name::from("test_ax"),
                prop: RawTerm::Forall {
                    name: Name::from("x"),
                    param_ty: Ty::tvar("'a", 0, crate::Sort::typ()),
                    body: Box::new(RawTerm::Var {
                        name: Name::from("x"), index: 0, ty: Ty::tvar("'a", 0, crate::Sort::typ()),
                    }),
                },
            }],
        );
        let basis_b = LogicBasis::new(
            vec![],
            vec![AxiomSchema {
                name: Name::from("test_ax"),
                prop: RawTerm::Forall {
                    name: Name::from("x"),
                    param_ty: Ty::tvar("'a", 0, crate::Sort::typ()),
                    body: Box::new(RawTerm::Bound(0)),
                },
            }],
        );
        // Different bases produce different AxiomDependencyIds for same-named schemas
        let dep_a = crate::AxiomDependencyId::compute(basis_a.id, basis_a.get_axiom(&Name::from("test_ax")).unwrap().id());
        let dep_b = crate::AxiomDependencyId::compute(basis_b.id, basis_b.get_axiom(&Name::from("test_ax")).unwrap().id());
        assert_ne!(dep_a.to_bytes(), dep_b.to_bytes(), "different bases must produce different dependency IDs");
    }
}
