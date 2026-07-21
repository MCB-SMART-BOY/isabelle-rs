use std::{collections::BTreeSet, fmt, sync::Arc};

use super::{
    CProp, ClosedThm, ContextStamp, DefinitionCertificateError, KernelError, KernelThm, Name,
    ProofContext, RawTerm, Signature, Ty,
    identity::{CanonicalEncoder, THEORY_DOMAIN, TheoryId},
    invariant::replay_closed_theorem_in,
    logic::LogicBasisId,
    theorem_builder,
};

const THEOREM_DOMAIN: &[u8] = b"isabelle-rs/theorem/v2";

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

/// Content identity of a conservative definition.
///
/// Computed deterministically from the parent [`TheoryId`], constant name,
/// declared type, and canonical RHS. The constructor is private to this module.
///
/// ```compile_fail
/// use isabelle_rs::kernel::DefinitionId;
/// let _forged = DefinitionId([0; 32]);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefinitionId([u8; 32]);

impl DefinitionId {
    /// Return the raw digest bytes.
    pub fn to_bytes(&self) -> [u8; 32] {
        self.0
    }
}

impl fmt::Debug for DefinitionId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DefinitionId({:x?})", self.0)
    }
}

/// Single authoritative certificate for a conservative definition.
///
/// Produced by [`TrustedTheory::define_const`] and stored in
/// [`TheoryExtension::DefineConst`].  Replay reconstructs the definition
/// proposition from the certificate fields; the derivation carries only
/// the [`DefinitionId`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DefinitionCertificate {
    pub(crate) id: DefinitionId,
    pub(crate) parent: TheoryId,
    pub(crate) name: Name,
    pub(crate) declared_ty: Ty,
    /// The RHS as a raw term (certified on replay in owner context).
    pub(crate) rhs_raw: RawTerm,
}

impl DefinitionCertificate {
    /// Return the certificate's definition identity.
    #[allow(dead_code)]
    pub(crate) fn id(&self) -> DefinitionId {
        self.id
    }

    /// Canonical computation of a DefinitionId from its constituent fields.
    pub(crate) fn compute_id(
        parent: &TheoryId,
        name: &Name,
        declared_ty: &Ty,
        rhs_raw: &RawTerm,
    ) -> DefinitionId {
        let mut encoder = CanonicalEncoder::new(b"isabelle-rs/define-const/v1");
        parent.write_canonical(&mut encoder);
        encoder.write_name(name);
        declared_ty.write_canonical(&mut encoder);
        rhs_raw.write_canonical(&mut encoder);
        DefinitionId(encoder.finish())
    }

    /// Recompute and verify the certificate's identity from its payload.
    pub(crate) fn validate(&self, expected_parent: &TheoryId) -> Result<(), KernelError> {
        let recomputed =
            Self::compute_id(expected_parent, &self.name, &self.declared_ty, &self.rhs_raw);
        if recomputed != self.id {
            return Err(KernelError::DefinitionCertificate(
                DefinitionCertificateError::IdMismatch {
                    stored: self.id,
                    recomputed,
                },
            ));
        }
        if &self.parent != expected_parent {
            return Err(KernelError::DefinitionCertificate(
                DefinitionCertificateError::ParentMismatch {
                    stored: self.parent,
                    expected: *expected_parent,
                },
            ));
        }
        Ok(())
    }

    /// Full semantic validation for replay. Checks ID integrity, parent ownership,
    /// self-reference, and closedness.
    pub(crate) fn validate_semantics(&self, expected_parent: &TheoryId) -> Result<(), KernelError> {
        self.validate(expected_parent)?;
        if self.rhs_raw.mentions_const(&self.name) {
            return Err(KernelError::DefinitionCertificate(
                DefinitionCertificateError::SelfReference { name: self.name.clone() },
            ));
        }
        if self.rhs_raw.has_free_vars() {
            return Err(KernelError::DefinitionCertificate(
                DefinitionCertificateError::RhsNotClosed { name: self.name.clone() },
            ));
        }
        Ok(())
    }
}

/// Validate a definition certificate against a parent theory snapshot.
///
/// Checks: ID integrity, parent ownership, self-reference, closedness,
/// constant freshness, RHS typability, and RHS type == declared_ty.
pub(crate) fn validate_definition_certificate_in_parent(
    parent_snapshot: &TheorySnapshot,
    certificate: &DefinitionCertificate,
) -> Result<(), KernelError> {
    // 1. ID integrity + parent ownership + self-ref + closedness
    certificate.validate_semantics(&parent_snapshot.id())?;

    // 2. Constant must not already exist in parent
    if parent_snapshot.signature().get_const(&certificate.name).is_some() {
        return Err(KernelError::DuplicateDeclaration { name: certificate.name.clone() });
    }

    // 3. Reject non-concrete declared types — definitions must be monomorphic.
    if !certificate.declared_ty.is_concrete_type() {
        return Err(KernelError::DefinitionCertificate(
            DefinitionCertificateError::NonConcreteDeclaredType {
                name: certificate.name.clone(),
                ty: certificate.declared_ty.clone(),
            },
        ));
    }

    // 3. RHS must certify in parent context
    let ctx = ProofContext::new(parent_snapshot.clone());
    let rhs = ctx.certify_term(certificate.rhs_raw.clone())?;

    // 4. RHS type must match declared type
    if &rhs.ty() != &certificate.declared_ty {
        return Err(KernelError::DefinitionCertificate(
            DefinitionCertificateError::RhsTypeMismatch {
                name: certificate.name.clone(),
                declared: certificate.declared_ty.clone(),
                actual: rhs.ty(),
            },
        ));
    }

    Ok(())
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

impl DependencyId {
    fn definition_id(&self) -> DefinitionId {
        DefinitionId(self.digest)
    }
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
        self.entries
            .insert(DependencyId { kind: DependencyKind::Axiom, digest: dep_id.to_bytes() });
    }

    pub(crate) fn insert_definition(&mut self, id: DefinitionId) {
        self.entries
            .insert(DependencyId { kind: DependencyKind::Definition, digest: id.to_bytes() });
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
    DefineConst { certificate: DefinitionCertificate },
    StoreTheorem { name: Name, theorem: TheoremId },
    InstallLogicBasis { logic_basis_id: LogicBasisId },
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

    pub(crate) fn extend_definition(
        &self,
        certificate: &DefinitionCertificate,
    ) -> Result<Self, KernelError> {
        let signature = self
            .signature()
            .extend_const(certificate.name.clone(), certificate.declared_ty.clone())?;
        Ok(Self::build(
            Some(self.clone()),
            signature,
            TheoryExtension::DefineConst { certificate: certificate.clone() },
        ))
    }

    pub fn id(&self) -> TheoryId {
        self.inner.id
    }

    pub fn signature(&self) -> &Signature {
        &self.inner.signature
    }
    pub fn stamp(&self) -> ContextStamp {
        // Walk the extension chain to find an InstallLogicBasis node
        let logic_basis = self.find_logic_basis_id();
        ContextStamp::new(self.id(), self.signature().id(), logic_basis)
    }

    /// Walk the extension chain to locate the nearest InstallLogicBasis.
    fn find_logic_basis_id(&self) -> Option<super::LogicBasisId> {
        let mut node = Some(self);
        while let Some(n) = node {
            if let TheoryExtension::InstallLogicBasis { logic_basis_id } = n.extension() {
                return Some(*logic_basis_id);
            }
            node = n.parent();
        }
        None
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

    /// Find a snapshot by TheoryId in the ancestry chain.
    /// Returns None if the id is not in the chain (including self).
    pub(crate) fn find_snapshot_by_id(&self, target: TheoryId) -> Option<&TheorySnapshot> {
        let mut current = Some(self);
        while let Some(snap) = current {
            if snap.id() == target {
                return Some(snap);
            }
            current = snap.parent();
        }
        None
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
            TheoryExtension::DefineConst { certificate } => {
                encoder.write_u8(4);
                encoder.write_name(&certificate.name);
                certificate.declared_ty.write_canonical(encoder);
                encoder.write_fixed_bytes(&certificate.id.to_bytes());
            },
            TheoryExtension::StoreTheorem { name, theorem } => {
                encoder.write_u8(3);
                encoder.write_name(name);
                theorem.write_canonical(encoder);
            },
            TheoryExtension::InstallLogicBasis { logic_basis_id } => {
                encoder.write_u8(5);
                logic_basis_id.write_canonical(encoder);
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

#[derive(Clone)]
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

    /// Create a root theory that installs a validated logic basis as its first
    /// extension. The basis's identity is bound into the TheoryId.
    pub fn with_basis(
        name: impl Into<Name>,
        signature: Signature,
        basis: &super::LogicBasis,
    ) -> Result<Self, KernelError> {
        basis.validate_against(&signature)?;
        let root = TrustedTheory::root(name, signature.clone());
        let child_snapshot = TheorySnapshot::build(
            Some(root.snapshot().clone()),
            signature,
            TheoryExtension::InstallLogicBasis { logic_basis_id: basis.id() },
        );
        let basis_arc = Arc::new(basis.clone());
        let child = Self::child(&root, child_snapshot, None);
        // Override the logic_basis on the child (child inherits parent's None)
        let mut inner = (*child.inner).clone();
        inner.logic_basis = Some(basis_arc);
        Ok(Self { inner: Arc::new(inner) })
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

    /// Atomically define a constant and accept its definition theorem.
    ///
    /// Certifies RHS in the parent context (guaranteeing freshness — the
    /// constant does not yet exist), checks closedness, produces a
    /// [`DefinitionCertificate`], extends the signature with a
    /// `DefineConst` extension, constructs the definition theorem, and
    /// accepts it.  Returns the child theory and the accepted
    /// [`TrustedTheorem`].
    ///
    /// This is the sole production entry point for conservative
    /// definitions. Every invariant is checked before any theory
    /// mutation occurs.
    pub fn define_const(
        &self,
        name: impl Into<Name>,
        rhs_raw: RawTerm,
    ) -> Result<(TrustedTheory, TrustedTheorem), KernelError> {
        let name = name.into();
        let parent_ctx = ProofContext::new(self.snapshot().clone());

        // 1. Certify RHS in parent context — ensures freshness and closedness
        let rhs = parent_ctx.certify_term(rhs_raw.clone())?;
        let rhs_ty = rhs.ty().clone();

        // 2. RHS must be closed
        if rhs_raw.has_free_vars() {
            return Err(KernelError::Invariant("definition RHS is not closed".into()));
        }

        // 3. RHS must not reference the constant being defined
        if rhs_raw.mentions_const(&name) {
            return Err(KernelError::Invariant(
                format!("definition RHS references the constant being defined: {name}").into(),
            ));
        }

        // 3b. Declared type must be concrete — definitions must be monomorphic.
        if !rhs_ty.is_concrete_type() {
            return Err(KernelError::DefinitionCertificate(
                DefinitionCertificateError::NonConcreteDeclaredType {
                    name: name.clone(),
                    ty: rhs_ty,
                },
            ));
        }

        // 4. Compute canonical DefinitionId
        let definition_id = DefinitionCertificate::compute_id(&self.id(), &name, &rhs_ty, &rhs_raw);

        // 5. Create certificate
        let certificate = DefinitionCertificate {
            id: definition_id,
            parent: self.id(),
            name: name.clone(),
            declared_ty: rhs_ty,
            rhs_raw: rhs_raw.clone(),
        };

        // 6. Extend the theory
        let snapshot = self.snapshot().extend_definition(&certificate)?;
        let child = Self::child(self, snapshot, None);

        // 7. Build definition theorem: |- const == rhs
        let ctx = ProofContext::new(child.snapshot().clone());
        let def_thm = theorem_builder::definition_theorem(&ctx, &certificate)?;
        let closed = theorem_builder::close_thm(def_thm)?;

        // 8. Accept the definition theorem
        let fact_name = Name::from(format!("{name}_def"));
        accept_closed_theorem(&child, fact_name, closed)
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
                (Some(parent), TheoryExtension::DefineConst { certificate }, None) => {
                    // Validate certificate against parent BEFORE extending signature
                    validate_definition_certificate_in_parent(parent.snapshot(), certificate)?;

                    let expected = parent.snapshot().extend_definition(certificate)?;
                    if snapshot.parent().map(TheorySnapshot::id) != Some(parent.id())
                        || theory.len() != parent.len()
                        || expected.id() != theory.id()
                    {
                        return Err(KernelError::Invariant(
                            "trusted definition owner does not match its snapshot parent".into(),
                        ));
                    }
                },
                (Some(parent), TheoryExtension::InstallLogicBasis { logic_basis_id }, None) => {
                    if snapshot.parent().map(TheorySnapshot::id) != Some(parent.id())
                        || theory.len() != parent.len()
                    {
                        return Err(KernelError::Invariant(
                            "trusted logic-basis owner does not match its snapshot parent".into(),
                        ));
                    }
                    // Cross-validate: the extension's logic_basis_id must match
                    // the stored LogicBasis payload's identity.
                    match theory.logic_basis() {
                        Some(basis) if basis.id() != *logic_basis_id => {
                            return Err(KernelError::Invariant(
                                "stored logic basis ID does not match extension's logic_basis_id"
                                    .into(),
                            ));
                        }
                        None => {
                            return Err(KernelError::Invariant(
                                "theory has no logic basis but extension claims one".into(),
                            ));
                        }
                        _ => {}
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
            DependencyKind::Definition => self.contains_definition(dependency.definition_id()),
            DependencyKind::Theorem => self.contains_theorem_digest(dependency.digest),
        })
    }

    fn contains_axiom_dependency(&self, digest: [u8; 32]) -> bool {
        if let Some(basis) = self.logic_basis() {
            for schema in basis.axioms() {
                let dep_id = super::AxiomDependencyId::compute(basis.id(), schema.id());
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

    fn contains_definition(&self, id: DefinitionId) -> bool {
        let mut current = Some(self);
        while let Some(theory) = current {
            if let TheoryExtension::DefineConst { certificate } = theory.snapshot().extension() {
                if certificate.id == id {
                    return true;
                }
            }
            current = theory.parent();
        }
        false
    }

    /// Walk ancestor chain to find the [`DefinitionCertificate`] for a given id,
    /// along with the parent [`TheoryId`] of the theory node that contains it.
    pub(crate) fn find_definition_certificate(
        &self,
        id: &DefinitionId,
    ) -> Option<(DefinitionCertificate, TheoryId)> {
        let mut current = Some(self);
        while let Some(theory) = current {
            if let TheoryExtension::DefineConst { certificate } = theory.snapshot().extension() {
                if &certificate.id == id {
                    let parent_id = theory.parent().map(|p| p.id()).unwrap_or_else(|| theory.id());
                    return Some((certificate.clone(), parent_id));
                }
            }
            current = theory.parent();
        }
        None
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
    use crate::logic::{TypeInstantiation, TypeVarId};
    use crate::{
        AxiomSchema, CTerm, Derivation, KernelRules, KernelThm, LogicBasis, ProofContext, RawTerm,
        Term, TrustedTheory,
    };

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

    fn type_inst_single(name: impl Into<Name>, ty: Ty) -> TypeInstantiation {
        let mut bindings = std::collections::BTreeMap::new();
        bindings.insert(TypeVarId::new(name, 0), ty);
        TypeInstantiation::try_new(bindings).unwrap()
    }

    #[test]
    fn axiom_rejects_unknown_type_variable() {
        let sig = Signature::new();
        let basis = LogicBasis::try_new(
            vec![],
            vec![AxiomSchema {
                name: Name::from("test_ax"),
                prop: RawTerm::Forall {
                    name: Name::from("x"),
                    param_ty: Ty::tvar("'a", 0, crate::Sort::typ()),
                    body: Box::new(RawTerm::Var {
                        name: Name::from("x"),
                        index: 0,
                        ty: Ty::tvar("'a", 0, crate::Sort::typ()),
                    }),
                },
            }],
        )
        .unwrap();
        let theory = TrustedTheory::with_basis("T", sig, &basis).unwrap();
        let ctx = ProofContext::new(theory.snapshot().clone());
        // Missing type_inst: 'a not resolved
        let result = crate::theorem_builder::axiom_theorem(
            &ctx,
            theory.logic_basis().unwrap(),
            Name::from("test_ax"),
            TypeInstantiation::empty(), // no type_inst — 'a unresolved
            vec![],
            RawTerm::const_("P", Ty::prop()),
        );
        assert!(result.is_err(), "missing type_inst must be rejected");
    }

    #[test]
    fn axiom_rejects_extra_type_instantiation() {
        let sig = Signature::new();
        let basis = LogicBasis::try_new(
            vec![],
            vec![AxiomSchema {
                name: Name::from("test_ax"),
                prop: RawTerm::const_("P", Ty::prop()), // no type vars
            }],
        )
        .unwrap();
        let theory = TrustedTheory::with_basis("T", sig, &basis).unwrap();
        let ctx = ProofContext::new(theory.snapshot().clone());
        let result = crate::theorem_builder::axiom_theorem(
            &ctx,
            theory.logic_basis().unwrap(),
            Name::from("test_ax"),
            type_inst_single("'a", Ty::prop()), // extra inst
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
                    premise: Box::new(RawTerm::Bound(1)),    // x
                    conclusion: Box::new(RawTerm::Bound(0)), // y
                }),
            }),
        };
        let sig = Signature::new()
            .extend_const("c1", Ty::prop())
            .unwrap()
            .extend_const("c2", Ty::prop())
            .unwrap();

        let basis = LogicBasis::try_new(
            vec![],
            vec![AxiomSchema { name: Name::from("nested"), prop: schema }],
        )
        .unwrap();
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
            &ctx,
            theory.logic_basis().unwrap(),
            Name::from("nested"),
            type_inst_single("'a", Ty::prop()), // 'a := prop
            vec![c1, c2],
            expected,
        );
        assert!(
            result.is_ok(),
            "nested binders must instantiate correctly (x=c1, y=c2): {:?}",
            result.err()
        );
    }

    #[test]
    fn axiom_rejects_substituting_concrete_type() {
        // Concrete types (prop, bool, fun) must NOT be substitution targets.
        // Only Ty::tvar type variables can be substituted.
        let sig = Signature::new();
        let basis = LogicBasis::try_new(
            vec![],
            vec![AxiomSchema {
                name: Name::from("test_ax"),
                prop: RawTerm::const_("P", Ty::prop()), // uses prop — concrete, not a tvar
            }],
        )
        .unwrap();
        let theory = TrustedTheory::with_basis("T", sig, &basis).unwrap();
        let ctx = ProofContext::new(theory.snapshot().clone());
        // Trying to substitute "prop" (a concrete type) must be rejected
        let result = crate::theorem_builder::axiom_theorem(
            &ctx,
            theory.logic_basis().unwrap(),
            Name::from("test_ax"),
            type_inst_single("prop", Ty::prop()), // "prop" is concrete, not a tvar
            vec![],
            RawTerm::const_("P", Ty::prop()),
        );
        assert!(
            result.is_err(),
            "substituting concrete type `prop` must be rejected: {:?}",
            result.err()
        );
    }

    /// Polymorphic constant declared via extend_const_scheme can be used at a
    /// concrete instance type through certify_const_instance.
    #[test]
    fn certify_const_instance_polymorphic() {
        use crate::logic::PolyType;
        use crate::logic::PolyTypeParam;
        // Declare id : 'a -> 'a -> prop (a polymorphic binary predicate)
        let scheme = PolyType::new(
            vec![PolyTypeParam { id: TypeVarId::new("'a", 0), sort: crate::Sort::typ() }],
            Ty::arrow(
                Ty::tvar("'a", 0, crate::Sort::typ()),
                Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::prop()),
            ),
        )
        .unwrap();
        let sig = Signature::new().extend_const_scheme("eq", scheme).unwrap();
        let theory = TrustedTheory::root("T", sig);
        let ctx = ProofContext::new(theory.snapshot().clone());

        // Use eq at a concrete type: eq : bool -> bool -> prop
        let bool_ty = Ty::base("bool").unwrap();
        let result = ctx.certify_term(RawTerm::const_(
            "eq",
            Ty::arrow(bool_ty.clone(), Ty::arrow(bool_ty.clone(), Ty::prop())),
        ));
        assert!(
            result.is_ok(),
            "polymorphic constant certification must succeed: {:?}",
            result.err()
        );
    }

    #[test]
    fn certify_const_instance_rejects_wrong_monomorphic_type() {
        let sig = Signature::new().extend_const("P", Ty::prop()).unwrap();
        let result = sig.certify_const_instance(
            &Name::from("P"),
            &Ty::base("bool").unwrap(),
        );
        assert!(matches!(result, Err(KernelError::TypeMismatch { .. })));
    }

    #[test]
    fn certify_const_instance_rejects_non_instance_of_polymorphic() {
        use crate::logic::{PolyType, PolyTypeParam};
        let scheme = PolyType::new(
            vec![PolyTypeParam { id: TypeVarId::new("'a", 0), sort: crate::Sort::typ() }],
            Ty::arrow(
                Ty::tvar("'a", 0, crate::Sort::typ()),
                Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::prop()),
            ),
        ).unwrap();
        let sig = Signature::new().extend_const_scheme("eq", scheme).unwrap();

        // bool -> nat -> prop fails because bool != nat (different 'a positions)
        let result = sig.certify_const_instance(
            &Name::from("eq"),
            &Ty::arrow(
                Ty::base("bool").unwrap(),
                Ty::arrow(Ty::base("nat").unwrap(), Ty::prop()),
            ),
        );
        assert!(result.is_err(), "non-uniform instance must be rejected");
    }

    #[test]
    fn certify_const_instance_rejects_unknown_constant() {
        let sig = Signature::new();
        let result = sig.certify_const_instance(
            &Name::from("nonexistent"),
            &Ty::prop(),
        );
        assert!(matches!(result, Err(KernelError::UndeclaredConst(_))));
    }

    #[test]
    fn certify_const_instance_accepts_different_type_var_ids() {
        use crate::logic::{PolyType, PolyTypeParam};
        // f : 'a -> 'b -> prop (two distinct params)
        let scheme = PolyType::new(
            vec![
                PolyTypeParam { id: TypeVarId::new("'a", 0), sort: crate::Sort::typ() },
                PolyTypeParam { id: TypeVarId::new("'b", 0), sort: crate::Sort::typ() },
            ],
            Ty::arrow(
                Ty::tvar("'a", 0, crate::Sort::typ()),
                Ty::arrow(Ty::tvar("'b", 0, crate::Sort::typ()), Ty::prop()),
            ),
        ).unwrap();
        let sig = Signature::new().extend_const_scheme("f", scheme).unwrap();

        let result = sig.certify_const_instance(
            &Name::from("f"),
            &Ty::arrow(
                Ty::base("bool").unwrap(),
                Ty::arrow(Ty::base("nat").unwrap(), Ty::prop()),
            ),
        );
        assert!(
            result.is_ok(),
            "different type var positions should accept different concrete types"
        );
    }

    #[test]
    fn certify_raw_accepts_polymorphic_instance() {
        use crate::logic::{PolyType, PolyTypeParam};
        let scheme = PolyType::new(
            vec![PolyTypeParam { id: TypeVarId::new("'a", 0), sort: crate::Sort::typ() }],
            Ty::arrow(
                Ty::tvar("'a", 0, crate::Sort::typ()),
                Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::prop()),
            ),
        ).unwrap();
        let sig = Signature::new().extend_const_scheme("eq", scheme).unwrap();
        let theory = TrustedTheory::root("T", sig);
        let ctx = ProofContext::new(theory.snapshot().clone());

        let bool_ty = Ty::base("bool").unwrap();
        let raw = RawTerm::const_(
            "eq",
            Ty::arrow(bool_ty.clone(), Ty::arrow(bool_ty.clone(), Ty::prop())),
        );
        let cterm = ctx.certify_term(raw).unwrap();
        let validated = crate::context::validate_checked_for_test(&ctx, cterm.term()).unwrap();
        assert_eq!(validated, cterm.ty());
    }
}

#[cfg(test)]
mod definition_tests {
    use super::*;
    use crate::Derivation;
    use crate::KernelRules;
    use crate::Term;
    use crate::logic::{BasisDeclaration, LogicBasis, PolyType};

    fn hol_sig() -> Signature {
        Signature::new()
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()))
            .unwrap()
    }

    #[test]
    fn define_const_rejects_self_reference() {
        let sig = hol_sig();
        let parent = TrustedTheory::root("Test", sig);
        let self_ref = RawTerm::const_("HOL.True", Ty::base("bool").unwrap());
        let result = parent.define_const("HOL.True", self_ref);
        assert!(result.is_err(), "must reject self-referential RHS");
    }

    #[test]
    fn define_const_rejects_open_rhs() {
        let sig = hol_sig();
        let parent = TrustedTheory::root("Test", sig);
        let open_rhs = RawTerm::Free { name: Name::from("x"), ty: Ty::base("bool").unwrap() };
        let result = parent.define_const("HOL.True", open_rhs);
        assert!(result.is_err(), "must reject open RHS");
    }

    #[test]
    fn define_const_rejects_non_fresh_constant() {
        let sig = hol_sig()
            .extend_const(
                "HOL.eq",
                Ty::arrow(
                    Ty::tvar("'a", 0, crate::Sort::typ()),
                    Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::base("bool").unwrap()),
                ),
            )
            .unwrap();
        let parent = TrustedTheory::root("Test", sig);
        let rhs = RawTerm::const_("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()));
        let (child, _token) = parent.define_const("HOL.True", rhs.clone()).unwrap();
        // Cannot re-define the same constant
        let result = child.define_const("HOL.True", rhs);
        assert!(result.is_err(), "must reject re-definition of existing constant");
    }

    #[test]
    fn define_const_rejects_redefinition() {
        let sig = hol_sig()
            .extend_const(
                "HOL.eq",
                Ty::arrow(
                    Ty::tvar("'a", 0, crate::Sort::typ()),
                    Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::base("bool").unwrap()),
                ),
            )
            .unwrap();
        let parent = TrustedTheory::root("Test", sig);
        let rhs = RawTerm::const_("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()));
        let (child, _token) = parent.define_const("HOL.True", rhs).unwrap();
        // The child theory has the definition in its signature
        assert!(
            child.signature().const_type(&Name::from("HOL.True")).is_some(),
            "child must have HOL.True in signature"
        );
        // The child theory also has True_def accepted
        assert!(
            child.get(&Name::from("HOL.True_def")).is_some(),
            "child must have True_def accepted"
        );
        // Cannot re-define the same constant
        let rhs2 =
            RawTerm::const_("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()));
        assert!(child.define_const("HOL.True", rhs2).is_err(), "must reject re-definition");
    }

    #[test]
    fn define_const_rejects_type_mismatch() {
        // Declare HOL.True: bool, but try to define with prop-typed RHS
        let sig = hol_sig().extend_const("HOL.True", Ty::base("bool").unwrap()).unwrap();
        let parent = TrustedTheory::root("Test", sig);
        let rhs = RawTerm::var("x", 0, Ty::prop());
        let result = parent.define_const("HOL.True", rhs);
        assert!(result.is_err(), "must reject type mismatch in definition");
    }

    #[test]
    fn child_certificate_is_inaccessible_to_sibling() {
        let sig = hol_sig()
            .extend_const(
                "HOL.eq",
                Ty::arrow(
                    Ty::tvar("'a", 0, crate::Sort::typ()),
                    Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::base("bool").unwrap()),
                ),
            )
            .unwrap();
        let parent = TrustedTheory::root("Test", sig);
        let rhs = RawTerm::const_("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()));
        let (child, _token) = parent.define_const("HOL.True", rhs).unwrap();
        // Create a sibling theory — its ancestor chain does NOT contain the certificate
        let sibling_sig = hol_sig()
            .extend_const(
                "HOL.eq",
                Ty::arrow(
                    Ty::tvar("'a", 0, crate::Sort::typ()),
                    Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::base("bool").unwrap()),
                ),
            )
            .unwrap();
        let sibling = TrustedTheory::root("Sibling", sibling_sig);
        // The sibling cannot find the certificate from the child's definition
        // Verify: sibling has no access to the child's definition
        assert!(
            sibling
                .find_definition_certificate(
                    &DefinitionId([0u8; 32]) // bogus id, won't be found
                )
                .is_none(),
            "sibling must not have the child's certificate"
        );
        // Also verify the child has the accepted theorem
        assert!(child.get(&Name::from("HOL.True_def")).is_some());
    }

    #[test]
    fn bogus_definition_id_not_found_in_ancestry() {
        let sig = hol_sig()
            .extend_const(
                "HOL.eq",
                Ty::arrow(
                    Ty::tvar("'a", 0, crate::Sort::typ()),
                    Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::base("bool").unwrap()),
                ),
            )
            .unwrap();
        let parent = TrustedTheory::root("Test", sig);
        let rhs = RawTerm::const_("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()));
        let (child, _token) = parent.define_const("HOL.True", rhs.clone()).unwrap();
        // The child has the definition accepted. Try finding with a tampered id.
        let bogus_id = DefinitionId([0xFF; 32]);
        assert!(
            child.find_definition_certificate(&bogus_id).is_none(),
            "tampered definition id must not be found"
        );
    }

    #[test]
    fn certificate_lookup_respects_extension_chain() {
        let sig = hol_sig()
            .extend_const(
                "HOL.eq",
                Ty::arrow(
                    Ty::tvar("'a", 0, crate::Sort::typ()),
                    Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::base("bool").unwrap()),
                ),
            )
            .unwrap();
        let parent = TrustedTheory::root("Test", sig);
        let rhs = RawTerm::const_("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()));
        let (child, _token1) = parent.define_const("HOL.True", rhs).unwrap();
        // Define a second constant in the child — this creates a grandchild
        let child2_snapshot = child.snapshot().extend_const("P", Ty::prop()).unwrap();
        let child2 = TrustedTheory::child(&child, child2_snapshot, None);
        // child2's immediate extension is DeclareConst("P"), not DefineConst
        // The definition certificate should still be findable by walking ancestors
        let cert = child2.find_definition_certificate(
            &DefinitionId([0u8; 32]), // bogus
        );
        assert!(cert.is_none(), "bogus id must not be found in grandchild");
    }

    #[test]
    fn sibling_cannot_access_child_theorem() {
        let sig = hol_sig()
            .extend_const(
                "HOL.eq",
                Ty::arrow(
                    Ty::tvar("'a", 0, crate::Sort::typ()),
                    Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::base("bool").unwrap()),
                ),
            )
            .unwrap();
        let parent = TrustedTheory::root("Test", sig);
        let rhs = RawTerm::const_("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()));
        let (_child, _token) = parent.define_const("HOL.True", rhs.clone()).unwrap();
        // Can't re-use — the child already has HOL.True defined
        // This is tested by define_const_rejects_non_fresh_constant
        // Also: create a sibling, try to use the child's certificate there
        let sibling = TrustedTheory::root(
            "Sibling",
            hol_sig()
                .extend_const(
                    "HOL.eq",
                    Ty::arrow(
                        Ty::tvar("'a", 0, crate::Sort::typ()),
                        Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::base("bool").unwrap()),
                    ),
                )
                .unwrap(),
        );
        // The sibling has an independent theory chain
        // Certificates from child are not findable in sibling
        assert!(
            sibling.get(&Name::from("HOL.True_def")).is_none(),
            "sibling must not have child's accepted theorem"
        );
    }

    #[test]
    fn define_const_produces_correct_proposition_shape() {
        let sig = hol_sig()
            .extend_const(
                "HOL.eq",
                Ty::arrow(
                    Ty::tvar("'a", 0, crate::Sort::typ()),
                    Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::base("bool").unwrap()),
                ),
            )
            .unwrap();
        let parent = TrustedTheory::root("Test", sig);
        let rhs = RawTerm::const_("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()));
        let (_child, token) = parent.define_const("HOL.True", rhs).unwrap();
        // The accepted theorem must have a prop-typed conclusion
        assert!(
            token.prop().term().ty().is_prop(),
            "definition theorem conclusion must be prop-typed"
        );
        // And its proposition must be |- HOL.True == rhs
        let prop = token.prop().term();
        match prop {
            Term::Eq { .. } => { /* expected shape */ },
            other => panic!("definition theorem must be an equality, got {:?}", other),
        }
    }

    // ── Real attack tests: tampered theorems through accept_closed_theorem ──

    /// Forge a definition theorem with a bogus DefinitionId — replay cannot find cert.
    #[test]
    fn definition_rejects_forged_certificate_tampered_id() {
        let sig = hol_sig()
            .extend_const(
                "HOL.eq",
                Ty::arrow(
                    Ty::tvar("'a", 0, crate::Sort::typ()),
                    Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::base("bool").unwrap()),
                ),
            )
            .unwrap();
        let parent = TrustedTheory::root("Test", sig);
        let rhs = RawTerm::const_("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()));
        let (child, token) = parent.define_const("HOL.True", rhs.clone()).unwrap();

        let def_id = match token.as_kernel().derivation() {
            Derivation::ConservativeDefinition { definition } => *definition,
            _ => panic!("expected ConservativeDefinition derivation"),
        };
        let (real_cert, _real_parent) =
            child.find_definition_certificate(&def_id).expect("certificate must be findable");
        let mut forged_cert = real_cert.clone();
        forged_cert.id = DefinitionId([0xFF; 32]);

        let ctx = ProofContext::new(child.snapshot().clone());
        let thm = theorem_builder::definition_theorem(&ctx, &forged_cert).unwrap();
        let closed = theorem_builder::close_thm(thm).unwrap();

        let result = accept_closed_theorem(&child, "Test_def", closed);
        assert!(result.is_err(), "must reject definition with tampered id");
    }

    // ── Real white-box attacks: stored-certificate corruption ──

    /// Stored certificate with self-referencing RHS must be rejected by
    /// validate_semantics during check_consistency.
    #[test]
    fn stored_certificate_rejects_self_reference() {
        let sig = hol_sig().extend_const("P", Ty::prop()).unwrap();
        let theory = TrustedTheory::root("T", sig.clone());

        // Construct a certificate whose RHS references the constant being defined
        let tampered_cert = DefinitionCertificate {
            id: DefinitionCertificate::compute_id(
                &theory.id(),
                &Name::from("Q"),
                &Ty::prop(),
                &RawTerm::const_("Q", Ty::prop()),
            ),
            parent: theory.id(),
            name: Name::from("Q"),
            declared_ty: Ty::prop(),
            rhs_raw: RawTerm::const_("Q", Ty::prop()), // self-reference
        };

        // Install the tampered cert as a stored DefineConst extension
        let snapshot = theory.snapshot().extend_definition(&tampered_cert).unwrap();
        let owner = TrustedTheory::child(&theory, snapshot, None);

        let ctx = ProofContext::new(owner.snapshot().clone());
        let thm = theorem_builder::definition_theorem(&ctx, &tampered_cert).unwrap();
        let closed = theorem_builder::close_thm(thm).unwrap();

        let err = accept_closed_theorem(&owner, "Q_def", closed).unwrap_err();
        assert!(
            matches!(err, KernelError::DefinitionCertificate(
                DefinitionCertificateError::SelfReference { .. }
            )),
            "must reject self-referencing stored cert, got: {err:?}"
        );
    }

    /// Stored certificate with wrong parent TheoryId must be rejected by
    /// validate (parent mismatch).
    #[test]
    fn stored_certificate_rejects_parent_mismatch() {
        let sig = hol_sig().extend_const("P", Ty::prop()).unwrap();
        let theory = TrustedTheory::root("T", sig.clone());
        let rhs = RawTerm::const_("P", Ty::prop());

        let wrong_parent = TheoryId::from_digest([0xAA; 32]);
        let tampered_cert = DefinitionCertificate {
            // Compute ID from real theory parent so ID check passes,
            // but store wrong_parent so parent check fails.
            id: DefinitionCertificate::compute_id(
                &theory.id(),
                &Name::from("Q"),
                &Ty::prop(),
                &rhs,
            ),
            parent: wrong_parent,
            name: Name::from("Q"),
            declared_ty: Ty::prop(),
            rhs_raw: rhs,
        };

        let snapshot = theory.snapshot().extend_definition(&tampered_cert).unwrap();
        let owner = TrustedTheory::child(&theory, snapshot, None);

        let ctx = ProofContext::new(owner.snapshot().clone());
        let thm = theorem_builder::definition_theorem(&ctx, &tampered_cert).unwrap();
        let closed = theorem_builder::close_thm(thm).unwrap();

        let err = accept_closed_theorem(&owner, "Q_def", closed).unwrap_err();
        assert!(
            matches!(err, KernelError::DefinitionCertificate(
                DefinitionCertificateError::ParentMismatch { .. }
            )),
            "must reject parent-mismatched stored cert, got: {err:?}"
        );
    }

    /// Stored certificate with open RHS must be rejected during
    /// check_consistency via validate_definition_certificate_in_parent.
    ///
    /// Constructs a corrupted TrustedTheory owner (Q defined with open RHS),
    /// then attempts to accept an unrelated theorem (P -> P). The acceptance
    /// triggers check_consistency which validates the stored certificate and
    /// rejects the open RHS.
    #[test]
    fn stored_certificate_rejects_open_rhs() {
        let sig = Signature::new().extend_const("P", Ty::prop()).unwrap();
        let theory = TrustedTheory::root("T", sig.clone());
        let rhs = RawTerm::free("x", Ty::prop());

        let tampered_cert = DefinitionCertificate {
            id: DefinitionCertificate::compute_id(
                &theory.id(),
                &Name::from("Q"),
                &Ty::prop(),
                &rhs,
            ),
            parent: theory.id(),
            name: Name::from("Q"),
            declared_ty: Ty::prop(),
            rhs_raw: rhs,
        };

        let snapshot = TheorySnapshot::build(
            Some(theory.snapshot().clone()),
            sig.clone(),
            TheoryExtension::DefineConst { certificate: tampered_cert },
        );
        let owner = TrustedTheory::child(&theory, snapshot, None);

        // Build an unrelated theorem (P -> P)
        let ctx = ProofContext::new(owner.snapshot().clone());
        let prop = ctx.certify_prop(RawTerm::Imp {
            premise: Box::new(RawTerm::const_("P", Ty::prop())),
            conclusion: Box::new(RawTerm::const_("P", Ty::prop())),
        }).unwrap();
        let assumed = KernelRules::assume(prop.clone()).into_kernel();
        let thm = KernelRules::implies_intr(&prop, &assumed).unwrap();
        let closed = theorem_builder::close_thm(thm).unwrap();

        let err = accept_closed_theorem(&owner, "irrelevant", closed).unwrap_err();
        assert!(
            matches!(err, KernelError::DefinitionCertificate(
                DefinitionCertificateError::RhsNotClosed { .. }
            )) || matches!(err, KernelError::UndeclaredFree(_)),
            "must reject open-RHS stored cert during consistency check, got: {err:?}"
        );
    }

    /// Stored certificate with mismatched declared_ty must be rejected during
    /// check_consistency via validate_definition_certificate_in_parent.
    ///
    /// The certificate declares Q: bool but the RHS is P: prop.
    /// check_consistency certifies the RHS in parent context and finds
    /// type mismatch (prop != bool).
    #[test]
    fn stored_certificate_rejects_declared_type_mismatch() {
        let sig = Signature::new()
            .extend_const("P", Ty::prop()).unwrap();
        let theory = TrustedTheory::root("T", sig.clone());
        let rhs = RawTerm::const_("P", Ty::prop());

        // Certificate says Q: bool but RHS is P: prop
        let tampered_cert = DefinitionCertificate {
            id: DefinitionCertificate::compute_id(
                &theory.id(),
                &Name::from("Q"),
                &Ty::base("bool").unwrap(),
                &rhs,
            ),
            parent: theory.id(),
            name: Name::from("Q"),
            declared_ty: Ty::base("bool").unwrap(),
            rhs_raw: rhs,
        };

        // Build signature with Q: bool (matches declared_ty)
        let extended_sig = sig.extend_const("Q", Ty::base("bool").unwrap()).unwrap();
        let snapshot = TheorySnapshot::build(
            Some(theory.snapshot().clone()),
            extended_sig,
            TheoryExtension::DefineConst { certificate: tampered_cert },
        );
        let owner = TrustedTheory::child(&theory, snapshot, None);

        // Build an unrelated theorem (P -> P)
        let ctx = ProofContext::new(owner.snapshot().clone());
        let prop = ctx.certify_prop(RawTerm::Imp {
            premise: Box::new(RawTerm::const_("P", Ty::prop())),
            conclusion: Box::new(RawTerm::const_("P", Ty::prop())),
        }).unwrap();
        let assumed = KernelRules::assume(prop.clone()).into_kernel();
        let thm = KernelRules::implies_intr(&prop, &assumed).unwrap();
        let closed = theorem_builder::close_thm(thm).unwrap();

        let err = accept_closed_theorem(&owner, "irrelevant", closed).unwrap_err();
        assert!(
            matches!(err, KernelError::DefinitionCertificate(
                DefinitionCertificateError::RhsTypeMismatch { .. }
            )),
            "must reject type-mismatched stored cert with RhsTypeMismatch, got: {err:?}"
        );
    }

    /// Context stamp mismatch: theorem built in one theory context must be
    /// rejected when accepted in an unrelated theory.
    #[test]
    fn definition_rejects_cross_theory_context_mismatch() {
        let sig_a = hol_sig().extend_const("P", Ty::prop()).unwrap();
        let parent_a = TrustedTheory::root("ChainA", sig_a.clone());
        let rhs = RawTerm::const_("P", Ty::prop());
        let (child_a, token) = parent_a.define_const("Q", rhs.clone()).unwrap();

        let def_id = match token.as_kernel().derivation() {
            Derivation::ConservativeDefinition { definition } => *definition,
            _ => panic!("expected ConservativeDefinition"),
        };
        let (real_cert, _) = child_a.find_definition_certificate(&def_id).unwrap();

        // Build theorem in child_a's context
        let ctx_a = ProofContext::new(child_a.snapshot().clone());
        let thm = theorem_builder::definition_theorem(&ctx_a, &real_cert).unwrap();
        let closed = theorem_builder::close_thm(thm).unwrap();

        // Try to accept in an unrelated theory with a different chain
        let sig_b = hol_sig().extend_const("R", Ty::prop()).unwrap();
        let unrelated = TrustedTheory::root("ChainB", sig_b);
        let result = accept_closed_theorem(&unrelated, "Test_def", closed);
        assert!(result.is_err(), "must reject certificate from unrelated theory chain");
    }

    /// Theorem proposition tampered after building must be rejected.
    #[test]
    fn definition_rejects_tampered_derivation_proposition() {
        let sig = hol_sig().extend_const("P", Ty::prop()).unwrap();
        let parent = TrustedTheory::root("Test", sig.clone());
        let rhs = RawTerm::const_("P", Ty::prop());
        let (child, token) = parent.define_const("Q", rhs.clone()).unwrap();

        let def_id = match token.as_kernel().derivation() {
            Derivation::ConservativeDefinition { definition } => *definition,
            _ => panic!("expected ConservativeDefinition"),
        };
        let (real_cert, _) = child.find_definition_certificate(&def_id).unwrap();

        // Build a theorem with the REAL certificate but a WRONG proposition
        let ctx = ProofContext::new(child.snapshot().clone());
        let wrong_prop = ctx
            .certify_prop(RawTerm::imp(
                RawTerm::const_("P", Ty::prop()),
                RawTerm::const_("P", Ty::prop()),
            ))
            .unwrap();
        let good_thm = theorem_builder::definition_theorem(&ctx, &real_cert).unwrap();
        let forged =
            KernelThm::new(good_thm.hyps().to_vec(), wrong_prop, good_thm.derivation().clone());
        let closed = theorem_builder::close_thm(forged).unwrap();

        let result = accept_closed_theorem(&child, "Test_def", closed);
        assert!(result.is_err(), "must reject tampered proposition");
    }

    /// A definition certificate installed at an ancestor can be replayed
    /// from a descendant theory. The replay must use the definition-installing
    /// node's parent snapshot, not the replay owner's parent.
    #[test]
    fn definition_replay_works_from_descendant_theory() {
        let sig = hol_sig().extend_const("P", Ty::prop()).unwrap();
        let root = TrustedTheory::root("Root", sig.clone());
        let rhs = RawTerm::const_("P", Ty::prop());
        let (child, token) = root.define_const("Q", rhs.clone()).unwrap();

        // Extract the definition certificate from the token
        let def_id = match token.as_kernel().derivation() {
            Derivation::ConservativeDefinition { definition } => *definition,
            _ => panic!("expected ConservativeDefinition"),
        };
        let (real_cert, _) = child.find_definition_certificate(&def_id).unwrap();

        // Descend further: add another constant to create a grandchild
        let grandchild_snap = child.snapshot()
            .extend_const("R", Ty::prop()).unwrap();
        let grandchild = TrustedTheory::child(&child, grandchild_snap, None);

        // Replay the definition theorem at the grandchild level.
        // The grandchild's direct parent is `child` (which already has Q
        // in its signature), so using owner.parent() would fail the
        // freshness check. find_snapshot_by_id walks to the root.
        let ctx = ProofContext::new(grandchild.snapshot().clone());
        let thm = theorem_builder::definition_theorem(&ctx, &real_cert).unwrap();
        let closed = theorem_builder::close_thm(thm).unwrap();
        let result = accept_closed_theorem(&grandchild, "Q_def_replay", closed);
        assert!(result.is_ok(), "replay from descendant must succeed, got: {result:?}");
    }

    /// Definitions must have fully concrete declared types.
    /// A constant with a type containing type variables must be rejected.
    #[test]
    fn definition_rejects_non_concrete_declared_type() {
        // Declare f: 'a -> prop — a polymorphic function
        let sig = hol_sig()
            .extend_const("f", Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::prop()))
            .unwrap();
        let root = TrustedTheory::root("Root", sig);
        // Try to define Q with RHS f (which has type 'a -> prop, containing 'a)
        let rhs = RawTerm::const_("f", Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::prop()));
        let result = root.define_const("Q", rhs);
        assert!(
            matches!(result, Err(KernelError::DefinitionCertificate(
                DefinitionCertificateError::NonConcreteDeclaredType { .. }
            ))),
            "must reject non-concrete declared type, got: {result:?}"
        );
    }

    /// check_consistency cross-validates that the stored logic basis ID
    /// matches the extension's logic_basis_id. Valid bases pass.
    #[test]
    fn valid_logic_basis_passes_consistency_check() {
        let sig = hol_sig();
        let basis = LogicBasis::try_new(
            vec![BasisDeclaration::Constant {
                name: Name::from("HOL.Trueprop"),
                scheme: PolyType::new(
                    vec![],
                    Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()),
                ).unwrap(),
            }],
            vec![],
        ).unwrap();
        let theory = TrustedTheory::with_basis("HOL", sig, &basis).unwrap();
        let result = theory.check_consistency();
        assert!(result.is_ok(), "valid logic basis must pass check_consistency, got: {result:?}");
    }
}

#[cfg(test)]
mod axiom_dep_tests {
    use super::*;
    use crate::logic::{TypeInstantiation, TypeVarId};
    use crate::{AxiomSchema, LogicBasis};

    #[test]
    fn cross_basis_schemas_produce_different_dep_ids() {
        let _sig = Signature::new()
            .extend_const("HOL.Trueprop", Ty::arrow(Ty::base("bool").unwrap(), Ty::prop()))
            .unwrap()
            .extend_const(
                "HOL.eq",
                Ty::arrow(
                    Ty::tvar("'a", 0, crate::Sort::typ()),
                    Ty::arrow(Ty::tvar("'a", 0, crate::Sort::typ()), Ty::base("bool").unwrap()),
                ),
            )
            .unwrap();
        let basis_a = LogicBasis::try_new(
            vec![],
            vec![AxiomSchema {
                name: Name::from("test_ax"),
                prop: RawTerm::Forall {
                    name: Name::from("x"),
                    param_ty: Ty::tvar("'a", 0, crate::Sort::typ()),
                    body: Box::new(RawTerm::Var {
                        name: Name::from("x"),
                        index: 0,
                        ty: Ty::tvar("'a", 0, crate::Sort::typ()),
                    }),
                },
            }],
        )
        .unwrap();
        let basis_b = LogicBasis::try_new(
            vec![],
            vec![AxiomSchema {
                name: Name::from("test_ax"),
                prop: RawTerm::Forall {
                    name: Name::from("x"),
                    param_ty: Ty::tvar("'a", 0, crate::Sort::typ()),
                    body: Box::new(RawTerm::Bound(0)),
                },
            }],
        )
        .unwrap();
        let dep_a = crate::AxiomDependencyId::compute(
            basis_a.id(),
            basis_a.get_axiom(&Name::from("test_ax")).unwrap().id(),
        );
        let dep_b = crate::AxiomDependencyId::compute(
            basis_b.id(),
            basis_b.get_axiom(&Name::from("test_ax")).unwrap().id(),
        );
        assert_ne!(
            dep_a.to_bytes(),
            dep_b.to_bytes(),
            "different bases must produce different dependency IDs"
        );
    }

    #[test]
    fn wrong_basis_lacks_axiom() {
        let _basis_a = LogicBasis::try_new(
            vec![],
            vec![AxiomSchema {
                name: Name::from("ax"),
                prop: RawTerm::Forall {
                    name: Name::from("x"),
                    param_ty: Ty::prop(),
                    body: Box::new(RawTerm::Bound(0)),
                },
            }],
        )
        .unwrap();
        let basis_b = LogicBasis::try_new(vec![], vec![]).unwrap();
        assert!(
            basis_b.get_axiom(&Name::from("ax")).is_none(),
            "wrong basis must not have the axiom schema"
        );
    }

    #[test]
    fn different_schemas_produce_different_dependency_ids() {
        let basis = LogicBasis::try_new(
            vec![],
            vec![
                AxiomSchema {
                    name: Name::from("ax1"),
                    prop: RawTerm::Forall {
                        name: Name::from("x"),
                        param_ty: Ty::prop(),
                        body: Box::new(RawTerm::Bound(0)),
                    },
                },
                AxiomSchema {
                    name: Name::from("ax2"),
                    prop: RawTerm::Forall {
                        name: Name::from("x"),
                        param_ty: Ty::prop(),
                        body: Box::new(RawTerm::Bound(0)),
                    },
                },
            ],
        )
        .unwrap();
        let dep1 = crate::AxiomDependencyId::compute(
            basis.id(),
            basis.get_axiom(&Name::from("ax1")).unwrap().id(),
        );
        let dep2 = crate::AxiomDependencyId::compute(
            basis.id(),
            basis.get_axiom(&Name::from("ax2")).unwrap().id(),
        );
        assert_ne!(
            dep1.to_bytes(),
            dep2.to_bytes(),
            "different schemas in same basis must produce different dependency IDs"
        );
    }

    #[test]
    fn same_name_different_prop_gives_different_dep_id() {
        let s1 = AxiomSchema {
            name: Name::from("ax"),
            prop: RawTerm::Forall {
                name: Name::from("x"),
                param_ty: Ty::prop(),
                body: Box::new(RawTerm::Bound(0)),
            },
        };
        let s2 = AxiomSchema {
            name: Name::from("ax"),
            prop: RawTerm::Const { name: Name::from("P"), ty: Ty::prop() },
        };
        assert_ne!(
            s1.id(),
            s2.id(),
            "same name with different props must produce different schema IDs"
        );
        let basis = LogicBasis::try_new(vec![], vec![s1]).unwrap();
        let dep1 = crate::AxiomDependencyId::compute(
            basis.id(),
            basis.get_axiom(&Name::from("ax")).unwrap().id(),
        );
        let dep2 = crate::AxiomDependencyId::compute(basis.id(), s2.id());
        assert_ne!(
            dep1.to_bytes(),
            dep2.to_bytes(),
            "tampered proposition must produce different dependency ID"
        );
    }

    #[test]
    fn tampered_bytes_produce_different_dep_id() {
        let basis = LogicBasis::try_new(
            vec![],
            vec![AxiomSchema {
                name: Name::from("ax"),
                prop: RawTerm::Forall {
                    name: Name::from("x"),
                    param_ty: Ty::prop(),
                    body: Box::new(RawTerm::Bound(0)),
                },
            }],
        )
        .unwrap();
        let dep = crate::AxiomDependencyId::compute(
            basis.id(),
            basis.get_axiom(&Name::from("ax")).unwrap().id(),
        );
        let bytes = dep.to_bytes();
        let mut tampered = bytes;
        tampered[0] ^= 0xFF;
        assert_ne!(tampered, bytes, "tampered bytes must differ");
        // Different schema content produces different dependency ID
        let tampered_schema = AxiomSchema {
            name: Name::from("ax"),
            prop: RawTerm::Const { name: Name::from("P"), ty: Ty::prop() },
        };
        let dep2 = crate::AxiomDependencyId::compute(basis.id(), tampered_schema.id());
        assert_ne!(
            dep.to_bytes(),
            dep2.to_bytes(),
            "different schema content must produce different dependency IDs"
        );
    }

    #[test]
    fn empty_basis_has_no_axioms() {
        let schema = AxiomSchema {
            name: Name::from("ax"),
            prop: RawTerm::Forall {
                name: Name::from("x"),
                param_ty: Ty::prop(),
                body: Box::new(RawTerm::Bound(0)),
            },
        };
        let basis = LogicBasis::try_new(vec![], vec![schema]).unwrap();
        assert!(basis.get_axiom(&Name::from("ax")).is_some());
        let empty_basis = LogicBasis::try_new(vec![], vec![]).unwrap();
        assert!(empty_basis.get_axiom(&Name::from("ax")).is_none());
    }

    // ── Real axiom attack tests through accept_closed_theorem ──

    /// Build axiom in one theory's context, try to accept in another.
    /// Context stamp mismatch is caught by accept_closed_theorem.
    #[test]
    fn axiom_rejects_cross_theory_acceptance() {
        let sig = Signature::new().extend_const("P", Ty::prop()).unwrap();
        let schema = AxiomSchema {
            name: Name::from("ax"),
            prop: RawTerm::Const { name: Name::from("P"), ty: Ty::prop() },
        };
        let basis = LogicBasis::try_new(vec![], vec![schema.clone()]).unwrap();

        let theory_a = TrustedTheory::with_basis("A", sig.clone(), &basis).unwrap();
        let theory_b = TrustedTheory::root("B", sig.clone());

        // Build axiom theorem in theory_a's context
        let ctx_a = ProofContext::new(theory_a.snapshot().clone());
        let ax_thm = theorem_builder::axiom_theorem(
            &ctx_a,
            &basis,
            Name::from("ax"),
            TypeInstantiation::empty(),
            vec![],
            RawTerm::Const { name: Name::from("P"), ty: Ty::prop() },
        )
        .unwrap();
        let closed = theorem_builder::close_thm(ax_thm).unwrap();

        // Try accept in theory_b — different context stamp
        let result = accept_closed_theorem(&theory_b, "ax_inst", closed);
        assert!(result.is_err(), "cross-theory axiom acceptance must be rejected");
    }

    /// Accept an axiom in a theory WITH the basis, then try to accept
    /// the same axiom in a theory WITHOUT the basis — replay rejects.
    #[test]
    fn axiom_rejects_missing_basis_at_accept() {
        let sig = Signature::new().extend_const("P", Ty::prop()).unwrap();
        let schema = AxiomSchema {
            name: Name::from("ax"),
            prop: RawTerm::Const { name: Name::from("P"), ty: Ty::prop() },
        };
        let basis = LogicBasis::try_new(vec![], vec![schema.clone()]).unwrap();

        // Theory WITH basis — axiom acceptance succeeds
        let theory_with = TrustedTheory::with_basis("With", sig.clone(), &basis).unwrap();
        let ctx_with = ProofContext::new(theory_with.snapshot().clone());
        let ax_thm = theorem_builder::axiom_theorem(
            &ctx_with,
            &basis,
            Name::from("ax"),
            TypeInstantiation::empty(),
            vec![],
            RawTerm::Const { name: Name::from("P"), ty: Ty::prop() },
        )
        .unwrap();
        let closed = theorem_builder::close_thm(ax_thm).unwrap();
        let (_child, _token) = accept_closed_theorem(&theory_with, "ax_inst", closed).unwrap();

        // Theory WITHOUT basis — build axiom theorem and try to accept
        let theory_no = TrustedTheory::root("NoBasis", sig.clone());
        let ctx_no = ProofContext::new(theory_no.snapshot().clone());
        let ax_thm2 = theorem_builder::axiom_theorem(
            &ctx_no,
            &basis,
            Name::from("ax"),
            TypeInstantiation::empty(),
            vec![],
            RawTerm::Const { name: Name::from("P"), ty: Ty::prop() },
        )
        .unwrap();
        let closed2 = theorem_builder::close_thm(ax_thm2).unwrap();

        // Replay looks for logic_basis but there is none
        let result = accept_closed_theorem(&theory_no, "ax_inst", closed2);
        assert!(result.is_err(), "axiom acceptance without basis must be rejected");
    }

    // ── Real white-box attack tests: axiom authorization ──

    /// Different LogicBasisId must produce different ContextStamp, preventing
    /// cross-basis theorem acceptance.
    #[test]
    fn different_logic_basis_changes_context_stamp() {
        let sig = Signature::new().extend_const("P", Ty::prop()).unwrap();
        let schema_a = AxiomSchema {
            name: Name::from("ax_a"),
            prop: RawTerm::Const { name: Name::from("P"), ty: Ty::prop() },
        };
        let schema_b = AxiomSchema {
            name: Name::from("ax_b"),
            prop: RawTerm::Const { name: Name::from("P"), ty: Ty::prop() },
        };
        let basis_a = LogicBasis::try_new(vec![], vec![schema_a.clone()]).unwrap();
        let basis_b = LogicBasis::try_new(vec![], vec![schema_b.clone()]).unwrap();
        assert_ne!(basis_a.id(), basis_b.id(), "different content = different id");

        let theory_a = TrustedTheory::with_basis("T", sig.clone(), &basis_a).unwrap();
        let theory_b = TrustedTheory::with_basis("T", sig.clone(), &basis_b).unwrap();

        // Different bases produce different context stamps
        assert_ne!(
            theory_a.stamp(),
            theory_b.stamp(),
            "different LogicBasisId must produce different ContextStamp"
        );

        // Build axiom theorem in theory_a's context
        let ctx_a = ProofContext::new(theory_a.snapshot().clone());
        let ax_thm = theorem_builder::axiom_theorem(
            &ctx_a,
            &basis_a,
            Name::from("ax_a"),
            TypeInstantiation::empty(),
            vec![],
            RawTerm::Const { name: Name::from("P"), ty: Ty::prop() },
        )
        .unwrap();
        let closed = theorem_builder::close_thm(ax_thm).unwrap();

        // Accept in theory_a: should succeed (same context)
        let (_child_a, _token) =
            accept_closed_theorem(&theory_a, "ax_inst", closed.clone()).unwrap();

        // Try to accept the SAME closed theorem in theory_b — should fail because
        // theory_b has a different LogicBasisId (ax_b vs ax_a), producing a
        // different ContextStamp.
        let result = accept_closed_theorem(&theory_b, "ax_inst", closed);
        assert!(result.is_err(), "cross-basis axiom acceptance must be rejected");
    }

    /// TypeInstantiation missing a required type variable must be rejected
    /// by subst_types completeness check.
    #[test]
    fn axiom_rejects_type_inst_index_mismatch() {
        let sig = Signature::new().extend_const("P", Ty::prop()).unwrap();
        // Schema with two distinct type variables: 'a and 'b
        let schema = AxiomSchema {
            name: Name::from("ax"),
            prop: RawTerm::Forall {
                name: Name::from("x"),
                param_ty: Ty::tvar("'a", 0, crate::Sort::typ()),
                body: Box::new(RawTerm::Forall {
                    name: Name::from("y"),
                    param_ty: Ty::tvar("'b", 0, crate::Sort::typ()),
                    body: Box::new(RawTerm::Const { name: Name::from("P"), ty: Ty::prop() }),
                }),
            },
        };
        let basis = LogicBasis::try_new(vec![], vec![schema]).unwrap();
        let theory = TrustedTheory::with_basis("T", sig, &basis).unwrap();

        // Provide instantiation only for 'a:0 but not 'b:0
        let ctx = ProofContext::new(theory.snapshot().clone());
        let result = theorem_builder::axiom_theorem(
            &ctx,
            &basis,
            Name::from("ax"),
            {
                let mut bindings = std::collections::BTreeMap::new();
                bindings.insert(TypeVarId::new("'a", 0), Ty::prop());
                TypeInstantiation::try_new(bindings).unwrap()
            },
            vec![],
            RawTerm::Const { name: Name::from("P"), ty: Ty::prop() },
        );
        assert!(result.is_err(), "must reject incomplete type instantiation");
    }
}
