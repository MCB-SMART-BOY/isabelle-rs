//! Private proof binders are not real theorem hypotheses. Only a checked,
//! completely closed binder tree can materialize an ordinary theorem.
mod check;
mod composition;
mod composition_assumption;
mod composition_beta;
mod composition_flatten;
mod composition_lift;
pub use composition::{CompositionCandidate, CompositionFlags, CompositionOptions};
mod composition_env;
mod composition_flex;
mod composition_index;
pub(crate) mod export;
mod inspect;
mod lower;
mod permutation;
mod scope_lower;
mod source_instantiate;
mod source_normalize;
mod source_parameters;
mod terms;
mod transform;
pub(crate) use composition::{ResolutionReplay, replay_eq_assumption, replay_exact_resolution};
pub(crate) use composition_assumption::{AssumptionReplay, replay_assumption};
pub(crate) use composition_index::replay_index_rename;
pub(crate) use composition_lift::replay_lift_rule;
pub(crate) use permutation::{replay_permutation, replay_rotation};
pub(crate) use source_instantiate::replay_source_instantiation;
pub(crate) use source_parameters::collect_lexical_frees;
pub(crate) use terms::visit_free_variables;

use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    sync::Arc,
};

use crate::obligations::ProofPayload;
use crate::{
    Derivation, KernelError, KernelRules, KernelThm, Name, ProofContext, Sort, Term, TrustedTheory,
    Ty,
};

/// Invalid scoped proof data is user-fixable; it never authorizes a theorem.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum BoundProofError {
    /// A de Bruijn distance exceeds the representation.
    #[error("proof binder index overflow")]
    IndexOverflow,
    /// A proof refers to a slot outside its lexical scope.
    #[error("proof hypothesis slot {slot} is outside depth {depth}")]
    UnboundHypothesis { slot: usize, depth: usize },
    /// The requested equality is not a residual pair in this exact theorem.
    #[error("flex pair {slot} is outside the {pairs} recorded residual pairs")]
    UnboundFlexPair { slot: usize, pairs: usize },
    /// A lowered premise cannot obtain a real source hypothesis.
    #[error("source hypothesis is absent from the proof binder scope")]
    MissingHypothesis,
    /// A leaf is not an exact authorized occurrence in the replayed source.
    #[error("proof leaf {leaf} is not an authorized source occurrence")]
    UnauthorizedLeaf { leaf: usize },
    /// A local leaf instance does not cover the original typed parameters exactly.
    #[error("proof leaf {leaf} has an invalid typed local instance")]
    InvalidLeafInstance { leaf: usize },
    /// A source operation still needs a class, flex, or staged certificate.
    #[error("sort stripping requires an implemented certificate for {operation}")]
    UnsupportedSortExportVariant { operation: &'static str },
    /// The unchanged prefix cannot exceed the number of outer premises.
    #[error("fixed premise index {fixed} exceeds {nprems} outer premises")]
    FixedPremiseOutOfRange { fixed: usize, nprems: usize },
    /// A selected subgoal is an outer premise, indexed from zero in Rust.
    #[error("selected subgoal {index} is outside {nprems} outer premises")]
    SelectedSubgoalOutOfRange { index: usize, nprems: usize },
    /// A rule does not have the requested number of outer premises.
    #[error("rule has only {available} outer premises, requested {requested}")]
    RulePremisesOutOfRange { requested: usize, available: usize },
    /// Rotation must be within the (possibly empty) movable premise chain.
    #[error("rotation {rotation} is outside a chain of {nprems} premises")]
    RotationOutOfRange { rotation: isize, nprems: usize },
    /// An equation was neither discharged by a checked conversion nor retained in F.
    #[error("{operation} equation at source slot {slot} has no checked proof")]
    UnprovedEquation { operation: &'static str, slot: usize },
    /// A match candidate attempts to instantiate the proof state.
    #[error("match composition must not assign schematic variables in the state")]
    MatchStateAssignment,
    /// A supposedly pre-incremented rule reuses a state schematic identity.
    #[error("incremented rule shares schematic identity {name}.{index} with state")]
    NamespaceCollision { name: Name, index: usize },
    /// An elimination candidate must select a real premise of A1.
    #[error("elimination assumption slot {choice} is invalid")]
    InvalidEliminationChoice { choice: usize },
    /// An assignment cycle would make the normalization or schematic scope ill-defined.
    #[error("recursive {kind} assignment in composition candidate")]
    RecursiveAssignment { kind: &'static str },
    /// Finite unifier data exceeded the kernel's candidate materialization budget.
    #[error("composition candidate {kind} exceeds {resource} limit {limit}")]
    CandidateResourceLimit { kind: &'static str, resource: &'static str, limit: usize },
    /// A candidate claims a schematic identity absent from its source proof.
    #[error("composition assignment for absent schematic variable {name}.{index}")]
    AbsentAssignment { name: Name, index: usize },
    /// A valid scoped proof must prove the exact source H ==> P contract.
    #[error("closed bound proof does not preserve the source proposition and hypotheses")]
    StatementMismatch,
}

/// Opaque checked-proof candidate. No public constructors or mutable fields.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundProof {
    root: Proof,
}

type Proof = Arc<Node>;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Node {
    Hyp(usize),
    ImpliesIntro {
        assumption: Term,
        body: Proof,
    },
    ImpliesElim(Proof, Proof),
    ForallIntro {
        name: Name,
        ty: Ty,
        body: Proof,
    },
    ForallElim {
        premise: Proof,
        argument: Term,
    },
    EqAbs {
        name: Name,
        ty: Ty,
        body: Proof,
    },
    EqSym(Proof),
    Binary {
        rule: BinaryRule,
        left: Proof,
        right: Proof,
    },
    Reflexive(Term),
    Beta(Term),
    /// Only the exact `F[j]` pair is usable and it remains in the output F.
    EqFlex(usize),
    Eta(Term),
    AuthorizedLeaf(LeafInstance),
    /// A fully source-replayed inner export; its own implication binders remain
    /// in its proposition instead of becoming outer-scope hypotheses.
    ClosedExportTransport(LeafInstance),
    ExportHead(LeafExportView),
}

/// Source-specific statement plus precisely the OFCLASS binder slots required
/// by this occurrence. Built only after checking its original leaf schema.
#[derive(Clone, Debug, PartialEq, Eq)]
struct LeafExportView {
    instance: LeafInstance,
    slots: Vec<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BinaryRule {
    Transitive,
    Combination,
    EqualIntr,
    EqualElim,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LeafInstance {
    source: usize,
    types: BTreeMap<Ty, Ty>,
    terms: BTreeMap<TermKey, Term>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct TermKey {
    name: Name,
    index: Option<usize>,
    ty: Ty,
}

impl TermKey {
    fn from_term(term: &Term) -> Option<Self> {
        match term {
            Term::Free { name, ty } => {
                Some(Self { name: name.clone(), index: None, ty: ty.clone() })
            },
            Term::Var { name, index, ty } => {
                Some(Self { name: name.clone(), index: Some(*index), ty: ty.clone() })
            },
            _ => None,
        }
    }
}

struct Sources<'a> {
    leaves: Vec<&'a KernelThm>,
    // Addresses only locate already-replayed source occurrences while lowering.
    // They are not persisted, hashed, or used as theorem authority.
    indexes: HashMap<*const KernelThm, usize>,
}

impl<'a> Sources<'a> {
    fn collect(theorem: &'a KernelThm) -> Self {
        let mut result = Self { leaves: Vec::new(), indexes: HashMap::new() };
        result.visit(theorem);
        result
    }
    fn collect_pair(first: &'a KernelThm, second: &'a KernelThm) -> Self {
        let mut result = Self::collect(first);
        result.visit(second);
        result
    }

    fn visit(&mut self, theorem: &'a KernelThm) {
        match theorem.derivation() {
            Derivation::AxiomInstance { .. }
            | Derivation::ConservativeDefinition { .. }
            | Derivation::OfClass { .. }
            | Derivation::UnconstrainT { .. }
            | Derivation::TheoremRef { .. } => {
                self.indexes.insert(std::ptr::from_ref(theorem), self.leaves.len());
                self.leaves.push(theorem);
            },
            _ => theorem.derivation().for_each_premise(&mut |premise| self.visit(premise)),
        }
    }
}

fn of_class_term(owner: &TrustedTheory, ty: &Ty, class: &Name) -> Result<Term, KernelError> {
    let tag = Ty::apply("itself", vec![ty.clone()])?;
    let of_class = crate::RawTerm::app(
        crate::RawTerm::const_(format!("{class}_class"), Ty::arrow(tag.clone(), Ty::prop())),
        crate::RawTerm::const_("Pure.type", tag),
    );
    Ok(ProofContext::new(owner.snapshot().clone()).certify_prop(of_class)?.term().clone())
}

impl KernelRules {
    /// Replay the source, bind its proof before replacing proof-only types,
    /// and independently check the resulting Pure proof. No hypotheses or
    /// obligations are discarded merely because they disappeared from P.
    pub fn strip_shyps(
        owner: &TrustedTheory,
        context: &ProofContext,
        theorem: &KernelThm,
    ) -> Result<KernelThm, KernelError> {
        let mut dependencies = crate::DependencySet::empty();
        crate::invariant::replay_source_in(owner, context, theorem, &mut dependencies)?;
        let solved = if theorem.payload().sort_obligations().is_empty() {
            None
        } else {
            Some(Self::solve_constraints(owner, theorem)?)
        };
        let theorem = solved.as_ref().unwrap_or(theorem);
        let (_, unwitnessed) = validate_source(owner, theorem)?;
        let sources = Sources::collect(theorem);
        let root = lower::lower_theorem(theorem, &sources)?;
        let root = transform::replace_proof_only_types_checked(root, theorem, owner, &unwitnessed)?;
        let proof = BoundProof { root };
        let frees = source_parameters::collect_source_parameters(theorem);
        let source = if frees.is_empty() {
            theorem.clone()
        } else {
            let names = frees.iter().map(|(name, _)| name.clone()).collect();
            let index = generalization_index(theorem)?;
            Self::generalize(theorem, &BTreeSet::new(), &names, index)?
        };
        Ok(materialize(owner, context, source, &proof, &sources, &unwitnessed, true)?.0)
    }
    /// Export sorts only after the original proof has been fully replayed and
    /// stripped; no OFCLASS hypothesis enters the theorem H field.
    pub fn unconstrain_t(
        owner: &TrustedTheory,
        context: &ProofContext,
        theorem: &KernelThm,
    ) -> Result<KernelThm, KernelError> {
        let source = Self::strip_shyps(owner, context, theorem)?;
        Ok(export::replay_export(owner, context, &source, None)?.0)
    }
}

fn validate_source(
    owner: &TrustedTheory,
    theorem: &KernelThm,
) -> Result<(crate::DependencySet, BTreeSet<Sort>), KernelError> {
    if !theorem.payload().sort_obligations().is_empty() {
        return Err(BoundProofError::UnsupportedSortExportVariant {
            operation: "class constraints",
        }
        .into());
    }
    if !theorem.payload().pending().is_empty() {
        return Err(BoundProofError::UnsupportedSortExportVariant {
            operation: "pending transaction",
        }
        .into());
    }
    let atoms = collect_present_atoms(theorem);
    let present: BTreeSet<_> = atoms.iter().filter_map(Ty::atomic_sort).collect();
    let mut dependencies = crate::DependencySet::empty();
    let mut unsolved = Vec::new();
    for sort in theorem.payload().shyps() {
        if present.contains(sort) {
            continue;
        }
        let Some(witness) = crate::class_proof::find_class_witness(owner, sort, &atoms) else {
            unsolved.push((owner.signature().minimize_sort(sort)?, sort.clone()));
            continue;
        };
        for class in sort.classes() {
            dependencies.extend(
                crate::class_proof::derive_of_class(owner, &witness, class)?.dependencies(),
            );
        }
    }
    let (extra_dependencies, extra) = reduce_unwitnessed(owner, &unsolved)?;
    dependencies.extend(&extra_dependencies);
    Ok((dependencies, extra))
}

fn collect_present_atoms(theorem: &KernelThm) -> BTreeSet<Ty> {
    let mut atoms = BTreeSet::new();
    terms::collect_type_atoms(theorem.prop().term(), &mut atoms);
    for hypothesis in theorem.hyps() {
        terms::collect_type_atoms(hypothesis.term(), &mut atoms);
    }
    for (left, right) in theorem.payload().flex_pairs() {
        terms::collect_type_atoms(left.term(), &mut atoms);
        terms::collect_type_atoms(right.term(), &mut atoms);
    }
    atoms
}

fn reduce_unwitnessed(
    owner: &TrustedTheory,
    unsolved: &[(Sort, Sort)],
) -> Result<(crate::DependencySet, BTreeSet<Sort>), KernelError> {
    let mut representatives = BTreeSet::new();
    for (minimal, _) in unsolved {
        let is_dominated = unsolved.iter().any(|(stronger, _)| {
            owner.signature().is_sort_le(stronger, minimal)
                && !owner.signature().is_sort_le(minimal, stronger)
        });
        if !is_dominated {
            representatives.insert(minimal.clone());
        }
    }
    let mut dependencies = crate::DependencySet::empty();
    for (minimal, original) in unsolved {
        let representative = representatives
            .iter()
            .find(|candidate| owner.signature().is_sort_le(candidate, minimal))
            .ok_or(KernelError::UnknownClassEvidence)?;
        let witness = Ty::tvar("__strip_extra", 0, representative.clone());
        for class in original.classes() {
            dependencies.extend(
                crate::class_proof::derive_of_class(owner, &witness, class)?.dependencies(),
            );
        }
    }
    Ok((dependencies, representatives))
}

pub(crate) fn replay_bound_proof(
    owner: &TrustedTheory,
    context: &ProofContext,
    theorem: &KernelThm,
    proof: &BoundProof,
) -> Result<(KernelThm, crate::DependencySet), KernelError> {
    let (mut dependencies, unwitnessed) = validate_source(owner, theorem)?;
    let sources = Sources::collect(theorem);
    let is_canonical_adapter =
        is_canonical_strip_proof(owner, theorem, proof, &sources, &unwitnessed)?;
    let (result, proof_dependencies) = materialize(
        owner,
        context,
        theorem.clone(),
        proof,
        &sources,
        &unwitnessed,
        is_canonical_adapter,
    )?;
    dependencies.extend(&proof_dependencies);
    Ok((result, dependencies))
}

fn is_canonical_strip_proof(
    owner: &TrustedTheory,
    theorem: &KernelThm,
    proof: &BoundProof,
    sources: &Sources<'_>,
    unwitnessed: &BTreeSet<Sort>,
) -> Result<bool, KernelError> {
    // A user-supplied Generalize belongs to the immediate source proof.
    // Check its complete canonical tree before considering the wrapper added
    // by strip_shyps for free parameters that only occur in the proof.
    let lowered = lower::lower_theorem(theorem, sources)?;
    let canonical =
        transform::replace_proof_only_types_checked(lowered, theorem, owner, unwitnessed)?;
    if canonical == proof.root {
        return Ok(true);
    }
    let Derivation::Generalize { type_names, term_names, index, source_frees, premise } =
        theorem.derivation()
    else {
        return Ok(false);
    };
    let frees = source_parameters::collect_source_parameters(premise);
    if !type_names.is_empty()
        || frees.is_empty()
        || theorem.prop() != premise.prop()
        || theorem.hyps() != premise.hyps()
        || theorem.payload().flex_pairs() != premise.payload().flex_pairs()
        || *source_frees
            != collect_lexical_frees(premise)
                .into_iter()
                .filter(|(name, _)| term_names.contains(name))
                .collect::<Vec<_>>()
        || *term_names != frees.iter().map(|(name, _)| name.clone()).collect()
    {
        return Ok(false);
    }
    let lowered = lower::lower_theorem(premise, sources)?;
    let canonical =
        transform::replace_proof_only_types_checked(lowered, premise, owner, unwitnessed)?;
    if *index != generalization_index(premise)? {
        return Ok(false);
    }
    Ok(canonical == proof.root)
}

fn generalization_index(theorem: &KernelThm) -> Result<usize, KernelError> {
    theorem.max_var_index().map_or(Ok(0), |index| {
        index.checked_add(1).ok_or(KernelError::GeneralizeIndexOverflow { index, offset: 1 })
    })
}

fn materialize(
    owner: &TrustedTheory,
    context: &ProofContext,
    theorem: KernelThm,
    proof: &BoundProof,
    sources: &Sources<'_>,
    unwitnessed: &BTreeSet<Sort>,
    is_canonical_adapter: bool,
) -> Result<(KernelThm, crate::DependencySet), KernelError> {
    let (proposition, mut sorts, dependencies) = check::check_closed_with_source(
        context,
        owner,
        sources,
        &proof.root,
        check::CheckTransport {
            source: theorem.prop().term(),
            target: theorem.prop().term(),
            is_canonical_adapter,
            flex_pairs: theorem.payload().flex_pairs(),
        },
    )?;
    let hypotheses: Vec<_> = theorem.hyps().iter().map(|hyp| hyp.term().clone()).collect();
    let expected = Term::mk_imp_chain(&hypotheses, theorem.prop().term())?;
    if !proposition.alpha_eq(&expected) {
        return Err(BoundProofError::StatementMismatch.into());
    }
    sorts.extend(unwitnessed.iter().cloned());
    let payload =
        ProofPayload::from_bound_proof(sorts, theorem.prop(), theorem.hyps(), theorem.payload())?;
    Ok((
        KernelThm::new_with_payload(
            theorem.hyps().to_vec(),
            theorem.prop().clone(),
            payload,
            Derivation::StripShyps { premise: Box::new(theorem), proof: proof.clone() },
        ),
        dependencies,
    ))
}
