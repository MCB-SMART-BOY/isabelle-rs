use std::collections::BTreeSet;

use super::{CProp, CTerm, InstEntry, KernelThm, Name, TrustedTheorem, Ty};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Derivation {
    TheoremRef {
        theorem: TrustedTheorem,
    },
    Assume {
        prop: CProp,
    },
    Weaken {
        assumption: CProp,
        premise: Box<KernelThm>,
    },

    Reflexive {
        term: CTerm,
    },
    Symmetric {
        premise: Box<KernelThm>,
    },
    Transitive {
        left: Box<KernelThm>,
        right: Box<KernelThm>,
    },
    BetaConversion {
        redex: CTerm,
    },
    EtaConversion {
        redex: CTerm,
    },

    ForallIntr {
        variable: CTerm,
        premise: Box<KernelThm>,
    },
    ForallElim {
        forall: Box<KernelThm>,
        arg: CTerm,
    },
    ImpliesIntr {
        assumption: CProp,
        premise: Box<KernelThm>,
    },
    ImpliesElim {
        major: Box<KernelThm>,
        minor: Box<KernelThm>,
    },
    Combination {
        function: Box<KernelThm>,
        argument: Box<KernelThm>,
    },
    Abstraction {
        variable_name: Name,
        variable_type: Ty,
        premise: Box<KernelThm>,
    },
    EqualIntr {
        left: Box<KernelThm>,
        right: Box<KernelThm>,
    },
    EqualElim {
        equality: Box<KernelThm>,
        minor: Box<KernelThm>,
    },
    SubstPremise {
        /// Propositional equality theorem `A == B`.
        equality: Box<KernelThm>,
        /// Goal state `G1 ==> ... ==> A ==> ... ==> R`.
        goal_state: Box<KernelThm>,
        /// The selected goal subgoal index (0-based).
        selected_subgoal_index: usize,
    },
    Generalize {
        /// Fixed type and term names selected at this boundary.
        type_names: BTreeSet<Name>,
        term_names: BTreeSet<Name>,
        /// Shared fresh index; trailing underscores add checked offsets.
        index: usize,
        /// Exact lexically unbound typed frees selected in the source proof.
        source_frees: Vec<(Name, Ty)>,
        premise: Box<KernelThm>,
    },
    /// Complete source replay in a kernel-issued local capsule, followed by
    /// recertification of every output field without local declarations.
    ExportScope {
        scope: crate::ProofScope,
        premise: Box<KernelThm>,
    },
    Instantiate {
        /// Finite type substitution applied before matching term keys.
        type_inst: crate::logic::TypeInstantiation,
        /// Substitution entries with certified replacements.
        subst: Vec<InstEntry>,
        premise: Box<KernelThm>,
    },
    /// Source-ordered type→term candidate replay. The checked proof records
    /// conversions that can arise only after instantiation (e.g. beta after
    /// forall elimination); lowering must not recreate an unnormalized DAG.
    SourceInstantiate {
        type_inst: crate::logic::TypeInstantiation,
        subst: Vec<InstEntry>,
        premise: Box<KernelThm>,
        proof: crate::BoundProof,
    },
    /// Canonical source-only schematic index renaming, replayed before use.
    SourceRenameIndex {
        increment: usize,
        premise: Box<KernelThm>,
        proof: crate::BoundProof,
    },
    Resolve1Match {
        /// The rule applied to the goal.
        rule: Box<KernelThm>,
        /// The goal state that received the resolution step.
        goal_state: Box<KernelThm>,
        /// The index of the selected subgoal (0-based).
        selected_subgoal_index: usize,
        /// The matching substitution (rule conclusion → selected subgoal).
        subst: Vec<InstEntry>,
    },
    AxiomInstance {
        axiom_name: Name,
        /// Type substitution: maps schematic type variables to concrete types.
        type_inst: crate::logic::TypeInstantiation,
        /// Term substitution: ordered list of replacements for schema binders.
        term_inst: Vec<CTerm>,
    },
    /// Replay reconstructs the definition proposition from the owner theory's
    /// [`DefinitionCertificate`](super::DefinitionCertificate).
    ConservativeDefinition {
        definition: super::DefinitionId,
    },
    /// Pure OFCLASS, with the checked proof re-verified at accepting replay.
    OfClass {
        proof: crate::ClosedOfClassProof,
    },
    /// Every sorted type obligation is discharged by an exact owner-checked
    /// class proof; the premise and all other payload fields remain unchanged.
    SolveConstraints {
        premise: Box<KernelThm>,
        proofs: Vec<crate::ClosedOfClassProof>,
    },
    /// The source is replayed before its closed private proof is checked.
    StripShyps {
        premise: Box<KernelThm>,
        proof: crate::BoundProof,
    },
    /// Source-replayed sort export with a privately checked Γp/κ proof.
    UnconstrainT {
        premise: Box<KernelThm>,
        proof: crate::BoundProof,
    },
    /// The complete source DAG is replayed in its actual committed ancestor
    /// before its full payload is re-certified in the destination owner.
    Transfer {
        premise: Box<KernelThm>,
    },
    /// A checked, proposition-preserving adjustment of Isabelle's maxidx.
    /// The index remains metadata; replay clamps it to actual theorem contents.
    AdjustMaxIndex {
        premise: Box<KernelThm>,
        requested: Option<usize>,
    },
    /// Source-preserving closed adapter for an outer implication-tail rotation.
    PermutePrems {
        premise: Box<KernelThm>,
        fixed: usize,
        rotation: isize,
        proof: crate::BoundProof,
    },
    /// Source-preserving closed adapter for one selected nested subgoal.
    RotateRule {
        premise: Box<KernelThm>,
        selected_subgoal_index: usize,
        rotation: isize,
        proof: crate::BoundProof,
    },
    /// Source-replayed local Pure spine lifting; proposition/H/F/dependencies retained.
    LiftRule {
        premise: Box<KernelThm>,
        goal: CTerm,
        proof: crate::BoundProof,
    },
    /// Owner-checked bicomposition; replay checks both sources and their private DAG.
    Bicompose {
        rule: Box<KernelThm>,
        state: Box<KernelThm>,
        selected: usize,
        premise_count: usize,
        flags: crate::bound_proof::CompositionFlags,
        residual_pairs: Vec<(CTerm, CTerm)>,
        elimination_choice: Option<usize>,
        proof: crate::BoundProof,
    },
    /// Owner-checked assumption candidate with complete residual equations.
    Assumption {
        state: Box<KernelThm>,
        selected: usize,
        /// Number of implication premises in the selected goal before candidate instantiation.
        source_assumptions: usize,
        choice: usize,
        residual_pairs: Vec<(CTerm, CTerm)>,
        proof: crate::BoundProof,
    },
    /// Source-replayed, checked binder proof for one selected subgoal.
    EqAssumption {
        state: Box<KernelThm>,
        selected: usize,
        choice: usize,
        proof: crate::BoundProof,
    },
}

impl Derivation {
    pub(crate) fn for_each_certified_term<'a>(&'a self, f: &mut impl FnMut(&'a CTerm)) {
        match self {
            Self::Reflexive { term }
            | Self::BetaConversion { redex: term }
            | Self::EtaConversion { redex: term }
            | Self::ForallIntr { variable: term, .. }
            | Self::ForallElim { arg: term, .. }
            | Self::LiftRule { goal: term, .. } => f(term),
            Self::Instantiate { subst, .. }
            | Self::SourceInstantiate { subst, .. }
            | Self::Resolve1Match { subst, .. } => {
                for entry in subst {
                    f(entry.replacement());
                }
            },
            Self::Bicompose { residual_pairs, .. } | Self::Assumption { residual_pairs, .. } => {
                for (left, right) in residual_pairs {
                    f(left);
                    f(right);
                }
            },
            Self::AxiomInstance { term_inst, .. } => {
                for term in term_inst {
                    f(term);
                }
            },
            _ => {},
        }
    }
    pub(crate) fn for_each_premise<'a>(&'a self, f: &mut impl FnMut(&'a KernelThm)) {
        match self {
            Self::Symmetric { premise }
            | Self::Weaken { premise, .. }
            | Self::ForallIntr { premise, .. }
            | Self::ImpliesIntr { premise, .. }
            | Self::Abstraction { premise, .. }
            | Self::Generalize { premise, .. }
            | Self::ExportScope { premise, .. }
            | Self::SolveConstraints { premise, .. }
            | Self::StripShyps { premise, .. }
            | Self::UnconstrainT { premise, .. }
            | Self::Transfer { premise }
            | Self::PermutePrems { premise, .. }
            | Self::AdjustMaxIndex { premise, .. }
            | Self::RotateRule { premise, .. }
            | Self::LiftRule { premise, .. }
            | Self::Instantiate { premise, .. }
            | Self::SourceInstantiate { premise, .. }
            | Self::SourceRenameIndex { premise, .. } => f(premise),
            Self::ForallElim { forall, .. } => f(forall),
            Self::Transitive { left, right } | Self::EqualIntr { left, right } => {
                f(left);
                f(right);
            },
            Self::ImpliesElim { major, minor } => {
                f(major);
                f(minor);
            },
            Self::Combination { function, argument } => {
                f(function);
                f(argument);
            },
            Self::EqualElim { equality, minor } => {
                f(equality);
                f(minor);
            },
            Self::SubstPremise { equality, goal_state, .. } => {
                f(equality);
                f(goal_state);
            },
            Self::Resolve1Match { rule, goal_state, .. } => {
                f(rule);
                f(goal_state);
            },
            Self::Bicompose { rule, state, .. } => {
                f(rule);
                f(state);
            },
            Self::EqAssumption { state, .. } | Self::Assumption { state, .. } => f(state),
            Self::TheoremRef { .. }
            | Self::Assume { .. }
            | Self::Reflexive { .. }
            | Self::BetaConversion { .. }
            | Self::EtaConversion { .. }
            | Self::OfClass { .. }
            | Self::AxiomInstance { .. }
            | Self::ConservativeDefinition { .. } => {},
        }
    }
}
