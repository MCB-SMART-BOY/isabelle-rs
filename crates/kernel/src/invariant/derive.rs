use super::{
    ReplayEnvironment, require_same_context, validate_cprop, validate_cterm, validate_substitution,
};
use crate::{
    ContextStamp, DependencySet, Derivation, KernelError, KernelRules, KernelThm, LogicBasis,
    RawTerm, TrustedTheory,
};

/// Exhaustive inference table: sources have already been independently replayed.
/// Kept together for auditability; scope-changing rules are handled by the caller.
pub(super) fn replay_rule(
    expected: ContextStamp,
    environment: Option<&ReplayEnvironment>,
    dependencies: &mut DependencySet,
    derivation: &Derivation,
    premises: &[KernelThm],
    logic_basis: Option<&LogicBasis>,
    owner: Option<&TrustedTheory>,
) -> Result<KernelThm, KernelError> {
    let source = |index| premises.get(index).ok_or(KernelError::AcceptanceReplayMismatch);
    let effective_context = std::cell::OnceCell::new();
    let context = || {
        effective_context
            .get_or_init(|| environment.map(ReplayEnvironment::context_for_bound))
            .as_deref()
            .ok_or(KernelError::UnsupportedAcceptanceDerivation)
    };
    let owner = || owner.ok_or(KernelError::UnsupportedAcceptanceDerivation);
    match derivation {
        Derivation::AdjustMaxIndex { requested, .. } => {
            Ok(KernelRules::adjust_max_index(source(0)?, *requested))
        },
        Derivation::TheoremRef { theorem } => {
            context()?;
            let imported = KernelRules::theorem_ref(owner()?, theorem)?.into_kernel();
            dependencies.insert_theorem(theorem.id());
            Ok(imported)
        },
        Derivation::Assume { prop } => {
            validate_cprop(expected, environment, prop)?;
            Ok(KernelRules::assume(prop.clone())?.into_kernel())
        },
        Derivation::Reflexive { term } => {
            validate_cterm(expected, environment, term)?;
            Ok(KernelRules::reflexive(term.clone()).into_kernel())
        },
        Derivation::BetaConversion { redex } => {
            validate_cterm(expected, environment, redex)?;
            Ok(KernelRules::beta_conversion(redex.clone())?.into_kernel())
        },
        Derivation::EtaConversion { redex } => {
            validate_cterm(expected, environment, redex)?;
            Ok(KernelRules::eta_conversion(redex.clone())?.into_kernel())
        },
        Derivation::Weaken { assumption, .. } => {
            validate_cprop(expected, environment, assumption)?;
            KernelRules::weaken(assumption, source(0)?)
        },
        Derivation::ImpliesIntr { assumption, .. } => {
            validate_cprop(expected, environment, assumption)?;
            KernelRules::implies_intr(assumption, source(0)?)
        },
        Derivation::Symmetric { .. } => KernelRules::symmetric(source(0)?),
        Derivation::Transitive { .. } => KernelRules::transitive(source(0)?, source(1)?),
        Derivation::ImpliesElim { .. } => KernelRules::implies_elim(source(0)?, source(1)?),
        Derivation::Combination { .. } => KernelRules::combination(source(0)?, source(1)?),
        Derivation::EqualIntr { .. } => KernelRules::equal_intr(source(0)?, source(1)?),
        Derivation::EqualElim { .. } => KernelRules::equal_elim(source(0)?, source(1)?),
        Derivation::ForallElim { arg, .. } => {
            validate_cterm(expected, environment, arg)?;
            KernelRules::forall_elim(source(0)?, arg)
        },
        Derivation::SubstPremise { selected_subgoal_index, .. } => {
            KernelRules::subst_premise(source(0)?, source(1)?, *selected_subgoal_index)
        },
        Derivation::Instantiate { type_inst, subst, .. } => {
            validate_substitution(expected, environment, subst)?;
            if let Some(env) = environment {
                env.context.validate_type_instantiation(type_inst)?;
            }
            crate::rules::replay_instantiation(None, source(0)?, type_inst, subst)
        },
        Derivation::SolveConstraints { proofs, .. } => {
            let solved =
                crate::class_proof::replay_solve_constraints(owner()?, source(0)?, proofs)?;
            for proof in proofs {
                dependencies.extend(proof.dependencies());
            }
            Ok(solved)
        },
        Derivation::OfClass { proof } => {
            let checked = crate::class_proof::replay_of_class(owner()?, proof)?;
            dependencies.extend(proof.dependencies());
            Ok(checked.into_kernel())
        },
        Derivation::StripShyps { proof, .. } => {
            let (checked, evidence) =
                crate::bound_proof::replay_bound_proof(owner()?, context()?, source(0)?, proof)?;
            dependencies.extend(&evidence);
            Ok(checked)
        },
        Derivation::UnconstrainT { proof, .. } => {
            let (checked, evidence) = crate::bound_proof::export::replay_export(
                owner()?,
                context()?,
                source(0)?,
                Some(proof),
            )?;
            dependencies.extend(&evidence);
            Ok(checked)
        },
        Derivation::SourceRenameIndex { increment, proof, .. } => {
            let (checked, evidence) = crate::bound_proof::replay_index_rename(
                owner()?,
                context()?,
                source(0)?.clone(),
                *increment,
                Some(proof),
            )?;
            dependencies.extend(&evidence);
            Ok(checked)
        },
        Derivation::SourceInstantiate { type_inst, subst, proof, .. } => {
            let (checked, evidence) = crate::bound_proof::replay_source_instantiation(
                owner()?,
                context()?,
                source(0)?.clone(),
                type_inst,
                subst,
            )?;
            if !matches!(checked.derivation(),
                Derivation::SourceInstantiate { proof: canonical, .. } if canonical == proof)
            {
                return Err(KernelError::AcceptanceReplayMismatch);
            }
            dependencies.extend(&evidence);
            Ok(checked)
        },
        Derivation::Bicompose {
            selected,
            premise_count,
            flags,
            residual_pairs,
            elimination_choice,
            proof,
            ..
        } => {
            let (checked, evidence) = crate::bound_proof::replay_exact_resolution(
                owner()?,
                context()?,
                source(0)?.clone(),
                source(1)?.clone(),
                crate::bound_proof::ResolutionReplay {
                    selected: *selected,
                    premise_count: *premise_count,
                    flags: *flags,
                    residual: residual_pairs,
                    elimination_choice: *elimination_choice,
                    proof,
                },
            )?;
            dependencies.extend(&evidence);
            Ok(checked)
        },
        Derivation::EqAssumption { selected, choice, proof, .. } => {
            let (checked, evidence) = crate::bound_proof::replay_eq_assumption(
                owner()?,
                context()?,
                source(0)?.clone(),
                *selected,
                *choice,
                proof,
            )?;
            dependencies.extend(&evidence);
            Ok(checked)
        },
        Derivation::Assumption {
            selected,
            source_assumptions,
            choice,
            residual_pairs,
            proof,
            ..
        } => {
            let (checked, evidence) = crate::bound_proof::replay_assumption(
                owner()?,
                context()?,
                source(0)?.clone(),
                crate::bound_proof::AssumptionReplay {
                    selected: *selected,
                    choice: *choice,
                    source_assumptions: *source_assumptions,
                    residual: residual_pairs,
                    proof,
                },
            )?;
            dependencies.extend(&evidence);
            Ok(checked)
        },
        Derivation::LiftRule { goal, proof, .. } => {
            let (checked, evidence) = crate::bound_proof::replay_lift_rule(
                owner()?,
                context()?,
                source(0)?.clone(),
                goal,
                proof,
            )?;
            dependencies.extend(&evidence);
            Ok(checked)
        },
        Derivation::PermutePrems { fixed, rotation, proof, .. } => {
            let (checked, evidence) = crate::bound_proof::replay_permutation(
                owner()?,
                context()?,
                source(0)?.clone(),
                *fixed,
                *rotation,
                proof,
            )?;
            dependencies.extend(&evidence);
            Ok(checked)
        },
        Derivation::RotateRule { selected_subgoal_index, rotation, proof, .. } => {
            let (checked, evidence) = crate::bound_proof::replay_rotation(
                owner()?,
                context()?,
                source(0)?.clone(),
                *selected_subgoal_index,
                *rotation,
                proof,
            )?;
            dependencies.extend(&evidence);
            Ok(checked)
        },
        Derivation::Resolve1Match { selected_subgoal_index, subst, .. } => {
            validate_substitution(expected, environment, subst)?;
            let rule = source(0)?;
            let state = source(1)?;
            let goal = state.prop().term().select_subgoal(*selected_subgoal_index).ok_or(
                KernelError::SubgoalIndexOutOfRange {
                    index: *selected_subgoal_index,
                    nprems: state.prop().term().nprems(),
                },
            )?;
            let canonical = KernelRules::match_terms_certified(
                rule.prop().term().dest_imp_chain().1,
                &goal,
                expected,
            )?;
            if subst != &canonical {
                return Err(KernelError::AcceptanceReplayMismatch);
            }
            KernelRules::resolve1_match(rule, state, *selected_subgoal_index)
        },
        Derivation::AxiomInstance { axiom_name, type_inst, term_inst } => {
            let ctx = context()?;
            let (basis, schema) = if let Ok(owner) = owner() {
                owner
                    .find_axiom_origin(axiom_name)
                    .ok_or_else(|| KernelError::UnapprovedAxiom { name: axiom_name.clone() })?
            } else {
                let basis = logic_basis.ok_or(KernelError::UnsupportedAcceptanceDerivation)?;
                let schema = basis
                    .get_axiom(axiom_name)
                    .ok_or_else(|| KernelError::UnapprovedAxiom { name: axiom_name.clone() })?;
                (basis, schema)
            };
            ctx.validate_type_instantiation(type_inst)?;
            for term in term_inst {
                validate_cterm(expected, environment, term)?;
            }
            let typed = crate::term::subst_types(&schema.prop, type_inst)?;
            let prop = crate::term::instantiate_schema_binders(ctx, typed, term_inst)?;
            dependencies.insert_axiom(crate::AxiomDependencyId::compute(basis.id(), schema.id()));
            Ok(KernelThm::new(Vec::new(), prop, derivation.clone()))
        },
        Derivation::ConservativeDefinition { definition } => {
            let owner = owner()?;
            let (certificate, parent) = owner
                .find_definition_certificate(definition)
                .ok_or(KernelError::UnknownTheoremDependency)?;
            crate::theory::validate_definition_certificate_in_parent(
                owner
                    .snapshot()
                    .find_snapshot_by_id(parent)
                    .ok_or(KernelError::UnknownTheoremDependency)?,
                &certificate,
            )?;
            let raw = RawTerm::eq(
                RawTerm::const_(certificate.name.clone(), certificate.declared_ty.clone()),
                certificate.rhs_raw.clone(),
            );
            let prop = context()?.certify_prop(raw)?;
            require_same_context(expected, prop.context())?;
            dependencies.insert_definition(*definition);
            Ok(KernelThm::new(Vec::new(), prop, derivation.clone()))
        },
        Derivation::Generalize { .. }
        | Derivation::ExportScope { .. }
        | Derivation::Transfer { .. }
        | Derivation::ForallIntr { .. }
        | Derivation::Abstraction { .. } => Err(KernelError::UnsupportedAcceptanceDerivation),
    }
}
