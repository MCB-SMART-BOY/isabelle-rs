use super::{
    CProp, CTerm, ContextStamp, Derivation, InstEntry, KernelError, KernelRules, KernelThm, Name,
    ProofContext, RawTerm, Term, Ty,
    theory::{DependencySet, TrustedTheory},
};

/// Canonical result reconstructed by owner-parameterized accepting replay.
pub(in crate::kernel) struct ReplayResult {
    context: ContextStamp,
    hyps: Vec<CProp>,
    prop: CProp,
    dependencies: DependencySet,
}

impl ReplayResult {
    fn from_kernel(theorem: KernelThm, dependencies: DependencySet) -> Self {
        Self {
            context: theorem.context(),
            hyps: theorem.hyps().to_vec(),
            prop: theorem.prop().clone(),
            dependencies,
        }
    }

    pub(in crate::kernel) fn context(&self) -> ContextStamp {
        self.context
    }

    pub(in crate::kernel) fn hyps(&self) -> &[CProp] {
        &self.hyps
    }

    pub(in crate::kernel) fn prop(&self) -> &CProp {
        &self.prop
    }

    pub(in crate::kernel) fn dependencies(&self) -> &DependencySet {
        &self.dependencies
    }
}

fn require_same_context(expected: ContextStamp, actual: ContextStamp) -> Result<(), KernelError> {
    if expected != actual {
        return Err(KernelError::MixedContext { expected, actual });
    }
    Ok(())
}

fn preflight_substitution_contexts(
    expected: ContextStamp,
    subst: &[InstEntry],
) -> Result<(), KernelError> {
    for entry in subst {
        require_same_context(expected, entry.replacement().context())?;
    }
    Ok(())
}

fn validate_cprop(
    expected: ContextStamp,
    validator: Option<&ProofContext>,
    prop: &CProp,
) -> Result<(), KernelError> {
    require_same_context(expected, prop.context())?;
    if let Some(context) = validator {
        context.validate_cprop(prop)?;
    } else if !prop.term().ty().is_prop() {
        return Err(KernelError::NotProposition(prop.term().ty()));
    }
    Ok(())
}

fn validate_cterm(
    expected: ContextStamp,
    validator: Option<&ProofContext>,
    term: &CTerm,
) -> Result<(), KernelError> {
    require_same_context(expected, term.context())?;
    if let Some(context) = validator {
        context.validate_cterm(term)?;
    }
    Ok(())
}

fn validate_substitution(
    expected: ContextStamp,
    validator: Option<&ProofContext>,
    subst: &[InstEntry],
) -> Result<(), KernelError> {
    preflight_substitution_contexts(expected, subst)?;
    for entry in subst {
        validate_cterm(expected, validator, entry.replacement())?;
        if entry.replacement().ty() != *entry.var_ty() {
            return Err(KernelError::TypeMismatch {
                expected: entry.var_ty().clone(),
                actual: entry.replacement().ty(),
            });
        }
    }
    Ok(())
}

fn validate_theorem_fields(
    expected: ContextStamp,
    validator: Option<&ProofContext>,
    theorem: &KernelThm,
) -> Result<(), KernelError> {
    require_same_context(expected, theorem.context())?;
    if theorem.prop().context() != expected {
        return Err(if validator.is_some() {
            KernelError::MixedContext { expected, actual: theorem.prop().context() }
        } else {
            KernelError::Invariant("theorem context does not match proposition context".into())
        });
    }
    for hypothesis in theorem.hyps() {
        if hypothesis.context() != expected {
            return Err(if validator.is_some() {
                KernelError::MixedContext { expected, actual: hypothesis.context() }
            } else {
                KernelError::Invariant("theorem context does not match hypothesis context".into())
            });
        }
    }

    validate_cprop(expected, validator, theorem.prop())?;
    for hypothesis in theorem.hyps() {
        validate_cprop(expected, validator, hypothesis)?;
    }
    Ok(())
}

fn rebuild_premise(
    expected: ContextStamp,
    validator: Option<&ProofContext>,
    dependencies: &mut DependencySet,
    theorem: &KernelThm,
) -> Result<KernelThm, KernelError> {
    validate_theorem_fields(expected, validator, theorem)?;
    let replayed =
        replay_derivation(expected, validator, dependencies, theorem.derivation(), None)?;
    if replayed.context() != theorem.context()
        || replayed.hyps() != theorem.hyps()
        || replayed.prop() != theorem.prop()
    {
        return Err(if validator.is_some() {
            KernelError::AcceptanceReplayMismatch
        } else {
            KernelError::Invariant("derivation replay does not match theorem fields".into())
        });
    }
    Ok(replayed)
}

/// Structural diagnostic replay. It proves no owning-theory authorization and
/// cannot construct a [`super::TrustedTheorem`].
pub fn check_kernel_thm(theorem: &KernelThm) -> Result<(), KernelError> {
    let mut dependencies = DependencySet::empty();
    rebuild_premise(theorem.context(), None, &mut dependencies, theorem)?;
    Ok(())
}

/// Replay one closed candidate under the exact immutable owner context.
pub(in crate::kernel) fn replay_closed_theorem_in(
    theory: &TrustedTheory,
    theorem: &super::ClosedThm,
) -> Result<ReplayResult, KernelError> {
    let expected = theory.stamp();
    let validator = ProofContext::new(theory.snapshot().clone());
    validate_theorem_fields(expected, Some(&validator), theorem.as_kernel())?;
    let mut dependencies = DependencySet::empty();
    let replayed = replay_derivation(
        expected,
        Some(&validator),
        &mut dependencies,
        theorem.as_kernel().derivation(),
        theory.logic_basis(),
    )?;
    Ok(ReplayResult::from_kernel(replayed, dependencies))
}

fn replay_derivation(
    expected: ContextStamp,
    validator: Option<&ProofContext>,
    dependencies: &mut DependencySet,
    derivation: &Derivation,
    logic_basis: Option<super::LogicBasisId>,
) -> Result<KernelThm, KernelError> {
    match derivation {
        Derivation::TheoremRef { theorem } => {
            let context = validator.ok_or(KernelError::UnsupportedAcceptanceDerivation)?;
            if !context.theory().has_ancestor(theorem.accepted_in()) {
                return Err(KernelError::UnknownTheoremDependency);
            }
            let prop = context.recertify_prop(theorem.prop())?;
            dependencies.insert_theorem(theorem.id());
            Ok(KernelThm::new(
                Vec::new(),
                prop,
                Derivation::TheoremRef { theorem: theorem.clone() },
            ))
        },
        Derivation::Assume { prop } => {
            validate_cprop(expected, validator, prop)?;
            Ok(KernelRules::assume(prop.clone()).into_kernel())
        },
        Derivation::Reflexive { term } => {
            validate_cterm(expected, validator, term)?;
            Ok(KernelRules::reflexive(term.clone()).into_kernel())
        },
        Derivation::Symmetric { premise } => {
            require_same_context(expected, premise.context())?;
            let premise = rebuild_premise(expected, validator, dependencies, premise)?;
            KernelRules::symmetric(&premise)
        },
        Derivation::Transitive { left, right } => {
            require_same_context(expected, left.context())?;
            require_same_context(expected, right.context())?;
            let left = rebuild_premise(expected, validator, dependencies, left)?;
            let right = rebuild_premise(expected, validator, dependencies, right)?;
            KernelRules::transitive(&left, &right)
        },
        Derivation::ImpliesIntr { assumption, premise } => {
            require_same_context(expected, assumption.context())?;
            require_same_context(expected, premise.context())?;
            validate_cprop(expected, validator, assumption)?;
            let premise = rebuild_premise(expected, validator, dependencies, premise)?;
            KernelRules::implies_intr(assumption, &premise)
        },
        Derivation::ImpliesElim { major, minor } => {
            require_same_context(expected, major.context())?;
            require_same_context(expected, minor.context())?;
            let major = rebuild_premise(expected, validator, dependencies, major)?;
            let minor = rebuild_premise(expected, validator, dependencies, minor)?;
            KernelRules::implies_elim(&major, &minor)
        },
        Derivation::BetaConversion { redex } => {
            validate_cterm(expected, validator, redex)?;
            Ok(KernelRules::beta_conversion(redex.clone())?.into_kernel())
        },
        Derivation::ForallIntr { variable, premise } => {
            require_same_context(expected, variable.context())?;
            require_same_context(expected, premise.context())?;
            validate_cterm(expected, validator, variable)?;
            let premise = rebuild_premise(expected, validator, dependencies, premise)?;
            KernelRules::forall_intr(variable, &premise)
        },
        Derivation::ForallElim { forall, arg } => {
            require_same_context(expected, forall.context())?;
            require_same_context(expected, arg.context())?;
            validate_cterm(expected, validator, arg)?;
            let forall = rebuild_premise(expected, validator, dependencies, forall)?;
            KernelRules::forall_elim(&forall, arg)
        },
        Derivation::Combination { function, argument } => {
            require_same_context(expected, function.context())?;
            require_same_context(expected, argument.context())?;
            let function = rebuild_premise(expected, validator, dependencies, function)?;
            let argument = rebuild_premise(expected, validator, dependencies, argument)?;
            KernelRules::combination(&function, &argument)
        },
        Derivation::Abstraction { variable_name, variable_type, premise } => {
            require_same_context(expected, premise.context())?;
            let premise = rebuild_premise(expected, validator, dependencies, premise)?;
            KernelRules::abstraction(variable_name.clone(), variable_type.clone(), &premise)
        },
        Derivation::EqualIntr { left, right } => {
            require_same_context(expected, left.context())?;
            require_same_context(expected, right.context())?;
            let left = rebuild_premise(expected, validator, dependencies, left)?;
            let right = rebuild_premise(expected, validator, dependencies, right)?;
            KernelRules::equal_intr(&left, &right)
        },
        Derivation::EqualElim { equality, minor } => {
            require_same_context(expected, equality.context())?;
            require_same_context(expected, minor.context())?;
            let equality = rebuild_premise(expected, validator, dependencies, equality)?;
            let minor = rebuild_premise(expected, validator, dependencies, minor)?;
            KernelRules::equal_elim(&equality, &minor)
        },
        Derivation::SubstPremise { equality, goal_state, selected_subgoal_index } => {
            require_same_context(expected, equality.context())?;
            require_same_context(expected, goal_state.context())?;
            let equality = rebuild_premise(expected, validator, dependencies, equality)?;
            let goal_state = rebuild_premise(expected, validator, dependencies, goal_state)?;
            KernelRules::subst_premise(&equality, &goal_state, *selected_subgoal_index)
        },
        Derivation::Generalize { frees, start_index, premise } => {
            require_same_context(expected, premise.context())?;
            if validator.is_some()
                && let Some((name, _)) = frees.first()
            {
                return Err(KernelError::UndeclaredFree(name.clone()));
            }
            let premise = rebuild_premise(expected, validator, dependencies, premise)?;
            let expected_start = premise.max_var_index().map_or(0, |index| index + 1);
            if expected_start != *start_index {
                return Err(KernelError::Invariant(format!(
                    "generalize start_index mismatch: expected {expected_start}, recorded {start_index}"
                )));
            }
            KernelRules::generalize(&premise, frees)
        },
        Derivation::Instantiate { subst, premise } => {
            require_same_context(expected, premise.context())?;
            preflight_substitution_contexts(expected, subst)?;
            validate_substitution(expected, validator, subst)?;
            let premise = rebuild_premise(expected, validator, dependencies, premise)?;
            KernelRules::instantiate(&premise, subst)
        },
        Derivation::Resolve1Match { rule, goal_state, selected_subgoal_index, subst } => {
            require_same_context(expected, rule.context())?;
            require_same_context(expected, goal_state.context())?;
            preflight_substitution_contexts(expected, subst)?;
            validate_substitution(expected, validator, subst)?;
            let rule = rebuild_premise(expected, validator, dependencies, rule)?;
            let goal_state = rebuild_premise(expected, validator, dependencies, goal_state)?;
            let expected_subst = KernelRules::match_terms_certified(
                &rule.prop().term().dest_imp_chain().1,
                &goal_state.prop().term().select_subgoal(*selected_subgoal_index).ok_or_else(
                    || KernelError::SubgoalIndexOutOfRange {
                        index: *selected_subgoal_index,
                        nprems: goal_state.prop().term().nprems(),
                    },
                )?,
                expected,
            )?;
            if subst != &expected_subst {
                return Err(KernelError::Invariant(
                    "resolve1_match subst does not match re-derived substitution".into(),
                ));
            }
            KernelRules::resolve1_match(&rule, &goal_state, *selected_subgoal_index)
        },

        Derivation::AxiomInstance { axiom_name, type_inst, term_inst } => {
            let ctx = validator.ok_or(KernelError::UnsupportedAcceptanceDerivation)?;
            if logic_basis.is_none() {
                return Err(KernelError::Invariant(
                    "AxiomInstance requires an installed logic basis".into(),
                ));
            }
            dependencies.insert_axiom(axiom_name.clone());
            let prop = ctx.certify_prop(RawTerm::const_(axiom_name.clone(), Ty::prop()))?;
            Ok(KernelThm::new(
                Vec::new(),
                prop,
                Derivation::AxiomInstance {
                    axiom_name: axiom_name.clone(),
                    type_inst: type_inst.clone(),
                    term_inst: term_inst.clone(),
                },
            ))
        },

        Derivation::ConservativeDefinition { const_name, rhs, witness } => {
            let ctx = validator.ok_or(KernelError::UnsupportedAcceptanceDerivation)?;
            if ctx.signature().const_type(const_name).is_some() {
                return Err(KernelError::DuplicateDeclaration { name: const_name.clone() });
            }
            let _ = ctx.validate_cterm(rhs)?;
            // Use a synthetic prop — the definition is validated by freshness check.
            let prop = CProp::new(
                Term::Var { name: Name::from("def"), index: 0, ty: Ty::prop() },
                expected,
            )?;
            Ok(KernelThm::new(
                Vec::new(),
                prop,
                Derivation::ConservativeDefinition {
                    const_name: const_name.clone(),
                    rhs: rhs.clone(),
                    witness: witness.clone(),
                },
            ))
        },
    }
}
