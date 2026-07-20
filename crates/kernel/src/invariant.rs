use super::{
    CProp, CTerm, ContextStamp, Derivation, InstEntry, KernelError, KernelRules, KernelThm, ProofContext, RawTerm,
    theory::{DependencySet, TrustedTheory},
};

/// Canonical result reconstructed by owner-parameterized accepting replay.
pub(crate) struct ReplayResult {
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

    pub(crate) fn context(&self) -> ContextStamp {
        self.context
    }

    pub(crate) fn hyps(&self) -> &[CProp] {
        &self.hyps
    }

    pub(crate) fn prop(&self) -> &CProp {
        &self.prop
    }

    pub(crate) fn dependencies(&self) -> &DependencySet {
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
    logic_basis: Option<&super::LogicBasis>,
    owner: Option<&TrustedTheory>,
) -> Result<KernelThm, KernelError> {
    validate_theorem_fields(expected, validator, theorem)?;
    let replayed =
        replay_derivation(expected, validator, dependencies, theorem.derivation(), logic_basis, owner)?;
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
    rebuild_premise(theorem.context(), None, &mut dependencies, theorem, None, None)?;
    Ok(())
}

/// Replay one closed candidate under the exact immutable owner context.
pub(crate) fn replay_closed_theorem_in(
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
        Some(theory),
    )?;
    Ok(ReplayResult::from_kernel(replayed, dependencies))
}

fn replay_derivation(
    expected: ContextStamp,
    validator: Option<&ProofContext>,
    dependencies: &mut DependencySet,
    derivation: &Derivation,
    logic_basis: Option<&super::LogicBasis>,
    owner: Option<&TrustedTheory>,
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
            let premise = rebuild_premise(expected, validator, dependencies, premise, logic_basis, owner)?;
            KernelRules::symmetric(&premise)
        },
        Derivation::Transitive { left, right } => {
            require_same_context(expected, left.context())?;
            require_same_context(expected, right.context())?;
            let left = rebuild_premise(expected, validator, dependencies, left, logic_basis, owner)?;
            let right = rebuild_premise(expected, validator, dependencies, right, logic_basis, owner)?;
            KernelRules::transitive(&left, &right)
        },
        Derivation::ImpliesIntr { assumption, premise } => {
            require_same_context(expected, assumption.context())?;
            require_same_context(expected, premise.context())?;
            validate_cprop(expected, validator, assumption)?;
            let premise = rebuild_premise(expected, validator, dependencies, premise, logic_basis, owner)?;
            KernelRules::implies_intr(assumption, &premise)
        },
        Derivation::ImpliesElim { major, minor } => {
            require_same_context(expected, major.context())?;
            require_same_context(expected, minor.context())?;
            let major = rebuild_premise(expected, validator, dependencies, major, logic_basis, owner)?;
            let minor = rebuild_premise(expected, validator, dependencies, minor, logic_basis, owner)?;
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
            let premise = rebuild_premise(expected, validator, dependencies, premise, logic_basis, owner)?;
            KernelRules::forall_intr(variable, &premise)
        },
        Derivation::ForallElim { forall, arg } => {
            require_same_context(expected, forall.context())?;
            require_same_context(expected, arg.context())?;
            validate_cterm(expected, validator, arg)?;
            let forall = rebuild_premise(expected, validator, dependencies, forall, logic_basis, owner)?;
            KernelRules::forall_elim(&forall, arg)
        },
        Derivation::Combination { function, argument } => {
            require_same_context(expected, function.context())?;
            require_same_context(expected, argument.context())?;
            let function = rebuild_premise(expected, validator, dependencies, function, logic_basis, owner)?;
            let argument = rebuild_premise(expected, validator, dependencies, argument, logic_basis, owner)?;
            KernelRules::combination(&function, &argument)
        },
        Derivation::Abstraction { variable_name, variable_type, premise } => {
            require_same_context(expected, premise.context())?;
            let premise = rebuild_premise(expected, validator, dependencies, premise, logic_basis, owner)?;
            KernelRules::abstraction(variable_name.clone(), variable_type.clone(), &premise)
        },
        Derivation::EqualIntr { left, right } => {
            require_same_context(expected, left.context())?;
            require_same_context(expected, right.context())?;
            let left = rebuild_premise(expected, validator, dependencies, left, logic_basis, owner)?;
            let right = rebuild_premise(expected, validator, dependencies, right, logic_basis, owner)?;
            KernelRules::equal_intr(&left, &right)
        },
        Derivation::EqualElim { equality, minor } => {
            require_same_context(expected, equality.context())?;
            require_same_context(expected, minor.context())?;
            let equality = rebuild_premise(expected, validator, dependencies, equality, logic_basis, owner)?;
            let minor = rebuild_premise(expected, validator, dependencies, minor, logic_basis, owner)?;
            KernelRules::equal_elim(&equality, &minor)
        },
        Derivation::SubstPremise { equality, goal_state, selected_subgoal_index } => {
            require_same_context(expected, equality.context())?;
            require_same_context(expected, goal_state.context())?;
            let equality = rebuild_premise(expected, validator, dependencies, equality, logic_basis, owner)?;
            let goal_state = rebuild_premise(expected, validator, dependencies, goal_state, logic_basis, owner)?;
            KernelRules::subst_premise(&equality, &goal_state, *selected_subgoal_index)
        },
        Derivation::Generalize { frees, start_index, premise } => {
            require_same_context(expected, premise.context())?;
            if validator.is_some()
                && let Some((name, _)) = frees.first()
            {
                return Err(KernelError::UndeclaredFree(name.clone()));
            }
            let premise = rebuild_premise(expected, validator, dependencies, premise, logic_basis, owner)?;
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
            let premise = rebuild_premise(expected, validator, dependencies, premise, logic_basis, owner)?;
            KernelRules::instantiate(&premise, subst)
        },
        Derivation::Resolve1Match { rule, goal_state, selected_subgoal_index, subst } => {
            require_same_context(expected, rule.context())?;
            require_same_context(expected, goal_state.context())?;
            preflight_substitution_contexts(expected, subst)?;
            validate_substitution(expected, validator, subst)?;
            let rule = rebuild_premise(expected, validator, dependencies, rule, logic_basis, owner)?;
            let goal_state = rebuild_premise(expected, validator, dependencies, goal_state, logic_basis, owner)?;
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
            let basis = logic_basis.ok_or_else(|| KernelError::Invariant(
                "AxiomInstance requires an installed logic basis".into(),
            ))?;
            // Look up the axiom schema FROM THE BASIS (not from derivation)
            let schema = basis.get_axiom(axiom_name)
                .ok_or_else(|| KernelError::Invariant(
                    format!("axiom `{axiom_name}` not found in installed logic basis").into(),
                ))?;
            // Independently reconstruct: type subst → instantiate binders
            let typed = crate::term::subst_types(&schema.prop, type_inst)?;
            let body = crate::term::instantiate_schema_binders(&typed, term_inst)?;
            // Certify the independently-reconstructed proposition
            let replayed_prop = ctx.certify_prop(body)?;
            let _schema_id = schema.id();
            dependencies.insert_axiom(super::AxiomDependencyId::compute(basis.id, schema.id()));
            Ok(KernelThm::new(
                Vec::new(),
                replayed_prop,
                Derivation::AxiomInstance {
                    axiom_name: axiom_name.clone(),
                    type_inst: type_inst.clone(),
                    term_inst: term_inst.clone(),
                },
            ))
        },

        Derivation::ConservativeDefinition { definition: def_id } => {
            let ctx = validator.ok_or(KernelError::UnsupportedAcceptanceDerivation)?;

            // 1. Walk the owner's extension chain to find the matching certificate
            let owner = owner.ok_or(KernelError::UnsupportedAcceptanceDerivation)?;
            let certificate = owner.find_definition_certificate(def_id)
                .ok_or_else(|| KernelError::Invariant(
                    format!("definition {def_id:?} not found in owner theory ancestry").into(),
                ))?;

            // 2. Verify constant is declared in owner signature with declared type
            let declared_ty = ctx.signature()
                .const_type(&certificate.name)
                .ok_or_else(|| KernelError::UndeclaredConst(certificate.name.clone()))?;
            if declared_ty != &certificate.declared_ty {
                return Err(KernelError::TypeMismatch {
                    expected: declared_ty.clone(),
                    actual: certificate.declared_ty.clone(),
                });
            }

            // 3. Re-certify RHS and verify type matches declared type
            let rhs = ctx.certify_term(certificate.rhs_raw.clone())?;
            if &rhs.ty() != &certificate.declared_ty {
                return Err(KernelError::TypeMismatch {
                    expected: certificate.declared_ty.clone(),
                    actual: rhs.ty(),
                });
            }

            // 4. Verify RHS has no free variables
            if certificate.rhs_raw.has_free_vars() {
                return Err(KernelError::Invariant(
                    "definition RHS is not closed".into(),
                ));
            }

            // 5. Independently reconstruct: |- const_name == rhs
            let reconstructed = RawTerm::Eq {
                lhs: Box::new(RawTerm::Const {
                    name: certificate.name.clone(),
                    ty: certificate.declared_ty.clone(),
                }),
                rhs: Box::new(certificate.rhs_raw.clone()),
            };
            let replayed = ctx.certify_prop(reconstructed)?;

            // 6. Insert the definition dependency
            dependencies.insert_definition(*def_id);

            Ok(KernelThm::new(
                Vec::new(),
                replayed,
                Derivation::ConservativeDefinition { definition: *def_id },
            ))
        },
    }
}
