use std::collections::BTreeSet;

use super::{
    ReplayEnvironment, collect_const_dependencies, collect_recorded_operand_dependencies,
    require_same_context, validate_cterm, validate_theorem_fields,
};
use crate::{
    ContextStamp, DependencySet, Derivation, KernelError, KernelRules, KernelThm, LogicBasis, Name,
    Term, TrustedTheory, Ty,
};

pub(super) struct Replayed {
    pub(super) theorem: KernelThm,
    pub(super) environment: Option<ReplayEnvironment>,
}

#[derive(Clone, Copy)]
pub(super) struct ReplayFrame<'a> {
    pub(super) expected: ContextStamp,
    pub(super) environment: Option<&'a ReplayEnvironment>,
    pub(super) logic_basis: Option<&'a LogicBasis>,
    pub(super) owner: Option<&'a TrustedTheory>,
}

impl ReplayFrame<'_> {
    pub(super) fn rebuild(
        self,
        dependencies: &mut DependencySet,
        theorem: &KernelThm,
    ) -> Result<Replayed, KernelError> {
        // Only structural/stamp/index checks precede the source transformation.
        validate_theorem_fields(self.expected, None, theorem)?;
        let result = self.rebuild_derivation(dependencies, theorem.derivation())?;
        validate_theorem_fields(self.expected, result.environment.as_ref(), theorem)?;
        let replayed = &result.theorem;
        if replayed.context() != theorem.context()
            || replayed.hyps() != theorem.hyps()
            || replayed.prop() != theorem.prop()
            || replayed.payload() != theorem.payload()
            || replayed.max_var_index() != theorem.max_var_index()
        {
            return Err(if self.environment.is_some() {
                KernelError::AcceptanceReplayMismatch
            } else {
                KernelError::Invariant("derivation replay does not match theorem fields".into())
            });
        }
        if let Some(owner) = self.owner {
            collect_const_dependencies(owner, theorem, dependencies)?;
            collect_recorded_operand_dependencies(owner, theorem.derivation(), dependencies)?;
        }
        Ok(result)
    }

    fn rebuild_derivation(
        self,
        dependencies: &mut DependencySet,
        derivation: &Derivation,
    ) -> Result<Replayed, KernelError> {
        match derivation {
            Derivation::Generalize { type_names, term_names, index, source_frees, premise } => self
                .rebuild_generalize(
                    dependencies,
                    premise,
                    type_names,
                    term_names,
                    *index,
                    source_frees,
                ),
            Derivation::ForallIntr { variable, premise } => {
                let Term::Free { name, ty } = variable.term() else {
                    return Err(KernelError::NotAbstractable(variable.ty()));
                };
                self.rebuild_binder(dependencies, premise, name, ty, Some(variable))
            },
            Derivation::Abstraction { variable_name, variable_type, premise } => {
                self.rebuild_binder(dependencies, premise, variable_name, variable_type, None)
            },
            Derivation::ExportScope { scope, premise } => {
                require_same_context(scope.stamp(), premise.context())?;
                let owner = self.owner.ok_or(KernelError::UnsupportedAcceptanceDerivation)?;
                let context = scope.restore(owner.snapshot())?;
                let theorem = crate::rules::export_scope_with_dependencies(
                    owner,
                    &context,
                    premise,
                    dependencies,
                )?;
                require_same_context(self.expected, theorem.context())?;
                Ok(Replayed {
                    theorem,
                    environment: Some(ReplayEnvironment::new(&crate::ProofContext::new(
                        owner.snapshot().clone(),
                    ))),
                })
            },
            Derivation::Transfer { premise } => {
                let owner = self.owner.ok_or(KernelError::UnsupportedAcceptanceDerivation)?;
                let (theorem, evidence) = crate::rules::transfer_with_dependencies(owner, premise)?;
                dependencies.extend(&evidence);
                require_same_context(self.expected, theorem.context())?;
                Ok(Replayed {
                    theorem,
                    environment: Some(ReplayEnvironment::new(&crate::ProofContext::new(
                        owner.snapshot().clone(),
                    ))),
                })
            },
            _ => self.rebuild_ordinary(dependencies, derivation),
        }
    }

    fn rebuild_ordinary(
        self,
        dependencies: &mut DependencySet,
        derivation: &Derivation,
    ) -> Result<Replayed, KernelError> {
        preflight_ordinary_contexts(self.expected, derivation)?;
        let mut premises = Vec::new();
        // A premise transformation cannot revoke the current frame's lexical scope.
        let mut environment = self.environment.cloned();
        let mut result: Result<(), KernelError> = Ok(());
        derivation.for_each_premise(&mut |premise| {
            if result.is_err() {
                return;
            }
            result = (|| {
                let replayed = self.rebuild(dependencies, premise)?;
                merge_environment(&mut environment, replayed.environment)?;
                premises.push(replayed.theorem);
                Ok(())
            })();
        });
        result?;
        let theorem = super::derive::replay_rule(
            self.expected,
            environment.as_ref(),
            dependencies,
            derivation,
            &premises,
            self.logic_basis,
            self.owner,
        )?;
        if let Derivation::Instantiate { type_inst, subst, .. } = derivation {
            environment = environment.map(|env| env.instantiate(type_inst, subst)).transpose()?;
        }
        Ok(Replayed { theorem, environment })
    }

    fn rebuild_generalize(
        self,
        dependencies: &mut DependencySet,
        premise: &KernelThm,
        type_names: &BTreeSet<Name>,
        term_names: &BTreeSet<Name>,
        index: usize,
        source_frees: &[(Name, Ty)],
    ) -> Result<Replayed, KernelError> {
        let canonical: Vec<_> = crate::bound_proof::collect_lexical_frees(premise)
            .into_iter()
            .filter(|(name, _)| term_names.contains(name))
            .collect();
        if source_frees != canonical {
            return Err(KernelError::AcceptanceReplayMismatch);
        }
        let mut scoped = self.environment.cloned();
        for (name, ty) in source_frees {
            scoped = scoped.map(|env| env.with_free(name, ty)).transpose()?;
        }
        let source =
            ReplayFrame { environment: scoped.as_ref(), ..self }.rebuild(dependencies, premise)?;
        let theorem = KernelRules::generalize(&source.theorem, type_names, term_names, index)?;
        let environment = source
            .environment
            .map(|env| env.generalize(type_names, term_names, index))
            .transpose()?;
        Ok(Replayed { theorem, environment })
    }

    fn rebuild_binder(
        self,
        dependencies: &mut DependencySet,
        premise: &KernelThm,
        name: &Name,
        ty: &Ty,
        variable: Option<&crate::CTerm>,
    ) -> Result<Replayed, KernelError> {
        let scoped = self.environment.map(|env| env.bind_free(name, ty)).transpose()?;
        if let Some(variable) = variable {
            validate_cterm(self.expected, scoped.as_ref(), variable)?;
        }
        let source =
            ReplayFrame { environment: scoped.as_ref(), ..self }.rebuild(dependencies, premise)?;
        let theorem = if let Some(variable) = variable {
            KernelRules::forall_intr(variable, &source.theorem)?
        } else {
            KernelRules::abstraction(name.clone(), ty.clone(), &source.theorem)?
        };
        let environment = match (source.environment, self.environment) {
            (Some(env), Some(original)) => Some(env.without_binding(original)),
            (env, _) => env,
        };
        Ok(Replayed { theorem, environment })
    }
}

fn merge_environment(
    target: &mut Option<ReplayEnvironment>,
    source: Option<ReplayEnvironment>,
) -> Result<(), KernelError> {
    match (target.as_mut(), source) {
        (Some(target), Some(source)) => target.merge(&source),
        (None, source) => {
            *target = source;
            Ok(())
        },
        (_, None) => Ok(()),
    }
}

fn preflight_ordinary_contexts(
    expected: ContextStamp,
    derivation: &Derivation,
) -> Result<(), KernelError> {
    let mut result = Ok(());
    let mut check = |actual| {
        if result.is_ok() {
            result = require_same_context(expected, actual);
        }
    };
    derivation.for_each_premise(&mut |premise| check(premise.context()));
    derivation.for_each_certified_term(&mut |term| check(term.context()));
    match derivation {
        Derivation::Assume { prop }
        | Derivation::Weaken { assumption: prop, .. }
        | Derivation::ImpliesIntr { assumption: prop, .. } => check(prop.context()),
        _ => {},
    }
    result
}
