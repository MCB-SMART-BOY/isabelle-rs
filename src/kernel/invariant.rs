use super::{Derivation, KernelError, KernelRules, KernelThm};

pub fn check_kernel_thm(thm: &KernelThm) -> Result<(), KernelError> {
    if !thm.prop().term().ty().is_prop() {
        return Err(KernelError::NotProposition(thm.prop().term().ty()));
    }
    for hyp in thm.hyps() {
        if !hyp.term().ty().is_prop() {
            return Err(KernelError::NotProposition(hyp.term().ty()));
        }
    }

    let replayed = replay_derivation(thm.derivation())?;
    if replayed.hyps() != thm.hyps() || replayed.prop() != thm.prop() {
        return Err(KernelError::Invariant(
            "derivation replay does not match theorem fields".into(),
        ));
    }
    Ok(())
}

pub fn replay_derivation(derivation: &Derivation) -> Result<KernelThm, KernelError> {
    match derivation {
        Derivation::Assume { prop } => Ok(KernelRules::assume(prop.clone()).into_kernel()),
        Derivation::Reflexive { term } => Ok(KernelRules::reflexive(term.clone()).into_kernel()),
        Derivation::Symmetric { premise } => {
            check_kernel_thm(premise)?;
            KernelRules::symmetric(premise)
        },
        Derivation::Transitive { left, right } => {
            check_kernel_thm(left)?;
            check_kernel_thm(right)?;
            KernelRules::transitive(left, right)
        },
        Derivation::ImpliesIntr { assumption, premise } => {
            check_kernel_thm(premise)?;
            KernelRules::implies_intr(assumption, premise)
        },
        Derivation::ImpliesElim { major, minor } => {
            check_kernel_thm(major)?;
            check_kernel_thm(minor)?;
            KernelRules::implies_elim(major, minor)
        },
        Derivation::BetaConversion { redex } => {
            Ok(KernelRules::beta_conversion(redex.clone())?.into_kernel())
        },
        Derivation::ForallIntr { variable, premise } => {
            check_kernel_thm(premise)?;
            KernelRules::forall_intr(variable, premise)
        },
        Derivation::ForallElim { forall, arg } => {
            check_kernel_thm(forall)?;
            KernelRules::forall_elim(forall, arg)
        },
        Derivation::Combination { function, argument } => {
            check_kernel_thm(function)?;
            check_kernel_thm(argument)?;
            KernelRules::combination(function, argument)
        },
        Derivation::Abstraction { variable_name, variable_type, premise } => {
            check_kernel_thm(premise)?;
            KernelRules::abstraction(variable_name.clone(), variable_type.clone(), premise)
        },
        Derivation::EqualIntr { left, right } => {
            check_kernel_thm(left)?;
            check_kernel_thm(right)?;
            KernelRules::equal_intr(left, right)
        },
        Derivation::EqualElim { equality, minor } => {
            check_kernel_thm(equality)?;
            check_kernel_thm(minor)?;
            KernelRules::equal_elim(equality, minor)
        },
        Derivation::SubstPremise { equality, goal_state, selected_subgoal_index } => {
            check_kernel_thm(equality)?;
            check_kernel_thm(goal_state)?;
            KernelRules::subst_premise(equality, goal_state, *selected_subgoal_index)
        },
        Derivation::Generalize { frees, start_index, premise } => {
            check_kernel_thm(premise)?;
            let expected_start = premise.max_var_index().map_or(0, |m| m + 1);
            if expected_start != *start_index {
                return Err(KernelError::Invariant(format!(
                    "generalize start_index mismatch: expected {expected_start}, recorded {start_index}"
                )));
            }
            KernelRules::generalize(premise, frees)
        },
        Derivation::Instantiate { subst, premise } => {
            check_kernel_thm(premise)?;
            KernelRules::instantiate(premise, subst)
        },
        Derivation::Resolve1Match { rule, goal_state, selected_subgoal_index, subst } => {
            check_kernel_thm(rule)?;
            check_kernel_thm(goal_state)?;
            let expected_subst = KernelRules::match_terms_certified(
                &rule.prop().term().dest_imp_chain().1,
                &goal_state.prop().term().select_subgoal(*selected_subgoal_index).ok_or_else(
                    || KernelError::SubgoalIndexOutOfRange {
                        index: *selected_subgoal_index,
                        nprems: goal_state.prop().term().nprems(),
                    },
                )?,
            )?;
            if subst != &expected_subst {
                return Err(KernelError::Invariant(
                    "resolve1_match subst does not match re-derived substitution".into(),
                ));
            }
            KernelRules::resolve1_match(rule, goal_state, *selected_subgoal_index)
        },
    }
}
