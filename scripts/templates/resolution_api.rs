// Classification: design-only standalone template; not production code.
#![allow(dead_code)]

use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Name(pub String);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Term;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelThm;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstEntry;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KernelError {
    SubgoalIndexOutOfRange { index: usize, nprems: usize },
    RequiresLifting { rule_var: Name, goal_var: Name },
}

pub fn dest_imp_chain(_term: &Term) -> (Vec<Term>, Term) {
    unimplemented!("design template")
}

pub fn mk_imp_chain(_prems: &[Term], _conclusion: &Term) -> Term {
    unimplemented!("design template")
}

pub fn nprems(_prop: &Term) -> usize {
    unimplemented!("design template")
}

pub fn select_subgoal(_prop: &Term, _index: usize) -> Option<Term> {
    unimplemented!("design template")
}

pub fn replace_subgoal_with_premises(
    _prop: &Term,
    _index: usize,
    _new_prems: &[Term],
) -> Result<Term, KernelError> {
    unimplemented!("design template")
}

pub trait ResolutionKernel {
    fn bicompose(
        rule: &KernelThm,
        goal_state: &KernelThm,
        selected_subgoal_index: usize,
    ) -> Result<KernelThm, KernelError>;

    fn match_terms(pattern: &Term, target: &Term) -> Result<Vec<InstEntry>, KernelError>;

    fn lift_rule(rule: &KernelThm, goal: &KernelThm) -> KernelThm;
}

pub fn detect_collision(
    rule_frees: &HashSet<Name>,
    goal_frees: &HashSet<Name>,
    rule_vars: &HashSet<(Name, usize)>,
    goal_vars: &HashSet<(Name, usize)>,
) -> Result<(), KernelError> {
    if let Some(rule_var) = rule_frees.intersection(goal_frees).next() {
        return Err(KernelError::RequiresLifting {
            rule_var: rule_var.clone(),
            goal_var: rule_var.clone(),
        });
    }
    if let Some(rule_var) = rule_vars.intersection(goal_vars).next() {
        return Err(KernelError::RequiresLifting {
            rule_var: rule_var.0.clone(),
            goal_var: rule_var.0.clone(),
        });
    }
    Ok(())
}
