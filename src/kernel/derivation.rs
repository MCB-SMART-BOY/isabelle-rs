use super::{CProp, CTerm, InstEntry, KernelThm, Name, Ty};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Derivation {
    Assume {
        prop: CProp,
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
        /// The free variables that were schematicised, in order.
        frees: Vec<(Name, Ty)>,
        /// The starting Var index used (first free → Var(i, …), second → Var(i+1, …)).
        start_index: usize,
        premise: Box<KernelThm>,
    },
    Instantiate {
        /// Substitution entries with certified replacements.
        subst: Vec<InstEntry>,
        premise: Box<KernelThm>,
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
}
