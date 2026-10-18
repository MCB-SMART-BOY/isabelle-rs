//! Remove replayed local scope parameters from proof-only operands.
use std::collections::BTreeSet;

use crate::{KernelError, KernelThm, Name, ProofScope, Term};

use super::{Proof, inspect::ProofVariables, terms, transform};

fn collect_output_parameters(theorem: &KernelThm) -> (BTreeSet<Name>, BTreeSet<Name>) {
    let mut type_names = BTreeSet::new();
    let mut term_names = BTreeSet::new();
    let mut visit = |term: &Term| {
        term.for_each_type_annotation(&mut |ty| {
            ty.for_each_type_free(&mut |name, _| {
                type_names.insert(name.clone());
            });
        });
        terms::visit_free_variables(term, &mut |name, _| {
            term_names.insert(name.clone());
        });
    };
    visit(theorem.prop().term());
    for hyp in theorem.hyps() {
        visit(hyp.term());
    }
    for (left, right) in theorem.payload().flex_pairs() {
        visit(left.term());
        visit(right.term());
    }
    for (ty, _) in theorem.payload().sort_obligations() {
        ty.for_each_type_free(&mut |name, _| {
            type_names.insert(name.clone());
        });
    }
    (type_names, term_names)
}

pub(super) fn lower_export_scope(
    theorem: &KernelThm,
    scope: &ProofScope,
    proof: Proof,
) -> Result<Proof, KernelError> {
    let (present_types, present_terms) = collect_output_parameters(theorem);
    let variables = ProofVariables::collect(&proof);
    let type_names = scope
        .type_frees()
        .iter()
        .filter(|(name, sort)| {
            !present_types.contains(*name)
                && variables.atoms.iter().any(|atom| {
                    let mut matches = false;
                    atom.for_each_type_free(&mut |actual, actual_sort| {
                        matches |= actual == *name && actual_sort == *sort;
                    });
                    matches
                })
        })
        .map(|(name, _)| name.clone())
        .collect::<BTreeSet<_>>();
    let term_names = scope
        .frees()
        .keys()
        .filter(|name| {
            !present_terms.contains(*name)
                && variables.frees.iter().any(|(actual, _)| actual == *name)
        })
        .cloned()
        .collect::<BTreeSet<_>>();
    if type_names.is_empty() && term_names.is_empty() {
        return Ok(proof);
    }
    let index = variables.max_index.map_or(Ok(0), terms::next_depth)?;
    transform::generalize(proof, &type_names, &term_names, index)
}
