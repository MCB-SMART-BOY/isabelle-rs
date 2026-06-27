# Kernel Attack Tests

This is the regression matrix for trusted-kernel soundness attacks. Default
tests must pass in normal CI. Ignored tests document known holes that should
start failing loudly once the parser/type boundary work begins.

This matrix is scoped to the current Rust Isabelle/Pure-inspired kernel
prototype. Passing these tests does not mean full Isabelle compatibility or full
proofterm checking; it means the listed trusted-boundary regressions are covered.

## Default Tests

| Attack | Expected result | Test |
|---|---|---|
| Chain two equalities with known distinct object types through `transitive` | rejected with `KernelError::TypeMismatch` | `tests/kernel_soundness.rs::transitive_rejects_known_equality_type_mismatch`; `src/core/thm.rs::test_transitive_rejects_known_equality_type_mismatch` |
| Chain two dummy-typed equalities whose middle terms have incompatible known types | rejected with `KernelError::TypeMismatch` | `tests/kernel_soundness.rs::transitive_rejects_dummy_equality_type_with_known_middle_type_mismatch` |
| Beta-convert `(λx. x) a` and expose raw `Bound(0)` | rejected by construction; RHS is `a` | `tests/kernel_soundness.rs::beta_conversion_substitutes_the_argument`; `src/core/thm.rs::test_beta_conversion_substitutes_argument_for_bound_zero` |
| Abstract over a variable that is free in hypotheses | rejected with `FreeVarInHypotheses` | `tests/kernel_soundness.rs::abstraction_rejects_free_variable_in_hypotheses` |
| Treat `assume(A)` as an unconditional theorem | impossible through public shape; discharge requires `implies_intr` | `tests/kernel_soundness.rs::implies_intro_is_the_only_way_to_discharge_assume_here` |
| Count oracle-free `assume(A)` as a closed proved lemma | rejected by `is_closed_proved()` and batch stats | `tests/kernel_soundness.rs::implies_intro_is_the_only_way_to_discharge_assume_here`; `src/isar/method.rs::test_open_oracle_free_theorem_is_not_closed_proved_outcome`; `src/isar/method.rs::test_verify_batch_does_not_count_open_theorem_as_verified` |
| Count `accept_all` / proof-skipped theory processing as a closed proved theorem | rejected by `TheoryProcessor::process_source_verified`; indexed as admitted but not registered in final `Theory` | `src/theory/loader.rs::test_accept_all_is_admitted_not_closed_verified` |
| Report `accept_all` theory files as session-verified because they produced index entries | rejected by `SessionBuilder`; build/classifier report zero closed proved theorems | `src/theory/session_builder.rs::test_accept_all_does_not_report_session_verified_theorems`; `src/theory/session_builder.rs::test_accept_all_classifier_is_not_full_success` |
| Treat `HolTheoremDb` searchable facts as a trusted theorem table | DB exposes separate searchable and closed-proved counts | `src/hol/hol_loader.rs::test_hol_theorem_db_distinguishes_searchable_from_closed_proved`; `src/hol/hol_loader.rs::test_hol_theorem_db_counts_closed_proved_facts_separately` |
| Let `Typ::dummy()` pass unnoticed at an explicit non-dummy boundary | rejected by `CTerm::require_non_dummy` | `tests/kernel_soundness.rs::dummy_type_is_detectable_at_kernel_boundaries` |
| Drop oracle footprint through a real kernel rule | result remains tainted | `src/core/thm.rs::test_oracle_footprint_propagates_through_rules` |
| Drop oracle footprint through a multi-premise rule | result remains tainted | `src/core/thm.rs::test_union_of_proved_and_admitted_is_tainted` |
| Drop sort hypotheses through single-premise or multi-premise rules | `shyps` preserved/unioned | `src/core/thm.rs::test_shyps_propagate_through_single_premise_rule`; `src/core/thm.rs::test_shyps_union_through_multi_premise_rule` |
| Use `combination` with a known argument-domain mismatch | rejected with `KernelError::TypeMismatch` | `src/core/thm.rs::test_combination_rejects_known_type_mismatch` |
| Identify lambdas with distinct known binder types | rejected by `alpha_eq` | `src/core/thm.rs::test_alpha_eq_rejects_distinct_binder_types` |
| Use `implies_elim` across alpha-equal antecedents with incompatible known types | rejected with `KernelError::TypeMismatch` | `tests/kernel_soundness.rs::implies_elim_rejects_known_antecedent_type_mismatch` |
| Instantiate `!!x. P x` with a known wrong-typed term | rejected with `KernelError::TypeMismatch` | `tests/kernel_soundness.rs::forall_elim_rejects_known_binder_argument_type_mismatch` |
| Apply an environment that maps `?x::nat` to a `bool` term | public path rejects through `instantiate_checked`; old infallible behavior is internal test-only | `tests/kernel_soundness.rs::instantiate_checked_rejects_known_type_mismatch`; `src/core/thm.rs::test_instantiate_legacy_is_test_only_and_conservative` |
| Rewrite a premise through a same-name lhs with incompatible known type | `subst_premise` returns `None` | `tests/kernel_soundness.rs::subst_premise_rejects_known_lhs_premise_type_mismatch` |
| Discharge a subgoal through `bicompose` using same-name incompatible terms | `bicompose` returns `None` | `tests/kernel_soundness.rs::bicompose_rejects_known_alpha_match_type_mismatch` |
| Resolve through `bicompose_eresolve` using unifier same-name incompatible terms | `bicompose_eresolve` returns `None` | `tests/kernel_soundness.rs::bicompose_eresolve_rejects_known_unifier_type_mismatch` |
| Instantiate a rewrite rule with a known wrong-typed target term | `rewr_conv` returns `None` | `tests/kernel_soundness.rs::rewr_conv_rejects_ill_typed_rule_instantiation` |
| Transform a theorem with an attribute and present the result as oracle-free | result carries `admitted:attribute_transformation` | `src/isar/method.rs::test_apply_attributes_rule_format_is_admitted` |
| Replay `assume(A)` as if it were a closed proved lemma | replay succeeds as `A |- A`, but `is_closed_proved()` stays false | `src/core/proofterm.rs::assume_replay_succeeds_but_is_open` |
| Treat admitted theorem proof objects as independent kernel proofs | `check_proof()` rejects oracle proof replay | `src/core/proofterm.rs::admitted_theorem_does_not_pass_kernel_replay` |
| Use an admitted theorem as a premise to a supported replay rule | derived theorem remains usable as admitted, but independent replay fails on the oracle premise | `src/core/proofterm.rs::supported_replay_rejects_oracle_premise` |
| Replay a supported rule applied to an open premise and drop hypotheses | `hyps` are preserved and the result remains non-closed | `src/core/proofterm.rs::symmetric_replay_preserves_open_premise_hyps` |
| Mutate a theorem proposition after construction | `check_proof()` rejects mismatch against stored derivation | `src/core/thm.rs::test_check_proof_rejects_tampered_theorem_prop` |
| Mutate final theorem hypotheses after construction | `check_proof()` rejects burden mismatch | `src/core/thm.rs::test_check_proof_rejects_tampered_theorem_hyps` |
| Mutate final theorem oracle footprint after construction | `check_proof()` rejects burden mismatch | `src/core/thm.rs::test_check_proof_rejects_tampered_theorem_oracles` |
| Mutate final theorem unresolved `tpairs` after construction | `check_proof()` rejects burden mismatch | `src/core/thm.rs::test_check_proof_rejects_tampered_theorem_tpairs` |
| Mutate a nested premise derivation after construction | `check_proof()` rejects the derived theorem | `src/core/thm.rs::test_check_proof_rejects_tampered_premise_derivation` |
| Mark a proof body checked through an old path and then validate a tampered theorem | `Thm::validate_proof` replays burdens anyway | `src/core/thm.rs::test_validate_proof_rechecks_stale_checked_body` |
| Replay minimal proof rules without deriving their conclusion | `reflexive`, `symmetric`, `transitive`, `implies_intr`, and `implies_elim` are structurally replayed | `src/core/proofterm.rs::{reflexive_replay_succeeds_and_is_closed_proved,symmetric_replay_succeeds,transitive_replay_succeeds,implies_intro_and_elim_replay_succeed}` |
| Reject alpha-equivalent middle terms in supported `transitive` replay even though the kernel accepted them | replay uses kernel alpha-equivalence and known-type compatibility | `src/core/proofterm.rs::transitive_replay_accepts_alpha_equivalent_middle_terms` |
| Confuse unsupported replay rule with tampering or oracle failure | unsupported rules produce an explicit unsupported-rule error | `src/core/proofterm.rs::unsupported_rule_is_reported_separately_from_tampering` |

## Ignored Known-Gap Tests

These tests encode the desired final kernel behavior but are intentionally
ignored until parser/loader/type annotation are aligned. They should be enabled
only after the corresponding front-end representation gap is fixed.

| Known gap | Desired result | Ignored test |
|---|---|---|
| `Free("zero")` matches `Const("Groups.zero")` by suffix | `alpha_eq` rejects Free/Const confusion | `src/core/thm.rs::test_alpha_eq_should_reject_free_const_suffix_match` |
| `Var("x", i)` matches `Free("x")`, ignoring schematic index | `alpha_eq` rejects Var/Free confusion | `src/core/thm.rs::test_alpha_eq_should_reject_var_free_index_confusion` |

## Next Attack Tests To Add

- `subst_premise` must not rewrite across Free/Const or Var/Free confusion once
  strict `alpha_eq` is enabled.
- `bicompose` and `bicompose_eresolve` still need explicit oracle/tpairs/shyps
  propagation tests with non-empty burdens on both premises.
- `instantiate_checked` should eventually validate sort constraints and richer
  application typing once `CTerm` becomes a hard certification boundary.
- Trusted-boundary paths returning `Option<Thm>` should eventually distinguish
  ordinary non-match from `KernelError` rejection for auditability.
- Attribute transformations still need real derivation-producing conversions;
  they are currently honest admissions, not proved transformations.
- Proof replay still needs coverage for
  `combination`/`abstraction`/`beta_conversion`/`forall_*`/`instantiate`/
  `bicompose*`; unsupported rules currently fail replay instead of being
  trusted.
- Next T4 attack-test batch should start with `beta_conversion`,
  `forall_intr`, and `forall_elim`, then move to
  `combination`/`abstraction`, checked instantiation, and resolution rules.
