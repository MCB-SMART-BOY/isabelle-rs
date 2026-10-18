# Kernel Attack Tests

This regression matrix separates legacy `src/core` behavior from the strict
TCB in `crates/kernel` (re-exported by `src/kernel/mod.rs`). The historical
attack rows remain useful, but the current declaration, source, loader,
proof-result, and automation boundaries also have dedicated contract suites.
Passing those tests does not mean full Isabelle/HOL or TPTP compatibility or a
successful official Isabelle runtime differential. Among the bundled
125-case sample, only the audited `HOL::TrueI` projection reaches a kernel
token (`KernelTrustedClosed: 1/125`); the separate Rust THM consumers are
outside that sample. The complete HOL theory and unrelated HOL/ML commands
are not checked by the projection.

The 125-case result is a dated bundled-source observation, not a rerun after
the automation migration. P2/P3/P4 implementation has resumed, and external
Rust THM consumers have narrow executed closure evidence, but no full native
compatibility acceptance; check the [current delivery state](../status/PROJECT_STATUS.md#current-delivery-state)
and [Rust variable consumer record](../status/PROJECT_STATUS.md#rust-thm-type-and-variable-transformations-2026-10-19).
This matrix names intended regression tests, not the outcome of a current full
workspace test.

## Default Tests

| Attack | Expected result | Test |
|---|---|---|
| Chain two equalities with known distinct object types through `transitive` | rejected with `KernelError::TypeMismatch` | `tests/kernel_soundness.rs::transitive_rejects_known_equality_type_mismatch`; `src/core/thm.rs::test_transitive_rejects_known_equality_type_mismatch` |
| Chain two dummy-typed equalities whose middle terms have incompatible known types | rejected with `KernelError::TypeMismatch` | `tests/kernel_soundness.rs::transitive_rejects_dummy_equality_type_with_known_middle_type_mismatch` |
| Chain two equalities through Free/Const suffix-compatible middle terms | rejected with `KernelError::MidTermsNotEquiv` | `tests/kernel_soundness.rs::transitive_rejects_free_const_suffix_middle_term` |
| Beta-convert `(λx. x) a` and expose raw `Bound(0)` | rejected by construction; RHS is `a` | `tests/kernel_soundness.rs::beta_conversion_substitutes_the_argument`; `src/core/thm.rs::test_beta_conversion_substitutes_argument_for_bound_zero` |
| Abstract over a variable that is free in hypotheses | rejected with `FreeVarInHypotheses` | `tests/kernel_soundness.rs::abstraction_rejects_free_variable_in_hypotheses` |
| Treat `assume(A)` as an unconditional theorem | impossible through public shape; discharge requires `implies_intr` | `tests/kernel_soundness.rs::implies_intro_is_the_only_way_to_discharge_assume_here` |
| Count oracle-free `assume(A)` as a closed proved lemma | rejected by `is_closed_proved()` and batch stats | `tests/kernel_soundness.rs::implies_intro_is_the_only_way_to_discharge_assume_here`; `src/isar/method.rs::test_open_oracle_free_theorem_is_not_closed_proved_outcome`; `src/isar/method.rs::test_verify_batch_does_not_count_open_theorem_as_verified` |
| Count a compat, open, admitted, or axiom-accepted result as `TransitionalStrictClosed` in verification reports | `ProofOutcome` keeps those legacy buckets separate; only `ProofOutcome::TransitionalStrictClosed` increments the transitional count, and that count is not `KernelTrustedClosed` | `src/isar/method.rs::{proof_outcome_classifies_transitional_strict_closed,proof_outcome_does_not_count_axiom_accepted_strict_result,proof_outcome_classifies_compat_closed_oracle_free,proof_outcome_classifies_open_oracle_free,proof_outcome_classifies_admitted_reason}` |
| Present a theorem declaration as a verified LSP result before retaining and checking its proof block | registered outer commands are split, but the experimental document executor leaves every declaration as `lemma-proof-pending` with an unsolved goal; it does not invoke theorem verification at declaration time | `src/document/document.rs::document_splits_registered_outer_commands`; `src/fleche/engine.rs::{lemma_declaration_remains_pending,full_document_does_not_verify_a_declaration_before_proof_close}` |
| Count a compat implication identity as the transitional strict vertical slice | strict `A ==> A` is covered separately from compat `A ==> A`; only the checked path reaches the legacy summary bucket, while the independent kernel test exercises a real `CProp` theorem | `tests/kernel_rewrite_soundness.rs::strict_kernel_pure_imp_identity_closes`; `src/isar/method.rs::{strict_vertical_slice_pure_imp_identity,proof_outcome_counts_pure_imp_identity_as_transitional_strict_closed,proof_outcome_does_not_count_compat_identity_as_transitional_strict_closed}` |
| Return an oracle-free proof-method result with ambient proof-state hypotheses as an accepted lemma | proof result must be exported by legal `implies_intr` discharge of known context assumptions, or explicitly admitted as `admitted:goal_export_*`; unknown hyps, open subgoals, unresolved `tpairs`, and prop mismatches are not dropped | `src/isar/method.rs::{proof_closure_discharge_single_goal_hyp,proof_closure_discharge_two_premises,proof_closure_does_not_drop_unknown_hyp,proof_closure_rejects_oracle_or_admitted,proof_closure_rejects_prop_mismatch,proof_closure_rejects_open_subgoals,proof_closure_rejects_unresolved_tpairs,proof_closure_alpha_equivalent_hyp_can_discharge,proof_closure_preserves_prop_as_original_goal,goal_initialization_does_not_return_self_hyp,verify_hol_trans_no_open_hyps,verify_nat_suc_not_zero_no_self_hyp,verify_no_open_oracle_free_results_in_core_batch}` |
| Treat open, admitted, unresolved, or conditional rewrite theorems as unconditional simp rules | `RewriteRule::from_thm` rejects theorem hyps, oracle/admitted footprints, unresolved `tpairs`, and Pure premises; conditional rewriting and unproved HOL built-in templates are skipped in v1 | `src/core/simplifier.rs::{rewrite_rule_rejects_theorem_with_hyps,rewrite_rule_rejects_oracle_or_admitted_theorem,rewrite_rule_rejects_unresolved_tpairs,rewrite_rule_rejects_conditional_rule_in_v1,simp_does_not_import_rule_hyps_into_result,simp_skips_conditional_rule_in_v1}`; `src/tools/simp.rs::test_builtin_rules_require_closed_theorem_sources` |
| Introduce a proof-state local assumption through compatibility theorem construction | `ProofState::assume` now certifies the proposition through the checked path and produces a Strict open theorem `A |- A` | `src/isar/proof_state.rs::{proof_state_local_assumption_is_strict_open_theorem,proof_state_local_assumption_passes_strict_invariant}` |
| Count a strict proof-state local assumption as a closed proved lemma | rejected by `is_strict_closed_proved()` because the theorem remains open | `src/isar/proof_state.rs::proof_state_local_assumption_not_closed_proved` |
| Feed a compatibility or dummy-tainted CTerm into proof-state checked assumption | rejected with `KernelError::CompatCTerm` / `KernelError::DummyType` | `src/isar/proof_state.rs::{proof_state_checked_assumption_rejects_compat_cterm,proof_state_checked_assumption_rejects_dummy_type}` |
| Initialize a proof goal through compatibility theorem construction | `Goal::init` and `ProofState::new_checked_goal` use checked proposition certification and strict `ThmKernel::assume` | `src/isar/proof.rs::{proof_goal_checked_constructor_is_strict_open_theorem,proof_goal_checked_constructor_passes_strict_invariant}`; `src/isar/proof_state.rs::{proof_state_checked_goal_is_strict_open_theorem,proof_state_checked_goal_passes_strict_invariant}` |
| Count a strict proof goal as a closed proved lemma | rejected by `is_strict_closed_proved()` because the goal theorem is an open proof obligation | `src/isar/proof.rs::proof_goal_checked_constructor_is_strict_open_theorem`; `src/isar/proof_state.rs::proof_state_checked_goal_not_closed_proved` |
| Feed a compatibility or dummy-tainted CTerm into checked proof-goal construction | rejected with `KernelError::CompatCTerm` / `KernelError::DummyType` | `src/isar/proof.rs::{proof_goal_checked_constructor_rejects_compat_cterm,proof_goal_checked_constructor_rejects_dummy_type}`; `src/isar/proof_state.rs::{proof_state_checked_goal_rejects_compat_cterm,proof_state_checked_goal_rejects_dummy_type}` |
| Let a raw proof goal self-declare an undeclared constant because it carries a non-dummy type | rejected by `ProofCertContext` / checked goal constructors with `KernelError::UndeclaredConstant` | `src/isar/proof.rs::proof_goal_checked_constructor_rejects_undeclared_const`; `src/isar/proof_state.rs::proof_state_checked_goal_rejects_undeclared_const` |
| Let a raw proof goal self-declare an undeclared local free because it carries a non-dummy type | rejected by `ProofCertContext`; local frees must be declared in the proof context | `src/isar/proof_state.rs::proof_state_checked_goal_rejects_undeclared_free` |
| Reject a declared proof-context constant or local free after context-based certification | declared constants and local frees are accepted and still construct Strict open theorems | `src/isar/proof.rs::proof_goal_checked_constructor_accepts_declared_const`; `src/isar/proof_state.rs::{proof_state_checked_goal_accepts_declared_const,proof_state_checked_assumption_accepts_declared_local_free}` |
| Certify a proof goal with an ill-typed application despite declared names | rejected by context-based checked certification with `KernelError::TypeMismatch` | `src/isar/proof_state.rs::proof_state_checked_goal_rejects_ill_typed_application` |
| Construct fake subgoals through compatibility theorem scaffolding | checked subgoal scaffolding preserves `ThmTrust::Strict` and passes strict invariants while remaining open | `src/isar/proof_state.rs::checked_subgoal_scaffolding_preserves_strict_trust` |
| Let the new strict kernel accept legacy compatibility states | rejected by construction: no dummy type, undeclared Const/Free rejected, `ProofObligation` is not a theorem, `SearchFact` cannot convert to `TrustedTheorem` | `tests/kernel_rewrite_soundness.rs` |
| Let strict matcher substitution ordering depend on `HashMap` iteration order | rejected by deterministic `(name, index, type)` sorting before `InstEntry` construction | `crates/kernel/src/unify.rs::match_terms_multiple_distinct_vars_are_sorted`; `crates/kernel/src/rules.rs::match_terms_certified_multiple_distinct_vars_are_sorted` |
| Treat `resolve1_match` as full Isabelle `bicompose` | conservative one-way matching without lifting/freshening/flex-flex | `crates/kernel/src/rules.rs::{resolve1_rejects_variable_collision_without_lifting,resolve1_rejects_goal_var_namespace_collision_without_lifting,resolve1_invariant_with_multiple_bindings_is_deterministic}` |
| Produce a `resolve1_match` theorem when the rule conclusion does not match the selected goal subgoal | strict matcher rejects before construction | `crates/kernel/src/rules.rs::resolve1_rejects_match_failure` |
| Interpret `selected_subgoal_index` as a rule-premise index instead of a goal-subgoal index | selects a goal subgoal, not a rule premise | `crates/kernel/src/rules.rs::resolve1_selected_index_is_goal_subgoal_not_rule_premise` |
| Forget the matching substitution on inserted rule premises | result proposition contains substituted premises | `crates/kernel/src/rules.rs::resolve1_applies_substitution_to_rule_premises` |
| Substitute a same-namespace goal-side schematic Var silently | `RequiresLifting` instead of merging namespaces | `crates/kernel/src/rules.rs::resolve1_rejects_goal_var_namespace_collision_without_lifting` |
| Drop rigid hypotheses during resolution | rigid hypotheses remain present after matching | `crates/kernel/src/rules.rs::resolve1_preserves_rigid_hypotheses_after_matching` |
| Misorder retained and inserted subgoals during resolution | full substituted proposition preserves subgoal order | `crates/kernel/src/rules.rs::resolve1_multiple_bindings_preserve_subgoal_order` |
| Forge empty-premise resolution while keeping solved subgoal | replay recomputes deletion and rejects tamper | `crates/kernel/src/rules.rs::resolve1_empty_rule_premises_tamper_kept_subgoal_rejected` |
| Tamper resolution result or substitution | replay recomputes strict match | `crates/kernel/src/rules.rs::{resolve1_invariant_check_passes,resolve1_tampered_result_rejected,resolve1_invariant_with_multiple_bindings_is_deterministic}` |
| Treat strict `subst_premise` as object-equality rewriting | `NotProposition` | `crates/kernel/src/rules.rs::subst_premise_rejects_object_equality`; `tests/kernel_rewrite_soundness.rs::subst_premise_rejects_object_equality` |
| Rewrite rhs-to-lhs automatically | `AntecedentMismatch` without explicit symmetry | `crates/kernel/src/rules.rs::subst_premise_rejects_symmetric_direction`; `tests/kernel_rewrite_soundness.rs::subst_premise_rejects_symmetric_direction` |
| Interpret strict `subst_premise` index as equality-side index | index addresses goal subgoal | `crates/kernel/src/rules.rs::subst_premise_selected_index_is_goal_subgoal`; `tests/kernel_rewrite_soundness.rs::subst_premise_selected_index_is_goal_subgoal` |
| Rewrite missing or mismatched goal subgoal | `SubgoalIndexOutOfRange` / `AntecedentMismatch` | `crates/kernel/src/rules.rs::{subst_premise_rejects_out_of_range,subst_premise_rejects_mismatch}`; `tests/kernel_rewrite_soundness.rs::{subst_premise_rejects_out_of_range,subst_premise_rejects_mismatch}` |
| Drop unrelated goal subgoals or hypotheses | non-selected subgoals preserved; burdens unioned | `crates/kernel/src/rules.rs::{subst_premise_preserves_other_subgoals,subst_premise_preserves_hypotheses}`; `tests/kernel_rewrite_soundness.rs::subst_premise_preserves_other_subgoals_and_hypotheses` |
| Tamper strict `subst_premise` result | replay recomputes premise replacement | `crates/kernel/src/rules.rs::{subst_premise_invariant_check_passes,subst_premise_tampered_result_rejected}` |
| Present `accept_all` / proof-skipped source processing as a complete theory | `TheoryProcessor::process_source_verified` rejects `accept_all` before processing and publishes no partial theory/index | `src/theory/loader.rs::process_complete_source`; `tests/theory_load_contract.rs::process_source_unimplemented_commands_never_publish_partial_theory` |
| Report files with failed parents or incomplete proofs as successful session loads | `SessionBuilder` counts failures and blocks descendants; independent completed files may load | `tests/session_load_contract.rs::{build_missing_parent_and_cycle_only_schedule_independent_theory,classifier_matches_build_registry_for_runtime_failure_and_scan_failures}` |
| Treat `HolTheoremDb` searchable facts as an accepted transitional table | DB exposes separate searchable and legacy closed-proved counts; neither is a final new-kernel `TrustedTheory` | `src/hol/hol_loader.rs::test_hol_theorem_db_distinguishes_searchable_from_closed_proved`; `src/hol/hol_loader.rs::test_hol_theorem_db_counts_closed_proved_facts_separately` |
| Accept a source proposition prefix, or authorize synthetic source without provenance, through the registered sampled `TrueI` adapter | `parse_term` rejects incomplete input; `parse_term_with_status` preserves `Incomplete` only for explicit search diagnostics. The adapter rejects unverified status/shape as `admitted:strict_adapter_source_prop_unverified`, without entering legacy proof fallback or granting a token | `src/isar/term_parser.rs` full-consumption tests; `src/isar/method.rs::{strict_adapter_rejects_unconsumed_source_proposition_suffix,strict_adapter_rejects_true_i_without_source_provenance,strict_adapter_synthetic_metadata_cannot_borrow_source_token}` |
| Recover a malformed `True` proposition into a candidate, or resolve contextual `True` as global `HOL.True` | malformed or mistyped `True =`, `True :: nat`, and `True :: prop` produce no lemma candidate. Parsed contextual input requires `StandaloneHolTrueAlias` and rejects before parser-gap; this shape is a fail-closed guard, not trusted source authority | `src/isar/method.rs::{strict_adapter_rejects_contextual_true_source,strict_adapter_forged_metadata_cannot_rebind_local_source}`; `tests/sampled_true_i.rs::sampled_true_i_local_statement_is_rejected` |
| Treat a lemma or context terminator inside a comment/cartouche/string as active outer syntax | the source mask preserves line count but hides embedded text before command detection and nested-context tracking; commented-out `TrueI` is absent, and a commented `end` cannot escape a local context | `src/hol/hol_loader.rs::{commented_lemma_is_not_parsed_as_source_command,commented_end_cannot_escape_local_theorem_context}` |
| Use a contextual, locale-qualified, commented, or cartouche-contained `True` definition as global checked `True_def`, or obtain `HOL.eq` from commented axiomatization text | checked definition/type evidence is restricted to visible top-level blocks; non-command and local definitions remain absent and commented declarations cannot populate the type environment | `src/hol/hol_loader.rs::{checked_true_def_requires_visible_top_level_definition,commented_axiomatization_cannot_supply_checked_source_types}` |
| Treat a checked definition source as a theorem/fact or proof-progress entry | `True_def` is stored only in `HolTheoremDb::checked_definitions`, not `by_name`/`all`, and does not affect closed-proved counts | `src/hol/hol_loader.rs::{true_def_checked_source_exists,true_def_checked_source_rejects_dummy_or_compat,true_def_source_is_not_counted_as_theorem}` |
| Silently overwrite checked-source type environment declarations while enabling checked definition sources | equal declarations merge, but conflicting constant or type declarations are rejected instead of replacing the existing verification environment | `src/hol/hol_loader.rs::{checked_source_env_merge_preserves_equal_declaration,checked_source_env_merge_rejects_conflicting_const_type,checked_source_env_merge_rejects_conflicting_type_decl}` |
| Revive the removed legacy HOL object-reflexivity or `True_def` transport bridges as proof authority | Legacy bool-valued `HOL.eq` / `HOL.True` is not a strict `CProp`; the 2026-10-03 transitional bridge coverage was removed with those APIs | Current audited source projection: `tests/sampled_true_i.rs::{sampled_true_i_changed_equality_schema_is_rejected,sampled_true_i_changed_definition_is_rejected,sampled_true_i_changed_refl_schema_is_rejected}` |
| Accept sampled `HOL::TrueI` from forged metadata, a changed declaration/proof, or a contextual source | The current `try_strict_adapter` binds the public candidate to audited complete source, returns an accepted exact-owner token only on verified projection, and rejects a shape hit without legacy proof fallback | `src/isar/method.rs::{strict_adapter_forged_metadata_cannot_rebind_local_source,strict_adapter_changed_source_invalidates_accepted_definition,strict_adapter_rejects_contextual_true_source}`; `tests/sampled_true_i.rs::{sampled_true_i_real_hol_source_returns_replayable_exact_token,sampled_true_i_changed_statement_is_rejected,sampled_true_i_changed_proof_is_rejected}` |
| Let `Typ::dummy()` pass unnoticed at an explicit non-dummy boundary | rejected by `CTerm::require_non_dummy` | `tests/kernel_soundness.rs::dummy_type_is_detectable_at_kernel_boundaries` |
| Treat a bool-valued HOL term as a new-kernel theorem proposition | `ProofContext::certify_prop` rejects plain `bool`, `HOL.True : bool`, and `HOL.eq a b : bool` with `NotProposition`; applying a declared `HOL.Trueprop : bool => prop` is required before CProp certification. This test covers only the current type-level boundary: it does not yet bind that declaration to immutable HOL theory/logic provenance. | `tests/kernel_rewrite_soundness.rs::{reject_bool_as_theorem_proposition,reject_hol_true_bool_without_trueprop,reject_hol_eq_bool_without_trueprop,declared_trueprop_wraps_hol_true_as_cprop}` |
| Strictly certify a term whose type remains unresolved dummy | rejected by `CTerm::certify_checked` with `KernelError::DummyType` | `tests/kernel_soundness.rs::certify_checked_rejects_unresolved_dummy_type` |
| Strictly certify an ill-typed application | rejected by `CTerm::certify_checked` with `KernelError::TypeMismatch` | `tests/kernel_soundness.rs::certify_checked_rejects_ill_typed_application` |
| Strictly certify an inconsistent instantiation of a polymorphic constant | rejected by `CTerm::certify_checked` with `KernelError::TypeMismatch` | `tests/kernel_soundness.rs::certify_checked_rejects_inconsistent_polymorphic_application` |
| Use a compatibility CTerm through a strict kernel entry point | rejected by `ThmKernel::assume` / `ThmKernel::reflexive` with `KernelError::CompatCTerm` | `tests/kernel_soundness.rs::{checked_kernel_entry_rejects_dummy_typed_cterm,compat_cterm_cannot_enter_strict_assume}` |
| Strictly certify a fully typed declared proposition | accepted by `CTerm::certify_checked` and contains no dummy type | `tests/kernel_soundness.rs::certify_checked_accepts_fully_typed_simple_proposition` |
| Construct reflexivity from a checked CTerm and accidentally downgrade the conclusion to compat | result proposition remains `CertStatus::Checked` | `tests/kernel_soundness.rs::checked_cterm_constructs_checked_reflexive_theorem` |
| Treat a compatibility reflexive theorem as trusted because it is oracle-free and closed-shaped | `is_closed_proved()` may be true, but `ThmTrust::Compat` makes `is_strict_closed_proved()` false | `tests/kernel_soundness.rs::reflexive_compat_is_closed_shaped_but_not_strict_trusted` |
| Store a compatibility closed-shaped theorem in the legacy transitional `Theory` table | rejected by `Theory::add_theorem` strict gate; this does not make that table a new-kernel `TrustedTheory` | `tests/kernel_soundness.rs::trusted_theory_rejects_compat_closed_shaped_theorem` |
| Combine a strict theorem with a compat premise and upgrade the result to strict | result is tainted `ThmTrust::Compat` | `tests/kernel_soundness.rs::strict_and_compat_premises_do_not_produce_strict_result` |
| Treat an admitted theorem as strict because it is a theorem value | result carries `ThmTrust::Admitted` and fails strict trusted predicates | `tests/kernel_soundness.rs::admitted_theorem_is_not_strict_trusted` |
| Treat a compat/admitted theorem as passing strict kernel invariants | `check_kernel_invariants(Strict)` rejects non-Strict trust provenance | `tests/kernel_soundness.rs::{reflexive_compat_is_closed_shaped_but_not_strict_trusted,admitted_theorem_is_not_strict_trusted}` |
| Treat strict invariant success as closed lemma acceptance | strict `assume(A)` passes strict invariants as `A |- A`, but fails `is_strict_closed_proved()` | `src/core/thm.rs::test_strict_open_theorem_passes_strict_invariants_but_not_closed_proved` |
| Treat unsupported strict derivation as replay-checked because strict invariants passed | strict `beta_conversion` may pass structural strict invariants, but `check_proof()` still reports unsupported replay | `src/core/thm.rs::test_unsupported_strict_replay_is_structural_only` |
| Report a compat-only proof as a transitionally verified session theorem | `SessionBuilder` reports zero transitional strict theorem count | `src/theory/session_builder.rs::test_compat_proof_does_not_report_session_verified_theorems` |
| Drop oracle footprint through a real kernel rule | result remains tainted | `src/core/thm.rs::test_oracle_footprint_propagates_through_rules` |
| Drop oracle footprint through a multi-premise rule | result remains tainted | `src/core/thm.rs::test_union_of_proved_and_admitted_is_tainted` |
| Drop sort hypotheses through single-premise or multi-premise rules | `shyps` preserved/unioned | `src/core/thm.rs::test_shyps_propagate_through_single_premise_rule`; `src/core/thm.rs::test_shyps_union_through_multi_premise_rule` |
| Use `combination` with a known argument-domain mismatch | rejected with `KernelError::TypeMismatch` | `src/core/thm.rs::test_combination_rejects_known_type_mismatch` |
| Identify lambdas with distinct known binder types | rejected by `kernel_alpha_eq` | `src/core/thm.rs::test_alpha_eq_rejects_distinct_binder_types` |
| Identify dummy-vs-known lambda binders in trusted equality | rejected by `kernel_alpha_eq`; accepted only by explicit `compat_alpha_eq` | `src/core/thm.rs::test_kernel_alpha_eq_rejects_dummy_known_binder_match` |
| Match `Free("zero")` with `Const("Groups.zero")` by suffix in trusted equality | rejected by `kernel_alpha_eq`; accepted only by explicit `compat_alpha_eq` | `src/core/thm.rs::test_alpha_eq_should_reject_free_const_suffix_match` |
| Match `Var("x", i)` with `Free("x")` in trusted equality | rejected by `kernel_alpha_eq`; accepted only by explicit `compat_alpha_eq` | `src/core/thm.rs::test_alpha_eq_should_reject_var_free_index_confusion` |
| Ignore schematic variable indices | rejected by `kernel_alpha_eq` | `src/core/thm.rs::test_kernel_alpha_eq_rejects_distinct_var_indices` |
| Use `implies_elim` across alpha-equal antecedents with incompatible known types | rejected with `KernelError::TypeMismatch` | `tests/kernel_soundness.rs::implies_elim_rejects_known_antecedent_type_mismatch` |
| Use `implies_elim` across Var/Free same-name antecedents | rejected with `KernelError::AntecedentMismatch` | `tests/kernel_soundness.rs::implies_elim_rejects_var_free_antecedent_confusion` |
| Instantiate `!!x. P x` with a known wrong-typed term | rejected with `KernelError::TypeMismatch` | `tests/kernel_soundness.rs::forall_elim_rejects_known_binder_argument_type_mismatch` |
| Apply an environment that maps `?x::nat` to a `bool` term | public path rejects through `instantiate_checked`; old infallible behavior is internal test-only | `tests/kernel_soundness.rs::instantiate_checked_rejects_known_type_mismatch`; `src/core/thm.rs::test_instantiate_legacy_is_test_only_and_conservative` |
| Rewrite a premise through a same-name lhs with incompatible known type | `subst_premise` returns `None` (⚠️ LEGACY CORE) | `tests/kernel_soundness.rs::subst_premise_rejects_known_lhs_premise_type_mismatch` |
| Discharge a subgoal through `bicompose` using same-name incompatible terms | `bicompose` returns `None` (⚠️ LEGACY CORE) | `tests/kernel_soundness.rs::bicompose_rejects_known_alpha_match_type_mismatch` |
| Resolve through `bicompose_eresolve` using unifier same-name incompatible terms | `bicompose_eresolve` returns `None` (⚠️ LEGACY CORE) | `tests/kernel_soundness.rs::bicompose_eresolve_rejects_known_unifier_type_mismatch` |
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
| Mutate strict theorem internals after construction | `check_kernel_invariants(Strict)` rejects dummy taint, `maxidx` drift, and burden mismatches | `src/core/thm.rs::{test_strict_invariant_rejects_dummy_tainted_theorem,test_strict_invariant_rejects_tampered_maxidx,test_strict_invariant_rejects_tampered_hyps,test_strict_invariant_rejects_tampered_oracles,test_strict_invariant_rejects_tampered_tpairs}` |
| Mutate a nested premise derivation after construction | `check_proof()` rejects the derived theorem | `src/core/thm.rs::test_check_proof_rejects_tampered_premise_derivation` |
| Mark a proof body checked through an old path and then validate a tampered theorem | `Thm::validate_proof` replays burdens anyway | `src/core/thm.rs::test_validate_proof_rechecks_stale_checked_body` |
| Replay minimal proof rules without deriving their conclusion | `reflexive`, `symmetric`, `transitive`, `implies_intr`, and `implies_elim` are structurally replayed | `src/core/proofterm.rs::{reflexive_replay_succeeds_and_is_closed_proved,symmetric_replay_succeeds,transitive_replay_succeeds,implies_intro_and_elim_replay_succeed}` |
| Reject alpha-equivalent middle terms in supported `transitive` replay even though the kernel accepted them | replay uses kernel alpha-equivalence and known-type compatibility | `src/core/proofterm.rs::transitive_replay_accepts_alpha_equivalent_middle_terms` |
| Confuse unsupported replay rule with tampering or oracle failure | unsupported rules produce an explicit unsupported-rule error | `src/core/proofterm.rs::unsupported_rule_is_reported_separately_from_tampering` |

## Compatibility-Only Gaps

The former ignored Free/Const and Var/Free tests are now ordinary passing
strict-kernel tests. The old behavior remains only in `Hyps::compat_alpha_eq` so
legacy parser/loader paths can be isolated and audited explicitly.

| Compatibility debt | Trusted behavior | Compatibility behavior |
|---|---|---|
| `Free("zero")` vs `Const("Groups.zero")` suffix matching | `kernel_alpha_eq` rejects it | `compat_alpha_eq` still accepts it |
| `Var("x", i)` vs `Free("x")` matching | `kernel_alpha_eq` rejects it | `compat_alpha_eq` still accepts it |
| Dummy-vs-known binder type matching | `kernel_alpha_eq` rejects it | `compat_alpha_eq` still accepts it |

## Immutable Context Identity Attacks

`tests/kernel_context_identity.rs` and
`tests/kernel_declaration_boundary.rs` cover:

- deterministic, order-independent signature IDs, including type-constructor
  names/arity; ancestry-sensitive theory IDs and domain separation;
- duplicate declarations and immutable parent/sibling extensions;
- unknown constructors, wrong arity under unused binders, bad schematic/free
  annotations, and out-of-range type-variable indices;
- same text under wrong signatures, sibling ancestry, or stale parents;
- mixed two-premise rules and substitutions before logical shape checks;
- untrusted signature snapshot digest mismatches and duplicate declarations;
- installed basis rejection of undeclared, ill-scoped, mistyped, or
  inconsistently polymorphic axiom schemas, before they can authorize proofs;
- monomorphic conservative definitions reject hidden polymorphic RHS
  annotations and accept valid definition dependencies.

## Trusted Acceptance Attacks

`tests/kernel_trusted_acceptance.rs`,
`crates/kernel/src/theory.rs`, and `crates/kernel/src/invariant.rs`
cover strict owner replay and private-scope attacks:

- wrong theory, wrong signature, stale parent, and sibling-token rejection;
- forged closed candidates with hypotheses;
- tampered conclusion and derivation replay mismatch;
- duplicate theorem names without overwrite;
- immutable parent retention and sibling fact isolation;
- forged owner/snapshot/store/token inconsistencies;
- recursive recertification of same-stamp local frees and every substitution or
  quantifier payload;
- malformed cached application, abstraction, equality, and bound types;
- ancestry-authorized theorem references and replay-derived dependencies;
- equal logical theorem content accepted under different sibling fact names
  yields equal `TheoremId`s but non-interchangeable `(name, accepted_in)` tokens;
  aliases derived in those branches have distinct context-bound IDs;
- proof-erased search facts and private accepted-token construction;
- alpha-canonical, proof-irrelevant theorem identity;
- changed term namespace/index/type/node and dependency-kind identity;
- dependency insertion-order independence;
- an independent fixed theorem-ID golden vector;
- accepted-token precedence over legacy output and one exclusive statistics
  bucket;
- preservation of the sole sampled `HOL::TrueI` kernel token and mutually
  exclusive `KernelTrustedClosed: 1/125`, `TransitionalStrictClosed: 0/125`
  counts; unrelated HOL/ML commands remain outside the audited projection.

## Source AST Boundary Attacks

`src/isar/source_ast.rs` unit and compile-fail tests now cover:

- half-open UTF-8 byte spans and nested span preservation;
- raw dotted/bare name spellings without qualification classification;
- raw Pure/HOL-looking binder syntax without a semantic binder enum;
- distinct source nodes for shadowed binders;
- grouping and syntax-application structure;
- caller-forgeable diagnostic source labels separated from expression shape;
- absence of `ContextStamp` fields and direct conversions into `Term`, `CProp`,
  `ClosedThm`, `TrustedTheorem`, or `DependencySet`.

These tests protect a data representation only. The bounded strict parser
and elaborator now consume it for two standalone source fixtures and the
audited sampled `HOL::TrueI` projection; the AST alone proves neither source
authenticity nor broad name resolution or acceptance.

## Current Boundary Suites and Remaining Attack Work

Later Rust THM variable/scope and consumer boundaries are covered by
`crates/kernel/tests/{variable_transformations,scope_export,native_thm_closure,native_thm_variables}.rs`
and `crates/kernel/src/invariant/{variable_attacks,variable_scope_attacks}.rs`.
They exercise owner replay, real-H and sort/flex obligations, typed-Free
scope grants and rejection of tampered intermediate annotations. Their dated
local execution evidence is in the
[Rust variable consumer record](../status/PROJECT_STATUS.md#rust-thm-type-and-variable-transformations-2026-10-19),
not in the bundled 125-case sample or a fresh run of this matrix.

- `tests/theory_load_contract.rs` and `tests/session_load_contract.rs` cover
  complete-source rejection, persisted `typedecl`, duplicate/missing imports,
  missing `end`, transactional failure, and per-build registry isolation.
- `tests/legacy_proof_contract.rs` and `tests/legacy_pure_rule_contract.rs`
  cover fresh-goal/mismatched-show/open-scope rejection, checked scoped
  `A ==> A` completion, binder capture, exact result/hypothesis checks, and
  Compat taint preservation. Logical implication premises do not themselves
  mean unfinished tactic obligations.
- `tests/automation_rewrite_contract.rs` and
  `tests/automation_proof_contract.rs` cover rigid Free vs schematic Var
  rewrites, tampered/conditional rules, App/Abs certificate endpoints,
  rejected ATP step/formula/duplicate/missing evidence, and exact complete
  Metis/Meson result checks. These legacy checks do not grant kernel tokens.
- `src/theory/trusted_loader.rs` tests accept only the standalone Pure
  `!!P::prop. PROP P ==> PROP P` by `assumption` (including supported renamed
  binders/aliases); old `impI`, bare P, and malformed PROP fail without tokens.

Future work extends the audited sampled `HOL::TrueI` source-to-exact-owner
kernel integration to other HOL theorems, and broadens syntax/rules only with
complete checked evidence. Typed diagnostics for legacy `Option<Thm>` and
derivation-producing attributes remain separate debt; neither justifies new
trusted power in `src/core`.
