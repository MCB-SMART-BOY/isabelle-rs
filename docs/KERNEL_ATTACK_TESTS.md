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
| Chain two equalities through Free/Const suffix-compatible middle terms | rejected with `KernelError::MidTermsNotEquiv` | `tests/kernel_soundness.rs::transitive_rejects_free_const_suffix_middle_term` |
| Beta-convert `(λx. x) a` and expose raw `Bound(0)` | rejected by construction; RHS is `a` | `tests/kernel_soundness.rs::beta_conversion_substitutes_the_argument`; `src/core/thm.rs::test_beta_conversion_substitutes_argument_for_bound_zero` |
| Abstract over a variable that is free in hypotheses | rejected with `FreeVarInHypotheses` | `tests/kernel_soundness.rs::abstraction_rejects_free_variable_in_hypotheses` |
| Treat `assume(A)` as an unconditional theorem | impossible through public shape; discharge requires `implies_intr` | `tests/kernel_soundness.rs::implies_intro_is_the_only_way_to_discharge_assume_here` |
| Count oracle-free `assume(A)` as a closed proved lemma | rejected by `is_closed_proved()` and batch stats | `tests/kernel_soundness.rs::implies_intro_is_the_only_way_to_discharge_assume_here`; `src/isar/method.rs::test_open_oracle_free_theorem_is_not_closed_proved_outcome`; `src/isar/method.rs::test_verify_batch_does_not_count_open_theorem_as_verified` |
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
| Let strict matcher substitution ordering depend on `HashMap` iteration order | rejected by deterministic `(name, index, type)` sorting before `InstEntry` construction | `src/kernel/unify.rs::match_terms_multiple_distinct_vars_are_sorted`; `src/kernel/rules.rs::match_terms_certified_multiple_distinct_vars_are_sorted` |
| Treat `resolve1_match` as full Isabelle `bicompose` | impossible by API contract; current rule is conservative one-way matching without lifting/freshening/flex-flex | `src/kernel/rules.rs::{resolve1_rejects_variable_collision_without_lifting,resolve1_invariant_with_multiple_bindings_is_deterministic}` |
| Produce a `resolve1_match` theorem when the rule conclusion does not match the selected goal subgoal | rejected by the strict matcher before theorem construction | `src/kernel/rules.rs::resolve1_rejects_match_failure` |
| Interpret `selected_subgoal_index` as a rule-premise index instead of a goal-subgoal index | rejected/covered by selecting a nonmatching goal subgoal at index 0 and a matching one at index 1 | `src/kernel/rules.rs::resolve1_selected_index_is_goal_subgoal_not_rule_premise` |
| Forget to apply the matching substitution to rule premises inserted into the goal | result proposition must contain substituted rule premises | `src/kernel/rules.rs::resolve1_applies_substitution_to_rule_premises` |
| Forget to apply the matching substitution to remaining goal subgoals | result proposition must reflect the substituted goal chain | `src/kernel/rules.rs::resolve1_applies_substitution_to_goal_remaining_subgoals` |
| Forget to apply the matching substitution to theorem hypotheses | result burdens must contain substituted hypotheses, not stale schematic hypotheses | `src/kernel/rules.rs::resolve1_applies_substitution_to_hypotheses` |
| Let `resolve1_match` drift from the implication-chain subgoal replacement helper | result proposition is built through `Term::replace_subgoal_with_premises` and checked against the helper semantics | `src/kernel/rules.rs::resolve1_matches_replace_subgoal_helper_semantics` |
| Forge an empty-premise `resolve1_match` result that keeps the solved subgoal | invariant replay recomputes the selected-subgoal deletion and rejects theorem fields that still contain the solved premise | `src/kernel/rules.rs::resolve1_empty_rule_premises_tamper_kept_subgoal_rejected` |
| Tamper a strict `resolve1_match` result or recorded substitution | invariant replay recomputes the strict match and rejects mismatched theorem fields/substitution | `src/kernel/rules.rs::{resolve1_invariant_check_passes,resolve1_tampered_result_rejected,resolve1_invariant_with_multiple_bindings_is_deterministic}` |
| Count `accept_all` / proof-skipped theory processing as a closed proved theorem | rejected by `TheoryProcessor::process_source_verified`; indexed as admitted but not registered in final `Theory` | `src/theory/loader.rs::test_accept_all_is_admitted_not_closed_verified` |
| Report `accept_all` theory files as session-verified because they produced index entries | rejected by `SessionBuilder`; build/classifier report zero closed proved theorems | `src/theory/session_builder.rs::test_accept_all_does_not_report_session_verified_theorems`; `src/theory/session_builder.rs::test_accept_all_classifier_is_not_full_success` |
| Treat `HolTheoremDb` searchable facts as a trusted theorem table | DB exposes separate searchable and closed-proved counts | `src/hol/hol_loader.rs::test_hol_theorem_db_distinguishes_searchable_from_closed_proved`; `src/hol/hol_loader.rs::test_hol_theorem_db_counts_closed_proved_facts_separately` |
| Let `Typ::dummy()` pass unnoticed at an explicit non-dummy boundary | rejected by `CTerm::require_non_dummy` | `tests/kernel_soundness.rs::dummy_type_is_detectable_at_kernel_boundaries` |
| Strictly certify a term whose type remains unresolved dummy | rejected by `CTerm::certify_checked` with `KernelError::DummyType` | `tests/kernel_soundness.rs::certify_checked_rejects_unresolved_dummy_type` |
| Strictly certify an ill-typed application | rejected by `CTerm::certify_checked` with `KernelError::TypeMismatch` | `tests/kernel_soundness.rs::certify_checked_rejects_ill_typed_application` |
| Strictly certify an inconsistent instantiation of a polymorphic constant | rejected by `CTerm::certify_checked` with `KernelError::TypeMismatch` | `tests/kernel_soundness.rs::certify_checked_rejects_inconsistent_polymorphic_application` |
| Use a compatibility CTerm through a strict kernel entry point | rejected by `ThmKernel::assume` / `ThmKernel::reflexive` with `KernelError::CompatCTerm` | `tests/kernel_soundness.rs::{checked_kernel_entry_rejects_dummy_typed_cterm,compat_cterm_cannot_enter_strict_assume}` |
| Strictly certify a fully typed declared proposition | accepted by `CTerm::certify_checked` and contains no dummy type | `tests/kernel_soundness.rs::certify_checked_accepts_fully_typed_simple_proposition` |
| Construct reflexivity from a checked CTerm and accidentally downgrade the conclusion to compat | result proposition remains `CertStatus::Checked` | `tests/kernel_soundness.rs::checked_cterm_constructs_checked_reflexive_theorem` |
| Treat a compatibility reflexive theorem as trusted because it is oracle-free and closed-shaped | `is_closed_proved()` may be true, but `ThmTrust::Compat` makes `is_strict_closed_proved()` false | `tests/kernel_soundness.rs::reflexive_compat_is_closed_shaped_but_not_strict_trusted` |
| Store a compatibility closed-shaped theorem in the final trusted `Theory` table | rejected by `Theory::add_theorem` strict gate | `tests/kernel_soundness.rs::trusted_theory_rejects_compat_closed_shaped_theorem` |
| Combine a strict theorem with a compat premise and upgrade the result to strict | result is tainted `ThmTrust::Compat` | `tests/kernel_soundness.rs::strict_and_compat_premises_do_not_produce_strict_result` |
| Treat an admitted theorem as strict because it is a theorem value | result carries `ThmTrust::Admitted` and fails strict trusted predicates | `tests/kernel_soundness.rs::admitted_theorem_is_not_strict_trusted` |
| Treat a compat/admitted theorem as passing strict kernel invariants | `check_kernel_invariants(Strict)` rejects non-Strict trust provenance | `tests/kernel_soundness.rs::{reflexive_compat_is_closed_shaped_but_not_strict_trusted,admitted_theorem_is_not_strict_trusted}` |
| Treat strict invariant success as closed lemma acceptance | strict `assume(A)` passes strict invariants as `A |- A`, but fails `is_strict_closed_proved()` | `src/core/thm.rs::test_strict_open_theorem_passes_strict_invariants_but_not_closed_proved` |
| Treat unsupported strict derivation as replay-checked because strict invariants passed | strict `beta_conversion` may pass structural strict invariants, but `check_proof()` still reports unsupported replay | `src/core/thm.rs::test_unsupported_strict_replay_is_structural_only` |
| Report a compat-only proof as a verified session theorem | `SessionBuilder` reports zero strict verified theorem count | `src/theory/session_builder.rs::test_compat_proof_does_not_report_session_verified_theorems` |
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

## Next Attack Tests To Add

- `subst_premise`, `bicompose`, and `bicompose_eresolve` (all ⚠️ LEGACY CORE) should get explicit
  Free/Const and Var/Free rejection tests now that strict `kernel_alpha_eq` is
  enabled.
- `bicompose` and `bicompose_eresolve` (⚠️ LEGACY CORE) still need explicit oracle/tpairs/shyps
  propagation tests with non-empty burdens on both premises.
- `certify_checked` and theorem trust taint are available, but most
  parser/HOL/Isar call sites still use best-effort `CTerm::certify` plus
  `_compat` theorem constructors; add call-site migration tests as strict mode
  expands.
- Existing parser/HOL/Isar users of theorem introduction have been moved to
  explicit `assume_compat` / `reflexive_compat`; each call-site category still
  needs migration or admission classification.
- `instantiate_checked` should eventually validate sort constraints and richer
  application typing once checked CTerms are used throughout trusted paths.
- Trusted-boundary paths returning `Option<Thm>` should eventually distinguish
  ordinary non-match from `KernelError` rejection for auditability.
- Attribute transformations still need real derivation-producing conversions;
  they are currently honest admissions, not proved transformations.
- Proof replay still needs coverage for
  `combination`/`abstraction`/`beta_conversion`/`forall_*`/`instantiate`/
  `bicompose*` (⚠️ LEGACY CORE); unsupported rules currently fail replay instead of being
  trusted.
- Next T4 attack-test batch should start with `beta_conversion`,
  `forall_intr`, and `forall_elim`, then move to
  `combination`/`abstraction`, checked instantiation, and resolution rules.
