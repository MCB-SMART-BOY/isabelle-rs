# Compatibility Constructor Call-Site Audit

Generated on 2026-06-28 during the Strict Kernel Phase.

Scope:

```text
src/**
tests/**
```

The scan intentionally excludes `target/`. The raw counts include constructor
definitions and test modules; they are an audit starting point, not proof that
each site has already been semantically migrated.

Commands:

```bash
rg -n "assume_compat\(" src tests --glob '!target'
rg -n "reflexive_compat\(" src tests --glob '!target'
```

## Summary

| Constructor | Raw occurrences | Main risk | Current trusted impact |
|---|---:|---|---|
| `assume_compat` | 270 | legacy code can still construct open/closed-shaped compatibility facts | tainted as `ThmTrust::Compat`; cannot satisfy `is_strict_closed_proved()` |
| `reflexive_compat` | 30 | legacy code can still construct oracle-free closed-shaped compatibility facts | tainted as `ThmTrust::Compat`; cannot satisfy `is_strict_closed_proved()` |

No sampled site in this pass justified weakening the strict kernel gate. The
right migration direction is:

```text
compat constructor remains searchable/debug-only
  -> classify the call site
  -> migrate to checked CTerm + strict rule, real derivation, or admit
  -> never count as trusted closed proved until strict
```

## Category Meanings

| Category | Meaning | Preferred action |
|---|---|---|
| `proof_state_local_assumption` | local proof state assumption of an open theorem such as `A |- A` | migrated to checked proposition plus strict `ThmKernel::assume` |
| `proof_state_goal_obligation` | proof-state `have`/`show`/`obtain` obligation still represented as theorem-shaped scaffolding | migrate after separating proof obligations from tactic/search intermediates |
| `fallback_should_admit` | unsupported feature or failed proof accepted as theorem | replace with `ThmKernel::admit(ct, "admitted:specific_reason")` |
| `parser_loader_debt` | parsed/generated term lacks strict certification or name/type resolution | keep compat/searchable only; fix parser/type boundary before strict migration |
| `test_fixture` | unit/property/integration test scaffolding | migrate high-value kernel tests to checked fixtures; keep compat tests only when testing compatibility behavior |
| `hol_bootstrap` | generated HOL/bootstrap/package facts without a real kernel derivation yet | design trusted bootstrap/definition package or admit/classify stubs |
| `tactic_intermediate` | proof-search, conversion, simplifier, or automation intermediate theorem shape | keep outside trusted table; migrate toward typed proof-state constructors and `Result` errors |
| `unknown_needs_review` | call site not classified by this pass | inspect before any migration |

## Primary Classification By Module

| Category | Files | `assume_compat` | `reflexive_compat` | Notes |
|---|---|---:|---:|---|
| `hol_bootstrap` | `src/hol/hol_loader.rs`, `src/hol/typedef_record.rs`, `src/hol/bnf_lfp.rs`, `src/hol/ctr_sugar.rs`, `src/hol/hol_rules.rs`, `src/hol/hol_consts.rs`, `src/hol/class_system.rs`, `src/hol/axclass.rs`, `src/hol/function.rs`, `src/hol/hol_theorems.rs`, `src/hol/inductive.rs`, `src/hol/inductive_set.rs`, `src/hol/locale.rs`, `src/hol/primcorec.rs`, `src/hol/simpdata.rs`, `src/hol/theory_db.rs`, `src/hol/transfer.rs` | 114 | 4 | Built-in/generated facts, datatype/BNF/record/class/locale package output, and HOL rule tables. |
| `parser_loader_debt` | `src/theory/loader.rs`, `src/theory/local_theory.rs`, `src/isar/spec.rs`, `src/isar/toplevel.rs`, `src/core/morphism.rs` | 17 | 0 | Parsed or generated facts still use best-effort certification. |
| `proof_state_goal_obligation` | `src/isar/proof_state.rs` | 3 | 0 | `have`, `show`, and `obtain` still construct proof obligations through compat. Migrate separately after goal/subgoal scaffolding. |
| `tactic_intermediate` | `src/core/conv.rs`, `src/core/tactic.rs`, `src/core/simplifier.rs`, `src/core/drule.rs`, `src/core/more_thm.rs`, `src/core/bires.rs`, `src/tools/metis.rs`, `src/tools/simp.rs`, `src/tools/meson.rs`, `src/tools/tptp.rs`, `src/tools/sledgehammer.rs`, `src/tools/reconstruct.rs`, `src/isar/linarith.rs` | 89 | 18 | Conversion, simplifier, Metis/Meson/TPTP, linarith, and tactical intermediates. |
| `tactic_intermediate` / `proof_state_local_assumption` / `test_fixture` | `src/isar/method.rs` | 29 | 0 | Mixed method dispatch, proof-state setup, and tests; classify per hunk before migration. |
| `test_fixture` | `tests/comprehensive.rs`, `tests/proptest.rs`, `tests/sledgehammer_e2e.rs`, `tests/integration_tests.rs`, `tests/kernel_soundness.rs`, `src/core/thm.rs`, `src/core/proofterm.rs`, `src/main.rs`, `src/isar/proof.rs`, `src/isar/proof_state.rs` | 18 | 8 | Includes unit/property/integration tests, examples, raw constructor definitions in `src/core/thm.rs`, and remaining legacy proof-state scaffolds. Strict-fixture migration cleared proofterm replay tests, property tests, and most kernel-facing unit tests. |

The category table sums to the raw scan counts. Some files are mixed; the table
uses the primary role for this pass rather than a line-by-line semantic proof.

## Exact File Counts

| File | `assume_compat` | `reflexive_compat` | Primary category |
|---|---:|---:|---|
| `src/hol/hol_loader.rs` | 56 | 1 | `hol_bootstrap` |
| `src/isar/method.rs` | 29 | 0 | mixed method/proof/test |
| `src/tools/metis.rs` | 22 | 0 | `tactic_intermediate` |
| `src/tools/simp.rs` | 20 | 4 | `tactic_intermediate` |
| `src/isar/proof_state.rs` | 4 | 0 | `proof_state_goal_obligation` / `test_fixture` |
| `src/core/conv.rs` | 14 | 4 | `tactic_intermediate` |
| `src/hol/typedef_record.rs` | 13 | 0 | `hol_bootstrap` |
| `src/hol/bnf_lfp.rs` | 12 | 0 | `hol_bootstrap` |
| `src/hol/ctr_sugar.rs` | 11 | 1 | `hol_bootstrap` |
| `src/isar/linarith.rs` | 9 | 1 | `tactic_intermediate` |
| `src/isar/spec.rs` | 8 | 0 | `parser_loader_debt` |
| `src/hol/hol_rules.rs` | 7 | 0 | `hol_bootstrap` |
| `src/tools/meson.rs` | 6 | 0 | `tactic_intermediate` |
| `src/core/tactic.rs` | 6 | 0 | `tactic_intermediate` |
| `tests/sledgehammer_e2e.rs` | 5 | 0 | `test_fixture` |
| `src/theory/loader.rs` | 5 | 0 | `parser_loader_debt` |
| `tests/comprehensive.rs` | 4 | 0 | `test_fixture` |
| `src/core/thm.rs` | 4 | 3 | `test_fixture` / definitions |
| `tests/kernel_soundness.rs` | 0 | 4 | `compat_taint_test` |
| `src/tools/tptp.rs` | 3 | 0 | `tactic_intermediate` |
| `src/core/simplifier.rs` | 3 | 7 | `tactic_intermediate` |
| `src/theory/local_theory.rs` | 2 | 0 | `parser_loader_debt` |
| `src/isar/proof.rs` | 1 | 0 | `test_fixture` |
| `src/hol/simpdata.rs` | 2 | 1 | `hol_bootstrap` |
| `src/hol/hol_consts.rs` | 2 | 1 | `hol_bootstrap` |
| `src/hol/class_system.rs` | 2 | 0 | `hol_bootstrap` |
| `src/core/drule.rs` | 2 | 0 | `tactic_intermediate` |
| `src/tools/sledgehammer.rs` | 1 | 0 | `tactic_intermediate` |
| `src/tools/reconstruct.rs` | 1 | 0 | `tactic_intermediate` |
| `src/main.rs` | 1 | 1 | `test_fixture` / example |
| `src/isar/toplevel.rs` | 1 | 0 | `parser_loader_debt` |
| `src/hol/transfer.rs` | 1 | 0 | `hol_bootstrap` |
| `src/hol/theory_db.rs` | 1 | 0 | `hol_bootstrap` |
| `src/hol/primcorec.rs` | 1 | 0 | `hol_bootstrap` |
| `src/hol/locale.rs` | 1 | 0 | `hol_bootstrap` |
| `src/hol/inductive_set.rs` | 1 | 0 | `hol_bootstrap` |
| `src/hol/inductive.rs` | 1 | 0 | `hol_bootstrap` |
| `src/hol/hol_theorems.rs` | 1 | 0 | `hol_bootstrap` |
| `src/hol/function.rs` | 1 | 0 | `hol_bootstrap` |
| `src/hol/axclass.rs` | 1 | 0 | `hol_bootstrap` |
| `src/core/morphism.rs` | 1 | 0 | `parser_loader_debt` |
| `src/core/more_thm.rs` | 1 | 2 | `tactic_intermediate` |
| `src/core/bires.rs` | 1 | 0 | `tactic_intermediate` |
| `src/core/proofterm.rs` | 0 | 0 | migrated to checked fixtures |
| `tests/proptest.rs` | 0 | 0 | migrated to checked fixtures |
| `tests/integration_tests.rs` | 2 | 0 | legacy TPTP/pretty-printer integration |

## Observations

- The largest compatibility debt is HOL/bootstrap generation, not the strict
  kernel itself.
- No obvious `fallback_should_admit` site was changed in this pass. The sampled
  method fallback paths already use classified `admitted:*` reasons.
- `src/isar/method.rs` is intentionally left as mixed: it contains proof-state
  setup, method tests, and theorem-shape construction. It should be migrated by
  hunk, not by whole file.
- `_compat` usage in tests is not automatically wrong. Kernel-facing tests
  should migrate to checked fixtures when they are testing trusted behavior;
  tests that characterize legacy behavior should keep `_compat` explicit.
- First test-fixture migration pass moved `src/core/proofterm.rs`, the
  trusted-path parts of `src/core/thm.rs`, and most of
  `tests/kernel_soundness.rs` to checked CTerms plus strict `ThmKernel`
  constructors. Remaining `tests/kernel_soundness.rs` `_compat` calls
  intentionally test compatibility taint and trusted-table rejection.
- Second test-fixture migration pass moved `tests/proptest.rs` kernel property
  scaffolds and `tests/integration_tests.rs::test_kernel_15_ops` to checked
  fixtures. Remaining `tests/integration_tests.rs` `_compat` calls are legacy
  TPTP/pretty-printer export tests over HOL/dummy syntax, not strict-kernel
  coverage.
- First production proof-state migration moved `ProofState::assume` to checked
  proposition certification plus strict `ThmKernel::assume`. It now produces a
  Strict open theorem (`A |- A`) that can pass strict invariants but cannot
  satisfy `is_strict_closed_proved()`. Remaining `src/isar/proof_state.rs`
  compatibility calls are `have`/`show` goal construction, `obtain`, and
  legacy subgoal/test scaffolding; they need separate parser/type or proof
  search design before strict migration.
- Proof goal boundary migration moved `Goal::init` to checked proposition
  certification plus strict `ThmKernel::assume`, and added checked
  `ProofState::new_checked_goal` / `set_subgoals_checked` constructors.
  Top-level goal initialization and fake induction subgoal scaffolding no
  longer default to compat theorem construction. Remaining proof-state compat
  sites are:
  - `src/isar/proof_state.rs::have` and `show`: `have_show_obtain_obligation`.
  - `src/isar/proof_state.rs::parse_and_exec_obtain`: `have_show_obtain_obligation`.
  - `src/isar/proof_state.rs::test_simple_by_proof`: `legacy_test_fixture` over dummy equality syntax.
  - `src/isar/proof.rs::test_chaining`: `legacy_test_fixture`.
- Proof-state checked certification now uses explicit `ProofCertContext`
  declarations. The old transition helper that walked a raw term and declared
  its Const/Free annotations into a temporary trusted `TypeEnv` has been
  removed; undeclared Const/Free nodes are proof-context certification errors,
  not accepted checked goals.

## Migration Order

1. Keep the current trust taint: `_compat` results must remain
   `ThmTrust::Compat`.
2. Migrate high-value kernel tests from `_compat` fixtures to checked fixtures.
3. Replace any newly discovered proof fallback `_compat` theorem with
   `ThmKernel::admit(ct, "admitted:specific_reason")`.
4. Continue proof-state migration by separating `have`, `show`, and `obtain`
   proof obligations from tactic/search scaffolding.
5. Audit HOL bootstrap packages separately and decide between real
   derivations, classified admissions, or trusted definitional extensions.
