# Kernel Rules Audit

This document is the working audit ledger for legacy `src/core/thm.rs`. The
goal is not to mirror all of Isabelle/Pure yet, but to make every trusted
constructor's logic rule, side conditions, trust-footprint behavior, and known
gaps explicit.

The new strict-kernel target architecture lives in `src/kernel/`; its ADR and
first primitive-rule contracts are documented in
[ADR-0001-kernel-core-rewrite.md](ADR-0001-kernel-core-rewrite.md) and
[KERNEL_PRIMITIVES.md](KERNEL_PRIMITIVES.md). New trusted work should prefer the
strict nucleus and adapters over further compatibility patching in this legacy
ledger.

For high-level positioning and roadmap context, read
[PROJECT_STATUS.md](PROJECT_STATUS.md) and [ROADMAP.md](ROADMAP.md). This file is
the rule-level ledger, not a claim of full Isabelle `thm.ML` equivalence.

## Invariants

- `Thm` fields remain private; external code must use `ThmKernel`.
- `assume` creates `A |- A`; it is not a theorem of `A` without hypotheses.
- `is_fully_proved()` means oracle-free only.
- `is_closed_proved()` means oracle-free closed shape only; compatibility
  theorems may satisfy it.
- Trusted lemma acceptance must use `is_strict_closed_proved()` (strict
  construction, oracle-free, no hypotheses, no unresolved `tpairs`, no dummy
  types).
- `admit` is the only intentional unproved-entry point and must tag `oracles`.
- `instantiate_checked` is the production theorem-instantiation boundary; the
  old infallible `instantiate` entry point is not available in production code.
- `Thm::check_proof()` replays proof objects for the supported T4 subset; it is
  not a shallow oracle/proposition field check.
- `Thm::validate_proof()` must use the same burden-aware replay gate. A stale
  `ProofBody.checked` flag must not bypass theorem-shape validation.
- `Derivation` and `ThmDeriv` are crate-internal proof records, not public
  theorem-construction authority.
- Single-premise rules must preserve `hyps`, `tpairs`, `shyps`, and `oracles`.
- Multi-premise rules must union `hyps`, `tpairs`, `shyps`, and `oracles`.
- Known non-dummy types must not be silently crossed by kernel rules.
- Trusted kernel equality uses `Hyps::kernel_alpha_eq`, not parser/loader
  compatibility matching.
- `Hyps::compat_alpha_eq` is an explicitly named legacy compatibility relation;
  it must not be used by trusted `ThmKernel` primitive rules.
- `CTerm::certify_checked(term, type_env)` is the strict certification API for
  new trusted paths. It rejects undeclared constants, ill-typed applications,
  unbound de Bruijn indices, and residual `Typ::dummy()`.
- `CTerm` now records `CertStatus::Checked` or `CertStatus::Compat`.
  `CTerm::certify` / `certify_compat` / `certify_typed` produce compatibility
  CTerms, not hard trusted certification.
- Strict `ThmKernel::assume` and `ThmKernel::reflexive` reject compatibility
  CTerms. Legacy behavior is explicitly named `assume_compat` /
  `reflexive_compat`.
- `ProofState::assume`, `Goal::init`, `ProofState::new_checked_goal`, and
  `ProofState::set_subgoals_checked` now route proof-state local assumptions
  and goal/subgoal obligations through checked certification plus strict
  `ThmKernel::assume`. These theorem values are Strict open obligations, not
  closed proved lemmas.
- Proof-state checked certification uses an explicit `ProofCertContext`
  derived from a theory/Isar context or supplied by tests. Consts and local
  frees must be declared there before certification; checked proof goals no
  longer auto-declare names from the raw term being certified.
- `Thm` records `ThmTrust::{Strict, Compat, Admitted}`. Compatibility theorem
  construction is tainted and cannot enter trusted theorem tables even if the
  theorem is oracle-free and closed-shaped.
- `Thm::check_kernel_invariants(KernelCheckMode::Strict)` is the strict audit
  gate for theorem internals: it requires `ThmTrust::Strict`, checked
  proposition/hypothesis CTerms, no dummy types in burdens, exact `maxidx`, no
  strict theorem oracle footprint, and burden-aware replay for the currently
  supported derivation subset.
- `check_kernel_invariants(Strict)` is not a closed-lemma predicate. Strict
  open theorems such as `A |- A` may pass it while still failing
  `is_strict_closed_proved()`.
- `check_kernel_invariants(Strict)` does not claim unsupported derivations have
  been independently replayed. Unsupported strict derivations are structurally
  audited until their replay rule is implemented.
- `KernelCheckMode::Compat` performs structural consistency checks only; it is
  for legacy/searchable facts and does not make a theorem trusted.
- `Typ::dummy()` tolerance is a parser/loader boundary compromise, not a kernel
  proof principle.

## Rule Ledger

| Rule | Anchor | Logical form | Side conditions | Propagation | Tests / status |
|---|---|---|---|---|---|
| `admit` | `ThmKernel::admit` | `|- A`, oracle-backed | caller supplies oracle name | empty `hyps/tpairs/shyps`; injects oracle; `ThmTrust::Admitted` | `test_admit_is_not_fully_proved`; `admitted_theorem_is_not_strict_trusted` |
| `assume` | `ThmKernel::assume` | `A |- A` | checked CTerm, no dummy | no oracle; `ThmTrust::Strict` | `compat_cterm_cannot_enter_strict_assume`; legacy tests use `assume_compat` |
| `assume_compat` | `ThmKernel::assume_compat` | `A |- A` | compatibility CTerm accepted | no oracle; `ThmTrust::Compat`; not a strict trusted entry | legacy parser/HOL/test scaffolding only |
| `reflexive` | `ThmKernel::reflexive` | `|- t == t` | checked CTerm, no dummy; derived equality CTerm remains checked | clean theorem; `ThmTrust::Strict` | `checked_cterm_constructs_checked_reflexive_theorem` |
| `reflexive_compat` | `ThmKernel::reflexive_compat` | `|- t == t` | compatibility CTerm accepted, may carry dummy | clean theorem shape but `ThmTrust::Compat` | `reflexive_compat_is_closed_shaped_but_not_strict_trusted` |
| `symmetric` | `ThmKernel::symmetric` | `Γ |- t == u` to `Γ |- u == t` | input must be equality | clone all premise burdens | oracle and shyp propagation tests |
| `transitive` | `ThmKernel::transitive` | `Γ |- t == u`, `Δ |- u == v` to `Γ∪Δ |- t == v` | middle terms strict-kernel alpha-equal; known middle-term and equality types compatible | union all premise burdens | type-mismatch and alpha-confusion attack tests |
| `combination` | `ThmKernel::combination` | `f == g`, `x == y` to `f x == g y` | first equality type must be function; known argument type compatible with domain | union all premise burdens | known mismatch and well-typed tests |
| `abstraction` | `ThmKernel::abstraction` | `Γ |- t == u` to `Γ |- (λx. t) == (λx. u)` | `x` not free in `Γ` | clone all premise burdens | free-in-hyp attack test |
| `beta_conversion` | `ThmKernel::beta_conversion` | `|- (λx. t) u == t[u/x]` | input must be an application whose function is an abstraction | clean theorem | Bound(0) substitution attack test |
| `implies_intr` | `ThmKernel::implies_intr` | `Γ∪{A} |- B` to `Γ |- A ==> B` | `A` present in hypotheses | remove discharged hyp; clone burdens | existing trivial/assume tests |
| `implies_elim` | `ThmKernel::implies_elim` | `Γ |- A ==> B`, `Δ |- A` to `Γ∪Δ |- B` | antecedent strict-kernel alpha-equal to minor proposition; known antecedent types compatible | union all premise burdens | type-mismatch attack test |
| `forall_intr` | `ThmKernel::forall_intr` | `Γ |- P` to `Γ |- !!x. P` | `x` not free in `Γ` | clone all premise burdens | free-in-hyp condition parallels abstraction |
| `forall_elim` | `ThmKernel::forall_elim` | `Γ |- !!x. P x` to `Γ |- P t` | input must be forall; known binder/argument types compatible | clone all premise burdens | binder/argument mismatch attack test |
| `instantiate_checked` | `ThmKernel::instantiate_checked` | `Γ |- P` to `Γθ |- Pθ` | environment assignments must preserve known variable types | clone burdens; normalizes hyps/prop | ill-typed env attack test |
| `instantiate_legacy` | `ThmKernel::instantiate_legacy` | test-only characterization of the removed infallible API | compiled only under `cfg(test)`; invalid environments leave theorem unchanged | clone burdens on success | internal no-unsound-theorem regression test |
| `bicompose` | `ThmKernel::bicompose` (⚠️ LEGACY CORE) | resolution/composition over a selected premise | selected premise exists; match/unify succeeds; known strict-alpha-match types compatible | union all premise burdens | alpha type-mismatch attack test |
| `subst_premise` | `ThmKernel::subst_premise` (⚠️ LEGACY CORE) | replace selected premise using `t == u` | selected premise strict-kernel alpha-equal to lhs; known lhs/premise types compatible | union all premise burdens | type-mismatch attack test |
| `bicompose_eresolve` | `ThmKernel::bicompose_eresolve` (⚠️ LEGACY CORE) | resolution with major-premise elimination | major premise matches available hyp/premise and conclusion matches subgoal; known types compatible | union all premise burdens | unifier type-mismatch attack test |
| `resolve1_match` | `KernelRules::resolve1_match` (strict `src/kernel/`) | backward resolution: rule conclusion matches selected goal subgoal → replace subgoal with rule premises under substitution | strict one-way matching only; no lifting/freshening; no full unification; no flex-flex; `RequiresLifting` on Free-variable collision | union and substitute hypotheses; invariant replay | 20 inline tests in `src/kernel/rules.rs`; see `docs/RESOLUTION_DESIGN.md` |

## Known Kernel Boundary Gaps

- `Hyps::kernel_alpha_eq` is now strict: it rejects Free/Const suffix matching,
  Var/Free matching, distinct schematic variable indices, and dummy-vs-known
  binder type matching.
- `Hyps::compat_alpha_eq` still preserves the old Free/Const, Var/Free, and
  dummy-binder behavior for explicitly named compatibility paths. This remains
  parser/loader boundary debt; do not use it in trusted `ThmKernel` rules.
- `forall_elim` enforces known binder/argument type compatibility, but
  `Pure::mk_all`/`lambda` still frequently leaves binder types as `Typ::dummy()`.
- `CTerm::certify_checked` is now available as a hard certification API, but
  most legacy parser/HOL/Isar call sites still use best-effort `CTerm::certify`
  or `certify_annotated`. Full trusted-path migration remains pending.
- `ThmKernel::assume` and `ThmKernel::reflexive` are now strict checked-entry
  rules. Existing legacy users were mechanically moved to `assume_compat` and
  `reflexive_compat`; those call sites are visible migration debt, not TCB.
- Proof-state local assumptions and goal/subgoal scaffolding have checked
  constructors. `have`, `show`, and `obtain` obligations still use explicit
  compatibility theorem scaffolding and remain separate proof-state migration
  debt.
- The checked proof-state constructors now reject undeclared constants and
  undeclared local frees even when the raw term carries non-dummy type
  annotations. This is a proof-context certification boundary, not just a
  no-dummy wrapper.
- `assume_compat` / `reflexive_compat` produce `ThmTrust::Compat`; final
  trusted theory tables and verified counts use `is_strict_closed_proved()`, so
  closed-shaped compatibility theorems remain searchable but untrusted.
- `is_strict_closed_proved()` is a cheap trusted-acceptance predicate.
  `check_kernel_invariants(Strict)` is the stronger audit predicate and should
  be used in strict-kernel tests and future CI gates.
- Passing `check_kernel_invariants(Strict)` means strict theorem internal
  consistency, not final closed theorem acceptance. Final trusted tables still
  use `is_strict_closed_proved()`.
- Unsupported replay rules may pass structural strict invariants but still fail
  `check_proof()` with an explicit unsupported-rule error.
- `ThmKernel::assume_checked` and `ThmKernel::reflexive_checked` remain
  transitional aliases for the strict names.
- Several tactic-facing operations still return `Option<Thm>`, so a rejected
  type mismatch is observationally the same as an ordinary match failure. This
  is sound but weak for diagnostics; the eventual shape should be closer to
  `Result<Option<Thm>, KernelError>` on trusted-boundary paths.
- Proof-object replay currently supports only `assume`, `reflexive`,
  `symmetric`, `transitive`, `implies_intr`, and `implies_elim`. Other kernel
  rules intentionally fail replay until their constructors/checkers are added.
- The next replay expansion batch is `beta_conversion`, `forall_intr`, and
  `forall_elim`; then `combination`/`abstraction`, then
  `instantiate_checked`, then resolution/substitution rules.
- `ProofBody::check(expected_prop)` remains a proposition-only compatibility
  helper and must not be used as a trusted theorem replay gate. The low-level
  proofterm check helpers are crate-internal; the public trusted entry points
  are `Thm::check_proof()` and `Thm::validate_proof()`.

## Proof Replay Snapshot

`Derivation` records the generated conclusion proposition and nested premise
derivations, so replay is independent of the mutable theorem fields being
checked. `Thm::check_proof()` reconstructs the theorem shape from the proof term
and compares:

```text
prop
hyps
tpairs
oracles
```

This makes `assume(A)` replay as a valid open theorem (`A |- A`) while still not
counting as `is_closed_proved()`. It also makes admitted/oracle-backed theorems
fail independent kernel replay instead of appearing as closed proofs.

The replay checker now uses the same strict kernel alpha-equivalence relation
and conservative known-type compatibility checks as the kernel for the
supported implication and transitivity paths. This avoids a completeness
mismatch where the kernel could construct a theorem whose supported derivation
then failed replay solely because middle terms were alpha-equivalent rather
than syntactically equal.

## Checked Instantiation Call-Site Audit

The legacy public `ThmKernel::instantiate` entry point has been removed from
production builds. The only infallible compatibility behavior is a private
`cfg(test)` helper used to keep the old "do not manufacture a theorem on bad
env" behavior characterized.

| Call site | Status | Rationale |
|---|---|---|
| `ThmKernel::bicompose` (⚠️ LEGACY CORE) | checked | Kernel resolution applies unifier through `instantiate_checked`; invalid env makes resolution fail. |
| `ThmKernel::bicompose_eresolve` (⚠️ LEGACY CORE) | checked | Elim-resolution applies unifier through `instantiate_checked`; invalid env makes resolution fail. |
| `ThmKernel::flexflex_resolve` | checked | Flex-flex resolution keeps the original theorem if checked instantiation fails. |
| `core::conv::instantiate_rule` | checked | Rewrite-rule instantiation now returns `None` on invalid env instead of returning an unrelated rule. |
| `tools::metis::try_all_resolutions` | checked | Clause resolution skips a unifier whose theorem instantiation is ill-typed. |
| `tools::metis::try_factor` | checked | Factoring skips ill-typed theorem instantiation. |
| `tools::metis::try_all_paramodulations` | checked | Paramodulation skips ill-typed equality/target instantiation. |
| `core::simplifier` / `tools::simp` | not theorem instantiation | These paths use `env.norm_term` to instantiate RHS/conditions, but do not call `ThmKernel::instantiate`; they remain part of the broader `CTerm` hard-certification work. |
| `core::tactic` | checked via kernel rules | Resolve/eresolve/simp tactics route through `bicompose` or `subst_premise` (⚠️ LEGACY CORE). |
| `core::bires` / `core::more_thm` | no direct instantiation | No migration needed in this pass. |
| `isar::method` debug matcher use | no theorem construction | Direct `Envir` use inspected is matcher diagnostics, not theorem instantiation. |

## Assume / Admit Audit Snapshot

`ThmKernel::assume` is legitimate for goal initialization, local assumptions,
and theorem shapes that intentionally carry the assumption as a hypothesis
(`A |- A`). This covers the main proof-state, tactic, Metis, linarith, and
kernel unit-test uses inspected in this pass.

The following paths are still trusted-boundary debt and must not be interpreted
as fully audited kernel derivations:

| Site | Current behavior | Risk | Next action |
|---|---|---|---|
| `isar::method::apply_attributes` for `[simplified]`, `[folded]`, `[unfolded]`, `[rule_format]` | rewrites/transforms a theorem proposition and admits the result as `admitted:attribute_transformation` | transformation is honest but not a kernel derivation | replace with a derivation-producing conversion |
| `isar::spec`, `theory::loader`, `hol_loader`, datatype/BNF/record generators | registers parsed/generated facts through `assume` | parser/loader/generated rule boundary is not yet an honest oracle boundary | classify by source and migrate stubs to `admit` |
| `core::conv` recursive conversions | temporary subterms are wrapped with `assume` while building conversions | may be fine as local conversion scaffolding, but still needs rule-by-rule proof-object replay | revisit during T4 proof checker integration |

Confirmed fallback/admit exit sites in `isar::method` are now classified more
precisely:

| Exit site | Oracle name |
|---|---|
| proof engine failed after all proof attempts | `admitted:proof_engine_failed` |
| built-in theorem uses schematic `Var` where parser produced `Free` | `admitted:parser_gap` |
| missing or empty proof script with no builtin theorem | `admitted:unsupported_method` |
| anonymous datatype/list rule stub | `admitted:datatype_stub` |
| theorem attribute transformation without kernel derivation | `admitted:attribute_transformation` |

## Current Delta From This Audit Pass

- `transitive` now rejects two known, distinct equality types instead of
  silently using the first equality type for the result.
- `transitive` now uses the same uniqueness-preserving `tpairs`/`shyps` union
  helpers as the other multi-premise rules.
- `beta_conversion` now substitutes the argument for `Bound(0)` via
  `term_subst::subst_bounds`, instead of returning the raw abstraction body.
- `implies_elim`, `forall_elim`, `subst_premise` (⚠️ LEGACY CORE), `bicompose` (⚠️ LEGACY CORE), and
  `bicompose_eresolve` (⚠️ LEGACY CORE) now reject alpha/unifier matches when both sides carry
  known incompatible concrete types.
- `instantiate_checked` rejects known ill-typed environment assignments before
  theorem instantiation; the old public infallible `instantiate` entry point is
  no longer available in production builds.
- `unify` rigid-rigid atom matching now rejects same-name `Const`/`Free` pairs
  with known incompatible concrete types.
- Production proof-search call sites in `core::conv` and `tools::metis` now use
  `instantiate_checked`.
- `isar::method` fallback admissions now use classified oracle names instead of
  one generic `"admitted"` tag for the audited exit sites.
- Lemma statistics first stopped at `Thm::is_closed_proved()`, not just an empty
  oracle footprint; open `A |- A` theorems no longer count as proved lemmas.
  The strict-kernel phase further requires `Thm::is_strict_closed_proved()` so
  compatibility closed-shapes no longer count either.
- Non-derivational theorem attribute transformations now use
  `admitted:attribute_transformation` instead of `assume`-wrapping the result.
- `TheoryProcessor::process_source_verified` and final `LocalTheory` registration
  now require `is_strict_closed_proved()`; `accept_all` remains searchable in
  the local index as an admitted theorem but does not enter the final trusted
  theorem table.
- `SessionBuilder` now reports strict closed proved theorem counts instead of
  indexed theorem entries; `accept_all` and compatibility-only files are not
  `FullSuccess`.
- `HolTheoremDb` is explicitly a proof-search fact index. It may contain open,
  admitted, or compatibility facts in `by_name`/nets, so trusted statistics
  must use strict `closed_proved_count()` or the final `Theory` table.
- T4 proof replay has a minimal closed loop for
  `assume/reflexive/symmetric/transitive/implies_intr/implies_elim`. Tampering
  with a theorem proposition or nested premise derivation is rejected by
  `check_proof`; admitted theorems fail replay and remain outside closed proved
  theorem acceptance.
- T4 replay consistency audit closed the stale `ProofBody.checked` bypass in
  `Thm::validate_proof`, added burden-mismatch regression tests for
  `hyps`/`tpairs`/`oracles`, documented `ProofBody::check` as proposition-only,
  and reduced `Derivation`/`ThmDeriv` plus low-level proofterm check helper
  visibility to crate-internal.
- Strict kernel alpha-equivalence is now separated from legacy compatibility
  matching. Trusted `ThmKernel` rules and replay use `kernel_alpha_eq`, while
  `compat_alpha_eq` is isolated for explicitly marked parser/loader
  compatibility paths.
