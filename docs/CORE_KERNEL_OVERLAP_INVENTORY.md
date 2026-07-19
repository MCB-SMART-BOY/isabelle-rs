# Core / Kernel Overlap Inventory

## Status

Initial architecture inventory. This is a migration planning document, not an
implementation patch.

The table's `P0`/`P1` labels indicate migration risk, not parallel execution
authorization. [ROADMAP.md](ROADMAP.md) orders current work: immutable context
identity, unique acceptance, then source/elaboration/HOL layers.

## Current Reality

`src/core` is still a legacy proof engine plus compatibility layer. It is not
yet a pure automation or candidate-generation layer.

`src/kernel` is the strict TCB nucleus and the target for trusted theorem
construction. It already contains primitive rules, strict matching, and
conservative resolution building blocks, but most HOL/Isar verification still
flows through legacy `src/core::Thm` paths.

The migration target is:

```text
src/kernel = only trusted theorem-construction layer
src/core   = legacy compatibility / automation / diagnostics / adapters
```

Until that migration is complete, `src/core` changes should be limited to:

```text
boundary hardening
diagnostics
migration adapters
```

New trusted proof rules should not be added to `src/core`.

## Inventory

| Feature | Core location | Kernel location | Current callers | Trust status | Migration target | Priority | Allowed core changes |
|---|---|---|---|---|---|---|---|
| Theorem construction | `src/core/thm.rs::Thm`, `ThmKernel` | `src/kernel/thm.rs::{KernelThm,OpenThm,ClosedThm,TrustedTheorem}` | Isar methods, HOL loader, tools, theory/session tables | Overlapping; core remains active legacy engine | Final trusted construction through `KernelThm -> ClosedThm -> TrustedTheorem` | P0 | Hardening, diagnostics, adapters only |
| Construction trust taint | `src/core/thm.rs::ThmTrust` | Strict types split open/closed/trusted stages | Core verification stats, theorem DB filters | Core has taint but not the target TCB | Keep legacy taint as `TransitionalStrictClosed`; authorize final acceptance only from a context-bound `src/kernel::TrustedTheorem` | P0 | Preserve and expose taint; never erase it |
| `assume` / reflexivity | `ThmKernel::{assume,assume_compat,reflexive,reflexive_compat}` | `KernelRules::{assume,reflexive}` | Proof state, parser/HOL compatibility, unit tests | Strict and compat variants coexist | Strict certification before strict rule calls | P0 | Remove silent fallback; keep compat explicit |
| Symmetry / transitivity | `ThmKernel::{symmetric,transitive}` | `KernelRules::{symmetric,transitive}` | Core rules, proofterm replay, tests | Implemented in both layers | Kernel-backed replay or adapter for accepted theorems | P1 | Keep behavior aligned; add diagnostics |
| Implication rules | `ThmKernel::{implies_intr,implies_elim}`, `core::drule` helpers | `KernelRules::{implies_intr,implies_elim}` | Isar goal export, proofterm replay, tactics | Core is still used for proof-method export | Route strict vertical slice through kernel implication rules | P0 | Boundary hardening and adapter support |
| Equality rules | Core equality theorem rules in `src/core/thm.rs` | `KernelRules::{equal_intr,equal_elim}` and equality-sensitive primitives | Rewriting, proofterm replay, HOL facts | Partial overlap; object equality adapters still noisy | Kernel replay for equality-derived facts | P1 | Diagnose parser/HOL equality gaps |
| Beta conversion | `ThmKernel::beta_conversion` | `KernelRules::beta_conversion` | Simplification/conversion tests | Implemented in both layers | Kernel conversion for strict replay path | P2 | Keep core checked; no trusted shortcuts |
| Instantiate / generalize | `src/core/term_subst.rs`, `ThmKernel::instantiate_checked`, generalize paths | `KernelRules::{instantiate,generalize}` | Isar method generalization, proofterm replay, tactic code | Core remains broad and compatibility-heavy | Strict substitution in kernel-backed proof search | P1 | Replace `None`/fallbacks with explicit reasons |
| Matching / unification | `src/core/unify.rs`, `src/core/envir.rs` | `src/kernel/unify.rs` strict matcher | Tactics, simplifier, resolution, method code | Core unifier still drives many methods | Kernel matcher for strict proof-search transitions | P1 | Diagnostics and adapter boundaries |
| Resolution / bicompose | `ThmKernel::{bicompose,subst_premise,bicompose_eresolve}` | `KernelRules::{resolve1_match,subst_premise,bicompose}` | Tactics and planned proof search | Core has broader legacy API; kernel has conservative subset | Kernel-backed `proof_search` resolution family | P1 | No new trusted resolution in core |
| Simplifier rewrite theorem handling | `src/core/simplifier.rs::RewriteRule::from_thm`, `Simplifier` | No trusted simplifier yet | `src/tools/simp.rs`, `src/isar/method.rs`, HOL simpdata | Core automation can affect proof outcomes | Automation proposes rewrites; strict replay checks theorem effects | P0 | Closed-rule admission, diagnostics, candidate adapters |
| Proofterm replay | `src/core/proofterm.rs` | `src/kernel/derivation.rs` invariant replay | Core theorem validation, tests | Core replay is partial; kernel replay covers implemented derivations | Kernel derivation replay for context-bound `KernelTrustedClosed` slices | P1 | Extend replay coverage only with clear contracts |
| Theorem acceptance | `Thm::is_strict_closed_proved`, theory/global filters | `accept_closed_theorem`, immutable `TrustedTheory`, sealed `TrustedTheorem` | Synthetic Pure tests and outcome classifier; no HOL adapter | Pure acceptance is exact-owner, replayed, dependency-aware, and conflict-safe; sampled HOL remains transitional | Feed source-elaborated, basis-authorized HOL derivations into the existing kernel gate | P0 | Reporting and burden-complete adapters only |
| Oracle/admit tracking | `ThmKernel::admit`, oracle footprints | Strict kernel has no implicit admit path | Parser gaps, datatype stubs, attributes, method fallback | Core admit is explicit but stringly typed | Structured `AdmitReason` under `ProofOutcome` | P0 | Split reasons; do not hide admits |
| Theorem DB / searchable facts | `src/hol/hol_loader.rs::HolTheoremDb`, global theory | `TrustedTheory`, `SearchFactDb` | Isar methods, tools, session loading | Searchable facts can be compat/admitted | Searchable facts stay separate from trusted facts | P0 | Add classification metadata |
| Parser / certification | Legacy `CTerm::certify` and compat paths | Strict `RawTerm -> CTerm/CProp` certification | Parser, Isar, HOL loader | Many call sites still compatibility-certified | Checked proposition elaboration for the first `KernelTrustedClosed` slice | P0 | Convert targeted paths; no best-effort trust |
| HOL constants/rules/stubs | HOL loader, simpdata, datatype stubs | No full HOL object logic kernel layer yet | Core verification batch and methods | Many facts are admitted or compat generated | HOL declarations feed strict-certified propositions | P2 | Keep stubs explicit and searchable only |

## Migration Rule

Every future change touching overlap areas should label itself as one of:

```text
hardening
diagnostic
migration adapter
strict migration
```

Changes that add trusted theorem acceptance to `src/core` are out of bounds.
