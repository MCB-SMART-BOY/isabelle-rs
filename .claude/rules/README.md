---
description: Isabelle-rs current status, trust laws, and rule index.
globs: "**/*.rs"
alwaysApply: true
version: 3.0
---
# Isabelle-rs Project Rules

Isabelle-rs is a Rust research prototype of an Isabelle/Pure-inspired LCF
kernel, not a full Isabelle rewrite.

Root [AGENTS.md](../../AGENTS.md) is the cross-agent authority. These rules only
add Claude-specific routing and must not override it.

## Current Trust Status

| Area | Status |
|---|---|
| Candidate target TCB | `src/kernel/`: checked `CProp`, private theorem construction, immutable context/fact ancestry, recursive accepting replay, theorem dependencies, and sealed trusted tokens. |
| Legacy quarantine | `src/core/` plus current HOL/Isar verification remain transitional proof authority. |
| Sampled results | `TransitionalStrictClosed: 1/125`; `KernelTrustedClosed: 0/125`. |
| Missing trusted loop | Data-only source AST → declaration-aware checked `HOL.Trueprop` elaboration → data-only HOL basis → conservative definitions → accepted HOL theorem. |
| Verification | `scripts/dev-check.sh` is authoritative; `scripts/README.md` indexes modes/templates. |

## Iron Laws

1. Keep theorem construction authority private to the correct kernel layer.
2. Never use `assume` as parser, method, proof-search, or stub fallback.
3. Never accept dummy or compat input in the candidate strict kernel.
4. Preserve types, hypotheses, `tpairs`, `shyps`, oracles, derivations, and
   theory provenance through inference.
5. Keep `ProofObligation` and `SearchFact` outside `TrustedTheory`.
6. Treat legacy `is_strict_closed_proved()` only as
   `TransitionalStrictClosed`.
7. Require context-bound new-kernel `TrustedTheorem` values for
   `KernelTrustedClosed`.
8. Do not add theorem-specific HOL primitives to `src/core` or `src/kernel`.
9. Do not expand `HOL::trans`, `hol_subst`, broad methods, or surface coverage
   before the minimum trusted HOL loop is designed and implemented.
10. Use typed errors for control flow; messages are display-only.
11. Add attack tests for every trusted-boundary side condition.
12. Keep large runnable or repeated examples in `scripts/` or classified
    `scripts/templates/`; short explanatory Markdown blocks are allowed.

## Rule Index

| Rule | Scope |
|---|---|
| [kernel](kernel.md) | Candidate TCB and legacy quarantine. |
| [type-system](type-system.md) | Checked terms, propositions, schemes, and sorts. |
| [isar](isar.md) | Source provenance and strict adapter order. |
| [theory-loading](theory-loading.md) | Theory parsing, fact databases, and acceptance. |
| [proof-methods](proof-methods.md) | Search/fallback boundaries. |
| [testing](testing.md) | Verification modes and attack coverage. |
| [error-handling](error-handling.md) | Typed rejection and fail-closed behavior. |
| [api-design](api-design.md) | Visibility and non-forgeable APIs. |
| [code-quality](code-quality.md) | Rust and documentation workflow. |
| [concurrency](concurrency.md) | Deterministic shared state. |
| [iterative](iterative.md) | Deep traversal conversion. |
| [performance](performance.md) | Candidate-only optimization. |
| [refactoring](refactoring.md) | Behavior-preserving structural changes. |
| [security](security.md) | Input, unsafe, dependency, and plugin boundaries. |
| [release](release.md) | Honest release verification and positioning. |
