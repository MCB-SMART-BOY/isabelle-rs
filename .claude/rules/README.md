---
description: Isabelle-rs current status, trust laws, and rule index.
globs: "**/*.rs"
alwaysApply: true
version: 3.0
---
# Isabelle-rs Project Rules

Isabelle-rs remains a Rust research prototype; complete native Isabelle2025
compatibility is an approved goal, not implemented behavior. For current progress,
trust metrics and blockers use [`PROJECT_STATUS.md`](../../docs/status/PROJECT_STATUS.md)
and [`TRUST.md`](../../docs/status/TRUST.md), not this routing index or session memory.
Root [AGENTS.md](../../AGENTS.md) is the cross-agent authority; these rules add
Claude-specific routing and must not override it.

`cargo +stable xtask verify` is the deterministic repository gate (including
workspace tests); `selftest` checks xtask independently. `strict` remains scoped
to the trusted boundary, and `core` measures a sampled 125-theorem diagnostic,
not full theory compilation. `all`/`broad` and Tier 2/3 are explicit, expensive
diagnostics, not verification replacements. Independent security audits and the
complete global validator remain separate; see the
[command catalog](../../scripts/README.md#verification) and
[development guide](../../docs/guides/DEVELOPMENT.md#engineering-workflow).

## Iron Laws

1. Keep theorem construction authority private to the correct kernel layer.
2. Never use `assume` as parser, method, proof-search, or stub fallback; sampled legacy admission is an explicitly classified diagnostic, never strict acceptance.
3. Never accept dummy or compat input in the candidate strict kernel.
4. Preserve types, hypotheses, `tpairs`, `shyps`, oracles, derivations, and
   theory provenance through inference.
5. Keep `ProofObligation` and `SearchFact` outside `TrustedTheory`.
6. Treat legacy `is_strict_closed_proved()` only as
   `TransitionalStrictClosed`.
7. Require context-bound new-kernel `TrustedTheorem` values for
   `KernelTrustedClosed`.
8. Do not add theorem-specific HOL primitives to `src/core` or `src/kernel`.
9. Expand native capability only under the staged [`ROADMAP.md`](../../docs/status/ROADMAP.md) program and a separately reviewed trust-boundary contract; one sampled token is not general HOL support.
10. Use typed errors for control flow; messages are display-only.
11. Add attack tests for every trusted-boundary side condition.
12. Put all runnable project automation in `xtask/`; `scripts/` retains official
    reference probe inputs and classified design templates only. Keep Markdown
    examples short and explanatory.

For the change lifecycle follow [`DEVELOPMENT.md#engineering-workflow`](../../docs/guides/DEVELOPMENT.md#engineering-workflow),
not the A–H product roadmap.

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
