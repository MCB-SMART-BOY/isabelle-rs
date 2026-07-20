---
name: Audit Kernel
description: Audit strict src/kernel and legacy src/core trust boundaries, context identity, replay, and theorem acceptance.
category: safety
version: 3.0.0
triggers: [kernel change, theorem construction, context identity, proof statistics, new inference rule, kernel safety]
permissions: [Bash:cargo test, Read, Grep]
---
# Audit Kernel

Read `AGENTS.md`, `docs/TRUST.md`,
`docs/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md`, `docs/KERNEL_PRIMITIVES.md`,
`docs/KERNEL_ATTACK_TESTS.md`, and ADR-0001 before review.

For `src/kernel`, reject dummy types, compatibility certification, fallback
theorem construction, upper-layer dependencies, public unchecked constructors,
mixed or forgeable context identities, context-free final acceptance, and
promotion from `ProofObligation`/`SearchFact` to `TrustedTheorem`. Every rule
needs explicit side conditions, burden/context propagation, replay, and attack
tests.

For legacy `src/core`, allow only migration diagnostics, non-proof-power
adapters, and soundness fixes. Do not add theorem-specific HOL primitives. Run
`scripts/audit-compat.sh`, then `scripts/dev-check.sh strict`; run `core` when
theorem statistics or adapter behavior changes.

Report `TransitionalStrictClosed` separately from `KernelTrustedClosed`. The
sampled baseline remains `1/125` versus `0/125`.
