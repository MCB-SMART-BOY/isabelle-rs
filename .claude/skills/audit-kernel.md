---
name: Audit Kernel
description: Audit isolated crates/kernel and legacy src/core trust boundaries, context identity, replay, and theorem acceptance; src/kernel is a re-export.
category: safety
version: 3.0.0
triggers: [kernel change, theorem construction, context identity, proof statistics, new inference rule, kernel safety]
permissions: [Bash:cargo test, Read, Grep]
---
# Audit Kernel

Read [`AGENTS.md`](../../AGENTS.md),
[`TRUST.md`](../../docs/status/TRUST.md),
[`KERNEL_TRUSTED_ACCEPTANCE_GAPS.md`](../../docs/kernel/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md),
[`KERNEL_PRIMITIVES.md`](../../docs/kernel/KERNEL_PRIMITIVES.md),
[`KERNEL_ATTACK_TESTS.md`](../../docs/kernel/KERNEL_ATTACK_TESTS.md), and
[`ADR-0001`](../../docs/adr/ADR-0001-kernel-core-rewrite.md) before review.

For `crates/kernel` (re-exported by `src/kernel`), reject unregistered type
constructors/arity, invalid axiom schemas at installation, non-monomorphic
definition RHS, dummy types, compatibility certification, fallback theorem
construction, upper-layer dependencies, public unchecked constructors, mixed
or forgeable context identities, context-free final acceptance, and promotion
from `ProofObligation`/`SearchFact` to `TrustedTheorem`. Check exact ancestor
token payloads, local replay Free scope, rule side conditions, burden/context
propagation, and attack tests.

For legacy `src/core`, allow only migration diagnostics, non-proof-power
adapters, and soundness fixes. Do not add theorem-specific HOL primitives. Run
`cargo +stable xtask compat`, then `cargo +stable xtask strict`; run `core` when
theorem statistics or adapter behavior changes.

Report `TransitionalStrictClosed` separately from `KernelTrustedClosed`. The
last pre-migration source-backed five-file sample reported
`TransitionalStrictClosed: 0/125` and `KernelTrustedClosed: 1/125`
(`HOL::TrueI` projection); that is not a new migrated-xtask pass. The two
standalone CLI fixtures do not contribute to the 125.
