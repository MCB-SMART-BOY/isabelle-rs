---
description: Candidate src/kernel TCB and legacy src/core trust rules.
globs: src/kernel/**, src/core/thm.rs, src/core/proofterm.rs, tests/kernel_*.rs
alwaysApply: false
version: 5.0
updated: 2026-07-18
---
# Kernel Rules

`src/kernel` is the candidate target Pure/LCF TCB nucleus, not yet the sole
project TCB. It admits no dummy type, compat certification, fallback theorem
construction, or upper-layer dependency. `ProofObligation` and `SearchFact`
cannot become `TrustedTheorem`; unchecked constructors remain kernel-private.

`src/core` is legacy quarantine. Changes are limited to soundness fixes,
diagnostics, and migration adapters; do not add theorem-specific HOL proof
power. Preserve hypotheses, `tpairs`, `shyps`, oracles, types, theory provenance,
and replay data through every inference.

Legacy strict shape counts only as `TransitionalStrictClosed`.
`KernelTrustedClosed` requires the token returned by exact-owner
`accept_closed_theorem`; object-logic results additionally require the missing
authorized basis/axiom/definition layers. Run `scripts/dev-check.sh strict` and
update the trust/attack ledgers.
