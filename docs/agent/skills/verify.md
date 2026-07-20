---
name: Verify Lemma
description: Verify lemmas and reports without conflating searchable, admitted, transitional, or kernel-trusted outcomes.
category: verification
version: 3.0.0
triggers: [lemma verification, proof failure, test failure, this lemma doesn't prove, verify fails]
permissions: [Bash:cargo test, Bash:cargo run, Read, Grep]
---
# Verify

Classify each result as `KernelTrustedClosed`, `TransitionalStrictClosed`, compat
closed-shaped, open, admitted with a specific reason, or failed. Record whether
`src/kernel`, legacy `src/core`, an Isar adapter, or a compatibility fallback
produced it.

For registered adapters, `Proved` and `Rejected` precede parser-gap/legacy
fallback; only `NotApplicable` may continue. Never count oracle-free open facts
or raw database entries as proved lemmas.

Run `scripts/dev-check.sh strict` for boundary changes and `core` for sampled
statistics. Use `scripts/audit-compat.sh` when compatibility matching or
certification is involved.
