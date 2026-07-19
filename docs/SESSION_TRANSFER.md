# Session Transfer

This file is intentionally short. Older session-transfer documents in this
repository are historical snapshots and must not be treated as current project
status.

For current context, read these in order:

1. Root [AGENTS.md](../AGENTS.md)
2. [PROJECT_STATUS.md](PROJECT_STATUS.md)
3. [TRUST.md](TRUST.md)
4. [KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](KERNEL_TRUSTED_ACCEPTANCE_GAPS.md)
5. [ROADMAP.md](ROADMAP.md)
6. [KERNEL_RULES.md](KERNEL_RULES.md)
7. [KERNEL_ATTACK_TESTS.md](KERNEL_ATTACK_TESTS.md)

## Current Project Position

```text
Isabelle-rs is a Rust research prototype of an Isabelle/Pure-inspired
LCF-style proof kernel. It focuses on explicit oracle footprints,
closed-theorem acceptance, and proof-object replay rather than broad
Isabelle/HOL feature parity.
```

Do not describe the current project as a full Rust rewrite of Isabelle.

## Current Priority

The sampled baseline remains:

```text
TransitionalStrictClosed: 1/125
KernelTrustedClosed:      0/125
```

Implementation must proceed in exactly this order:

```text
immutable SignatureId / TheoryId [implemented]
  -> unique context-bound acceptance [implemented]
  -> data-only source proposition AST [implemented]
  -> checked parser/declaration/type-scheme elaboration [next]
  -> data-only HOL logic-basis manifest
  -> generic conservative definition extension
  -> HOL::TrueI as HOL.Trueprop HOL.True
  -> HOL::trans only as a later reuse consumer
```

`refl` and `subst` remain HOL basis axioms. The manifest is data only: it has no
executable HOL validator or theorem factory. No `hol_subst`, additional theorem
adapter, or HOL-specific kernel primitive may bypass this order.

## Known Persistent Debts

- `compat_alpha_eq` Free/Const compatibility outside the strict kernel.
- `compat_alpha_eq` Var/Free compatibility outside the strict kernel.
- `Typ::dummy()` at parser/type/certification boundaries.
- No source-faithful HOL `Trueprop` elaboration or conservative definition
  mechanism yet.
- No immutable `SignatureId`, `TheoryId`, or `LogicBasisId` on accepted
  new-kernel theorems yet.
- Partial proofterm replay coverage.
- HOL/Isar tooling far from Isabelle parity.

## Verification Reminder

For trusted-boundary changes:

Run `scripts/dev-check.sh strict` from the repository root.

Do not claim broad `cargo test --lib` success unless the theory-loader
stack-sensitive test has been verified fixed.
