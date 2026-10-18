# Session Transfer

> Historical session-transfer snapshot (2026-10-03 sampled checkpoint), not
> current implementation or verification guidance. Its dependency-order
> proposal below predates sampled `HOL::TrueI` acceptance and the checked
> declaration, basis, and definition paths. The 2026-10-07 bundled sample
> instead records `TransitionalStrictClosed: 0/125` and
> `KernelTrustedClosed: 1/125` for audited `HOL::TrueI` alone; independent
> Pure/HOL fixtures remain outside the sample. The approved native
> compatibility program separately targets official Isabelle/ML and PIDE,
> neither delivered by these historical trust results nor by ISIP design.
> For current context read:
>
> 1. Root [AGENTS.md](../../AGENTS.md)
> 2. [PROJECT_STATUS.md](../status/PROJECT_STATUS.md)
> 3. [TRUST.md](../status/TRUST.md)
> 4. [KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](../kernel/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md)
> 5. [ROADMAP.md](../status/ROADMAP.md)
> 6. [KERNEL_RULES.md](../kernel/KERNEL_RULES.md)
> 7. [KERNEL_ATTACK_TESTS.md](../kernel/KERNEL_ATTACK_TESTS.md)
> 8. [xtask cutover evidence](../status/PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11)
> 9. [engineering workflow](../guides/DEVELOPMENT.md#engineering-workflow)

## Project Position at This Historical Checkpoint

```text
Isabelle-rs is a Rust research prototype of an Isabelle/Pure-inspired
LCF-style proof kernel. It focuses on explicit oracle footprints,
closed-theorem acceptance, and proof-object replay rather than broad
Isabelle/HOL feature parity.
```

Do not describe the current project as a full Rust rewrite of Isabelle.

## Historical Priority

The 2026-10-03 sampled baseline was:

```text
TransitionalStrictClosed: 1/125
KernelTrustedClosed:      0/125
```

The following was the historical proposal, not today's mandatory sequence:

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

## Known Debts at This Historical Checkpoint

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

For the separate dated xtask results and current project commands, see
[xtask cutover](../status/PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11)
and [engineering workflow](../guides/DEVELOPMENT.md#engineering-workflow).
No result in this transfer note establishes a passing complete library suite,
full native compatibility, or a passing global validation gate.
