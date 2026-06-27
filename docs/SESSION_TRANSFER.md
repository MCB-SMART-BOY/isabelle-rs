# Session Transfer

This file is intentionally short. Older session-transfer documents in this
repository are historical snapshots and must not be treated as current project
status.

For current context, read these in order:

1. [PROJECT_STATUS.md](PROJECT_STATUS.md)
2. [TRUST.md](TRUST.md)
3. [ROADMAP.md](ROADMAP.md)
4. [KERNEL_RULES.md](KERNEL_RULES.md)
5. [KERNEL_ATTACK_TESTS.md](KERNEL_ATTACK_TESTS.md)

## Current Project Position

```text
Isabelle-rs is a Rust research prototype of an Isabelle/Pure-inspired
LCF-style proof kernel. It focuses on explicit oracle footprints,
closed-theorem acceptance, and proof-object replay rather than broad
Isabelle/HOL feature parity.
```

Do not describe the current project as a full Rust rewrite of Isabelle.

## Current Priority

The next engineering track is:

1. Extend T4 proofterm replay beyond the current minimal rule set.
2. Tighten parser/type/certification boundaries.
3. Reduce admitted lemmas by classified reason.
4. Expand HOL/Isar/tool coverage later.

## Known Persistent Debts

- `alpha_eq` Free/Const compatibility.
- `alpha_eq` Var/Free compatibility.
- `Typ::dummy()` at parser/type/certification boundaries.
- Partial proofterm replay coverage.
- HOL/Isar tooling far from Isabelle parity.

## Verification Reminder

For trusted-boundary changes:

```bash
cargo fmt --check
cargo test --test kernel_soundness
cargo test core::proofterm::tests::
cargo test core::thm::tests::
cargo test --lib core::
cargo check
```

Do not claim broad `cargo test --lib` success unless the theory-loader
stack-sensitive test has been verified fixed.
