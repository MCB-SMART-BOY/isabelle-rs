# Development Guide

This guide covers day-to-day development commands for Isabelle-rs.

For project positioning, read [PROJECT_STATUS.md](PROJECT_STATUS.md). For the
trust model, read [TRUST.md](TRUST.md).

## Environment

- Rust stable matching the repository toolchain.
- Cargo.
- Large theory tests usually need:

```bash
export RUST_MIN_STACK=268435456
```

## Common Commands

Fast checks:

```bash
cargo fmt --check
cargo check
```

Trusted-kernel gate:

```bash
cargo fmt --check
cargo test --test kernel_soundness
cargo test core::proofterm::tests::
cargo test core::thm::tests::
cargo test --lib core::
cargo check
```

Theory verification:

```bash
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture
```

Broad library test:

```bash
RUST_MIN_STACK=268435456 cargo test --lib
```

Do not report broad `cargo test --lib` as passing unless the known
`theory::loader::tests::test_batch_scan_theories` stack-overflow behavior has
been verified fixed in the current checkout.

## Documentation-Only Changes

For docs-only edits:

```bash
cargo fmt --check
cargo check
```

No source test claims should be made unless the relevant tests were actually
run.

## Trusted-Kernel Change Rules

When touching these files:

```text
src/core/thm.rs
src/core/proofterm.rs
src/core/unify.rs
src/core/envir.rs
src/core/term.rs
src/core/types.rs
src/core/type_infer.rs
src/core/term_subst.rs
src/core/tactic.rs
src/core/simplifier.rs
```

follow this workflow:

1. Read [docs/KERNEL_RULES.md](KERNEL_RULES.md).
2. Add or update an attack test before or with the fix.
3. Preserve `hyps`, `tpairs`, `shyps`, and `oracles` through every rule.
4. Keep unproved fallback behind `ThmKernel::admit(ct, "admitted:specific_reason")`.
5. Never use `ThmKernel::assume` for proof failure, unsupported features, stubs,
   or attribute transformations.
6. Run the trusted-kernel gate.

## Theorem Status Vocabulary

Use these terms consistently:

| Term | Meaning |
|---|---|
| oracle-free | `thm.is_fully_proved()`; no oracle footprint. |
| closed proved shape | no oracle, no hypotheses, no unresolved `tpairs`; use `thm.is_closed_proved()` for shape only. |
| strict closed proved | strict construction plus closed proved shape and no dummy types; use `thm.is_strict_closed_proved()` for trusted acceptance. |
| open theorem | valid theorem with hypotheses, such as `A |- A`. |
| admitted theorem | theorem accepted with explicit oracle footprint. |
| searchable fact | fact available to proof search; may be open or admitted. |
| trusted theorem table | final exported table; should only contain strict closed proved theorems. |

## Proof Replay Development

Current supported replay rules:

```text
assume
reflexive
symmetric
transitive
implies_intr
implies_elim
```

When adding a new replay rule:

1. Mirror the corresponding `ThmKernel` side conditions.
2. Replay from stored derivation/proof data, not from the mutable theorem fields.
3. Compare reconstructed `prop`, `hyps`, `tpairs`, and `oracles`.
4. Make oracle/admitted premise behavior explicit.
5. Add positive and tampering tests.
6. Update [docs/KERNEL_RULES.md](KERNEL_RULES.md) and
   [docs/KERNEL_ATTACK_TESTS.md](KERNEL_ATTACK_TESTS.md).

`ProofBody::check(expected_prop)` is proposition-only compatibility code. Do not
use it as a trusted theorem replay gate. Use `Thm::check_proof()` or
`Thm::validate_proof()`.

## Files Not To Touch Accidentally

Do not modify these unless explicitly in scope:

```text
Cargo.lock
isabelle-source
```

The current repository often has unrelated dirty work. Preserve it.

## Current Engineering Priorities

1. Extend proofterm replay rule coverage.
2. Tighten parser/type/certification boundaries.
3. Reduce admitted lemmas by classified reason.
4. Expand HOL/Isar features only when doing so reduces admitted counts without
   widening trusted boundaries.
