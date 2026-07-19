# Development Guide

This guide covers day-to-day development commands for Isabelle-rs.

Start with root [AGENTS.md](../AGENTS.md). For project positioning, read
[PROJECT_STATUS.md](PROJECT_STATUS.md); for trust semantics, read
[TRUST.md](TRUST.md).

## Environment

- Rust stable matching the repository toolchain.
- Cargo.
- Large theory tests use the stack configured by
  [scripts/dev-check.sh](../scripts/dev-check.sh).

## Common Commands

Fast checks:

Run `scripts/dev-check.sh fast`.

Trusted-kernel gate (full, all changes):

Run `scripts/dev-check.sh strict`.

This unified gate runs:
1. `cargo +stable fmt --check`
2. `cargo +stable check --locked`
3. `bash scripts/check-kernel-firewall.sh` (no legacy deps or forbidden patterns in `src/kernel/`)
4. The `kernel_rewrite_soundness` and `kernel_context_identity` attack suites.
5. The current `kernel_soundness` boundary suite.
6. The strict `kernel::thm::`, `kernel::unify::tests::`,
   `kernel::rules::tests::`, and `kernel::theory::` inline suites.
7. The legacy `core::` compatibility suite.

Theory verification:

Run `scripts/dev-check.sh core`, `tier2`, or `tier3`. Use
`scripts/dev-check.sh broad` for all three.

Broad library test:

Run the explicit `scripts/dev-check.sh lib` mode.

Do not report broad `cargo test --lib` as passing unless the known
`theory::loader::tests::test_batch_scan_theories` stack-overflow behavior has
been verified fixed in the current checkout.

## Documentation-Only Changes

For docs-only edits:

Run `scripts/dev-check.sh docs`.

No source test claims should be made unless the relevant tests were actually
run.

## Documentation And Templates

Markdown may contain short explanatory Bash, Rust, PowerShell, TOML, or JSON
blocks when they clarify a local contract. Do not maintain large runnable or
duplicated scripts in documentation.

Put reusable commands and audits in [scripts/](../scripts/), and reusable
design/configuration skeletons in
[scripts/templates/](../scripts/templates/). Every template is classified in
[scripts/templates/README.md](../scripts/templates/README.md).
`scripts/check-rust-templates.sh` proves only that classified Rust design files
compile standalone; it does not validate production API compatibility,
architecture, theorem semantics, or trust.

## Trusted-Kernel Change Rules

When touching these files:

```text
src/kernel/**
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
| transitional strict closed | legacy strict construction plus closed proved shape and no dummy types; use `thm.is_strict_closed_proved()` for migration classification only. |
| kernel-trusted closed | context-bound `src/kernel::TrustedTheorem` over `CProp : prop`, with immutable theory/logic provenance and required replay; the sampled count is `0/125`. |
| open theorem | valid theorem with hypotheses, such as `A |- A`. |
| admitted theorem | theorem accepted with explicit oracle footprint. |
| searchable fact | fact available to proof search; may be open or admitted. |
| trusted theorem table | final new-kernel `TrustedTheory`; accepts only context-bound `src/kernel::TrustedTheorem` values, never a legacy classifier result. |

## Proof Replay Development

The legacy `src/core/proofterm.rs` compatibility replay minimum currently
documents:

```text
assume
reflexive
symmetric
transitive
implies_intr
implies_elim
```

The separate `src/kernel::Derivation` inventory is listed in
[KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](KERNEL_TRUSTED_ACCEPTANCE_GAPS.md); every
current variant has an exact-context replay arm. Logic-basis and dependency
resolution remain absent.

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

## Agent Harness And Review

Repository rules are harness-neutral. Oh My Pi is suitable as the primary
long-lived harness for context, LSP, structured edits, read-only audit fan-out,
and isolated worktrees. Codex-compatible models or CLI sessions remain useful
for bounded implementations, adversarial review, and independent reproduction.

Use separate implementation and review channels for high-risk TCB changes when
possible. Neither harness memory nor model agreement is proof evidence; source,
tests, ADRs, and the exact verification output remain authoritative.

Do not create commits, rebase, rewrite history, or push without explicit user
instruction.

## Files Not To Touch Accidentally

Do not modify these unless explicitly in scope:

```text
Cargo.lock
isabelle-source
```

An intentional lockfile update needs a dependency or security rationale and
locked verification. A successful `cargo metadata --locked` proves that the
lockfile is usable, not that an unexplained refresh belongs in the change.
Keep dependency/vendor changes separate from parser, trust, metrics, tests, and
documentation work. Preserve unrelated dirty work.

## Current Engineering Priorities

1. Keep immutable `TheoryId` / `SignatureId` propagation and exact-context
   strict theorem construction stable.
2. Keep the implemented context/dependency-aware, mutually exclusive
   `KernelTrustedClosed` acceptance gate stable.
3. Keep the implemented data-only source proposition AST semantically
   unresolved and disconnected from kernel theorem authority.
4. Next, integrate source parsing and elaborate checked judgments, constants,
   and polymorphic type schemes, including `HOL.Trueprop`, into `CProp : prop`.
5. Install the HOL logical basis as an immutable data-only manifest replayed by
   generic kernel code.
6. Add a generic conservative definition extension; do not promote
   `true_def_transport`.
7. Re-derive `HOL::TrueI` through the new kernel before adding another theorem
   adapter or object-logic proof primitive.
8. Extend replay and reduce admitted paths without widening legacy `src/core`
   trusted proof power.
