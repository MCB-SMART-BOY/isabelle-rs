# Trusted Kernel Baseline

This document records the trusted-kernel checkpoint created before the Strict
Kernel Phase. It is a baseline for kernel-boundary work; it is not a claim of
full Isabelle compatibility.

This is a historical checkpoint. The completed strict-kernel work below is not
the current next phase; use [ROADMAP.md](ROADMAP.md) for the active
`SignatureId` / `TheoryId` and acceptance sequence.

## Baseline Commits

The first trusted-kernel engineering pass is split into these reviewable
commits:

```text
e60580b kernel: harden primitive rules and checked instantiation
7465d48 trust: require closed proved theorems for trusted acceptance
2dee3d0 proofterm: add minimal burden-aware derivation replay
eef6d80 docs: reposition project as trusted Rust LCF kernel prototype
```

These commits separate:

- T2 kernel hardening and checked instantiation;
- closed theorem acceptance and proof-statistics honesty;
- minimal burden-aware proof replay;
- project positioning and trust-model documentation.

## Verified Gate

The current strict-kernel gate is `scripts/dev-check.sh strict`, backed by
[check-strict-kernel.sh](../scripts/check-strict-kernel.sh).

This unified gate runs 7 steps: `cargo +stable fmt --check`, `cargo +stable check --locked`,
`bash scripts/check-kernel-firewall.sh`, and test suites covering kernel rewrite
soundness, kernel soundness, inline kernel unit tests, and legacy core compatibility.

Recorded baseline result (historical snapshot; use `scripts/dev-check.sh strict`
for current counts):

```text
cargo +stable fmt --check                        passed
cargo +stable check                              passed
bash scripts/check-kernel-firewall.sh            FIREWALL CLEAN
cargo test --test kernel_rewrite_soundness       134 passed
cargo test --test kernel_soundness                26 passed
cargo test --lib kernel::thm::                    11 passed
cargo test --lib kernel::unify::tests::           15 passed
cargo test --lib kernel::rules::tests::           54 passed
cargo test --lib core::                          199 passed
```

Previous ignored tests (Free/Const suffix, Var/Free index) are now
passing tests — the Strict Kernel Phase resolved them at the equality
boundary.

Strict Kernel Phase update: trusted kernel equality now uses
`Hyps::kernel_alpha_eq`, so the Free/Const and Var/Free tests are ordinary
passing tests. The old behavior remains only in `Hyps::compat_alpha_eq`.

## Current Trust Semantics

Use these distinctions consistently:

```text
is_fully_proved() == oracle-free
is_closed_proved() == oracle-free + no hypotheses + no unresolved tpairs
```

`ThmKernel::assume(A)` constructs:

```text
A |- A
```

It does not construct:

```text
|- A
```

Accepted unproved propositions must use:

```text
ThmKernel::admit(cterm, "admitted:specific_reason")
```

and preserve the oracle footprint through later inference.

## Current T4 Replay Scope

Independent replay currently supports:

```text
assume
reflexive
symmetric
transitive
implies_intr
implies_elim
```

`Thm::check_proof()` and `Thm::validate_proof()` replay theorem derivations and
compare:

```text
prop
hyps
tpairs
oracles
```

This is a minimal kernel derivation replay checker, not a full Isabelle
`proofterm.ML` implementation.

## Historical Dirty Files

The original trusted-kernel baseline intentionally did not include:

```text
Cargo.lock
isabelle-source
```

At the time the original baseline was recorded, their remaining local changes
were:

- `Cargo.lock`: patch-level dependency lockfile updates, later committed as
  `ae036f2 deps: update lockfile`;
- `isabelle-source`: upstream Isabelle submodule pointer movement.

Dependency and vendor changes must be either reverted by the owner or committed
separately with an explicit rationale. A lock-only refresh is not justified by
successful locked metadata alone. Do not mix either file into kernel, trust,
proofterm, parser, metric, or roadmap changes.

## Historical Next Entry Point — Completed

The checkpoint originally proposed:

```text
kernel_alpha_eq / compat_alpha_eq separation
CTerm::certify_checked
Thm invariant checker
strict kernel mode
```

Those boundaries are now implemented. The current next entry is immutable
`SignatureId` / `TheoryId` propagation followed by one context-bound theorem
acceptance API. Do not broaden HOL/Isar coverage or extend legacy replay instead
of closing that context boundary.
