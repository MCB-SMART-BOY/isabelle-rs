# Trusted Kernel Baseline

This document records the trusted-kernel checkpoint created before the Strict
Kernel Phase. It is a baseline for kernel-boundary work; it is not a claim of
full Isabelle compatibility.

This is a historical checkpoint. The completed strict-kernel work below is not
the current next phase; use [ROADMAP.md](ROADMAP.md) for the active
source-elaboration and authorized HOL-basis sequence.

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

This unified gate runs 7 numbered stages: `cargo +stable fmt --check`,
`cargo +stable check --locked`, `bash scripts/check-kernel-firewall.sh`, and
test suites covering kernel rewrite soundness, immutable context identity,
kernel soundness, inline kernel units, and legacy core compatibility.

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

Those boundaries, immutable context identity, and the exact-owner acceptance
gate are now implemented. The current next entry is a source-aware proposition
AST followed by checked declaration/type-scheme elaboration. Do not broaden
HOL/Isar coverage or extend legacy replay instead of closing that source
boundary.

## Broad-Suite Failure Baseline

These 14 tests fail identically on `origin/dev` (`38c5f14`), the pre-Change-B
working tree, and the post-Change-B working tree. They are pre-existing
limitations of the legacy parser, type environment, and proof-engine adapters,
not regressions introduced by the kernel acceptance or outcome work.

### Differential-regression policy

Do not fix these failures inline with kernel or source-AST changes. Record new
failures as:

```text
new failures = (current failure set) − (this baseline inventory)
```

A non-empty new-failure set on a change that does not intentionally modify
legacy parsing or proof dispatch is a regression. Report it before proceeding.

### Inventory

```text
hol::simpdata::tests::test_hol_basic_simp_rules_nonempty
hol::simpdata::tests::test_init_hol_simpset_works
isar::toplevel::tests::test_equality_sym
isar::toplevel::tests::test_equality_trans
isar::toplevel::tests::test_mp_modus_ponens
isar::toplevel::tests::test_toplevel_lifecycle
theory::loader::tests::test_accept_all_is_admitted_not_closed_verified
theory::loader::tests::test_full_theory
theory::loader::tests::test_induct_cases
theory::loader::tests::test_multiple_lemmas
theory::loader::tests::test_nested_show
theory::loader::tests::test_set_thy_style_lemma
theory::loader::tests::test_simple_lemma
theory::loader::tests::test_structured_proof
```

Verified 2026-07-19 against `HEAD` of local `dev`.
