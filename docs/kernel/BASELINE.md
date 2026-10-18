# Trusted Kernel Baseline

This document records the trusted-kernel checkpoint created before the Strict
Kernel Phase. It is a baseline for kernel-boundary work; it is not a claim of
full Isabelle compatibility.

This is a historical checkpoint. The completed strict-kernel work below is not
the current next phase; use [ROADMAP.md](../status/ROADMAP.md) and the
[current delivery state](../status/PROJECT_STATUS.md#current-delivery-state)
for active work.

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

## Verification Guidance Versus Baseline

For current work, `cargo +stable xtask verify` is the deterministic repository
gate; the independent global workstation/security gate is
`~/.omp/agent/validate.sh`, not a step implied by `verify`.
`cargo +stable xtask strict` remains the focused kernel diagnostic;
`cargo +stable xtask core` remains the focused sampler;
`cargo +stable xtask selftest` runs product-independent automation tests;
`cargo +stable xtask test` runs complete workspace tests.
See [engineering workflow](../guides/DEVELOPMENT.md#engineering-workflow)
and the [current delivery state](../status/PROJECT_STATUS.md#current-delivery-state).
Neither this baseline nor the historical sample proves native P2/P3/P4
compatibility; implementation has resumed, but complete acceptance has not
been established. The current `strict` implementation is in
[xtask](../../xtask/src/tasks.rs); the following commands/counts are historical,
not output of `xtask`. The recorded `scripts/check-kernel-firewall.sh` entry
was removed in the xtask cutover; the current firewall check is part of
`cargo +stable xtask strict` and `cargo +stable xtask verify`.

Recorded baseline result (historical commands and counts, **not** results of
`cargo +stable xtask strict`):
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

## Historical Legacy Trust Semantics

These predicates describe `src/core::Thm`, not the accepted theorem from
`crates/kernel` re-exported through `src/kernel`. At this checkpoint:

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

Historically, legacy `src/core::ThmKernel` represented unproved propositions
through:

```text
ThmKernel::admit(cterm, "admitted:specific_reason")
```

It preserves the oracle footprint through inference. This is **not** accepted
`crates/kernel::TrustedTheorem` authority.

## Legacy T4 Replay Scope

Independent legacy `src/core/proofterm.rs` replay supports:

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

Those boundaries, immutable context identity, exact-owner acceptance, strict
type-constructor/arity validation, installed axiom-schema checks, conservative
definition replay, and the two narrow source-backed fixtures are now implemented.
An audited sampled `HOL::TrueI` projection also reaches exact-owner acceptance
(`KernelTrustedClosed: 1/125`); neither fixture counts in the sampled 125.
This does not authorize whole-theory HOL compilation, broad HOL/Isar coverage,
or more legacy trusted power.

## Broad-Suite Failure Baseline

The tests below were recorded as ignored at this historical checkpoint,
reflecting legacy parser/type/proof limitations rather than regressions in
kernel acceptance. This is not an inventory of present ignored tests: several
loader paths have since changed contracts or been removed. At that checkpoint,
CI ran ignored tests only as an advisory gate with
`continue-on-error: true`; consult current scripts for present CI behavior.

| Test | Reason |
|------|--------|
| `hol::simpdata::test_hol_basic_simp_rules_nonempty` | `simpdata initialization incomplete` |
| `hol::simpdata::test_init_hol_simpset_works` | `simpdata initialization incomplete` |
| `isar::toplevel::test_equality_sym` | `toplevel proof engine gap` |
| `isar::toplevel::test_equality_trans` | `toplevel proof engine gap` |
| `isar::toplevel::test_mp_modus_ponens` | `toplevel proof engine gap` |
| `isar::toplevel::test_toplevel_lifecycle` | `toplevel proof engine gap` |
| `theory::loader::test_accept_all_is_admitted_not_closed_verified` | `theory loader batch compatibility` |
| `theory::loader::test_full_theory` | `theory loader batch compatibility` |
| `theory::loader::test_induct_cases` | `theory loader batch compatibility` |
| `theory::loader::test_multiple_lemmas` | `theory loader batch compatibility` |
| `theory::loader::test_nested_show` | `theory loader batch compatibility` |
| `theory::loader::test_set_thy_style_lemma` | `theory loader batch compatibility` |
| `theory::loader::test_simple_lemma` | `theory loader batch compatibility` |
| `theory::loader::test_structured_proof` | `theory loader batch compatibility` |
| `integration_tests::test_theory_processor_pipeline` | `proof-context certification gap` |

## Post-Commit All-Targets Audit

On 2026-07-19, `cargo +stable check --locked` and
`scripts/check-strict-kernel.sh` passed independently at baseline `38c5f14`
(then `origin/dev`) and candidate commits `502acd2`, `3c72167`, `929d04e`,
`6840533`, and `6336271`.

`scripts/check-strict-kernel.sh` was an old entry point and was removed in the
xtask cutover; for present checks use `cargo +stable xtask strict` or the
complete repository gate `cargo +stable xtask verify`. The recorded historical
results above are not results of either current command.

`cargo +stable check --locked --all-targets` failed identically at all six
points with four errors in `benches/kernel_benchmarks.rs`:

```text
E0603: proofterm::check_proof is private (two calls)
E0308: implies_intr/implies_elim receive &Result<Thm> (two calls)
```

This proves the benchmark failure predates the candidate series; it does not
make the all-targets gate pass. Keep this debt separate from kernel acceptance,

As of 2026-07-19 (commit `878d8ae`), the two issues were fixed:
`ThmKernel::assume` now unwraps before `implies_intr`/`implies_elim`, and
`pub(crate)` `proofterm::check_proof` calls were replaced with the public
`replay_proof`. `--all-targets` now passes.
