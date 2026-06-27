# Trusted Kernel Baseline

This document records the current trusted-kernel checkpoint. It is a baseline
for future T4 replay expansion and parser/type-boundary work; it is not a claim
of full Isabelle compatibility.

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

The current trusted-kernel gate is:

```bash
cargo fmt --check
cargo check
cargo test --test kernel_soundness
cargo test core::proofterm::tests::
cargo test core::thm::tests::
cargo test --lib core::
```

Latest baseline result:

```text
cargo fmt --check                      passed
cargo check                            passed
cargo test --test kernel_soundness      13 passed
cargo test core::proofterm::tests::     13 passed
cargo test core::thm::tests::           31 passed, 2 ignored
cargo test --lib core::                 186 passed, 2 ignored
```

The two ignored tests are intentional regression markers for known T2 debts:

```text
Free / Const suffix matching
Var / Free index confusion
```

They belong to the parser/type/certification boundary and must not be hidden by
claiming T2 is complete.

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

## Remaining Dirty Files

The trusted-kernel baseline intentionally does not include:

```text
Cargo.lock
isabelle-source
```

At the time this baseline was recorded, their remaining local changes were:

- `Cargo.lock`: patch-level dependency lockfile updates;
- `isabelle-source`: upstream Isabelle submodule pointer movement.

They should be either reverted by the owner or committed separately with
specific messages such as:

```text
deps: update dependency lockfile
vendor: update Isabelle source submodule
```

Do not mix either file into kernel, trust, proofterm, or roadmap changes.

## Next Entry Point

The next code phase is T4 replay batch 1:

```text
beta_conversion
forall_intr
forall_elim
```

Do not start the next phase by broadening HOL/Isar coverage, adding LSP UI,
touching WASM runtime, or chasing more `.thy` files. The next proof work should
add replay constructors, replay checks, positive tests, attack tests, tamper
tests, and documentation for those three primitive rules only.
