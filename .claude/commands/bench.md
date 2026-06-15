---
name: bench
description: Run performance benchmarks and test matrix
category: meta
---

# /bench

Run the isabelle-rs test and benchmark suite.

## Fast Smoke Test

```bash
cargo test --lib core::thm
cargo test --lib core::unify
cargo test --lib tools::metis
cargo test --lib hol::hol_loader::lemma_tests
```

## Full Test Matrix

```bash
# Tier 1 (32MB)
cargo test --lib core::thm core::unify tools::metis

# Tier 2 (256MB)
RUST_MIN_STACK=268435456 cargo test --lib

# Tier 3 — Verification (KNOWN: List overflows)
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture
RUST_MIN_STACK=268435456 cargo test --test tier3_verify -- --nocapture
```

## Stack Requirements

| Suite | Minimum |
|-------|:-------:|
| Kernel | 32MB |
| Metis | 32MB |
| Full lib | 256MB |
| Verification | 256MB+ |
