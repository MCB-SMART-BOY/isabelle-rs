---
name: verify-all
description: Run the full verification test suite with appropriate stack size
category: verification
---

# /verify-all

Run the complete isabelle-rs verification pipeline.

## Quick

```bash
cargo test --lib core::thm core::unify tools::metis
```

## Full

```bash
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture
```

## Extended

```bash
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture
RUST_MIN_STACK=268435456 cargo test --test tier3_verify -- --nocapture
```

## All Integration

```bash
RUST_MIN_STACK=268435456 cargo test --test bnf_tests --test comprehensive --test integration_tests
```

## Expected Results (v1.7.0)

| Suite | Expected |
|-------|----------|
| Kernel tests | All pass |
| Metis tests | 22 pass |
| Core verification | HOL/Orderings/Set/Nat: 100%. List: overflow (known) |
| Tier 2/3 | Parse OK (accept_all mode) |
