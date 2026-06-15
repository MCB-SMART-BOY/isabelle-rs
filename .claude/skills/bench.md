---
name: bench
description: Run the complete test matrix at correct stack sizes. Check suite pass/fail status and identify regressions.
category: meta
version: 2.0.0
triggers: [benchmark, performance, test all, regression test]
permissions: [Bash:cargo test, Bash:RUST_MIN_STACK]
---

# Bench

Run the complete test matrix to check for regressions and performance issues.

## Test Matrix

```bash
# Tier 1: Fast kernel tests (32MB stack)
cargo test --lib core::thm
cargo test --lib core::unify
cargo test --lib tools::metis
cargo test --lib hol::hol_loader::lemma_tests

# Tier 2: Medium tests (256MB stack)
RUST_MIN_STACK=268435456 cargo test --lib

# Tier 3: Verification (256MB stack, KNOWN OVERFLOWS)
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture
RUST_MIN_STACK=268435456 cargo test --test tier3_verify -- --nocapture

# Tier 4: Integration tests
cargo test --test bnf_tests
cargo test --test comprehensive
cargo test --test integration_tests
cargo test --test proptest
```

## Expected Results (v1.9.0-dev)

| Suite | Expected | Notes |
|-------|----------|-------|
| `core::thm` | 12 pass | LCF kernel |
| `core::unify` | All pass | Higher-order unification |
| `cargo check --lib` | **0 warnings** | Required per SOP |
| `test_verify_all_core_files` | **5/5 files, 125/125 (100%)** | Core verification |
| `theory` module | 77 pass, 1 skip | ctr_sugar pre-existing |
| `method` module | 28 pass, 1 skip | batch_verify_all |
| `tier2_verify` | **6+/19 files 100%** | Fields.thy arithmetic bottleneck |
| `--lib` full | 710+ pass | 0 warnings |

## Quick Sanity Check

After any change, run at minimum:
```bash
cargo test --lib core::thm core::unify tools::metis
cargo test --lib hol::hol_loader::lemma_tests
cargo test --lib isar::method
```

## Known Performance Baselines

| Metric | Value |
|--------|-------|
| Kernel ops | 179ns–12μs (release, criterion) |
| Core test suite | ~4.1s (release mode) |
| Speedup from v0.4.0 | 24× |
| Stack overflow threshold | 3 tests overflow at 1GB |

## Stack Requirements

| Suite | Minimum | Safe |
|-------|:-------:|:----:|
| Kernel tests | 32MB | 64MB |
| Unify/Metis tests | 32MB | 64MB |
| Lemma tests | 32MB | 64MB |
| Full lib | 256MB | 512MB |
| Core verification | 256MB | 512MB |
| Batch scan | 256MB+ | **OVERFLOWS** |

## Related

- `.claude/skills/verify.md` — Verification-specific debugging
- `.claude/skills/debug-overflow.md` — Stack overflow fixes
- `.claude/rules/testing.md` — Full test rules
- `.claude/rules/performance.md` — Optimization patterns
