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
# Tier2: 19 HOL theories, use tmux for long runs
tmux new-session -d -s tier2 "RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture 2>&1"
tmux attach -t tier2  # check progress
```

## All Integration

```bash
RUST_MIN_STACK=268435456 cargo test --test bnf_tests --test comprehensive --test integration_tests
```

## Expected Results (v1.9.0-dev)

| Suite | Expected |
|-------|----------|
| Kernel tests | All pass |
| Core verification | 5/5 files 125/125 (100%) |
| Tier2 | 6+/19 files 100% (Fun→Rings ✅, Fields arithmetic bottleneck) |
| Theory tests | 77 pass, 1 skip (ctr_sugar pre-existing) |
| lib tests | 710+ pass |
| cargo check --lib | 0 warnings |
