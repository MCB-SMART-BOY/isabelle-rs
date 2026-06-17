---
name: bench
description: Run performance benchmarks and test matrix
category: meta
---
# /bench

运行完整测试矩阵。SOF 在 `.claude/skills/bench.md`。

```bash
cargo test --lib core::thm core::unify tools::metis
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture
```

期望: Core 125/125, Tier2 97/97 3821/3821.
