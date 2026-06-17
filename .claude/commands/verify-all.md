---
name: verify-all
description: Run the full verification test suite with appropriate stack size
category: verification
---
# /verify-all

完整验证流水线。详见 `.claude/skills/verify.md` + `.claude/skills/bench.md`。

```bash
cargo test --lib core::thm core::unify tools::metis
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture
tmux new-session -d -s tier2 "RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture 2>&1; exec bash"
cargo test --test bnf_tests --test integration_tests
```

期望: Core 125/125, Tier2 97/97 3821/3821, 700+ tests.
