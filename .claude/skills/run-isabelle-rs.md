---
name: run-isabelle-rs
description: Build, run, test, or verify isabelle-rs
category: development
triggers: [run isabelle, build project, run demo, compile .thy, test change, verify kernel]
---
# Run Isabelle-rs

Build, run, test, and verify the isabelle-rs proof assistant.

## 常用命令

```bash
# 构建
cargo build

# 严格内核攻击测试 (最快, 32MB 栈)
cargo test --test kernel_rewrite_soundness

# 所有测试 (需要 256MB 栈)
RUST_MIN_STACK=268435456 cargo test --lib

# 内核测试 (快速, 32MB 栈)
cargo test --lib core::thm
cargo test --test kernel_soundness

# 核心验证
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture

# Tier2 扩展验证 (建议用 tmux)
tmux new-session -d -s tier2 "RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture 2>&1; exec bash"
tmux attach -t tier2

# 代码质量
cargo clippy -- -D warnings
cargo fmt -- --check
```

## 栈需求
| 测试 | 栈 |
|------|:--:|
| kernel_rewrite_soundness | 32MB |
| Core kernel | 32MB |
| Full lib | 256MB |
| Core verification | 256MB |
| Tier2 verification | 256MB |

## 已知问题
- Hilbert_Choice/Transitive_Closure: 超时 (需更深迭代化)
- Fields/Num/Finite_Set: 结构化证明重放开销
- Partial_Function: 内存爆炸 (深层 fixpoint)
