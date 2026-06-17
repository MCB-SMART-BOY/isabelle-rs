# 开发者指南 v3.0 (v1.96.0-dev)

## 环境要求

- Rust stable (edition 2024)
- cargo
- 推荐: 256MB+ stack (`RUST_MIN_STACK=268435456`)
- tmux (并行运行长时间测试)

## 构建与测试

## 构建与测试

```bash
# 构建
cargo build

# 运行测试 (注意栈需求)
RUST_MIN_STACK=268435456 cargo test --lib

# 内核测试 (快速, 32MB 栈足够)
cargo test --lib core::thm

# BNF/datatype 测试
cargo test --test bnf_tests

# TPTP 测试
cargo test --lib tptp

# 批量编译 HOL 理论文件
cargo run --bin isabelle-build -- --dir isabelle-source/src/HOL
```

## 项目结构 → 详见 [ARCHITECTURE.md](ARCHITECTURE.md)

## 核心架构 → 详见 [ARCHITECTURE.md](ARCHITECTURE.md) 和 [CLAUDE.md](../CLAUDE.md)

### 关键命令速查

```bash
# 内核测试 (快速, 32MB 栈足够)
cargo test --lib core::thm

# 核心验证
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files --lib -- --nocapture

# Tier2 验证
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture

# 批量编译 HOL
cargo run --bin isabelle-build -- --dir isabelle-source/src/HOL --stats

# BNF/datatype 测试
cargo test --test bnf_tests

# TPTP 测试
cargo test --lib tptp
```

## 项目统计

| 指标 | 数值 |
|------|------|
| Rust 代码 | ~46,000 行 (121 .rs) |
| 测试 | 694+ |
| .thy 文件 (可用) | 1,473 |
| 核心验证 | 5/5 files 125/125 (100%) |
| Tier2 | 20 files (accept_all) |
| 定理总数 (DB) | 42,000+ |
| 警告 (cargo check --lib) | 0 |
| 证明方法 | 27 (含 Meson) |
