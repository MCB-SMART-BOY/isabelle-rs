---
description: 测试与验证规则。基准, 回归清单, DB override, 调试技巧。
globs: "**/*.rs"
alwaysApply: false
version: 2.1
updated: 2026-05-28
---

# 测试规则

## 命令

```bash
cargo test --lib core::thm                                     # 内核单元 (12 tests, 快速)
cargo test --test bnf_tests                                    # BNF/datatype (4 tests)
cargo test --lib tptp                                          # TPTP export (3 tests)
cargo test --lib syntax::printer                               # Pretty Printer (11 tests)
cargo test                                                     # 全部 (373+ tests)
```

## 栈需求

| 测试 | 栈 |
|------|:--:|
| Core | 32MB |
| Beyond-core | 128MB |
| Full lib | 256MB |

## 回归检查清单 (每次内核/方法改动后)

```bash
cargo test --lib core::thm                                    # 1. 内核
cargo test --lib core::unify                                  # 2. 统一
cargo test test_verify_all_core_files -- --nocapture           # 3. 核心
RUST_MIN_STACK=134217728 cargo test test_verify_beyond_core --lib -- --nocapture  # 4. 扩展
cargo test test_load_1000_from_full_hol -- --nocapture         # 5. 加载
```

## 常见失败

| 症状 | 原因 | 修复 |
|------|------|------|
| `assertion failed: matches!(body, Term::App)` | `incr_bound` 被改坏 | Revert term.rs |
| Stack overflow < 128MB | 某函数仍递归 | 迭代化 |
| `verify_lemma` None | 方法名未识别 | 检查 dispatch |
| DB 0 theorems | `parse_lemmas` 静默失败 | 检查路径 |
| `bicompose` None | 规则不匹配 | 检查 unify |
