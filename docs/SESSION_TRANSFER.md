# isabelle-rs v1.9.0 项目状态

> 当前会话：2026-06-16 | 状态：v1.9.0 发布，Route A + Phase 3 完成

---

## 一、项目概况

isabelle-rs v1.9.0 — Isabelle 证明助手内核的 Rust 移植。
- LCF 可信内核 (15 ops + tpairs/shyps) + 高阶合一 + Isar 证明语言
- ~54K Rust LOC, 124 files, 700+ tests
- Core 5/5 files 125/125 (100%), Tier2 9+/23 files 100%
- 核心 simpset 注入机制（Phase 3.1）
- 内存限界证明搜索（Phase 3.2）

## 二、v1.9.0 新特性

| 特性 | 描述 |
|------|------|
| class assumes 解析 | 类假设（如 divide_inverse）自动进入 by_name |
| attrs_index 反向索引 | field_simps 等 named_theorems 自动展开 |
| 核心 simpset | 6 个基础理论的 [simp] 规则注入（OnceLock 缓存） |
| 内存限界搜索 | PROOF_SEARCH_BUDGET + 深度分支剪枝 |
| VERIFY_DEADLINE | 7 检查点全覆盖 |
| rewrite 深度上限 | MAX_REWRITE_DEPTH=40 |

## 三、已知瓶颈

| 问题 | 状态 |
|------|:--:|
| Fields/Num — 跨文件 named_theorems (algebra_simps 等) | 🟡 待父理论加载 |
| Hilbert_Choice/Transitive_Closure — auto/blast 密集 | 🟡 内存预算保护但慢 |
| Finite_Set — 372 simp 调用 | 🟡 处理极慢 |
| HolTheoremDb LazyLock 首次加载 | 🟡 待优化 |

## 五、常用命令

```bash
# 构建
cargo check --lib

# tier2 验证 (tmux)
tmux new-session -d -s tier2 "RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture 2>&1"
tmux attach -t tier2  # 查看进度

# 核心验证
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files --lib -- --nocapture

# 所有测试
RUST_MIN_STACK=268435456 cargo test --lib
```

## 六、提交规则

- 中文提交信息
- 不含 Co-Authored-By
- Git user: MCB-SMART-BOY
