---
description: Isabelle-rs 项目总索引 — 状态、铁律、规则索引。每次对话必加载。
globs: "**/*.rs"
alwaysApply: true
version: 2.3
---
# Isabelle-rs 项目规则

> **Rust-native Isabelle/Pure-inspired strict LCF kernel research prototype.**
> 当前主线是 `src/kernel` 新 TCB + legacy quarantine，不是完整 Isabelle 替代品。

## 项目状态 (v2.3.0)

| 指标 | 值 |
|------|-----|
| 新 TCB | `src/kernel/` strict nucleus; no dummy, no compat, no fallback theorem construction |
| legacy 边界 | `src/core` / Isar / HOL / tools 进入 quarantine, 只通过 adapter 迁移 |
| strict kernel rules | all 15 primitives (assume, reflexive, symmetric, transitive, combination, abstraction, beta_conversion, implies_intr, implies_elim, forall_intr, forall_elim, equal_intr, equal_elim, generalize, instantiate) + `resolve1_match` prototype |
| 信任模型 | `TrustedTheory` 只接收 `TrustedTheorem`; `SearchFactDb` 不能提升为 trusted |
| 证明状态 | `ProofObligation` 与 theorem 分离; `assume(A)` 是 open theorem `A |- A` |
| 测试 gate | `bash scripts/check-strict-kernel.sh` (fmt + check + firewall + 124 attack + 26 soundness + 56 kernel inline + 199 core) |
| 战略 | 先完成 strict kernel 与 replay，再做 workspace/session/agent；不追 HOL/AFP 覆盖率 |

## 铁律 (15)

1. **`Thm`/`KernelThm` 只能在 `src/kernel/thm.rs` / `src/core/thm.rs` 内构造** — 外部用 `KernelRules` (strict) 或 `ThmKernel` (legacy)
2. **禁止 `Typ::dummy()` 进入内核推理规则**
3. **证明方法第一步必须调 `apply_safe_rules`**
4. **规则查找用 net** — `db.intro_net().lookup()` 非 `db.intros`
5. **深层递归必须迭代化** — 见 `iterative.md`
6. **改内核/方法后跑全量基准** — `test_verify_all_core_files`
7. **新加数据字段必须更新所有构造器**
8. **Isar 状态机三模式**: Forward → Chain → Backward
9. **`show` 必须记录 `refines`** — 用于 `qed` 父目标精化
10. **定理构造用 `CTerm::certify_annotated`** — 自动标注类型
11. **提交信息用中文，不含 `Co-Authored-By`**
12. **`prove_condition` 禁止调用 `self.rewrite()`** — 防止无限递归
13. **每次 src/ 变更后同步文档** — 运行 `/sync-docs`
14. **每次任务完成后审计变更** — `/audit-kernel` + `/verify` + `cargo check`
15. **每次对话结束更新 .claude/** — `CLAUDE.md` + 本文件

## 已知问题

| 问题 | 严重度 | 详情 |
|------|:--:|------|
| Fields/Num — 结构化 Isar 证明回放 | 🟡 中 | 205 lemmas × multi-step, 需 IsarProof Arc 全路径优化 |
| Hilbert_Choice/TC — auto 密集 | 🟡 中 | 56+40 auto, 需更深迭代化 |
| Finite_Set — 大文件 | 🟡 中 | 281 lemmas, 372 simp, 3h+ |
| Partial_Function — 内存爆炸 | 🟡 中 | 深层 fixpoint, 25GB+ |
| 4 Library files — 解析挂死 | 🟡 中 | Product_Order/Quotient_List/Sorted_Less/State_Monad |
| Metis skolemization 缺失 | 🟡 中 | CNF 缺 ∃-斯科伦化 |
| HolTheoremDb 惰性初始化慢 | 🟡 中 | 首次加载 1,473 .thy files |

## 架构

```
.thy → OuterSyntax::parse_spans() → CommandSpan[]
  → TheoryProcessor::process_span()
    ├─ theory → parse_header() → LocalTheory::begin()
    ├─ lemma  → IsarProof::lemma()
    ├─ proof  → open_block() (Arc<IsarContext>)
    ├─ apply/by → method dispatch → ThmKernel
    └─ qed     → goal refinement → close_block
```

## 规则索引

### 域规则 (globs 触发)
| 规则 | 触发文件 | 内容 |
|------|---------|------|
| [kernel](kernel.md) | `core/thm.rs, logic.rs, drule.rs` | LCF 内核 15 操作, Thm 字段, CTerm |
| [proof-methods](proof-methods.md) | `isar/method.rs` | 22+ 方法, 六层 fallback, safe rules |
| [isar](isar.md) | `isar/proof.rs, proof_context.rs` | Isar 三模式状态机 |
| [theory-loading](theory-loading.md) | `hol/hol_loader.rs, theory/loader.rs` | .thy 解析, DB, DAG |
| [type-system](type-system.md) | `core/types.rs, sign.rs` | TypeEnv, CTerm, Sort |
| [iterative](iterative.md) | `**/*.rs` | 4 种迭代化模式 |
| [performance](performance.md) | `core/net.rs, isar/method.rs` | Nets, OnceLock, 优化历史 |

### 工程规则 (globs 触发)
| 规则 | 触发文件 | 内容 |
|------|---------|------|
| [error-handling](error-handling.md) | `**/*.rs` | thiserror, Result, 错误分层 |
| [api-design](api-design.md) | `core/thm.rs, isar/method.rs` | Semver, trait, 可见性 |
| [concurrency](concurrency.md) | `core/net.rs, hol/hol_loader.rs` | Arc, OnceLock, thread_local! |
| [code-quality](code-quality.md) | `**/*.rs` | Clippy, 命名, 注释, 文档 |
| [testing](testing.md) | `**/*.rs` | 测试命令, 栈需求, 回归清单 |
| [release](release.md) | `Cargo.toml, docs/**` | 发布流程, CHANGELOG |
| [refactoring](refactoring.md) | `**/*.rs` | 提取函数/模块, 代码异味 |
| [security](security.md) | `**/*.rs` | Unsafe, 依赖, 输入验证 |

### 工作流入口 (skills + commands)
| 入口 | 类型 | 用途 |
|------|------|------|
| `/audit` | command → `audit-kernel` skill | 内核安全快速扫描 |
| `/bench` | command → `bench` skill | 性能基准测试 |
| `/verify-all` | command → `verify` + `bench` | 完整验证套件 |
| `/fix` | command (self-contained) | 自动修复 clippy/fmt |
| `sync-docs` | skill | 文档同步 |
| `release` | skill | 发布流程 |
