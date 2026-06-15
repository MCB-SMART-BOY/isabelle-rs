---
description: Isabelle-rs 项目总纲。Phase 48: Metis + Transfer/Lifting 完成。130 files, 670+ tests, ~48K LOC。
globs: "**/*.rs"
alwaysApply: true
version: 6.0
updated: 2026-06-03
---

# Isabelle-rs 项目规则

Rust 重写 Isabelle 证明助手内核。LCF 可信内核 + 高阶统一 + Isar 证明语言 + 理论加载 pipeline。

## 铁律

1. **`Thm` 只能在 `src/core/thm.rs` 内直接构造** — 外部必须用 `ThmKernel`
2. **禁止 `Typ::dummy()` 进入内核推理规则** — 用 `CTerm::term_type()` 或 `Pure::dest_equals_with_type()`
3. **证明方法第一步必须调 `apply_safe_rules`** — O(log n) net lookup, 匹配优先→resolution fallback
4. **规则查找用 net** — `db.intro_net().lookup()` 不是 `db.intros`
5. **深层递归必须迭代化** — 参考 `.claude/rules/iterative.md`
6. **改内核/方法后跑全量基准** — `RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture`
7. **新加数据字段必须更新所有构造器** — 特别是 `ParsedLemma`, `ProofState`, `HolTheoremDb`
8. **Isar 证明状态机三模式**: Forward (配置), Chain (链式), Backward (证明中)
9. **理论加载用 `TheoryProcessor`** — 解析 .thy → 命令分发 → LocalTheory → finalize
10. **`show` 必须记录 `refines`** — 用于 `qed` 时父目标精化
11. **定理构造用 `CTerm::certify_annotated`** — 自动从 TypeEnv 标注类型

## 状态

| 指标 | 值 |
|------|-----|
| 内核 | 15 ops + tpairs/shyps, 100% Isabelle 等价, 0 Typ::dummy() fallback |
| 证明引擎 | Isar state machine (3 modes) + 25 proof methods |
| 经典推理器 | best/depth/dup_step + 三阶段 safe rules |
| 算术求解 | Fourier-Motzkin 变量消去 (nat/int 线性算术) |
| HOL 简化器 | 条件重写 + solver 插件 (ArithSolver, AsmSolver) |
| BNF Lfp/Gfp | 完整: induction/coinduction/fold/rec/unfold/corec + map/set/rel/pred |
| Ctr_Sugar | case/disc/sel/split/cong/nchotomy/size 定理生成 |
| Meson | 模型消除证明器 — 一等证明方法 |
| Transfer/Lifting | 传输规则生成 + rel_fun/rel_set + 商类型定理 |
| 属性系统 | 完整 parse→classify→DB→apply_attributes 流水线 |
| 方法组合子 | THEN/ORELSE/REPEAT (参考 Isabelle) |
| 模块 | core (31), isar (18), hol (18), theory (8) + tools (6) + server/lsp/session/syntax/wasm (27) |
| Isar 命令 | 30+ 种 (完整覆盖) |
| 理论命令 | locale/class/instance/interpretation/typedef/record/datatype/fun/inductive |
| 语法 | Pretty printer (20+ operators) + thy_header parser |
| LSP | 8 handlers |
| 代码 | ~46K Rust LOC, 121 files |
| 测试 | 694+ |
| 验证 | Core 4/5 文件 100%, Tier2 3/20 文件 100% |
| 路线图 | Phase 0-53 完成 |

## 已知问题

| 问题 | 严重度 |
|------|:--:|
| test_batch_scan_theories 256MB 栈溢出 | 🔴 高 |
| test_verify_all_core_files 默认栈溢出 | 🔴 高 |
| test_batch_verify_all 1GB 栈溢出 | 🔴 高 |

## 架构

```
.thy → OuterSyntax::parse_spans() → CommandSpan[]
  → TheoryProcessor::process_span()
    ├─ theory → parse_header() → LocalTheory::begin()
    ├─ lemma  → IsarProof::lemma() (enter proof mode)
    ├─ proof  → open_block() (enter structured proof)
    ├─ have/show → enter sub-goal (Backward mode)
    ├─ fix/assume → local context
    ├─ apply/by → method dispatch → ThmKernel
    ├─ qed     → goal refinement (show matches parent)
    └─ end     → LocalTheory::finalize() → Arc<Theory>
  → SessionBuilder::build_session()
    ├─ TheoryGraph 扫描 + 拓扑排序
    ├─ 批量编译 .thy 文件
    └─ 统计报告
```

## 规则索引

### 域规则 (Domain Rules)

| 触发条件 | 文件 |
|---------|------|
| 修改 `src/core/thm.rs` / `logic.rs` / `drule.rs` | [kernel.md](kernel.md) |
| 修改 `src/isar/method.rs` | [proof-methods.md](proof-methods.md) |
| 修改 `src/isar/proof.rs` | [isar.md](isar.md) |
| 修改 `src/theory/thy_header.rs` | [theory-loading.md](theory-loading.md) |
| 修改 `src/tools/simp.rs` | [proof-methods.md](proof-methods.md) |
| 修改 `src/isar/linarith.rs` | [proof-methods.md](proof-methods.md) |
| 栈溢出 | [iterative.md](iterative.md) |
| 性能优化 | [performance.md](performance.md) |
| 修改类型系统 | [type-system.md](type-system.md) |
| 写测试/调试 | [testing.md](testing.md) |

### 工程规则 (Engineering Rules)

| 触发条件 | 文件 |
|---------|------|
| 错误处理 / Result / panic | [error-handling.md](error-handling.md) |
| 设计 pub API / trait / 可见性 | [api-design.md](api-design.md) |
| 使用 Arc/Mutex/OnceLock/thread_local! | [concurrency.md](concurrency.md) |
| 代码风格 / clippy / rustfmt / unsafe 审计 | [code-quality.md](code-quality.md) |
| 新版发布 / semver / changelog | [release.md](release.md) |
| 重构 (≥3 files) / 代码异味 | [refactoring.md](refactoring.md) |
| 使用 unsafe / 添加依赖 / 外部输入 | [security.md](security.md) |
| 添加文档 / rustdoc / ADR | [documentation.md](documentation.md) |
| CI/CD / GitHub Actions / 自动化 | [ci-cd.md](ci-cd.md) |
| 属性测试 / proptest / 不变量 | [property-testing.md](property-testing.md) |
| 每个 Phase 完成后的流程 | [phase-sop.md](phase-sop.md) |
