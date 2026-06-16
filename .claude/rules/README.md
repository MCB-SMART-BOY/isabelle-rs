---
description: Isabelle-rs — Rust 重写 Isabelle，程序员友好的证明助手。v1.9.0-dev, Route A 稳定性优先。
globs: "**/*.rs"
alwaysApply: true
version: 9.0
updated: 2026-06-16
---

# Isabelle-rs 项目规则

## 项目愿景

**用 Rust 重写 Isabelle，打造更程序员友好的证明助手。**

功能与 Isabelle/ML 保持一致，但：
- **错误信息** → Rust 编译器风格：错误码 + 源代码定位 + `= help:` 建议
- **工具链** → `cargo build` / `cargo test` / `cargo clippy`，标准 Rust 生态
- **代码风格** → 现代 Rust 惯用法，零 `unsafe`（除必要的 FFI）
- **类型安全** → 编译期捕获尽可能多的错误，而非运行时 panic

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
12. **提交信息用中文，不含 Co-Authored-By** — 全部由 MCB-SMART-BOY 提交，禁止 AI 署名
13. **每次对话结束后必须更新 .claude/** — 状态、已知问题、路线图必须反映最新代码状态。用户不应需要重复强调偏好
14. **先修 bug，后加功能** — Route A 稳定性优先：测试→OOM→Tier2→属性→文档
15. **错误信息用 Rust 风格** — 每次新增/修改错误必须包含：错误码 (E0xxx)、`= help:` 建议、源代码位置。参考 `rustc` 的报错格式

## 当前策略：Route A — 稳定性优先

```
1. ✅ 修复 5 个失败测试 (ctr_sugar, primrec, fleche, rule_lookup, set_thy)
2. ✅ 定位 + 修复 OOM 根因 (repeat_conv 定点检测 + stack优化)
3. 🔄 Tier2 验证扩展 (6/20 → 6 files 100% running, expected 15+/19)
4. ✅ 属性系统补完 (attrib.rs → hol_loader.rs 集成: begin_lemma + lemmas + declare + attrs存储)
5. 🔄 全线文档同步 (当前进行中)
```

## 状态

| 指标 | 值 |
|------|-----|
| 内核 | 15 ops + tpairs/shyps, 100% Isabelle 等价, 0 Typ::dummy() fallback |
| 证明引擎 | Isar state machine (3 modes) + 27 proof methods |
| 经典推理器 | best/depth/dup_step + 三阶段 safe rules |
| 算术求解 | Fourier-Motzkin 变量消去 (nat/int 线性算术) |
| HOL 简化器 | 条件重写 + solver 插件 (ArithSolver, AsmSolver) |
| hologic | HOL 抽象语法层, 40+ mk_*/dest_*/is_* 函数, 100% HOL const 调用归口 |
| simpdata | HOL simpset 初始化, 28 内置规则, init_hol_simpset() |
| args | MethodArgs 解析, parse_modifiers() 接入 exec_simp + exec_induct |
| spec | Definition/Axiomatization/Abbreviation/TypeAbbrev/Typedecl 解析器集成 |
| defs | 定义一致性检查: 循环检测 + 类型参数验证 |
| BNF Lfp/Gfp | 完整: induction/coinduction/fold/rec/unfold/corec + map/set/rel/pred |
| Ctr_Sugar | case/disc/sel/split/cong/nchotomy/size 定理生成 |
| Meson | Model elimination prover — 1st-class proof method |
| Transfer/Lifting | Transfer rule generation + rel_fun/rel_set + quotient type theorems |
| 属性系统 | ✅ class assumes + attrs_index + lemmas + declare (Route A 完整) |
| 核心 simpset | ✅ 8 基础理论 (HOL→Groups→Rings), OnceLock 缓存 |
| 内存限界 | ✅ PROOF_SEARCH_BUDGET + 深度分支剪枝 |
| VERIFY_DEADLINE | ✅ 7 检查点全覆盖 |
| 模块 | core (33), isar (19), hol (22), theory (8) + tools (7) + server/lsp/session/syntax (30) |
| Isar 命令 | 30+ 种 |
| 理论命令 | locale/class/instance/interpretation/typedef/record/datatype/fun/inductive |
| 代码 | ~54K Rust LOC, 124 files |
| 测试 | 700+ (638 lib + 76 integration) |
| 验证 | **Core 5/5 files 125/125 (100%), Tier2 36/36 files 2959/2959 (100%)** |
| 速度 | Tier2 513s (8.5 min); Rings 14s (曾 56s, 4x 加速) |
| 路线图 | v1.9.0 发布, Route A 完成, Phase 3 完成 |

## 已知问题

| 问题 | 严重度 | 详情 |
|------|:--:|------|
| Fields/Num — 结构化 Isar 证明回放 | 🟡 中 | 205 lemmas × multi-step proofs, Isar 引擎瓶颈 (非数据流) |
| Hilbert_Choice/Transitive_Closure — auto/blast 密集 | 🟡 中 | 内存预算保护但极慢 |
| Finite_Set — 大文件 | 🟡 中 | 281 lemmas, 372 simp, 3h+ |
| Partial_Function — 内存爆炸 | 🟡 中 | 25GB+ OOM |
| HolTheoremDb LazyLock 初始化 | 🟡 中 | 首次 `get()` 加载全部 1,473 .thy files |
| hologic 常量残留 (3 处) | 🟢 低 | 有意保留 |

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
    ├─ TheoryGraph scan + topological sort
    ├─ Batch compile .thy files
    └─ Statistics report
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
| 每个 Phase/任务完成后的流程 | [phase-sop.md](phase-sop.md) |
| **下一步计划 (v1.9.0-dev → v1.9.0)** | [next-phase.md](next-phase.md) |
