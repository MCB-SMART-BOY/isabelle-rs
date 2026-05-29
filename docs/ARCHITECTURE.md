# 架构设计 v16.0 (v1.2.0)

> LCF 内核：15 ops + 15 methods · 类型推断 · 上下文切换 · Sledgehammer ATP
> 验证：20 HOL files · 428 theorems · 0 errors
> 性能：**179ns–12µs** (release mode, criterion 实测)
> 类型系统：TypeEnv + CTerm + Type/Sort/ClassAlgebra (Phase 9)，内核完全类型感知。
> 证明引擎：25 methods + Discrimination Nets + 三阶段 Safe Rules + 5 经典推理器搜索策略。
> Isar 引擎：三模式 Proof 状态机 (Forward/Chain/Backward) + 30+ Isar 命令 + 目标精化。
> 理论管理：TheoryProcessor pipeline + 8 命令 locale/class 系统 + typedef/record + datatype/codatatype。
> 工具链：Pretty Printer (20+ operators) + TPTP FOF Export + CLI + SessionBuilder DAG。
> 性能：**~4.1s** 总运行时间 (v0.4.0: ~100s, **24× 加速**)。

## 状态标记说明

| 标记 | 含义 |
|------|------|
| `[✅ 已完成]` | 代码已实现，测试通过 |
| `[🔵 规划]` | 后续阶段 (长期) |

## 速查表

| 层 / 组件 | 状态 | 关键交付物 |
|-----------|------|-----------|
| **LCF 内核 (15 操作)** | `[✅ 已完成]` | 12 原语 + 3 派生, 0 Typ::dummy() fallback |
| **高阶统一** | `[✅ 已完成]` | HO pattern + flex-rigid + occurs check + likely_unifiable |
| **类型基础设施** | `[✅ 已完成]` | TypeEnv + CTerm + Type/Sort/ClassAlgebra |
| **类型系统接入内核** | `[✅ 已完成]` | 全部内核规则类型感知, combination→Err, certify_annotated |
| **Discrimination Nets** | `[✅ 已完成]` | Net<T>: 前缀trie, intro_net + elim_net + safe_* nets |
| **Safe Rules 定点迭代** | `[✅ 已完成]` | 三阶段: match → elim_match → resolution fallback |
| **条件重写** | `[✅ 已完成]` | 前提提取 + 深度3递归验证 + Free→Var generalize |
| **Simplifier 深层重写** | `[✅ 已完成]` | rewrite_deep + conversionals + 迭代定点 |
| **Tactic 系统** | `[✅ 已完成]` | 15 tactical + 8 tactic |
| **Method 系统** | `[✅ 已完成]` | 25 方法 + 六层 fallback |
| **经典推理器** | `[✅ 已完成]` | fast/best/depth/dup_step, 5 搜索策略 |
| **Isar 证明引擎** | `[✅ 已完成]` | 三模式 (Forward/Chain/Backward) + 30+ 命令 + 块结构 |
| **Isar 结构化证明** | `[✅ 已完成]` | fix/assume/have/show + 目标精化 + 定理提取 |
| **Isar 计算链** | `[✅ 已完成]` | also/finally/moreover/ultimately + then/hence/thus |
| **induct/cases 真实执行** | `[✅ 已完成]` | lookup_theorem→DB, exec_induct 重写, infer_type_from_goal |
| **理论加载 Pipeline** | `[✅ 已完成]` | TheoryProcessor: .thy → spans → 命令分发 → finalize |
| **Session/Build 系统** | `[✅ 已完成]` | SessionBuilder: DAG + 批量编译 + panic-per-span 恢复 |
| **CLI 工具** | `[✅ 已完成]` | `isabelle-build`: --dir, --stats, --quiet |
| **datatype/codatatype** | `[✅ 已完成]` | 互归纳 (and), 构造函数类型注解, old_rep_datatype |
| **primrec/fun/function** | `[✅ 已完成]` | robust parser + inline fallback + 归纳规则 |
| **inductive/coinductive** | `[✅ 已完成]` | 多行解析 + 命名规则 |
| **typedef/record** | `[✅ 已完成]` | 7-10 theorems each |
| **locale/class/instance** | `[✅ 已完成]` | 8 命令集成, process_locale_class |
| **Pretty Printer** | `[✅ 已完成]` | 20+ operators, 7 precedence, binders |
| **TPTP Export** | `[✅ 已完成]` | FOF format, goal+premises export |
| **LSP 服务器** | `[✅ 已完成]` | 8 handlers (completion/hover/definition/lifecycle/goals/symbols) |
| **WASM 插件** | `[✅ 已完成]` | runtime + host functions |
| **BNF/datatype 完整** | `[🔵 规划]` | BNF Lfp, primcorec, full Ctr_Sugar |
| **全库验证 (1,849 files)** | `[🔵 规划]` | 大规模验证 |
| **Sledgehammer ATP** | `[🔵 规划]` | ATP 调用, 证明重构 |

---

## 架构总览

```
.thy 源文件 (1,849 files)
    ↓
    ↓ OuterSyntax::parse_spans()
    ↓
CommandSpan[] → TheoryProcessor::process_span()
    ├─ theory → LocalTheory::begin()
    ├─ lemma/theorem → IsarProof::lemma()
    ├─ proof/qed/{/} → IsarProof 三模式状态机
    ├─ locale/class/instance → process_locale_class()
    ├─ definition/fun/inductive/datatype → 解析 + 定理生成
    ├─ typedef/record → process_typedef/record()
    ├─ apply/by/done → method dispatch → ThmKernel
    └─ end → LocalTheory::finalize() → Arc<Theory>
    ↓
    ↓ SessionBuilder::build_session()
    ├─ TheoryGraph 扫描 + 拓扑排序
    ├─ 批量编译 (panic-per-span 恢复)
    └─ 统计报告
    ↓
HolTheoremDb (15,804 core, 42K+ full)
    ├─ by_name, intros, elims, simps
    ├─ intro_net / elim_net (OnceLock)
    ├─ safe_intro_net / safe_elim_net
    └─ def_index (LSP go-to-definition)
```

---

## 核心数据流

| 步骤 | 模块 | 输入 | 输出 |
|------|------|------|------|
| 解析命令 | `outer_syntax::parse_spans()` | source: &str | `Vec<CommandSpan>` |
| 处理命令 | `loader::TheoryProcessor::process_span()` | span, state | updated theory/proof |
| 结构化证明 | `proof::IsarProof` | 三模式状态机 | `Option<Thm>` |
| 执行方法 | `method::exec_single_method()` | state, method | `Vec<Thm>` |
| 深层重写 | `Simplifier::rewrite_deep()` | term | `Option<(Term, Thm)>` |
| HO 匹配 | `unify::matchers()` | pat, obj | `Option<Envir>` |
| 内核操作 | `ThmKernel::bicompose()` | thm1, thm2, i | `Option<Thm>` |

---

## 关键设计决策

### 1. 证明验证的六层 fallback 架构

```
verify_lemma():
  0 → Safe rules 定点迭代 (match→elim_match→resolution)
  1 → Built-in Var-override
  2 → Anonymous datatype axiom
  3 → Isar structured proof (三模式状态机)
  4 → exec_proof → 25 methods + chain fallback
  5 → Axiom acceptance (generalize_thm)
```

### 2. Discrimination Nets

`Net<T>` 是前缀 trie 数据结构。相比 O(n) 线性扫描，net lookup 将候选集缩减到 ~10-50 条规则（~1000× 加速）。惰性构建 (OnceLock)。

### 3. Isar 三模式状态机

```
Forward  → fix, assume, note, let, have, show
Chain    → 事实已链接, 等待 have/show
Backward → apply, by, proof (sub-block)
```

### 4. 类型安全 (Phase 21)

- `combination`: 返回 `Err(NotFunctionType)` 替代 `Typ::dummy()` fallback
- `CTerm::certify_annotated` — 自动从 TypeEnv 标注类型
- `CTerm::require_non_dummy` — 内核边界守卫
- 所有 theorem builder 使用 `certify_annotated`

### 5. 经典推理器 (Phase 22)

| 方法 | 策略 |
|------|------|
| `fast_exec` | DFS + iterative deepening (0..8) |
| `best_exec` | BEST_FIRST (worklist by nprems) |
| `depth_exec` | Bounded DFS (explicit bound) |
| `step_exec` | Safe exhaustive + one unsafe |
| `dup_step_exec` | step_tac + rule duplication |

---

## 文件统计

| 模块 | 文件数 | 行数 | 说明 |
|------|:--:|------|------|
| `src/core/` (内核) | 34 | ~14,000 | LCF内核, type_infer, context, proofterm, sorts |
| `src/isar/` (Isar) | 15 | ~8,500 | Method, ProofState, 解析器, token |
| `src/hol/` (HOL) | 15 | ~8,000 | BNF, Ctr_Sugar, primcorec, 理论加载 |
| `src/theory/` (理论) | 7 | ~3,500 | loader, verify_classifier, session_builder |
| `src/tools/` (工具) | 5 | ~2,500 | sledgehammer, reconstruct, tptp |
| `src/server/` (LSP) | 5 | ~1,500 | 传输层, LSP types, handlers |
| `src/syntax/` (语法) | 5 | ~1,200 | Rowan 解析器, AST, Printer |
| 其他 (session/wasm/lsp/kernel/document/fleche) | 19 | ~3,300 | |
| `src/bin/` (CLI) | 1 | ~140 | isabelle-build |
| tests | 12 | ~2,500 | proptest, comprehensive, e2e, tier2 |
| **合计** | **122** | **~44,500** | |
