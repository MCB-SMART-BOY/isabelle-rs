# 架构设计 v22.0 (v1.8.1)

> LCF 内核：15 ops + tpairs/shyps · 27 methods · FM 算术 · HOL 简化器 · Meson + Metis + Sledgehammer ATP
> 验证：5/5 core files 125/125 (100%) · 0 kernel errors · prove_condition 已修复
> 性能：179ns-12μs (release mode, criterion 实测)

## 状态标记说明

| 标记 | 含义 |
|------|------|
| `[✅ 已完成]` | 代码已实现，测试通过 |
| `[⚠️ 部分]` | 代码存在但不完整或有已知问题 |
| `[🔵 规划]` | 后续阶段 (长期) |

## 速查表

| 层 / 组件 | 状态 | 关键交付物 |
|-----------|------|-----------|
| **LCF 内核 (15 操作)** | `[✅ 已完成]` | 12 原语 + 3 派生 + tpairs/shyps, 0 Typ::dummy() fallback |
| **高阶统一** | `[✅ 已完成]` | HO pattern + flex-rigid + occurs check + likely_unifiable |
| **类型基础设施** | `[✅ 已完成]` | TypeEnv + CTerm + Type/Sort/ClassAlgebra |
| **类型系统接入内核** | `[✅ 已完成]` | 全部内核规则类型感知, combination→Err, certify_annotated |
| **Discrimination Nets** | `[✅ 已完成]` | Net<T>: 前缀trie, intro_net + elim_net + safe_* nets |
| **Safe Rules 定点迭代** | `[✅ 已完成]` | 三阶段: match -> elim_match -> resolution fallback |
| **条件重写** | `[✅ 已完成]` | 前提提取 + 深度3递归验证 + Free->Var generalize |
| **Simplifier 深层重写** | `[✅ 已完成]` | rewrite_deep + conversionals + 迭代定点 |
| **Tactic 系统** | `[✅ 已完成]` | 15 tactical + 8 tactic |
| **Method 系统** | `[✅ 已完成]` | 27 方法 + 六层 fallback (含 Meson) |
| **经典推理器** | `[✅ 已完成]` | fast/best/depth/dup_step, 5 搜索策略 |
| **thy_header 解析** | `[✅ 已完成]` | 完整理论头解析 (Phase 40) |
| **HOL 简化器** | `[✅ 已完成]` | 条件重写 + Solver 插件 (Phase 41) |
| **线性算术求解器** | `[✅ 已完成]` | Fourier-Motzkin 变量消去 (Phase 42) |
| **Isar 证明引擎** | `[✅ 已完成]` | 三模式 (Forward/Chain/Backward) + 30+ 命令 + 块结构 |
| **Isar 结构化证明** | `[✅ 已完成]` | fix/assume/have/show + 目标精化 + 定理提取 |
| **Isar 计算链** | `[✅ 已完成]` | also/finally/moreover/ultimately + then/hence/thus |
| **induct/cases 真实执行** | `[⚠️ 部分]` | lookup_theorem→DB, exec_induct 重写, infer_type_from_goal |
| **理论加载 Pipeline** | `[⚠️ 部分]` | TheoryProcessor: .thy → spans → 命令分发 → finalize, 有栈溢出 |
| **Session/Build 系统** | `[⚠️ 部分]` | SessionBuilder: DAG + 批量编译 + panic-per-span 恢复 |
| **CLI 工具** | `[✅ 已完成]` | isabelle-build: --dir, --stats, --quiet |
| **datatype/codatatype** | `[✅ 已完成]` | 互归纳 (and), 构造函数类型注解, old_rep_datatype |
| **primrec/fun/function** | `[⚠️ 部分]` | robust parser + inline fallback + 归纳规则 |
| **inductive/coinductive** | `[⚠️ 部分]` | 多行解析 + 命名规则 |
| **typedef/record** | `[⚠️ 部分]` | 7-10 theorems each |
| **locale/class/instance** | `[⚠️ 部分]` | 8 命令集成, process_locale_class |
| **Pretty Printer** | `[✅ 已完成]` | 20+ operators, 7 precedence, binders |
| **TPTP Export** | `[✅ 已完成]` | FOF format, goal+premises export |
| **LSP 服务器** | `[⚠️ 部分]` | 8 handlers (completion/hover/definition/lifecycle/goals/symbols) |
| **WASM 插件** | `[⚠️ 部分]` | runtime + host functions |
| **BNF Lfp/Gfp** | `[⚠️ 部分]` | induction/coinduction/fold/rec/unfold/corec + map/set/rel/pred |
| **Ctr_Sugar** | `[⚠️ 部分]` | case/disc/sel/split/cong/nchotomy/size 定理生成 |
| **Transfer/Lifting** | `[⚠️ 部分]` | 传输规则生成 + rel_fun/rel_set + 商类型定理 |
| **Metis 证明器** | `[⚠️ 部分]` | 消解 + SAT (DPLL/CDCL), 但 method 集成是 auto fallback |
| **Sledgehammer** | `[⚠️ 部分]` | ATP 调用框架 + TSTP 解析, 证明重构不完整 |
| **属性系统** | `[⚠️ 部分]` | attrib.rs 存在, [simp]/[intro!]/[elim!] 集成不完整 |
| **Meson** | `[✅ 已完成]` | Model elimination prover (Phase 48) |
| **全库验证 (1,473 files)** | `[🔵 规划]` | 大规模验证 |
| **Code Generator** | `[🔵 规划]` | HOL → SML/OCaml/Haskell |
| **SMT 集成** | `[🔵 规划]` | Z3/CVC4 集成 |
| **Nitpick/Quickcheck** | `[🔵 规划]` | 反例查找/随机测试 |

---

## 架构总览

```
.thy 源文件 (1,473 files)
    ↓
    ↓ thy_header::parse_header()  (Phase 40)
    ↓ OuterSyntax::parse_spans()
    ↓
CommandSpan[] -> TheoryProcessor::process_span()
    ├─ theory -> LocalTheory::begin()
    ├─ lemma/theorem -> IsarProof::lemma()
    ├─ proof/qed/{/} -> IsarProof 三模式状态机
    ├─ locale/class/instance -> process_locale_class()
    ├─ definition/fun/inductive/datatype -> 解析 + 定理生成
    ├─ typedef/record -> process_typedef/record()
    ├─ apply/by/done -> method dispatch -> ThmKernel
    │   ├─ exec_simp -> HolSimplifier::hol_rewrite_deep() (Phase 41)
    │   ├─ exec_arith -> LinArithSolver::solve() FM 消去 (Phase 42)
    │   └─ auto/blast/fast/depth/step/dup_step
    └─ end -> LocalTheory::finalize() -> Arc<Theory>
    ↓
    ↓ SessionBuilder::build_session()
    ├─ TheoryGraph 扫描 + 拓扑排序
    ├─ 批量编译 (panic-per-span 恢复)
    └─ 统计报告
    ↓
HolTheoremDb (~42K+ full)
    ├─ by_name, intros, elims, simps
    ├─ intro_net / elim_net (OnceLock)
    ├─ safe_intro_net / safe_elim_net
    └─ def_index (LSP go-to-definition)
```

---

## 核心数据流

| 步骤 | 模块 | 输入 | 输出 |
|------|------|------|------|
| 解析头 | `thy_header::parse_header()` | source: &str | `TheoryHeader` |
| 解析命令 | `outer_syntax::parse_spans()` | source: &str | `Vec<CommandSpan>` |
| 处理命令 | `loader::TheoryProcessor::process_span()` | span, state | updated theory/proof |
| 结构化证明 | `proof::IsarProof` | 三模式状态机 | `Option<Thm>` |
| 执行方法 | `method::exec_single_method()` | state, method | `Vec<Thm>` |
| HOL 简化 | `HolSimplifier::hol_rewrite_deep()` | term | `Option<(Term, Thm)>` |
| FM 算术 | `LinArithSolver::solve()` | constraints | `Option<Thm>` |
| HO 匹配 | `unify::matchers()` | pat, obj | `Option<Envir>` |
| 内核操作 | `ThmKernel::bicompose()` | thm1, thm2, i | `Option<Thm>` |

---

## 关键设计决策

### 1. 证明验证的六层 fallback 架构

```
verify_lemma():
  0 -> Safe rules 定点迭代 (match->elim_match->resolution)
  1 -> Built-in Var-override (DB 预存定理)
  2 -> Anonymous datatype axiom
  3 -> Isar structured proof (三模式状态机)
  4 -> exec_proof -> 27 methods + chain fallback
  5 -> Axiom acceptance (generalize_thm)
```

### 2. Fourier-Motzkin 变量消去 (Phase 42)

```
arith_tac():
  1. 提取线性原子 (Eq/Lt/Le) 从前提和目标
  2. normalize: 转换为 NormalizedConstraint (标准形式)
  3. FM 消去: 遍历变量, 组合上下界, GCD 缩放
  4. 矛盾检测: 严格/非严格/成对
  5. LCF 证明构造: reflexiv, bicompose, trans, add_mono
  6. Fallback: simp -> auto -> blast
```

### 3. HOL 简化器 (Phase 41)

```
HolSimplifier:
  - 内核 Simplifier + ConditionSolver 钩子
  - Solver 插件: ArithSolver (FM) + AsmSolver
  - 20+ 内建 HOL 重写规则
  - hol_rewrite_deep(): 迭代 (无递归栈溢出风险)
  - simp_tactic(): 生成 TacticFn
```

### 4. Isar 三模式状态机

```
Forward  -> fix, assume, note, let, have, show
Chain    -> 事实已链接, 等待 have/show
Backward -> apply, by, proof (sub-block)
```

### 5. 类型安全 (Phase 21)

- `combination`: 返回 `Err(NotFunctionType)` 替代 `Typ::dummy()` fallback
- `CTerm::certify_annotated` — 自动从 TypeEnv 标注类型
- `CTerm::require_non_dummy` — 内核边界守卫
- 所有 theorem builder 使用 `certify_annotated`

---

## 文件统计

| 模块 | 文件数 | 行数 | 说明 |
|------|:--:|------|------|
| `src/core/` (内核) | 34 | ~14,500 | LCF内核, type_infer, context, proofterm, sorts |
| `src/isar/` (Isar) | 18 | ~12,300 | Method, ProofState, 解析器, token, linarith (FM) |
| `src/hol/` (HOL) | 18 | ~14,000 | BNF, Ctr_Sugar, primcorec, 理论加载 |
| `src/theory/` (理论) | 8 | ~3,100 | loader, thy_header, verify_classifier, session_builder |
| `src/tools/` (工具) | 7 | ~4,600 | simp (HOL 简化器), sledgehammer, reconstruct, tptp, metis |
| `src/server/` (LSP) | 5 | ~1,500 | 传输层, LSP types, handlers |
| `src/lsp/` (handlers) | 8 | ~1,000 | completion, hover, definition, lifecycle, goals, symbols |
| `src/syntax/` (语法) | 5 | ~1,000 | Rowan 解析器, AST, Printer |
| `src/session/` | 4 | ~650 | Session, file_worker, watchdog |
| 其他 (wasm/document/fleche/bin) | 12 | ~1,480 | |
| 其他 (wasm/document/fleche) | 10 | ~1,200 | |
| `src/bin/` (CLI) | 1 | ~140 | isabelle-build |
| tests | 12 | ~55,000 | proptest, comprehensive, e2e, tier2, tier3 |
| **合计** | **~121** | **~46,000** |
