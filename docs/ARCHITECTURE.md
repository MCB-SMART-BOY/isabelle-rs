# 架构设计 v9.1

> LCF 内核：15 操作 (12 原语 + 3 派生)，零 panic。
> 证明引擎：深层重写 + 条件验证 + HO 匹配 + 15 Method + 60% 基准验证率。
> Isar 引擎：ProofState 子目标栈 + have/show/case/next + then/hence/thus 链式推理。
> 全 HOL 库：115 .thy 文件，TheoryGraph DAG，1,472 文件全库扫描。
> 下一步：Phase 7 — 全 HOL 库加载 + 性能优化。

## 状态标记说明

| 标记 | 含义 |
|------|------|
| `[✅ 已完成]` | 代码已实现，测试通过 |
| `[🚧 进行中]` | 部分实现 |
| `[🟡 当前]` | 当前优先任务 |
| `[🔵 规划]` | 后续阶段 |

## 速查表

| 层 / 组件 | 状态 | 关键交付物 |
|-----------|------|-----------|
| **LCF 内核 (15 操作)** | `[✅ 已完成]` | 12 原语 + bicompose + bicompose_eresolve + subst_premise |
| **高阶模式匹配** | `[✅ 已完成]` | HO pattern: Free/Var 头 + β-归约 |
| **条件重写** | `[✅ 已完成]` | 前提提取 + 深度3递归验证 |
| **Simplifier 深层重写** | `[✅ 已完成]` | rewrite_deep + conversionals |
| **Term 解析器** | `[✅ 已完成]` | `parse_trm_no_imp` 优先级修复 |
| **Tactic 系统** | `[✅ 已完成]` | 8 tactic + 7 tactical |
| **Method 系统** | `[✅ 已完成]` | 15 方法 + subst/fact/arith |
| **datatype 解析** | `[✅ 已完成]` | 5 类合成规则 (induct/inject/distinct/exhaust/case) |
| **primrec/fun 解析** | `[✅ 已完成]` | 47 定义从 List.thy, 生成 simp 规则 |
| **class 解析** | `[✅ 已完成]` | 17 类型类, fixes 常量提取 |
| **old_rep_datatype** | `[✅ 已完成]` | Nat.thy 旧格式兼容 |
| **`lemmas` 命令** | `[✅ 已完成]` | 600+ 别名 |
| **TheoryGraph DAG** | `[✅ 已完成]` | 115 文件拓扑加载, 1,472 文件扫描 |
| **HolTheoremDb** | `[✅ 已完成]` | 15,804 定理, 15,395 by-name 索引 |
| **ProofState 引擎** | `[✅ 已完成]` | 子目标栈 + case/next + then/hence/thus |
| **Isar 解释器** | `[✅ 已完成]` | interpret_proof_script 完整生命周期 |
| **证明验证** | `[✅ 已完成]` | 60% 基准 (75/125 sampled) |
| **blast 搜索** | `[✅ 已完成]` | dresolve + term pruning + order_antisym |
| **induct/cases** | `[✅ 已完成]` | 3 候选项 + 15 子目标 + 事实累积 |
| **subst 方法** | `[✅ 已完成]` | (asm) 模式 + 定理驱动替换 |
| **迭代限制器** | `[✅ 已完成]` | thread_local 防止超时 |
| **LSP 服务器** | `[🚧 进行中]` | 7 handlers |
| **WASM 插件** | `[🚧 进行中]` | runtime + host functions |
| **全 HOL 库加载** | `[🟡 当前]` | Phase 7 — 1,395 DAG 节点待加载 |
| **arith 方法** | `[🟡 当前]` | 基础规则已加, 完整求解待实现 |
| **cargo publish** | `[🔵 规划]` | Phase 7.3 |

---

## 架构总览

```
.thy 源文件 (theories/HOL/, 115 files, 4.9MB)
    ↓
    ↓ parse_lemmas() ───────────────────────── [hol_loader.rs]
    │   ├─ parse_datatypes()     → induct/inject/distinct/exhaust/case
    │   ├─ parse_old_rep_datatype() → 旧格式兼容
    │   ├─ parse_primrecs()      → simp 规则
    │   ├─ parse_classes()       → 类型类常量
    │   └─ parse_lemmas_cmd()    → 别名解析
    ↓
ParsedLemma { name, theorem, proof_script, alias_for }
    ↓
    ↓ HolTheoremDb::from_lemmas()              [hol_loader.rs]
    ↓   ├─ by_name: 15,395 entries
    ↓   ├─ intros / elims / simps
    ↓   └─ alias resolution
    ↓
    ↓ verify_lemma()                           [method.rs]
    ↓   ├─ [Isar] interpret_proof_script()    [proof_state.rs]
    ↓   │     ├─ fix / assume → context extension
    ↓   │     ├─ have / show  → exec_proof + fact accumulation
    ↓   │     ├─ case / next  → subgoal navigation
    ↓   │     ├─ then/hence/thus → chaining
    ↓   │     └─ qed          → finalization
    ↓   │
    ↓   └─ [Simple] exec_proof() → exec_single_method()
    ↓         ├─ auto_exec  (assume→simp→resolve→eresolve→dresolve)
    ↓         ├─ blast_exec (+symmetry +order_antisym +dresolve)
    ↓         ├─ exec_induct (auto→blast→rule lookup→HO match)
    ↓         ├─ exec_simp   (rewrite_deep + add:/only:/del:)
    ↓         ├─ exec_subst  (substitution)
    ↓         └─ exec_arith  (basic arithmetic)
    ↓
ThmKernel (15 operations, zero panics)          [thm.rs]
    ├─ assume, reflexive, symmetric, transitive
    ├─ combination, abstraction, beta_conversion
    ├─ implies_intr, implies_elim
    ├─ forall_intr, forall_elim, instantiate
    ├─ bicompose, bicompose_eresolve, subst_premise
    └─ trivial (derived)
```

---

## 核心数据流

| 步骤 | 模块 | 输入 | 输出 |
|------|------|------|------|
| 解析 .thy | `hol_loader::parse_lemmas()` | source: &str | `Vec<ParsedLemma>` |
| 构建 DB | `HolTheoremDb::from_lemmas()` | &[ParsedLemma] | `HolTheoremDb` |
| 结构化证明 | `proof_state::interpret_proof_script()` | state, script, premises | `Option<Thm>` |
| 解析 proof | `method::split_chained_methods()` | "by (rule a) (erule b)" | `Vec<String>` |
| 执行方法 | `method::exec_single_method()` | state: &Thm, method: &str | `Vec<Thm>` |
| 深层重写 | `Simplifier::rewrite_deep()` | term: &Term | `Option<(Term, Thm)>` |
| 条件验证 | `Simplifier::prove_condition()` | cond: &Term, depth | bool |
| HO 匹配 | `unify::matchers()` | pat: &Term, obj: &Term | `Option<Envir>` |
| 内核操作 | `ThmKernel::bicompose()` | thm1, thm2, i | `Option<Thm>` |

---

## 关键设计决策

### 1. 运算符优先級 (term_parser.rs)
`=`、`&`、`|` 的 RHS 使用 `parse_trm_no_imp` 停止在 `==>` 前。

### 2. 高阶模式匹配 (unify.rs)
`collect_bound_args` 接受 `Free` 和 `Var` 作为 HO 模式头。

### 3. 归纳规则应用 (method.rs)
`exec_induct` 搜索 DB 中的归纳规则，通过 HO 匹配应用，`solve_subgoals` 逐子目标求解 (上限15, 事实累积)。

### 4. 条件重写 (simplifier.rs)
`RewriteRule::from_thm` 从定理前提中提取条件。`try_rule` 用递归 simplifier 验证条件 (深度3)。

### 5. Isar 引擎 (proof_state.rs)
`ProofState::Proving` 包含子目标栈 + 链式事实 + 嵌套深度。`interpret_proof_script` 驱动完整生命周期。

### 6. 迭代限制 (method.rs)
`thread_local!` 计数器防止 `auto_exec`/`blast_exec` 无限递归，每引理重置。

## 文件统计

| 模块 | 文件数 | 行数 |
|------|:--:|------|
| `src/core/` (内核) | 26 | ~6,000 |
| `src/isar/` (Isar) | 9 | ~4,000 |
| `src/hol/` (HOL) | 6 | ~2,500 |
| `src/kernel/` (派生) | 4 | ~500 |
| `src/server/` (LSP) | 4 | ~1,500 |
| `src/syntax/` (CST) | 3 | ~800 |
| `src/wasm/` (WASM) | 4 | ~500 |
| 其他 | 28 | ~4,200 |
| **合计** | **84** | **~20,000** |
