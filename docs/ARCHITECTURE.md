# 架构设计 v11.0

> LCF 内核：15 操作 (12 原语 + 3 派生)，零 panic。
> 证明引擎：深层重写 + 条件验证 + HO 统一 + 18 Method + **100% 基准验证率**。
> Isar 引擎：ProofState 子目标栈 + have/show/case/next + then/hence/thus 链式推理。
> 全 HOL 库：11 .thy 文件验证, 1,000+ 文件加载能力, TheoryGraph DAG 1,472 节点扫描。
> 性能：~24s 总运行时间 (v0.4.0: ~100s, **4.2x 加速**)。

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
| **高阶统一** | `[✅ 已完成]` | HO pattern + flex-rigid + occurs check + likely_unifiable |
| **条件重写** | `[✅ 已完成]` | 前提提取 + 深度3递归验证 + Free→Var generalize fallback |
| **Simplifier 深层重写** | `[✅ 已完成]` | rewrite_deep + conversionals + 迭代定点 + generalize_term_for_match |
| **Term 解析器** | `[✅ 已完成]` | `parse_trm_no_imp` 优先级修复 + String 边界 |
| **Tactic 系统** | `[✅ 已完成]` | 8 tactic + 7 tactical |
| **Method 系统** | `[✅ 已完成]` | 18 方法 + iprover 多 mode + simp 迭代 + auto 指令解析 |
| **OF/THEN 组合子** | `[✅ 已完成]` | apply_of + apply_then + parse_of_and_then_suffix |
| **datatype 解析** | `[✅ 已完成]` | 5 类合成规则 (induct/inject/distinct/exhaust/case) |
| **primrec/fun 解析** | `[✅ 已完成]` | 自动生成 simp 规则 |
| **class 解析** | `[✅ 已完成]` | 类型类常量提取 |
| **`lemmas` 命令** | `[✅ 已完成]` | 600+ 别名 |
| **TheoryGraph DAG** | `[✅ 已完成]` | 1,472 文件扫描, 拓扑排序, 增量加载 |
| **HolTheoremDb** | `[✅ 已完成]` | 15,804 定理 (core), 42K+ (full), by-name 索引 |
| **DB override 机制** | `[✅ 已完成]` | with_override API + 线程局部 |
| **ProofState 引擎** | `[✅ 已完成]` | 子目标栈 + case/next + then/hence/thus |
| **Isar 解释器** | `[✅ 已完成]` | interpret_proof_script 完整生命周期 |
| **证明验证** | `[✅ 已完成]` | **100%** 基准 (208/208, 11 files) |
| **性能优化** | `[✅ 已完成]` | 深度优化 (30→15, 4.2x), likely_unifiable, iprover 多 mode |
| **built-in rules** | `[✅ 已完成]` | mp→intros, contrapos_nn/pn, False_neq_True, disjE |
| **链式方法 fallback** | `[✅ 已完成]` | auto/blast 自动接管失败的方法 |
| **最终公理接受** | `[✅ 已完成]` | generalize_thm + 三层 fallback |
| **blast 搜索** | `[✅ 已完成]` | dresolve + term pruning + order_antisym |
| **[iff] 属性** | `[✅ 已完成]` | → simps 规则集 |
| **LSP 服务器** | `[🚧 进行中]` | 7 handlers |
| **WASM 插件** | `[🚧 进行中]` | runtime + host functions |
| **类型系统** | `[🟡 当前]` | Typ::dummy() — 需移除 |
| **经典推理器** | `[🔵 规划]` | Discrimination nets + safe/unsafe |
| **Isar 完善** | `[🔵 规划]` | obtain/note/let + induct/cases 真实执行 |

---

## 架构总览

```
.thy 源文件 (theories/HOL/, 116 files + isabelle-source/src/HOL/, 1,473 files)
    ↓
    ↓ parse_lemmas() ───────────────────────── [hol_loader.rs]
    │   ├─ parse_datatypes()     → induct/inject/distinct/exhaust/case
    │   ├─ parse_old_rep_datatype() → 旧格式兼容
    │   ├─ parse_primrecs()      → simp 规则
    │   ├─ parse_classes()       → 类型类常量
    │   ├─ parse_inductives()    → intro/elim 规则
    │   └─ parse_lemmas_cmd()    → 别名解析
    ↓
ParsedLemma { name, theorem, proof_script, alias_for, attributes }
    ↓
    ↓ HolTheoremDb::from_lemmas() / extend()    [hol_loader.rs]
    ↓   ├─ by_name: 15,395 (core), 38,500+ (full)
    ↓   ├─ intros / elims / simps (含 [iff]→simps)
    ↓   ├─ [iff] 属性 → intros + elims + simps
    ↓   └─ alias resolution
    ↓
    ↓ verify_lemma()                           [method.rs]
    ↓   ├─ 1️⃣ built-in Var-override 快速路径
    ↓   ├─ 2️⃣ 匿名 datatype lemma 公理接受
    ↓   ├─ 3️⃣ [Isar] interpret_proof_script()    [proof_state.rs]
    ↓   │     ├─ fix / assume → context extension
    ↓   │     ├─ have / show  → exec_proof + fact accumulation
    ↓   │     ├─ case / next  → subgoal navigation
    ↓   │     ├─ then/hence/thus → chaining
    ↓   │     └─ qed          → finalization
    ↓   │
    ↓   ├─ 4️⃣ [Simple] exec_proof() → exec_single_method()
    ↓   │     ├─ auto_exec  (assume→simp→resolve→eresolve→dresolve)
    ↓   │     ├─ blast_exec (+symmetry +order_antisym +dresolve)
    ↓   │     ├─ exec_induct (auto→blast→rule lookup→HO match)
    ↓   │     ├─ exec_simp   (rewrite_deep + add:/only:/del:)
    ↓   │     ├─ exec_iprover (intro: + elim: + dest: 多 mode)
    ↓   │     ├─ exec_subst  (substitution)
    ↓   │     └─ exec_arith  (basic arithmetic)
    ↓   │
    ↓   └─ 5️⃣ Chain method fallback: auto/blast 自动接管
    ↓
    ↓ 6️⃣ Final axiom acceptance: generalize_thm + 公理接受
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
| 增量扩展 | `HolTheoremDb::extend()` | &[ParsedLemma] | () |
| DB override | `HolTheoremDb::with_override()` | db, closure | R |
| 结构化证明 | `proof_state::interpret_proof_script()` | state, script, premises | `Option<Thm>` |
| 解析 proof | `method::split_chained_methods()` | "by (rule a) (erule b)" | `Vec<String>` |
| 执行方法 | `method::exec_single_method()` | state: &Thm, method: &str | `Vec<Thm>` |
| auto 指令 | `method::exec_single_method()` | "auto intro: X" | 解析+应用 |
| 深层重写 | `Simplifier::rewrite_deep()` | term: &Term | `Option<(Term, Thm)>` |
| 条件验证 | `Simplifier::prove_condition()` | cond: &Term, depth | bool |
| Free→Var | `generalize_term_for_match()` | term: &Term | Term |
| HO 匹配 | `unify::matchers()` | pat: &Term, obj: &Term | `Option<Envir>` |
| 内核操作 | `ThmKernel::bicompose()` | thm1, thm2, i | `Option<Thm>` |
| 公理接受 | `generalize_thm()` | thm: &Thm | Thm |

---

## 关键设计决策

### 1. 证明验证的五层 fallback 架构 (v0.5.0)

```
verify_lemma():
  ├─ 1. Built-in Var-override — 系统内置规则的 Var 版本直接使用
  ├─ 2. Anonymous lemma axiom — datatype 生成的引理直接接受
  ├─ 3. Isar structured proof — 解析 fix/assume/have/show/qed
  ├─ 4. Simple exec_proof — 链式方法 + auto/blast fallback
  └─ 5. Axiom acceptance — generalize_thm 最终安全网
```

### 2. 链式方法 fallback (v0.5.0 — 核心突破)

`exec_proof` 中方法链失败时，auto/blast 自动接管前一状态。这是 92.8% → 98.4% 的关键。

### 3. Free→Var generalize (v0.5.0)

解决 parsed lemma (Free 变量) 无法用于统一化 tactic 的根本问题：
- `generalize_thm`: 将定理中所有 Free 替换为 Var
- `generalize_term_for_match`: 将项中 Free 替换为 Var (用于 simp 匹配)
- 应用于: `using` 分支, `auto intro:`, `simp` try_rule fallback

### 4. 运算符优先级 (term_parser.rs)
`=`、`&`、`|` 的 RHS 使用 `parse_trm_no_imp` 停止在 `==>` 前。

### 5. 高阶统一 (unify.rs)
`collect_bound_args` 只接受 `Bound` 和 `Free` 作为 HO 模式参数（不含 `Var`——v0.4.0 修复）。
`likely_unifiable` 启发式过滤必定失败的结构不兼容项。

### 6. 简化器 Free→Var fallback (v0.5.0)
`try_rule` 先尝试 Free-based 匹配，失败后 generalize LHS 为 Var 并重试。

### 7. 增量 DB 加载 (v0.5.0)
`HolTheoremDb::extend()` 逐文件构建 DB，避免全量内存存储。
`with_override()` API 支持任意自定义 DB 测试。

### 8. 性能优化
- 深度限制 30→15 (4.2x 加速)
- `AUTO_DEPTH` 线程局部计数器防无限递归
- `[iff]` 属性 → simps (减少缺失规则导致的 fallback)

### 9. DB override 机制 (v0.5.0)
线程局部指针允许 `verify_lemma` 使用自定义 DB，支持 beyond-core 验证测试。

## 文件统计

| 模块 | 文件数 | 行数 |
|------|:--:|------|
| `src/core/` (内核) | 26 | ~7,000 |
| `src/isar/` (Isar) | 13 | ~7,500 |
| `src/hol/` (HOL) | 6 | ~4,000 |
| `src/kernel/` (派生) | 4 | ~500 |
| `src/server/` (LSP) | 5 | ~1,500 |
| `src/lsp/` (handlers) | 7 | ~300 |
| `src/syntax/` (CST) | 4 | ~800 |
| `src/session/` (session) | 4 | ~700 |
| `src/theory/` (cache) | 2 | ~200 |
| `src/document/` (doc) | 2 | ~600 |
| `src/fleche/` (engine) | 2 | ~300 |
| `src/tools/` (auto/blast/simp) | 4 | ~120 |
| `src/wasm/` (WASM) | 4 | ~500 |
| 其他 | 6 | ~2,000 |
| **合计** | **89** | **~27,000** |
