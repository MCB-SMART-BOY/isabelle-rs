# Roadmap

## 总体路线

Isabelle-rs 的路线图分为 7 个 Tier，从内核完备性到生产就绪逐步推进。每个 Tier 都建立在前面 Tier 的基础上。

```
Tier 0  ████████████  ✅ 完成    内核基础 (types, term, logic, sign, theory, thm)
Tier 1  ░░░░░░░░░░░░  🔴 下一步  证明引擎 (unify, envir, tactic, drule)
Tier 2  ░░░░░░░░░░░░  🟡 规划中  Isar 语言 (proof, toplevel, method)
Tier 3  ░░░░░░░░░░░░  🟡 规划中  逻辑基础设施 (proofterm, net, consts)
Tier 4  ░░░░░░░░░░░░  🟢 规划中  语法系统 (Syntax, parser, pretty printer)
Tier 5  ░░░░░░░░░░░░  🟢 部分完成 LSP 服务器 (transport, handler, extensions)
Tier 6  ░░░░░░░░░░░░  🔵 未来    HOL 对象逻辑
Tier 7  ░░░░░░░░░░░░  ⚪ 远期    生产就绪 (concurrency, build system)
```

---

## Tier 0 — 内核基础 ✅ 完成

**状态**：30 个测试通过，~3,200 行 Rust。

### 已完成模块

| 模块 | 文件 | 内容 |
|------|------|------|
| 类型系统 | `core/types.rs` | Sort, Typ, ClassAlgebra, dummyS, dummyT, maxidx |
| Lambda 项 | `core/term.rs` | 6 个构造器 (Const, Free, Var, Bound, Abs, App), de Bruijn |
| Pure 元逻辑 | `core/logic.rs` | Pure.imp `==>` / Pure.all `!!` / Pure.eq `==` |
| 签名系统 | `core/sign.rs` | TypeSignature, Signature, certify_typ, const_type |
| 理论管理 | `core/theory.rs` | Theory (pure, begin, add_theorem), ProofContext |
| LCF 内核 | `core/thm.rs` | ThmKernel: 9 条推理规则, CTerm, Hyps (α-equiv), Derivation |
| 文档模型 | `document/*` | Document, Node, Command, Snapshot, fork-point diff |
| 增量引擎 | `fleche/*` | Flèche, CommandExecutor trait, SimpleExecutor |
| LSP 服务器 | `server/*` | LSP 3.17 types, JSON-RPC transport, Request handler, Isabelle extensions |

---

## Tier 1 — 证明引擎 🔴 下一步

**目标**：使 Isabelle-rs 能够执行基本的证明搜索。

### 需要实现的模块

#### 1. `core/envir.rs` — 变量环境 (~400 行)

```
Environment = Map<Var → Term> × Map<TVar → Typ>
```
- `Envir.empty(maxidx)`: 创建空环境
- `Envir.genvar(name, typ)`: 生成 fresh schematic variable
- `Envir.lookup(var)`: 查找变量绑定
- `Envir.update(var, term)`: 更新绑定
- `Envir.norm_term(env, term)`: 正规化（替换所有已绑定变量）

对应 Isabelle: `envir.ML` (428 行)

#### 2. `core/term_subst.rs` — 代入 (~300 行)

- `subst_bounds(args, body)`: `(λx y. body)[x:=a, y:=b]`
- `subst_Vars(env, term)`: 替换所有 Var
- `subst_TVars(env, typ)`: 替换所有 TVar
- `instantiate(tyinst, tminst, term)`: 类型+项实例化
- `beta_norm(term)`: 完全 β-正规化（当前 `beta_conversion` 只处理一步）

对应 Isabelle: `term_subst.ML`

#### 3. ✅ `core/pattern.rs` — 模式匹配 (~160 行)

- `Pattern.match_(pat, obj)`: 将 `?P(x, y)` 匹配到具体项
- `Pattern.unify(pat1, pat2)`: 两个模式的统一
- `Pattern.rewrite(rule, goal)`: 用规则重写目标

对应 Isabelle: `pattern.ML` (526 行)

#### 4. `core/unify.rs` — 高阶统一 (~600 行)

Isabelle 统一算法的核心：
- `Unify.unifiers(env, pairs)`: 返回所有 unifier 的序列
- `Unify.matchers(env, pairs)`: 返回所有 matcher
- 使用 Huet 的高阶统一算法（半可判定但实践中足够）
- 限制搜索深度防止无穷循环

对应 Isabelle: `unify.ML` (668 行)

#### 5. `core/tactic.rs` + `core/tactical.rs` — 策略系统 (~400 行)

```
type Tactic = Goal → GoalSeq

fn all_tac(goal) → [goal]
fn no_tac(goal) → []
fn THEN(tac1, tac2)(goal) → tac2 ∘ tac1
fn ORELSE(tac1, tac2)(goal) → tac1(goal) | tac2(goal)
fn REPEAT(tac)(goal) → 重复应用直到失败
fn resolve_tac(thm)(goal) → 用定理消解目标
fn assume_tac(goal) → 若假设匹配则成功
```

对应 Isabelle: `tactic.ML` + `tactical.ML`

#### 6. ✅ `core/drule.rs` — 派生推理规则 (~170 行)

```
forall_intr (x, thm) → ∀x. P(x)  如果 x 不在假设中
forall_elim (ct, thm) → P(t)      如果 ∀x. P(x)
implies_intr_list ([A,B], C) → A==>B==>C
implies_elim_list (A==>B==>C, [A,B]) → C
zero_var_indexes (thm) → 重置所有 ?var 索引
incr_indexes (thm) → 增加所有索引
lift_rule (thm) → 提升规则到更大的上下文
```

对应 Isabelle: `drule.ML` (839 行)

#### 7. ✅ `core/variable.rs` — 变量操作 (~330 行)

```
Variable.variant_fixes (names, ctxt) → 重命名避免冲突
Variable.import_terms (terms, ctxt) → 导入到上下文
Variable.export_terms (terms, ctxt) → 从上下文导出
Variable.focus (term, ctxt) → 提取子目标
Variable.polymorphic (ctxt, term) → 泛化自由变量
```

对应 Isabelle: `variable.ML` (791 行)

### Tier 1 完成标准

- [ ] 两个项可以通过 `unify` 统一
- [ ] 可以用 `resolve_tac` 使用已知定理
- [ ] 可以执行 `by (rule ...)` 风格的简单证明
- [ ] `assume_tac` 可以闭合目标

---

## Tier 2 — Isar 证明语言 🟡 规划中

**目标**：支持 Isabelle/Isar 的结构化证明语法。

### 需要实现的模块

| 模块 | 行数估计 | 对应 Isabelle |
|------|---------|---------------|
| ✅ `isar/token.rs` | ~436 | `Isar/token.ML` (854) — 词法分析器 |
| ✅ `isar/parse.rs` | ~181 | 解析组合子 |
| ✅ `isar/proof.rs` | ~244 | `Isar/proof.ML` (1,370) — 证明状态机 |
| ✅ `isar/proof_context.rs` | ~230 | `Isar/proof_context.ML` (1,776) |
| ✅ `isar/toplevel.rs` | ~223 | `Isar/toplevel.ML` (788) — 顶层命令循环 |
| ✅ `isar/method.rs` | ~199 | `Isar/method.ML` (837) — proof method 系统 |
| `core/simplifier.rs` | ✅ ~280 | `raw_simplifier.ML` (1,576) — 重写引擎 |

### Isar 语法支持

```
theory Foo
imports Bar
begin

lemma my_lemma:
  assumes "A" and "B"
  shows "A ∧ B"
proof (rule conjI)
  case 1
  show "A" using assms(1) .
next
  case 2
  show "B" using assms(2) .
qed

end
```

- [ ] `have` / `show` / `hence` / `thus`
- [ ] `fix` / `assume` / `obtain`
- [ ] `proof (cases/induct/rule)` / `qed`
- [ ] `using` / `unfolding` / `from` / `with`
- [ ] `next` / `{ ... }` / `note`

---

## Tier 3 — 逻辑基础设施 🟡 规划中

| 模块 | 行数估计 | 对应 Isabelle |
|------|---------|---------------|
| ✅ `core/proofterm.rs` | ~2,000 | `proofterm.ML` (2,248) — 可检查的证明项 |
| ✅ `core/conjunction.rs` | ~300 | `conjunction.ML` — `A &&& B` |
| ✅ `core/bires.rs` | ~400 | `bires.ML` — 双向消解 |
| ✅ `core/net.rs` | ~350 | `net.ML` — 判别网 |
| ✅ `core/consts.rs` | ~400 | `consts.ML` (420) — 多态常量 |
| `core/defs.rs` | ~300 | `defs.ML` — 定义管理 |
| ✅ `core/facts.rs` | ~350 | `facts.ML` — 命名定理集 |
| ✅ `core/axclass.rs` | ~450 | `axclass.ML` (481) — 类型类 |
| ✅ `core/global_theory.rs` | ~400 | `global_theory.ML` (419) |

---

## Tier 4 — 语法系统 🟢 规划中

| 模块 | 行数估计 | 对应 Isabelle |
|------|---------|---------------|
| ✅ `isar/token.rs` | ~436 | Isabelle 符号词法分析 |
| `syntax/parser.rs` | ~700 | Earley 解析器 |
| `syntax/ast.rs` | ~400 | 抽象语法树 |
| ✅ `isar/term_parser.rs` | ~160 | Parser + Pretty printer |
| `syntax/syntax_phases.rs` | ~1,000 | 语法阶段管道 |
| `general/name_space.rs` | ~700 | 分层命名空间 |
| `general/binding.rs` | ~300 | 名称绑定 |
| `general/position.rs` | ~300 | 源码位置 |

---

## Tier 5 — LSP 服务器完善 🟢 部分完成

| 功能 | 状态 |
|------|:--:|
| `initialize` / `shutdown` | ✅ |
| `textDocument/didOpen` / `didChange` / `didClose` / `didSave` | ✅ |
| `textDocument/publishDiagnostics` | ✅ |
| `textDocument/hover` | ✅ |
| `textDocument/completion` | 🚧 |
| `textDocument/definition` | 🚧 |
| `textDocument/documentSymbol` | 🚧 |
| `textDocument/semanticTokens` | ❌ |
| `$/isabelle/proofStateChanged` | 🚧 |
| `$/isabelle/commandProgress` | 🚧 |
| `isabelle/proofStep` / `isabelle/proofUndo` | ❌ |
| `isabelle/waitForChecking` | ❌ |

---

## Tier 6 — HOL 对象逻辑 🔵 未来

HOL (Higher-Order Logic) 是 Isabelle 最常用的对象逻辑。🚧 已启动 — `hol/hol_theory.rs` 定义了 bool, Trueprop, 连接词和量词。

### HOL 核心 (~20,000 行所需)

```
hol/
├── hol_types.rs    — bool, nat, list, set, 'a option, 'a × 'b, ...
├── hol_consts.rs   — True, False, ∧, ∨, ⟶, ¬, ∀, ∃, =, THE, ...
├── hol_axioms.rs   — refl, subst, ext, select, Infinity
├── hol_derived.rs  — 派生规则 (ccontr, classical, ...)
├── nat.rs          — 自然数理论
├── set.rs          — 集合论
├── list.rs         — 列表理论
└── ...
```

### 所需工具 (~10,000 行)

```
tools/
├── argo.rs         — 线性算术求解器
├── simp.rs         — HOL 化简器
├── blast.rs        — 表aux证明
├── auto.rs         — 自动化证明
├── sledgehammer.rs — 外部 ATP 集成 (未来)
└── codegen.rs      — 代码生成 (HOL → SML/OCaml/Haskell/Scala)
```

---

## Tier 7 — 生产就绪 ⚪ 远期

- [ ] 并发执行（tokio async）
- [ ] Per-file worker 进程（Lean 4 风格 Watchdog）
- [ ] `.thy` 文件编译为二进制 artifact
- [ ] Session 管理（`ROOT` 文件解析）
- [ ] 与现有 Isabelle 理论的互操作
- [ ] QuickCheck 风格的内核测试
- [ ] 性能基准测试
