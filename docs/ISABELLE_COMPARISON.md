# Isabelle 功能对照

## 内核基础设施

| 功能 | Isabelle | Isabelle-rs | 说明 |
|------|:--:|:--:|------|
| Thm.assume | ✅ | ✅ | |
| Thm.reflexive | ✅ | ✅ | |
| Thm.symmetric | ✅ | ✅ | |
| Thm.transitive | ✅ | ✅ | |
| Thm.combination | ✅ | ✅ | 副作用检查 |
| Thm.abstraction | ✅ | ✅ | free_in 检查 |
| Thm.beta_conversion | ✅ | ✅ | |
| Thm.implies_intr | ✅ | ✅ | |
| Thm.implies_elim | ✅ | ✅ | |
| Thm.forall_intr | ✅ | ✅ | free_in 检查 |
| Thm.forall_elim | ✅ | ✅ | |
| Thm.instantiate | ✅ | ✅ | Envir → Thm |
| **原语合计** | **12** | **12** | **100% 等价** |
| Thm.bicompose | ✅ | ✅ | 核心 resolution |
| Thm.bicompose_eresolve | ✅ | ✅ | 消去匹配前提 |
| Thm.subst_premise | ✅ | ✅ | 等值替换前提 |
| **内核总计** | **15** | **15** | **100% 等价** |

## 统一与匹配

| 功能 | Isabelle | Isabelle-rs | 说明 |
|------|:--:|:--:|------|
| 一阶匹配 | ✅ | ✅ | `unify::matchers` |
| 高阶模式匹配 (HO pattern) | ✅ | ✅ | Free/Var 头 + 参数抽象 + 绑定 |
| β-归约 in norm_term | ✅ | ✅ | `(λx. body) arg → body[x:=arg]` |

## Tactic & Method 层

| 功能 | Isabelle | Isabelle-rs | 说明 |
|------|:--:|:--:|------|
| Tactic AST (All/No/Assume/Resolve/...) | ✅ | ✅ | 8 tactics + 7 tacticals |
| assume_tac | ✅ | ✅ | bicompose 实现 |
| resolve_tac | ✅ | ✅ | bicompose 实现 |
| eresolve_tac | ✅ | ✅ | bicompose_eresolve 实现 |
| dresolve_tac | ✅ | ✅ | make_elim + eresolve |
| simp_tac | ✅ | ✅ | rewrite_deep + subst_premise |

### Method 枚举

| Method | Isabelle | Isabelle-rs | 说明 |
|--------|:--:|:--:|------|
| `assumption` / `.` | ✅ | ✅ | |
| `rule` / `intro` | ✅ | ✅ | |
| `erule` | ✅ | ✅ | |
| `drule` | ✅ | ✅ | |
| `frule` | ✅ | ✅ | |
| `simp` | ✅ | ✅ | rewrite_deep + add:/only:/del: |
| `auto` | ✅ | ✅ | auto↔blast↔simp fallback |
| `blast` | ✅ | ✅ | +symmetry +order_antisym +dresolve |
| `unfold thms` | ✅ | ✅ | |
| `fold thms` | ✅ | ✅ | |
| `insert thms` | ✅ | ✅ | |
| `induct x` | ✅ | ✅ | HO 匹配 + resolve_tac + 子目标求解 |
| `cases x` | ✅ | ✅ | 构造子分析 |
| `subst` | ✅ | ✅ | (asm) 模式 + 定理驱动 |
| `fact` | ✅ | ✅ | 按名查找定理 |
| `arith` | ✅ | 🟡 | 基础算术规则 |
| `skip` | ✅ | ✅ | |
| `fail` | ✅ | ✅ | |

### 方法参数解析

| 功能 | Isabelle | Isabelle-rs |
|------|:--:|:--:|
| `rule name [OF ...]` | ✅ | ✅ |
| `intro:`/`elim:`/`dest:` | ✅ | ✅ |
| `unfold def1 def2` | ✅ | ✅ |
| `simp add:`/`only:`/`del:` | ✅ | ✅ |
| `by(method)` (no space) | ✅ | ✅ |

## 重写引擎

| 功能 | Isabelle | Isabelle-rs |
|------|:--:|:--:|
| RewriteRule | ✅ | ✅ |
| 顶层重写 (rewrite) | ✅ | ✅ |
| 深层重写 (rewrite_deep) | ✅ | ✅ |
| 等值证明构造 | ✅ | ✅ |
| β-归约 | ✅ | ✅ |
| Conversion 组合子 | ✅ | ✅ |
| 条件重写 | ✅ | ✅ (前提提取 + 深度3验证) |

## 定理加载

| 功能 | Isabelle | Isabelle-rs |
|------|:--:|:--:|
| 内联引理 `lemma name: "stmt"` | ✅ | ✅ |
| 多行 assumes/shows | ✅ | ✅ |
| fixes/obtains | ✅ | ✅ |
| 匿名引理 | ✅ | ✅ |
| Cartouche `\<open>...\<close>` | ✅ | ✅ |
| Locale 引理 `(in loc)` | ✅ | ✅ |
| OF combinator | ✅ | ✅ |
| `lemmas` 命令 | ✅ | ✅ (600+ aliases) |
| `datatype` | ✅ | ✅ (5 类合成规则) |
| `old_rep_datatype` | ✅ | ✅ |
| `primrec`/`fun` | ✅ | ✅ (simp 规则生成) |
| `class`/`fixes` | ✅ | ✅ (常量提取) |
| `typedef` | ✅ | 🟡 |
| `inductive`/`coinductive` | ✅ | ❌ |

## Isar 引擎

| 功能 | Isabelle | Isabelle-rs |
|------|:--:|:--:|
| `proof` / `qed` | ✅ | ✅ |
| `fix` / `assume` | ✅ | ✅ |
| `have` / `show` | ✅ | ✅ |
| `hence` / `thus` | ✅ | ✅ |
| `case` / `next` | ✅ | ✅ |
| `then` / `from` / `with` | ✅ | ✅ |
| `?case` / `?thesis` | ✅ | ✅ |
| `{...}` 嵌套块 | ✅ | ✅ |
| `obtain` | ✅ | ❌ |
| `note` / `let` | ✅ | ❌ |

## 理论管理

| 功能 | Isabelle | Isabelle-rs |
|------|:--:|:--:|
| 理论 DAG 拓扑排序 | ✅ | ✅ (115 nodes, 0 cycles) |
| 全库 DAG 扫描 | ✅ | ✅ (1,395 nodes from 1,472 files) |
| 增量定理数据库 | ✅ | ✅ |
| 带进度加载 | — | ✅ |

## 定理覆盖

| 指标 | 数值 |
|------|------|
| 加载 HOL .thy 文件 | 115 / 1,473 |
| 定理总数 | 15,804 |
| by-name 索引 | 15,395 |
| 基准验证率 | 60.0% (75/125 sampled) |

## 待实现（按 ROI 排序）

| 功能 | 阶段 | 优先级 | 预计 | 验证率提升 |
|------|:--:|:--:|------|:--:|
| `arith` 完整算术求解 | Phase 7 | 🟡 | 1-2周 | +80 |
| `obtain` 存在消除 | Phase 6.4 | 🟡 | 2-3天 | +40 |
| `inductive`/`coinductive` 解析 | Phase 4.5 | 🔵 | 1-2天 | +30 |
| 全 HOL 库加载 (1,473 文件) | Phase 7.1 | 🔵 | 1-2周 | — |
| 并行验证 (rayon) | Phase 7.2 | 🔵 | 1周 | — |
| LSP 完善 + `cargo publish` | Phase 7 | 🔵 | 2-3周 | — |
| 多逻辑 (FOL/ZF/CTT) | Phase 8 | ⚪ | 3-4周 | — |
| 工具链 (Sledgehammer/Codegen) | Phase 8 | ⚪ | 3-4周 | — |
