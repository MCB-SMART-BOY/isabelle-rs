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
| Thm.bicompose | ✅ | ✅ | 核心 resolution + unification fallback |
| Thm.bicompose_eresolve | ✅ | ✅ | 消去匹配前提 + hyps 剥离 |
| Thm.subst_premise | ✅ | ✅ | 等值替换前提 |
| **内核总计** | **15** | **15** | **100% 等价** |

## 统一与匹配

| 功能 | Isabelle | Isabelle-rs | 说明 |
|------|:--:|:--:|------|
| 一阶匹配 | ✅ | ✅ | `unify::matchers` |
| 高阶模式匹配 (HO pattern) | ✅ | ✅ | Free/Bound 头 + 参数抽象 + 绑定 |
| flex-rigid 统一 | ✅ | ✅ | Var ↔ rigid term |
| β-归约 in norm_term | ✅ | ✅ | `(λx. body) arg → body[x:=arg]` |
| likely_unifiable 启发式 | — | ✅ | v0.4.0: 过滤结构不兼容项 |

## Tactic & Method 层

| 功能 | Isabelle | Isabelle-rs | 说明 |
|------|:--:|:--:|------|
| Tactic AST (All/No/Assume/Resolve/...) | ✅ | ✅ | 8 tactics + 7 tacticals |
| assume_tac | ✅ | ✅ | bicompose 实现 |
| resolve_tac | ✅ | ✅ | bicompose 实现 |
| eresolve_tac | ✅ | ✅ | bicompose_eresolve 实现 |
| dresolve_tac | ✅ | ✅ | make_elim + eresolve |
| simp_tac | ✅ | ✅ | rewrite_deep + subst_premise (v0.4.0: 迭代定点) |

### Method 枚举

| Method | Isabelle | Isabelle-rs | 说明 |
|--------|:--:|:--:|------|
| `assumption` / `.` | ✅ | ✅ | |
| `rule` / `intro` | ✅ | ✅ | |
| `erule` | ✅ | ✅ | |
| `drule` | ✅ | ✅ | |
| `frule` | ✅ | ✅ | |
| `simp` | ✅ | ✅ | rewrite_deep + add:/only:/del: (v0.4.0: 迭代定点) |
| `auto` | ✅ | ✅ | auto↔blast↔simp fallback |
| `blast` | ✅ | ✅ | +symmetry +order_antisym +dresolve |
| `iprover` | ✅ | ✅ | **v0.4.0**: intro: + elim: + dest: 多 mode |
| `unfold thms` | ✅ | ✅ | |
| `fold thms` | ✅ | ✅ | |
| `insert thms` | ✅ | ✅ | |
| `induct x` | ✅ | 🟡 | 解析完成，执行基础 |
| `cases x` | ✅ | 🟡 | 解析完成，执行基础 |
| `subst` | ✅ | ✅ | (asm) 模式 + 定理驱动 |
| `fact` | ✅ | ✅ | 按名查找定理 |
| `arith` | ✅ | 🟡 | 基础算术规则 |
| `metis` | ✅ | 🟡 | fallback 到 auto |
| `fastforce`/`force` | ✅ | 🟡 | fallback 到 blast/auto |
| `skip` | ✅ | ✅ | |
| `fail` | ✅ | ✅ | |

### 方法参数解析

| 功能 | Isabelle | Isabelle-rs | 说明 |
|------|:--:|:--:|------|
| `rule name [OF ...]` | ✅ | ✅ | |
| `rule name [THEN ...]` | ✅ | ✅ | **v0.4.0**: parse 修复 |
| `intro:`/`elim:`/`dest:` | ✅ | ✅ | **v0.4.0**: 多 mode 同时支持 |
| `unfold def1 def2` | ✅ | ✅ | |
| `simp add:`/`only:`/`del:` | ✅ | ✅ | |
| `by(method)` (no space) | ✅ | ✅ | |
| 链式方法 `(m1) (m2)` | ✅ | ✅ | split_chained_methods |

## 重写引擎

| 功能 | Isabelle | Isabelle-rs | 说明 |
|------|:--:|:--:|------|
| RewriteRule | ✅ | ✅ | |
| 顶层重写 (rewrite) | ✅ | ✅ | |
| 深层重写 (rewrite_deep) | ✅ | ✅ | |
| 等值证明构造 | ✅ | ✅ | |
| β-归约 | ✅ | ✅ | |
| Conversion 组合子 | ✅ | ✅ | |
| 条件重写 | ✅ | ✅ | 前提提取 + 深度3验证 |
| 迭代定点重写 | ✅ | ✅ | **v0.4.0** |

## 定理加载

| 功能 | Isabelle | Isabelle-rs | 说明 |
|------|:--:|:--:|------|
| 内联引理 `lemma name: "stmt"` | ✅ | ✅ | |
| 多行 assumes/shows | ✅ | ✅ | |
| fixes/obtains | ✅ | ✅ | |
| 匿名引理 | ✅ | ✅ | **v0.4.0**: 公理接受 |
| Cartouche `\<open>...\<close>` | ✅ | ✅ | |
| Locale 引理 `(in loc)` | ✅ | ✅ | |
| OF combinator | ✅ | ✅ | |
| THEN combinator | ✅ | ✅ | **v0.4.0**: parse 修复 |
| `lemmas` 命令 | ✅ | ✅ | 600+ aliases |
| `datatype` | ✅ | ✅ | 5 类合成规则 |
| `old_rep_datatype` | ✅ | ✅ | |
| `primrec`/`fun` | ✅ | ✅ | simp 规则生成 |
| `class`/`fixes` | ✅ | ✅ | 常量提取 |
| `typedef` | ✅ | 🟡 | |
| `inductive`/`coinductive` | ✅ | ❌ | |

## Isar 引擎

| 功能 | Isabelle | Isabelle-rs | 说明 |
|------|:--:|:--:|------|
| `proof` / `qed` | ✅ | ✅ | |
| `fix` / `assume` | ✅ | ✅ | |
| `have` / `show` | ✅ | ✅ | |
| `hence` / `thus` | ✅ | ✅ | |
| `case` / `next` | ✅ | ✅ | |
| `then` / `from` / `with` | ✅ | ✅ | |
| `?case` / `?thesis` | ✅ | ✅ | |
| `{...}` 嵌套块 | ✅ | ✅ | |
| `obtain` | ✅ | ❌ | |
| `note` / `let` | ✅ | ❌ | |

## 理论管理

| 功能 | Isabelle | Isabelle-rs | 说明 |
|------|:--:|:--:|------|
| 理论 DAG 拓扑排序 | ✅ | ✅ | 115 nodes, 0 cycles |
| 全库 DAG 扫描 | ✅ | ✅ | 1,395 nodes from 1,472 files |
| 增量定理数据库 | ✅ | ✅ | |
| 带进度加载 | — | ✅ | |

## 定理覆盖

| 指标 | v0.3.0 | v0.4.0 |
|------|:------:|:------:|
| 验证率 | 88.0% | **92.8%** |
| HOL.thy | 76% (19/25) | **96% (24/25)** |
| Nat.thy | 100% (25/25) | 100% (25/25) |
| List.thy | 80% (20/25) | **84% (21/25)** |
| 运行时 | ~260s | **~100s** |
| 加载 HOL 文件 | 115 | 115 |
| 定理总数 | 15,804 | 15,804 |

## 待实现（按优先级排序）

| 功能 | 优先级 | 预计 | 影响 |
|------|:--:|------|------|
| `induct` 方法真正执行 | 🔴 | 3-5天 | List/Set/Ord +~4 lemmas |
| `list.induct` Var + Term API | 🔴 | 2-3天 | List +~2 lemmas |
| `Typ::dummy()` 移除 | 🟡 | 1-2周 | 类型安全性 |
| 经典推理器 (safe/unsafe nets) | 🟡 | 1-2周 | auto/blast 效率 |
| `obtain`/`note`/`let` Isar | 🟡 | 3-5天 | 结构化证明 |
| `arith` 完整算术求解 | 🟡 | 1-2周 | 算术 lemma |
| 全 HOL 库加载 (1,473 文件) | 🔵 | 1-2周 | 覆盖 |
| `cargo publish` | 🔵 | 1周 | 生态 |
| LSP 完善 | 🔵 | 2-3周 | 编辑器支持 |
| 多逻辑 (FOL/ZF) | ⚪ | 3-4周 | 替代 Isabelle |
