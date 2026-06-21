# isabelle-rs vs Isabelle 完整差距分析 v6.0

> v2.2.0 | 2026-06-21 | **T3 信任足迹达成** | Tier2 真实证明率 85.8%
> **总体覆盖: 核心内核 ~85%, 整体 ~25%** (诚实下调:旧 ~40% 高估)
> **isabelle-rs**: ~55K Rust LOC (124+ .rs) | **Isabelle**: 316,984 ML + 975,918 thy + 87,721 scala = ~138 万行

---

## 零、战略定位与可信路线

**Isabelle 本体精确规模**(实测 isabelle-source):

| 类别 | 文件 | 行数 | 性质 |
|------|:--:|--:|------|
| `.ML` (引擎+工具) | 758 | 316,984 | 需移植的核心 |
| `.thy` (理论库) | 1,843 | 975,918 | **97% 是应用,无需复刻** |
| `.scala` (PIDE/IDE) | 356 | 87,721 | Rust 替代 |

**关键认知:差距 ≠ 行数。** 97.6 万行 `.thy` 中,Analysis(17.8万)、Algebra(3.7万)、
Nominal/Bali/Auth/MicroJava(~10万)等都是 30 年积累的**应用成果**,不是引擎。真正要对标的
"引擎"是 Pure 内核(2.7万 ML)+ Isar(1.9万)+ HOL Tools(18.4万)。

**战略:放弃追广度,押注「内核可信 + 片段深度」。** 见 [TRUST.md](TRUST.md)。

### 可信度 (de Bruijn T1-T4)

| 性质 | 含义 | 达成度 |
|:--:|------|:--:|
| T1 不可伪造 | Thm 仅经内核规则构造 | 🟡 ~90% |
| T2 规则可靠 | 15 规则强制边条件 | 🟠 进行中 |
| **T3 信任可追溯** | oracle 足迹随推导传播 | ✅ **已达成** |
| T4 独立复检 | 证明项重放 (de Bruijn) | 🔴 ~30% |

---

## 总体对比

| 维度 | Isabelle | isabelle-rs | 覆盖度 |
|------|:--:|:--:|:--:|
| Pure 内核 (ML) | 60 files, ~27K LOC | 34 Rust files, ~14,500 LOC | **~55%** |
| Pure/Isar (ML) | 41 files | 18 Rust files, ~12,300 LOC | **~40%** |
| HOL Tools (ML) | 258 files, ~184K LOC | 18 Rust files, ~14,000 LOC | **~8%** |
| HOL .thy files | 1,473 | 97 verified (**真证明 85.8%, 3277/3821**), ~30 accept_all | **~7%** |
| Scala (PIDE/Build) | ~88K LOC | 0 (Rust 替代) | N/A |
| 其他逻辑 (FOL/ZF/...) | 8 logics | 0 | **0%** |

### 代码规模对比

| 组件 | 必须移植 (ML) | isabelle-rs (Rust) | 覆盖度 |
|------|:--:|:--:|:--:|
| Pure 内核 | ~22,000 | ~14,500 | ~65% |
| Pure/Isar | ~18,700 | ~12,300 | ~65% |
| Pure/Syntax | ~5,600 | ~1,000 | ~18% |
| Pure/Thy + PIDE + Tools | ~12,200 | ~4,600 | ~38% |
| **Pure 合计** | **~58,500** | **~32,400** | **~55%** |
| Provers | ~7,300 | ~2,300 | ~32% |
| HOL Tools | ~126,400 | ~14,000 | ~11% |

---

## 一、Pure 内核 (60 ML files → 34 Rust files)

### ✅ 已完成 (34/60)

| Isabelle ML | isabelle-rs Rust | 功能 |
|-------------|-----------------|------|
| `thm.ML` (2752行) | `thm.rs` (1527行) | LCF 内核 15 原语规则 + tpairs/shyps |
| `logic.ML` | `logic.rs` (171行) | Pure 元逻辑 (==>/!!/==) |
| `term.ML` | `term.rs` (334行) | λ 项 (Const/Free/Var/Bound/Abs/App) |
| `type.ML` | `types.rs` (427行) | 类型系统 (Type/TFree/TVar/Sort) |
| `sorts.ML` | `sorts.rs` (314行) | Sort algebra (class_le/sort_le/of_sort) |
| `sign.ML` | `sign.rs` (454行) | 签名 (certify_term/prop) |
| `theory.ML` | `theory.rs` | 理论 (declarations/axioms/theorems) |
| `envir.ML` | `envir.rs` | 合一环境 (Envir) |
| `unify.ML` (668行) | `unify.rs` (519行) | 高阶合一 (HO pattern + flex-rigid) |
| `tactic.ML` + `tactical.ML` | `tactic.rs` (511行) | 策略与策略组合子 |
| `net.ML` | `net.rs` (254行) | Discrimination Nets |
| `pattern.ML` | `pattern.rs` | 模式匹配 |
| `term_subst.ML` | `term_subst.rs` | 项替换 (instantiate/generalize) |
| `term_ord.ML` | `term_ord.rs` | 项排序 |
| `name.ML` | `name.rs` | 变量名管理 |
| `morphism.ML` | `morphism.rs` (545行) | 定理传输 |
| `conv.ML` | `conv.rs` (611行) | 结构化转换 (14 组合子) |
| `proofterm.ML` | `proofterm.rs` (356行) | 证明项 + ProofBody + check_proof |
| `type_infer.ML` | `type_infer.rs` (466行) | Hindley-Milner 类型推断 |
| `context.ML` (900行) | `context.rs` | Theory/Proof 上下文切换 |
| `simplifier.ML` | `simplifier.rs` (548行) | 简化器 (rewrite/rewrite_deep) |
| `drule.ML` (839行) | `drule.rs` (151行) | 派生规则 |
| `bires.ML` | `bires.rs` | 双向消解 |
| `more_thm.ML` | `more_thm.rs` | 定理扩展操作 |
| `conjunction.ML` | `conjunction.rs` | 合取操作 |
| `consts.ML` | `consts.rs` | 常量声明 |
| `global_theory.ML` | `global_theory.rs` | 全局理论 |
| `facts.ML` | `facts.rs` | 事实数据库 |
| `pure_thy.ML` | `hol_loader.rs` (4533行) | Pure 理论引导 (HOL 加载) |
| 其他 | `arena.rs`, `error.rs` (127行), `variable.rs` | 内存管理, 错误类型, 变量 |

### 🟡 部分完成 (需要增强)

| Isabelle ML | 状态 | 缺失内容 |
|-------------|:--:|------|
| `axclass.ML` (600行) | 🟡 | `axclass.rs` 仅 15% 完成度, 类型类代数基本为空 |
| `variable.ML` | 🟡 | `variable.rs` 仅基础实现 |
| `search.ML` | 🟡 | 深度优先/BEST_FIRST 在 method.rs 中实现，但缺少完整的搜索策略框架 |

### ❌ 未实现 (~15/60)

| Isabelle ML | 功能 | 优先级 |
|-------------|------|:--:|
| `assumption.ML` | 假设管理策略 | P1 |
| `cterm_items.ML` | CTerm 元数据 | P2 |
| `goal_display.ML` | 目标显示 | P2 |
| `library.ML` | 工具函数 | P3 |
| `more_pattern.ML` | 高级模式匹配 | P2 |
| `more_unify.ML` | 高级合一 | P2 |
| `par_tactical.ML` | 并行策略 | P3 |
| `pure_syn.ML` | Pure 语法 | P2 |
| `skip_proof.ML` | 跳过证明 | P2 |
| `soft_type_system.ML` | 软类型系统 | P3 |
| `term_items.ML` | 项元数据 | P3 |
| `term_sharing.ML` | 项共享/记忆化 | P3 |
| `term_xml.ML` | XML 序列化 | P3 |
| `thm_deps.ML` | 定理依赖 | P2 |
| `thm_name.ML` | 定理命名 | P2 |

---

## 二、Pure/Isar (41 ML files → 18 Rust files)

### ✅ 已完成 (18/41)

| Isabelle ML | isabelle-rs Rust | 行数 |
|-------------|-----------------|:--:|
| `proof.ML` (1000行) | `proof.rs` + `proof_state.rs` | 2187 |
| `method.ML` (900行) | `method.rs` | 3866 |
| `keyword.ML` | `keyword.rs` | 602 |
| `outer_syntax.ML` | `outer_syntax.rs` | 423 |
| `token.ML` | `token.rs` | 667 |
| `parse.ML` | `parse.rs` + `term_parser.rs` | 1329 |
| `locale.ML` (845行) | `locale.rs` | 504 |
| `local_theory.ML` | `local_theory.rs` | 262 |
| `calculation.ML` (260行) | `proof.rs` | (内嵌) |
| `obtain.ML` (400行) | `proof.rs` | (内嵌) |
| `toplevel.ML` | `toplevel.rs` | 411 |
| `class.ML` + `class_declaration.ML` | `class_system.rs` | 292 |
| `interpretation.ML` | `locale.rs` | (内嵌) |
| `attrib.ML` | `attrib.rs` | 307 |
| `rule_cases.ML` | `rule_cases.rs` | 246 |
| `spec.ML` | `spec.rs` | 291 |
| `diag.ML` | `diag.rs` + `hol_diag.rs` | 96 |
| `proof_context.ML` | `proof_context.rs` | 290 |

### 🟡 部分完成

| 功能 | 状态 | 说明 |
|------|:--:|------|
| 属性系统 | 🟡 | attrib.rs 存在，但 [simp]/[intro!]/[elim!] 集成不完整 |
| 证明上下文 | 🟡 | proof_context.rs 存在，但功能有限 |
| 规范解析 | 🟡 | spec.rs 存在，但不完整 |

### ❌ 未实现 (~20/41)

| Isabelle ML | 功能 | 优先级 |
|-------------|------|:--:|
| `args.ML` | 方法参数解析 | P1 |
| `auto_bind.ML` | 自动绑定 | P2 |
| `bundle.ML` | 捆绑包 | P3 |
| `code.ML` | 代码生成 (Isar 层) | P3 |
| `context_rules.ML` | 上下文规则 | P2 |
| `element.ML` | Locale 元素 | P2 |
| `entity.ML` | 实体管理 | P3 |
| `experiment.ML` | 实验 | P3 |
| `expression.ML` | Locale 表达式 | P2 |
| `generic_target.ML` | 通用目标 | P2 |
| `isar_cmd.ML` | Isar 命令实现 | P2 |
| `local_defs.ML` | 局部定义 | P1 |
| `named_target.ML` | 命名目标 | P2 |
| `object_logic.ML` | 对象逻辑 | P2 |
| `overloading.ML` | 重载 | P2 |
| `parse_spec.ML` | 规范解析 | P1 |
| `proof_display.ML` | 证明显示 | P3 |
| `proof_node.ML` | 证明节点 | P3 |
| `spec_rules.ML` | 规范规则 | P2 |
| `specification.ML` | 规范 | P1 |
| `subgoal.ML` | 子目标 | P2 |
| `target_context.ML` | 目标上下文 | P2 |
| `typedecl.ML` | 类型声明 | P1 |

---

## 三、HOL Tools (258 ML files → 18 Rust files)

### 已有实现

| 工具 | isabelle-rs | 行数 | 完成度 | 缺失 |
|------|:---:|:--:|:--:|------|
| **Theory Loading** | hol_loader.rs + theory_graph.rs | 5512 | 70% | 完整属性分类, 更复杂的 .thy 结构 |
| **Method System** | method.rs | 3866 | 80% | 方法组合子, 更完整的方法参数解析 |
| **Metis** | metis.rs | 2305 | 60% | 与 method 系统集成 (目前 metis→auto fallback) |
| **Ctr_Sugar** | ctr_sugar.rs | 1926 | 65% | 完整 Ctr_Sugar 插件, record 集成 |
| **BNF Lfp/Gfp** | bnf_lfp.rs | 1837 | 70% | 完整 BNF 公理, fp_sugar, bnf_comp |
| **Transfer/Lifting** | transfer.rs | 1266 | 50% | 完整商类型, 自动 relator 派生 |
| **HOL Simplifier** | simp.rs | 1135 | 65% | 更复杂的条件重写策略 |
| **LinArith** | linarith.rs | 1554 | 60% | 非线性算术, presburger |
| **Thy Header** | thy_header.rs | 835 | 80% | imports 关键字处理 |
| **Locale** | locale.rs | 504 | 40% | 完整 locale 表达式 |
| **Primcorec** | primcorec.rs | 468 | 35% | 完整 corec 检查, 互余归纳 |
| **Sledgehammer** | sledgehammer.rs | 362 | 30% | ATP 调用, 事实选择, minimizer |
| **Reconstruct** | reconstruct.rs | 452 | 40% | 完整 TSTP→LCF 重放 |
| **Inductive** | inductive.rs | 394 | 35% | 完整 intro/elim/induct 规则生成 |
| **Function** | function.rs | 352 | 25% | fun/function 完整处理 |
| **Class System** | class_system.rs | 292 | 30% | 完整类型类推理 |
| **Typedef/Record** | typedef_record.rs | 416 | 45% | 完整 record 包 |
| **TPTP** | tptp.rs | 239 | 35% | TFF0/THF 格式 |

### ❌ 完全缺失

| 工具 | ML 规模 | 功能 | 优先级 |
|------|:--:|------|:--:|
| **Code Generator** | ~8K | HOL → SML/OCaml/Haskell | P3 |
| **ATP systems** | ~10K | E/Vampire/Zipperposition 深度集成 | P1 |
| **Meson** | ~3K | 经典逻辑证明 | P2 |
| **Argo** | ~5K | 线性算术 | P2 |
| **SMT** | ~8K | SMT solver 集成 | P2 |
| **Nitpick** | ~10K | 反例查找 | P3 |
| **Quickcheck** | ~3K | 随机测试 | P3 |
| **Quotient** | ~2K | 商类型 | P2 |
| **Predicate_Compile** | ~4K | 谓词编译 | P3 |
| **Mirabelle** | ~2K | 自动化测试 | P3 |
| **Old_Datatype** | ~3K | 旧 datatype 包 | P3 |
| **Nunchaku** | ~1K | 反例查找 | P3 |
| **Qelim** | ~1K | 量词消去 | P2 |
| **Eisbach** | ~2K | 证明方法定义语言 | P3 |

---

## 四、基础设施

### ✅ 已完成

| 组件 | 行数 | 完成度 |
|------|:--:|:--:|
| LSP Server (8 handlers) | ~1500 | 70% |
| Pretty Printer (20+ operators) | ~1000 | 75% |
| Session Management | ~650 | 50% |
| WASM Runtime | ~500 | 40% |
| Document Model | ~560 | 30% |
| Fleche Engine | ~330 | 20% |
| Kernel Arena/Data | ~1270 | 50% |
| CLI (isabelle-build) | ~140 | 60% |

---

## 五、验证覆盖

| Tier | 文件数 | 状态 |
|------|:--:|------|
| Tier 0: Core (5 files) | Bool, HOL, Fun, Orderings, Set | ✅ 通过 |
| Tier 2: Extended (15 files) | Product_Type, Sum_Type, Option, Lattices, Groups, Rings, Fields, Relation, Equiv_Relations, Map, Finite_Set, Num, Power, Complete_Lattices | ⚠️ accept_all 模式 |
| Tier 3: Broad (16 files) | Set_Interval, Big_Operators, OrderedGroup, OrderedRing, Rings, Nat_Numeral, Int_Numeral, Divides, Parity, GCD, Sqrt, List_Pred, String, Char_ord, Enum, Quickcheck_Random | ⚠️ accept_all 模式 |
| Full library | 1,473 files | ❌ 未测试 |

---

## 六、已知问题

| 问题 | 严重度 | 位置 | 状态 |
|------|:--:|------|:--:|
| `hologic.ML` 缺失 — HOL 项操作散落各处 | 🔴 P0 | 25+ files | **下一步: Phase 49** |
| `simpdata.ML` 缺失 — simp 规则集不完整 | 🔴 P0 | method.rs, linarith.rs | **下一步: Phase 50** |
| `args.ML` 缺失 — 方法参数解析 | 🔴 P0 | method.rs | **下一步: Phase 51** |
| `metis` 方法 → `auto` fallback | 🟡 P1 | method.rs | 待集成 |
| test_batch_scan_theories 256MB 栈溢出 | 🟡 P1 | theory/loader.rs | 根因待定 |
| 属性系统集成不完整 | 🟠 P1 | attrib.rs → hol_loader.rs | 待完成 |
| axclass.rs 仅 15% 完成 | 🟡 P2 | core/axclass.rs, hol/axclass.rs | 待完成 |
| `specification.ML` / `defs.ML` / `typedecl.ML` 缺失 | 🟠 P1 | — | Phase 52-54 |
| ~~auto.rs/blast.rs 空壳桩~~ | — | — | ✅ **v1.8.0 已删除** |
| ~~kernel/ 与 core/ 功能重叠~~ | — | — | ✅ **v1.8.0 已合并** |
| ~~test_verify_all_core_files 栈溢出~~ | — | — | ✅ **v1.8.1 已修复** |
| ~~prove_condition 设计缺陷~~ | — | — | ✅ **v1.8.1 已修复** |

---

## 七、证明引擎 — 27 方法明细

| 方法 | 状态 | 说明 |
|------|:--:|------|
| auto | ✅ | 完整实现 (method.rs) |
| blast | ✅ | 完整实现 (method.rs) |
| fast | ✅ | DFS + iterative deepening (0..8) |
| best | ✅ | BEST_FIRST worklist |
| safe | ✅ | 三阶段 safe rules |
| step | ✅ | safe exhaustive + 1 unsafe |
| depth | ✅ | bounded DFS |
| dup_step | ✅ | step + duplication |
| simp | ✅ | HOL 条件重写 + Solver 插件 |
| iprover | ✅ | intro/elim/dest 解析 |
| subst | ✅ | 等式替换 |
| unfold/fold | ✅ | 定义展开/折叠 |
| insert/erule/drule/frule | ✅ | 规则应用 |
| assumption/rule | ✅ | 基本方法 |
| coinduct/coinduction | ✅ | 余归纳规则 |
| try/try0 | ✅ | 多方法尝试 |
| meson | ✅ | Model elimination prover |
| skip/fail | ✅ | 控制流 |
| induct/cases | ⚠️ | 可用, 但部分规则查找不完整 |
| metis | ⚠️ | metis.rs 存在, 但 dispatch → auto fallback |
| arith | ⚠️ | FM 线性算术, presburger 部分 |

## 八、理论命令与 Isar 语言

### 理论命令

| 命令 | 状态 | 命令 | 状态 |
|------|:--:|------|:--:|
| lemma/theorem | ✅ | locale | ⚠️ |
| class | ⚠️ | subclass | ⚠️ |
| instance | ⚠️ | interpretation | ⚠️ |
| definition | ✅ | fun/function | ⚠️ |
| inductive/coinductive | ⚠️ | datatype/codatatype | ✅ |
| primrec | ⚠️ | typedef/record | ⚠️ |

### Isar 语言

| 命令 | 状态 | 命令 | 状态 |
|------|:--:|------|:--:|
| proof/qed/{/} | ✅ | have/show | ✅ |
| fix/assume | ✅ | obtain | ✅ |
| apply/by/done | ✅ | note/let | ✅ |
| also/finally | ✅ | moreover/ultimately | ✅ |
| then/hence/thus | ✅ | from/with/using | ✅ |
| case/next | ✅ | defer/prefer | ✅ |
| sorry | ✅ | interpretation | ⚠️ |

## 九、工具链

| 工具 | 状态 | 说明 |
|------|:--:|------|
| Pretty Printer | ✅ | 20+ operators, 7 levels |
| TPTP Export | ✅ | FOF format |
| Session Builder | ⚠️ | DAG + batch compile, 有栈溢出 |
| CLI | ✅ | isabelle-build |
| LSP | ⚠️ | 8 handlers, 功能有限 |
| WASM | ⚠️ | 基础 runtime |

---

## 十、总结：差距量化

```
isabelle-rs v2.2.0                   Isabelle 完整分布

LCF 内核 (15 ops + tpairs/shyps)  ██████████████████   ~90%  (T2 加固中)
信任足迹 T3 (oracle 追踪)         ████████████████████ 100%  ✅ 新增
Isar 状态机 (三模式)             ████████████████████ 100%
Isar 命令 (30+ 种)              ██████████████████    90%
经典推理器 (5 策略)             █████████████████     85%
真实证明率 (Tier2 实测)         █████████████████     85.8% (3277/3821)
Pretty Printer                  ███████████████       75%
Method 引擎 (27 方法)           ██████████████████    90%
理论加载 Pipeline                █████████████████     85%
HOL Tools (基础)                █████████████         65%
BNF / Ctr_Sugar                 ███████████           55%
Transfer/Lifting / Metis        ██████████            50%
属性系统                         ██████                30%
Sledgehammer / CodeGen / SMT    ██                    ~5% (战略上不追)
全库验证 (1,473 files)          █                     ~7%

核心内核覆盖:                 █████████████████    ~85%
总体功能覆盖:                 █████                    ~25%
```

### v2.2.0 优先级排序 (可信优先)

| 优先级 | 任务 | 影响 |
|:--:|------|------|
| 🥇 P0 | **T2 内核加固** — tpairs/shyps 传播 + alpha_eq 收紧 + combination 类型检查 | LCF 可信性,每条配回归测试 |
| 🥈 P0 | **T1 后门收口** — hol_rules/hol_consts 假定理制造机降级或标记 oracle | 杜绝伪造定理 |
| 🥉 P1 | **缩小 544 admitted** — Rings(80)+Lattices_Big(63)+Complete_Lattices(25) | 真实证明率 85.8%→95%+ |
| P1 | named_theorems 重写集接全 (field_simps/algebra_simps) | 代数化简软肋根因 |
| P2 | T4 独立证明项复检 — proofterm.rs check_proof 补完并接通 | de Bruijn 黄金标准 (北极星) |
| P3 | ~~Sledgehammer/CodeGen/SMT~~ | **战略上不追** — 无底洞,非差异化价值 |

### v1.9.0 优先级排序 (历史,按影响力)

| 优先级 | 任务 | 工作量 | 影响 |
|:--:|------|:--:|------|
| 🥇 P0 | **hologic.ML → hologic.rs** | 3-5 days | HOL 项操作统一, 25+ 文件受益 |
| 🥈 P0 | **simpdata.ML → simpdata.rs** | 2-3 days | `by simp` 成功率 +20-40% |
| 🥉 P0 | **args.ML 解析完善** | 2-3 days | `simp add:`/`induct rule:` 语法 |
| P1 | specification.ML 基础设施 | 3-5 days | 解锁 `fun`/`function`/`inductive` |
| P1 | defs.ML 定义一致性检查 | 2-3 days | LCF 可信性 |
| P1 | typedecl.ML + local_defs.ML | 2-3 days | 补全 Isar 语法 |
| P2 | Metis 真正集成 | 3-5 days | 一阶逻辑证明 |
| P2 | 属性系统完成 | 2-3 days | [simp]/[intro!]/[elim!] 全 pipeline |
| P2 | proof_context.ML 增强 | 3-5 days | 完整 Isar 上下文 |
| P3 | Code Generator | 4-8 weeks | HOL → SML/OCaml/Haskell |
| P3 | SMT 集成 | 2-4 weeks | Z3/CVC4 |
