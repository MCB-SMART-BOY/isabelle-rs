# Isabelle-rs vs Isabelle 完整差距分析

> v1.2.0 | 2026-05-29

---

## 总体对比

| 维度 | Isabelle | isabelle-rs | 覆盖度 |
|------|:--:|:--:|:--:|
| Pure 内核 (ML) | 60 files, ~27K LOC | ~14K Rust LOC | **~50%** |
| Pure/Isar (ML) | 41 files | ~15 Rust files | **~35%** |
| HOL Tools (ML) | 258 files, ~126K LOC | ~8K Rust LOC | **~6%** |
| HOL .thy files | 1,473 | 20 verified | **~1.4%** |
| Scala (PIDE/Build) | ~68K LOC | 0 (Rust 替代) | N/A |
| 其他逻辑 (FOL/ZF/...) | 8 logics | 0 | **0%** |

---

## 一、Pure 内核 (60 ML files → 34 Rust files)

### ✅ 已完成 (30/60)

| Isabelle ML | isabelle-rs Rust | 功能 |
|-------------|-----------------|------|
| `thm.ML` (2752行) | `thm.rs` | LCF 内核 15 原语规则 |
| `logic.ML` | `logic.rs` | Pure 元逻辑 (==>/!!/==) |
| `term.ML` | `term.rs` | λ 项 (Const/Free/Var/Bound/Abs/App) |
| `type.ML` | `types.rs` | 类型系统 (Type/TFree/TVar/Sort) |
| `sorts.ML` | `sorts.rs` | Sort algebra (class_le/sort_le/of_sort) |
| `sign.ML` | `sign.rs` | 签名 (certify_term/prop) |
| `theory.ML` | `theory.rs` | 理论 (declarations/axioms/theorems) |
| `envir.ML` | `envir.rs` | 合一环境 (Envir) |
| `unify.ML` (668行) | `unify.rs` | 高阶合一 (HO pattern + flex-rigid) |
| `tactic.ML` + `tactical.ML` | `tactic.rs` | 策略与策略组合子 |
| `net.ML` | `net.rs` | Discrimination Nets |
| `pattern.ML` | `pattern.rs` | 模式匹配 |
| `term_subst.ML` | `term_subst.rs` | 项替换 (instantiate/generalize) |
| `term_ord.ML` | `term_ord.rs` | 项排序 |
| `name.ML` | `name.rs` | 变量名管理 |
| `morphism.ML` | `morphism.rs` | 定理传输 |
| `conv.ML` | `conv.rs` | 结构化转换 (14 组合子) |
| `proofterm.ML` | `proofterm.rs` | 证明项 + ProofBody + check_proof |
| `type_infer.ML` | `type_infer.rs` | Hindley-Milner 类型推断 |
| `context.ML` (900行) | `context.rs` | Theory/Proof 上下文切换 |
| `simplifier.ML` | `simplifier.rs` | 简化器 (rewrite/rewrite_deep) |
| `drule.ML` (839行) | `drule.rs` | 派生规则 |
| `bires.ML` | `bires.rs` | 双向消解 |
| `more_thm.ML` | `more_thm.rs` | 定理扩展操作 |
| `conjunction.ML` | `conjunction.rs` | 合取操作 |
| `consts.ML` | `consts.rs` | 常量声明 |
| `global_theory.ML` | `global_theory.rs` | 全局理论 |
| `facts.ML` | `facts.rs` | 事实数据库 |
| `axclass.ML` (600行) | `axclass.rs` | 类型类 (基础) |
| `pure_thy.ML` | `hol_loader.rs` | Pure 理论引导 (HOL 加载) |
| `config.ML` | (分散在各处) | 配置 |

### 🟡 部分完成 (需要增强)

| Isabelle ML | 状态 | 缺失内容 |
|-------------|:--:|------|
| `search.ML` | 🟡 | 深度优先/BEST_FIRST 在 method.rs，但缺少完整的搜索策略 |
| `variable.ML` | 🟡 | `variable.rs` 仅基础实现 |
| `goal.ML` | 🟡 | goal 操作分散在 proof.rs 和 method.rs |
| `primitive_defs.ML` | 🟡 | 基础定义在 theory.rs |
| `defs.ML` | 🟡 | 定义管理不完整 |

### ❌ 未实现 (12/60)

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
| `type_infer_context.ML` | 类型推断上下文 | P2 |
| `zterm.ML` | Z-term | P3 |

---

## 二、Pure/Isar (41 ML files → ~15 Rust files)

### ✅ 已完成 (13/41)

| Isabelle ML | isabelle-rs Rust |
|-------------|-----------------|
| `proof.ML` (1000行) | `proof.rs` |
| `method.ML` (900行) | `method.rs` |
| `keyword.ML` | `keyword.rs` |
| `outer_syntax.ML` | `outer_syntax.rs` |
| `token.ML` | `token.rs` |
| `parse.ML` | `parse.rs` + `term_parser.rs` |
| `locale.ML` (845行) | `locale.rs` |
| `local_theory.ML` | `local_theory.rs` |
| `calculation.ML` (260行) | `proof.rs` |
| `obtain.ML` (400行) | `proof.rs` |
| `toplevel.ML` | `toplevel.rs` |
| `class.ML` + `class_declaration.ML` | `class_system.rs` |
| `interpretation.ML` | `locale.rs` |

### ❌ 未实现 (28/41)

| Isabelle ML | 功能 | 优先级 |
|-------------|------|:--:|
| `attrib.ML` | 属性系统 ([simp], [intro!], [elim!]) | P1 |
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
| `proof_context.ML` | 证明上下文 (完整) | P1 |
| `proof_display.ML` | 证明显示 | P3 |
| `proof_node.ML` | 证明节点 | P3 |
| `rule_cases.ML` | 规则情况 | P1 |
| `runtime.ML` | 运行时 | P3 |
| `spec_rules.ML` | 规范规则 | P2 |
| `specification.ML` | 规范 | P1 |
| `subgoal.ML` | 子目标 | P2 |
| `target_context.ML` | 目标上下文 | P2 |
| `typedecl.ML` | 类型声明 | P1 |

---

## 三、HOL Tools (258 ML files, ~126K LOC)

### 已有基础

| 工具 | isabelle-rs | 完成度 | 缺失 |
|------|:---:|:--:|------|
| **BNF** | map/set/rel/pred | 10% | Lfp, Gfp, fp_sugar, bnf_axioms, bnf_comp, bnf_def, bnf_fp_n2m |
| **Ctr_Sugar** | case/disc/sel/split/cong/nchotomy/size | 50% | 完整 Ctr_Sugar 插件 |
| **primcorec** | 基础 | 30% | 完整 corec 检查, 互余归纳 |
| **Function** | 解析 | 10% | fun/function 完整处理 |
| **Inductive** | 解析 + 基础规则 | 30% | 完整 intro/elim/induct 生成 |
| **Sledgehammer** | ATP 调用 + TSTP 解析 | 20% | 完整证明重构, minimizer, relevance filter |
| **typedef/record** | 基础定理 | 40% | 完整 record 包 |
| **linarith** | stub | 5% | 线性算术求解器 |
| **TPTP** | FOF 导出 | 30% | TFF0/THF 格式 |

### ❌ 完全缺失 (需要大量工作)

| 工具 | ML 规模 | 功能 | 优先级 |
|------|:--:|------|:--:|
| **Code Generator** | ~8K | HOL → SML/OCaml/Haskell | P3 |
| **ATP systems** | ~10K | E/Vampire/Zipperposition 深度集成 | P1 |
| **Meson** | ~3K | 经典逻辑证明 | P2 |
| **Metis** | ~2K | 一阶逻辑证明 | P2 |
| **Argo** | ~5K | 线性算术 | P2 |
| **SMT** | ~8K | SMT solver 集成 | P2 |
| **Transfer** | ~3K | 类型传输 | P1 |
| **Lifting** | ~2K | 商类型提升 | P1 |
| **Nitpick** | ~10K | 反例查找 | P3 |
| **Quickcheck** | ~3K | 随机测试 | P3 |
| **Quotient** | ~2K | 商类型 | P2 |
| **Predicate_Compile** | ~4K | 谓词编译 | P3 |
| **Mirabelle** | ~2K | 自动化测试 | P3 |
| **Old_Datatype** | ~3K | 旧 datatype 包 | P3 |
| **Nunchaku** | ~1K | 反例查找 | P3 |
| **Qelim** | ~1K | 量词消去 | P2 |

---

## 四、其他逻辑 (8 logics, 0% covered)

| 逻辑 | 文件 | 说明 |
|------|:--:|------|
| FOL | ~20 | 一阶逻辑 |
| ZF | ~20 | Zermelo-Fraenkel 集合论 |
| CCL | ~10 | Classical Computational Logic |
| CTT | ~10 | Constructive Type Theory |
| Cube | ~5 | Lambda Cube |
| FOLP | ~5 | FOL with Proof Terms |
| LCF | ~5 | Logic for Computable Functions |
| Sequents | ~5 | Sequent Calculus |

> 这些逻辑的优先级较低——HOL 是最主要的对象逻辑。

---

## 五、总结：差距量化

```
isabelle-rs v1.2.0          Isabelle 完整分布

Pure 内核:    ████████ 50%   ████████████████████ 60 files, ~27K ML
Pure/Isar:    ██████   35%   ████████████████████ 41 files
HOL Tools:    █         6%   ████████████████████ 258 files, ~126K ML
.thy 验证:    ▏        1.4%  ████████████████████ 1,473 files
Scala:        无需移植 (Rust 替代 PIDE/Build)
其他逻辑:     0%              8 logics

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
总体功能覆盖:  ~20–25%
核心内核覆盖:  ~85–90%
```

### 优先级排序 (按影响力)

| 优先级 | 任务 | 工作量 | 影响 |
|:--:|------|:--:|:--:|
| P0 | 全库 .thy 验证 (1,473 files) | 持续 | 验证覆盖率 1.4%→50%+ |
| P1 | attrib.ML (属性系统) | 2-3 days | 正确解析 [simp]/[intro!] |
| P1 | proof_context.ML 完整 | 3-5 days | 完整 Isar 上下文 |
| P1 | Transfer/Lifting | 1-2 weeks | 类型系统完整性 |
| P1 | Sledgehammer 证明重构 | 2-4 weeks | ATP→Isabelle 证明 |
| P2 | BNF Lfp/Gfp 完整 | 3-6 weeks | datatype 包完整 |
| P2 | specification.ML | 1 week | 规范命令 |
| P3 | Code Generator | 4-8 weeks | 代码生成 |
| P3 | Nitpick/Quickcheck | 4-8 weeks | 反例/测试 |
