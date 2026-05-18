# 开发者指南

## 环境要求

- Rust 1.80+
- cargo

## 构建与测试

```bash
# 构建
cargo build

# 运行测试 (210+ 个)
cargo test

# 运行特定测试
cargo test --lib test_induct_rule_application -- --nocapture

# 查看基准验证率
cargo test test_verify_all_core_files -- --nocapture

# 查看单个文件验证率
cargo test test_verify_list_thy_sample -- --nocapture

# 查看数据类解析
cargo test datatype_tests -- --nocapture
```

## 项目结构

```
src/
├── core/              # LCF 可信内核
│   ├── thm.rs         # Thm + ThmKernel (15 操作)
│   ├── unify.rs       # 高阶统一 + HO 模式匹配
│   ├── simplifier.rs  # 重写引擎 (rewrite_deep, 条件验证)
│   ├── tactic.rs      # Tactic AST + 解释器
│   ├── envir.rs       # 变量环境 (β-归约)
│   ├── logic.rs       # Pure 逻辑常量
│   ├── term.rs        # Term (lambda calculus)
│   ├── types.rs       # Sort, Typ
│   ├── theory.rs      # Theory, ProofContext
│   └── ... (26 files)
├── isar/              # Isar 证明引擎
│   ├── method.rs      # Method 引擎 (15 方法 + subst/fact/arith)
│   ├── term_parser.rs # Term 解析器 (优先级修复)
│   ├── token.rs       # Isabelle tokenizer
│   ├── proof_state.rs # ProofState + Isar 解释器
│   └── ... (9 files)
├── hol/               # HOL 理论加载
│   ├── hol_loader.rs  # .thy 解析 + datatype/primrec/class 合成
│   ├── theory_graph.rs # TheoryGraph DAG + 进度加载
│   └── ... (6 files)
├── kernel/            # 派生规则 + 数据管理
├── server/            # LSP 服务器
├── lsp/               # LSP 路由 + handlers
├── session/           # 会话管理 (Actor)
├── syntax/            # Rowan CST 解析器
├── theory/            # SQLite 缓存
├── wasm/              # WASM 运行时
├── lib.rs             # Crate 入口
└── main.rs            # 二进制入口 (demo + LSP)
```

## 核心架构

### 内核 → Tactic → Method 数据流

```
.thy 源文件
    ↓ parse_lemmas()
    │   ├─ parse_datatypes()     → induct/inject/distinct/exhaust/case
    │   ├─ parse_primrecs()      → simp 规则
    │   ├─ parse_classes()       → 类型类常量
    │   └─ parse_lemmas_cmd()    → 别名解析
ParsedLemma { name, theorem, proof_script }
    ↓ verify_lemma()
    │   ├─ [Isar] interpret_proof_script()
    │   │     ├─ fix / assume → 上下文扩展
    │   │     ├─ have / show  → exec_proof + 事实累积
    │   │     ├─ case / next  → 子目标导航
    │   │     └─ then/hence/thus → 链式推理
    │   └─ [Simple] exec_proof() → exec_single_method()
    ↓
Method::execute(state, premises): Vec<Thm>
    ├─ auto_exec (assume→simp→resolve→eresolve→dresolve)
    ├─ blast_exec (+symmetry +order_antisym +dresolve +term_pruning)
    ├─ exec_induct (auto→blast→rule lookup→HO match→solve_subgoals)
    ├─ exec_simp (rewrite_deep + add:/only:/del:)
    ├─ exec_subst (substitution in goal/assumptions)
    └─ exec_arith (basic arithmetic)
    ↓
ThmKernel (15 operations)
    ├─ 12 primitives
    └─ 3 kernel derived (bicompose, bicompose_eresolve, subst_premise)
```

### 运算符优先級

`parse_trm_no_imp` 用于 `=`/`&`/`|` 的 RHS，停止在 `==>` 前。

```
s = t ==> t = s  →  Pure.imp(HOL.eq(s, t), HOL.eq(t, s))  ✅
```

### 高阶模式匹配

`collect_bound_args` 接受 `Free`/`Var` 作为模式头。
`Envir::norm_term` 在 App 处执行 β-归约。

```rust
// Pattern: P(xs) where P is Free/Var
// Goal: length xs = 0
// Result: P → λxs. length xs = 0
```

### 条件重写

`RewriteRule::from_thm` 从定理前提中提取条件。`try_rule` 用递归 simplifier 验证条件 (深度3)。

### Isar 引擎

`ProofState::Proving` 包含子目标栈 (`subgoals`, `current_subgoal`) 和链式事实 (`chained_fact`)。`interpret_proof_script` 解析 Isar 命令并驱动状态机。

### 迭代限制

`thread_local!` 计数器 (`AUTO_DEPTH`/`AUTO_LIMIT`) 防止 `auto_exec`/`blast_exec` 无限递归。

### Term 构造 (必须通过 ThmKernel)

```rust
use crate::core::thm::{CTerm, Thm, ThmKernel};

let a = CTerm::certify(Term::const_("A", Typ::base("prop")));
let thm_a = ThmKernel::assume(a.clone());

let t = CTerm::certify(Term::free("t", Typ::dummy()));
let thm_refl = ThmKernel::reflexive(t);

let result = ThmKernel::implies_elim(&thm_ab, &thm_a).unwrap();
```

## 常用调试命令

```bash
# 查看 DB 中的定理数量
cargo test --lib test_by_name_index_populated -- --nocapture

# 查看归纳规则应用测试
cargo test --lib test_induct_rule_application -- --nocapture

# 查看 HO 匹配测试
cargo test --lib test_ho_pattern_induction -- --nocapture

# 查看验证率基准
cargo test test_verify_all_core_files -- --nocapture

# 查看 datatype 解析
cargo test datatype_tests -- --nocapture

# 查看 primrec 解析
cargo test primrec_tests -- --nocapture

# 查看 class 解析
cargo test class_tests -- --nocapture

# 查看条件重写测试
cargo test conditional_tests -- --nocapture

# 查看 Isar 引擎测试
cargo test isar_tests -- --nocapture
```

## 项目统计

| 指标 | 数值 |
|------|------|
| Rust 代码 | ~20,000 行 |
| 源文件 | 84 `.rs` |
| 测试 | 210+ |
| `.thy` 文件 | 116 (115 HOL + 1 Pure) |
| 定理总数 | 15,804 |
