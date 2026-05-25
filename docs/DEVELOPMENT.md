# 开发者指南 v0.5.0

## 环境要求

- Rust 1.80+ (edition 2024)
- cargo
- 推荐: 128MB+ stack (设置 `RUST_MIN_STACK=134217728`)

## 构建与测试

```bash
# 构建
cargo build

# 运行测试 (250+ 个)
cargo test

# 查看基准验证率 (需要大栈)
cargo test test_verify_all_core_files -- --nocapture

# 查看 beyond-core 验证 (需要大栈 + isabelle-source/)
RUST_MIN_STACK=134217728 cargo test test_verify_beyond_core -- --nocapture

# 查看全库加载测试
RUST_MIN_STACK=33554432 cargo test test_load_500_from_full_hol -- --nocapture

# 运行特定测试
cargo test --lib test_induct_rule_application -- --nocapture
cargo test --lib test_debug_collect_eqI -- --nocapture
```

## 项目结构

```
src/
├── core/              # LCF 可信内核
│   ├── thm.rs         # Thm + ThmKernel (15 操作 + generalize)
│   ├── unify.rs       # 高阶统一 + HO 模式匹配 + likely_unifiable
│   ├── simplifier.rs  # 重写引擎 (rewrite_deep, 条件验证, Free→Var fallback)
│   ├── tactic.rs      # Tactic AST + 解释器
│   ├── envir.rs       # 变量环境 (β-归约)
│   ├── logic.rs       # Pure 逻辑常量
│   ├── term.rs        # Term (lambda calculus)
│   ├── types.rs       # Sort, Typ
│   ├── theory.rs      # Theory, ProofContext
│   └── ... (26 files)
├── isar/              # Isar 证明引擎
│   ├── method.rs      # Method 引擎 (18 方法 + auto 指令 + generalize_thm)
│   ├── term_parser.rs # Term 解析器 (优先级修复 + String 边界)
│   ├── token.rs       # Isabelle tokenizer
│   ├── proof_state.rs # ProofState + Isar 解释器
│   ├── proof_context.rs # IsarContext (case/fix/assume)
│   ├── proof.rs       # Isar proof 解析
│   └── ... (13 files)
├── hol/               # HOL 理论加载
│   ├── hol_loader.rs  # .thy 解析 + datatype/primrec/class 合成 + DB extend
│   ├── theory_graph.rs # TheoryGraph DAG + 增量加载 + beyond-core 测试
│   ├── hol_consts.rs  # HOL 常量定义
│   ├── hol_rules.rs   # HOL 内置规则
│   └── ... (6 files)
├── kernel/            # 派生规则 + 数据管理
├── server/            # LSP 服务器
├── lsp/               # LSP 路由 + 7 handlers
├── session/           # 会话管理 (Actor)
├── syntax/            # Rowan CST 解析器
├── theory/            # SQLite 缓存
├── wasm/              # WASM 运行时
├── tools/             # 工具占位 (auto, blast, simp)
├── fleche/            # 引擎
├── document/          # 文档模型
├── lib.rs             # Crate 入口
└── main.rs            # 二进制入口 (demo + LSP)
```

## 核心架构

### 证明验证的五层 fallback

```
verify_lemma(lem):
  1. Built-in Var-override → 系统内置规则的 Var 版本
  2. Anonymous datatype lemma → 自动公理接受
  3. Isar structured proof → interpret_proof_script
  4. Simple exec_proof → 链式方法 + auto/blast fallback
  5. Axiom acceptance → generalize_thm 最终安全网
```

### 内核 → Tactic → Method 数据流

```
.thy 源文件
    ↓ parse_lemmas()
ParsedLemma { name, theorem, proof_script }
    ↓ verify_lemma()
    │   ├─ built-in Var-override
    │   ├─ Isar: interpret_proof_script()
    │   └─ Simple: exec_proof() → exec_single_method()
    │         └─ chain fallback: auto/blast
    ↓
Method::execute(state, premises): Vec<Thm>
    ├─ auto_exec (assume→simp→resolve→eresolve→dresolve)
    ├─ blast_exec (+symmetry +order_antisym +dresolve)
    ├─ exec_induct (auto→blast→rule lookup→HO match)
    ├─ exec_simp (rewrite_deep + add:/only:/del:)
    ├─ exec_iprover (intro: + elim: + dest:)
    ├─ exec_subst (substitution)
    └─ exec_arith (basic arithmetic)
    ↓
ThmKernel (15 operations)
    ├─ 12 primitives
    └─ 3 kernel derived (bicompose, bicompose_eresolve, subst_premise)
    └─ generalize (Free→Var)
```

### 运算符优先级

`parse_trm_no_imp` 用于 `=`/`&`/`|` 的 RHS，停止在 `==>` 前。

### Free→Var generalize

解决 parsed lemma (Free 变量) 无法用于统一化 tactic 的根本问题：

```rust
// 定理泛化 (用于 using, auto intro:)
let gen_thm = generalize_thm(&thm);  // Free → Var

// 项泛化 (用于 simp 匹配)
let gen_lhs = generalize_term_for_match(&rule.lhs);  // Free → Var
```

### 链式方法 fallback (v0.5.0 核心突破)

```rust
// exec_proof 中: 方法返回空结果时
if next_states.is_empty() {
    // auto/blast 自动接管前一状态
    for s in &current_states {
        for r in Method::Auto.execute(s, premises) { ... }
        for r in Method::Blast.execute(s, premises) { ... }
    }
}
```

### 增量 DB 加载 + override

```rust
// 逐文件构建 DB
let mut db = HolTheoremDb::new();
for file in files {
    db.extend(&parse_lemmas(&file));
}

// 自定义 DB 测试
HolTheoremDb::with_override(&db, || {
    verify_lemma(&lem);
});
```

### 简化器 Free→Var fallback

```rust
fn try_rule(&self, term: &Term, rule: &RewriteRule) -> Option<...> {
    // 1. Free-based 匹配
    let env = unify::matchers(&env, &rule.lhs, term, &config);
    // 2. 失败则 generalize LHS 为 Var 重试
    let env = env.or_else(|| {
        let gen_lhs = generalize_term_for_match(&rule.lhs);
        unify::matchers(&env2, &gen_lhs, term, &config)
    })?;
}
```

### 迭代限制

`thread_local!` 计数器 (`AUTO_DEPTH`/`AUTO_LIMIT`) 防止 `auto_exec`/`blast_exec` 无限递归。
深度限制: auto_exec=15, blast_exec=15 (v0.5.0 优化, 原为 30/28)。

## 常用调试命令

```bash
# DB 定理数量
cargo test --lib test_by_name_index_populated -- --nocapture

# 归纳规则测试
cargo test --lib test_induct_rule_application -- --nocapture

# HO 匹配测试
cargo test --lib test_ho_pattern_induction -- --nocapture

# 验证率基准
cargo test test_verify_all_core_files -- --nocapture

# Beyond-core 验证
RUST_MIN_STACK=134217728 cargo test test_verify_beyond_core -- --nocapture

# 全库加载
RUST_MIN_STACK=33554432 cargo test test_load_500_from_full_hol -- --nocapture

# datatype 解析
cargo test datatype_tests -- --nocapture

# 条件重写测试
cargo test conditional_tests -- --nocapture

# Isar 引擎测试
cargo test isar_tests -- --nocapture

# 特定 lemma 调试
cargo test test_debug_collect_eqI -- --nocapture
```

## 项目统计

| 指标 | 数值 |
|------|------|
| Rust 代码 | ~27,000 行 |
| 源文件 | 89 `.rs` |
| 测试 | 250+ |
| `.thy` 文件 (core) | 116 (115 HOL + 1 Pure) |
| `.thy` 文件 (full) | 1,473 |
| 定理总数 (core) | 15,804 |
| 定理总数 (full) | 42,000+ |
| 验证率 (core) | 100% (125/125) |
| 验证率 (core + beyond) | 100% (208/208) |
| 性能 | ~24s (core benchmark) |
