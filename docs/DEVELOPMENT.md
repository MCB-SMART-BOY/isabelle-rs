# 开发者指南 v0.7.0 Final

## 环境要求

- Rust 1.80+ (edition 2024)
- cargo
- 推荐: 128MB+ stack (`RUST_MIN_STACK=134217728`)

## 构建与测试

```bash
# 构建
cargo build

# 运行测试 (373+)
cargo test

# 内核测试 (快速)
cargo test --lib core::thm::

# BNF/datatype 测试
cargo test --test bnf_tests

# TPTP 测试
cargo test --lib tptp

# 批量编译 HOL 理论文件
cargo run --bin isabelle-build -- --dir isabelle-source/src/HOL
```

## 项目结构

```
src/
├── core/              # LCF 可信内核 (~9,000 LOC)
│   ├── thm.rs         # Thm + ThmKernel (15 操作)
│   ├── unify.rs       # 高阶统一
│   ├── simplifier.rs  # 重写引擎
│   ├── tactic.rs      # Tactic (15 tactical + 8 tactic)
│   ├── net.rs         # Discrimination Nets
│   ├── types.rs       # Type/Sort/ClassAlgebra + TypeEnv
│   ├── logic.rs       # Pure 逻辑常量
│   ├── term.rs        # Term (lambda calculus)
│   ├── theory.rs      # Theory, ProofContext
│   ├── sign.rs        # 签名 (certify_term/prop/infer_type)
│   ├── conv.rs        # Conv — 14 转换组合子
│   ├── morphism.rs    # Morphism — 定理传输
│   ├── name.rs        # NameContext
│   ├── term_ord.rs    # 项排序
│   ├── sorts.rs       # Sort algebra
│   └── ...
├── isar/              # Isar 证明引擎 (~8,500 LOC)
│   ├── method.rs      # 25 proof methods + 六层 fallback
│   ├── proof.rs       # IsarProof 三模式状态机
│   ├── proof_state.rs # ProofState + Isar 解释器
│   ├── token.rs       # Isabelle tokenizer
│   ├── term_parser.rs # Term 解析器
│   ├── keyword.rs     # 30+ command kinds
│   ├── outer_syntax.rs # 命令解析器 + 模式转移
│   └── ...
├── hol/               # HOL 理论加载 (~7,000 LOC)
│   ├── hol_loader.rs  # .thy 解析 + DB + nets + builtins
│   ├── theory_graph.rs # TheoryGraph DAG
│   ├── theory_db.rs   # HolTheoremDb (42K+ theorems)
│   ├── inductive.rs   # inductive/coinductive
│   ├── function.rs    # fun/function/primrec
│   ├── locale.rs      # locale parsing
│   ├── class_system.rs # instance/subclass
│   ├── axclass.rs     # type class algebra
│   ├── typedef_record.rs # typedef/record
│   └── ...
├── theory/            # 理论系统 (~3,000 LOC)
│   ├── loader.rs      # TheoryProcessor pipeline
│   ├── local_theory.rs # 增量理论构建
│   ├── session_builder.rs # DAG + 批量编译
│   ├── registry.rs    # 父理论注册
│   └── ...
├── server/            # LSP 服务器 (~1,500 LOC)
├── lsp/               # 8 LSP handlers (~500 LOC)
├── syntax/            # CST + Printer (~1,200 LOC)
│   ├── printer.rs     # Pretty Printer (20+ operators)
│   └── ...
├── tools/             # TPTP export
│   └── tptp.rs        # FOF format
├── session/           # 会话管理
├── wasm/              # WASM 运行时
├── bin/               # CLI 工具
│   └── isabelle-build.rs
└── document/          # 文档模型
```

## 核心架构

### 六层证明验证

```
verify_lemma():
  0 → Safe rules (match→elim_match→resolution)
  1 → Built-in Var-override
  2 → Anonymous datatype axiom
  3 → Isar structured proof (三模式)
  4 → exec_proof (25 methods)
  5 → Axiom acceptance
```

### 经典推理器

| 方法 | 策略 |
|------|------|
| `fast_exec` | DFS + iterative deepening (0..8) |
| `best_exec` | BEST_FIRST (worklist by nprems) |
| `depth_exec` | Bounded DFS (explicit bound) |
| `step_exec` | Safe exhaustive + one unsafe |
| `dup_step_exec` | step_tac + rule duplication |

### 类型安全

```rust
// 内核规则: 无一使用 Typ::dummy()
ThmKernel::reflexive(ct)     // uses ct.term_type()
ThmKernel::combination(...)  // returns Err, not Typ::dummy() fallback

// 理论构造: 自动标注
CTerm::certify_annotated(term)  // annotates from TypeEnv

// 边界守卫
CTerm::require_non_dummy(op)    // Err if type is dummy
```

## 项目统计

| 指标 | 数值 |
|------|------|
| Rust 代码 | ~39,000 行 |
| 源文件 | 111 `.rs` |
| 测试 | 370+ |
| .thy 文件 (full) | 1,849 |
| 定理总数 (full) | 42,000+ |
| 警告 | 13 |
| 性能 (core) | ~4.1s (24× from v0.4.0) |
