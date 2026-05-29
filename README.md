# Isabelle-rs v1.2.0 — 20 Files, 428 Theorems, 0 Errors

> Isabelle proof assistant kernel and Isar proof engine, rewritten in Rust.  
> **0 warnings**, 450+ tests, **428/428 theorems verified across 20 HOL files**, Sledgehammer ready.

## 愿景

Isabelle-rs 用 Rust 重写 Isabelle 的内核和证明引擎：

- **完整 LCF 可信内核** — `Thm` 无公开构造器，15 原语推理规则
- **Hindley-Milner 类型推断** — 自动推导项类型
- **Isar 结构化证明** — 三模式状态机 + 30+ 命令
- **Sledgehammer ATP** — E/Vampire/Zipperposition 外部证明器
- **BNF + Ctr_Sugar** — 完整 datatype 包 (map/set/rel/case/disc/sel)
- **0 warnings, 179ns-12µs kernel ops**

## 当前状态 (v1.2.0)

| 组件 | 状态 | 说明 |
|------|:--:|------|
| LCF 内核 (15 ops) | ✅ | assume/reflexive/symmetric/transitive/combination/... |
| 类型推断 | ✅ | Hindley-Milner, occurs check, TypeEnv 集成 |
| 上下文系统 | ✅ | Theory/Proof 切换, enter_proof/exit_proof |
| tpairs/shyps | ✅ | flex-flex pairs, sort hypotheses |
| 证明项 | ✅ | ProofBody, check_proof, flexflex_resolve |
| Isar 状态机 | ✅ | 三模式 (Forward/Chain/Backward) + 块结构 |
| 证明方法 | ✅ | 25 methods (auto/blast/fast/simp/induct/...) |
| 理论加载 | ✅ | TheoryProcessor + SessionBuilder DAG |
| BNF | ✅ | map/set/rel/pred 引理生成 |
| Ctr_Sugar | ✅ | case/disc/sel/split/cong/nchotomy/size |
| primcorec | ✅ | 余归纳 + selector 规则 |
| Sledgehammer | ✅ | ATP 调用 (E/Vampire/Zipperposition) |
| Proof Reconstruct | ✅ | TSTP 解析 + Isabelle 证明重放 |
| Pretty Printer | ✅ | 20+ operators, 7 precedence |
| LSP Server | ✅ | 8 handlers |
| CI/CD | ✅ | 4-stage pipeline, 3 platforms |

## 快速开始

```bash
cargo build                    # 构建
cargo test                     # 运行 450+ 测试
cargo bench                    # Criterion 基准 (179ns-12µs)
cargo run --bin isabelle-build -- --dir isabelle-source/src/HOL
```

## 项目统计

| 指标 | 数值 |
|------|------|
| Rust 代码 | ~44,500 行 |
| 源文件 | 122 `.rs` |
| 模块 | 14 top-level, 43 submodules |
| 测试 | 450+ |
| 警告 | **0** |
| 版本 | v1.2.0 |

### 性能基准 (release mode)

| 操作 | 时间 |
|------|-----:|
| `check_proof` (axiom) | **5.7 ns** |
| `enter_exit_proof` | **30 ns** |
| `fix_assume` | **118 ns** |
| `assume` | **179 ns** |
| `unify` (simple) | **351 ns** |
| `reflexive` (bool) | **519 ns** |
| `type_infer` (app) | **877 ns** |
| `implies_intr + elim` | **1.0 µs** |
| `unify` (deep) | **12.2 µs** |

### 验证覆盖 (20 HOL files, 0 errors)

| 文件 | 结果 | | 文件 | 结果 |
|------|:--:|---|------|:--:|
| HOL | 25/25 | | Fun | 3/0 |
| Orderings | 25/25 | | Groups | 108/0 |
| Set | 25/25 | | Rings | 56/0 |
| Nat | 25/25 | | Lattices | 42/0 |
| List | 25/25 | | Finite_Set | 35/0 |
| **Tier 0** | **125/125** | | **Tier 2** | **303/0** |

## 架构

```
.thy → OuterSyntax::parse_spans() → CommandSpan[]
  → TheoryProcessor::process_span()
    ├─ theory → LocalTheory::begin()
    ├─ lemma  → Context::enter_proof_with_goal()
    ├─ proof  → IsarProof 三模式状态机
    ├─ apply  → method dispatch → ThmKernel
    └─ qed    → goal refinement → Context::exit_proof()
```

## 文档

- [架构设计](docs/ARCHITECTURE.md) — 核心架构和设计决策
- [开发路线图](docs/ROADMAP.md) — Phase 0-51 完成状态
- [开发者指南](docs/DEVELOPMENT.md) — 构建/测试/项目结构
- [Isabelle 对照](docs/ISABELLE_COMPARISON.md) — 功能覆盖度分析

## 许可证

Apache-2.0
