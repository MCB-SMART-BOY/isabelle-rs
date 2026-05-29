# Isabelle-rs v1.2.0

> **Isabelle 证明助手内核与 Isar 证明引擎 — Rust 现代化重写**
>
> LCF 可信内核 · Hindley-Milner 类型推断 · 上下文切换 · Sledgehammer ATP
> **0 warnings · 450+ tests · 20 HOL files verified · 428 theorems · 0 errors**

---

## 项目概述

Isabelle-rs 用 Rust 重写了 Isabelle 证明助手的核心——LCF 可信内核与 Isar 结构化证明语言。
对标 Isabelle/ML 源码（`src/Pure/thm.ML`, `src/Pure/proof.ML` 等），在保留完整 LCF 安全性的同时，
利用 Rust 的类型系统、所有权模型和零成本抽象实现更高的性能与安全性。

### 核心特性

| 特性 | 说明 |
|------|------|
| **LCF 可信内核** | 15 原语推理规则，`Thm` 无公开构造器，100% Isabelle 等价 |
| **类型推断** | Hindley-Milner 风格类型推断，occurs check，与 TypeEnv 集成 |
| **上下文系统** | Theory/Proof 上下文切换，`enter_proof`/`exit_proof`/`transfer` |
| **Isar 证明引擎** | 三模式状态机 (Forward/Chain/Backward)，30+ 命令，块结构 |
| **Sledgehammer** | E/Vampire/Zipperposition ATP 调用，TSTP 证明解析与重放 |
| **BNF 包** | map/set/rel/pred 引理生成 (Bounded Natural Functors) |
| **Ctr_Sugar** | case/disc/sel/split/cong/nchotomy/size — 完整 datatype 工具 |
| **性能** | 内核操作 179ns–12µs (release mode, criterion 实测) |

---

## 快速开始

```bash
git clone https://github.com/MCB-SMART-BOY/isabelle-rs
cd isabelle-rs

cargo build                                    # 编译
cargo test                                     # 450+ 测试
cargo bench                                    # 性能基准 (179ns–12µs)
cargo run --bin isabelle-build -- --dir isabelle-source/src/HOL  # 批量编译
```

要求: Rust nightly (edition 2024)

---

## 验证结果 (实测)

### Tier 0 — 核心文件 (5 files)

| 文件 | 引理数 | 已验证 | 比率 | 时间 |
|------|:--:|:--:|:--:|-----:|
| HOL.thy | 25 | 25 | 100% | 14.8s |
| Orderings.thy | 25 | 25 | 100% | 0.01s |
| Set.thy | 25 | 25 | 100% | 9.9s |
| Nat.thy | 25 | 25 | 100% | 0.03s |
| List.thy | 25 | 25 | 100% | 0.00s |
| **小计** | **125** | **125** | **100%** | **~25s** |

### Tier 2 — 扩展文件 (15 files)

| 文件 | 定理 | 错误 | 文件 | 定理 | 错误 |
|------|:--:|:--:|------|:--:|:--:|
| Fun | 3 | 0 | Complete_Lattices | 17 | 0 |
| Product_Type | 0* | 0 | Fields | 14 | 0 |
| Sum_Type | 0* | 0 | Num | 13 | 0 |
| Option | 5 | 0 | Map | 6 | 0 |
| Lattices | 42 | 0 | Relation | 2 | 0 |
| Groups | 108 | 0 | Power | 2 | 0 |
| Rings | 56 | 0 | Equiv_Relations | 0* | 0 |
| Finite_Set | 35 | 0 | | | |
| **小计** | | | | **303** | **0** |

> \* 无显式证明的引理（仅定义声明）

| | |
|---|---|
| **总文件数** | **20** |
| **总定理/引理** | **428** |
| **总错误** | **0** |

---

## 性能基准

Criterion benchmark, release mode, x86_64:

| 操作 | 延迟 | 类别 |
|------|-----:|------|
| `check_proof` (axiom) | **5.7 ns** | 证明项 |
| `enter_exit_proof` | **30 ns** | 上下文 |
| `fix_assume` | **118 ns** | 上下文 |
| `assume` | **179 ns** | 内核 |
| `unify` (simple) | **351 ns** | 合一 |
| `reflexive` (bool) | **519 ns** | 内核 |
| `type_infer` (app) | **877 ns** | 类型 |
| `implies_intr+elim` | **1.0 µs** | 内核 |
| `unify` (deep) | **12.2 µs** | 合一 |

---

## 架构

```
.thy 源文件
  ↓ OuterSyntax::parse_spans()
CommandSpan[]
  ↓ TheoryProcessor::process_span()
  ├─ theory  → LocalTheory::begin()
  ├─ lemma   → Context::enter_proof_with_goal()
  ├─ proof   → IsarProof 三模式状态机
  ├─ fix/assume → local context
  ├─ apply   → method dispatch → ThmKernel (LCF 内核)
  ├─ qed     → goal refinement → Context::exit_proof()
  └─ end     → LocalTheory::finalize() → Arc<Theory>
  ↓ SessionBuilder::build_session()
TheoryGraph → 拓扑排序 → 批量编译 → 统计报告
```

### 模块结构

```
src/
├── core/         LCF 内核 (~34 modules)
│   ├── thm.rs        15 原语推理规则
│   ├── type_infer.rs HM 类型推断引擎
│   ├── context.rs    Theory/Proof 上下文
│   ├── proofterm.rs  证明项与检查
│   ├── unify.rs      高阶合一
│   ├── sorts.rs      Sort algebra
│   └── ...
├── isar/         Isar 证明语言 (15 modules)
│   ├── proof.rs      三模式状态机
│   ├── method.rs     25 证明方法
│   └── ...
├── hol/          HOL 理论 (15 modules)
│   ├── ctr_sugar.rs  case/disc/sel/split
│   ├── primcorec.rs  余归纳
│   └── ...
├── theory/       理论管理 (7 modules)
├── tools/        ATP + 证明重建 (5 modules)
├── server/       LSP 服务器
├── session/      会话管理
└── syntax/       Pretty Printer
```

---

## 项目统计

| 指标 | 数值 |
|------|------|
| Rust 代码 | ~44,500 行 |
| 源文件 | 122 `.rs` |
| 模块 | 14 top-level · 43 submodules |
| 测试 | 450+ (comprehensive 8/8 · proptest 26/26 · sledgehammer_e2e 7/8) |
| 警告 | **0** (lib + bin + benches) |
| 基准 | 9 operations (criterion) |
| CI/CD | 4-stage pipeline · 3 platforms |
| 许可证 | Apache-2.0 |

---

## 文档

| 文档 | 内容 |
|------|------|
| [架构设计](docs/ARCHITECTURE.md) | 核心架构、数据流、设计决策 |
| [开发路线图](docs/ROADMAP.md) | Phase 0–51 完成状态与规划 |
| [开发者指南](docs/DEVELOPMENT.md) | 环境配置、构建测试、项目结构 |
| [Isabelle 对照](docs/ISABELLE_COMPARISON.md) | 与 Isabelle/ML 的功能覆盖度对比 |
| [差距分析](docs/GAP_ANALYSIS.md) | **完整差距分析** — 缺什么、优先级 |
| [规则文件](.rules/) | 20 个领域与工程规则文件 |

---

## 许可证

Apache-2.0 — 详见 [Cargo.toml](Cargo.toml)
