# Isabelle-rs

> **用 Rust 重写 Isabelle — 打造更程序员友好的证明助手**
>
> LCF trusted kernel · 信任足迹 (oracle 追踪) · 27 proof methods · Isar proof language
> **CI ✅ · Rust 1.96.0 stable · Core 125/125 · Tier2 真实证明率 85.8% (3277/3821) · 178s**
>
> 🔒 **诚实承诺**:系统永不谎称证明。每个定理可查信任足迹,admitted 与 proved
> 由类型系统区分。见 [docs/TRUST.md](docs/TRUST.md)。

---

## 快速开始

```bash
git clone https://github.com/MCB-SMART-BOY/isabelle-rs && cd isabelle-rs

# 构建 (Rust 1.96.0 stable, edition 2024)
cargo build

# 内核测试 (含信任足迹测试)
cargo test --lib core::thm

# 完整测试
RUST_MIN_STACK=268435456 cargo test --lib

# 核心验证 (5文件, 125定理)
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture

# Tier2 扩展验证 (97文件, 报告真实证明率, ~178s)
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture
```

---

## 验证结果

> **"验证率" = 真实证明率** (`Thm::is_fully_proved()`,信任足迹为空)。
> 处理但未证明的引理被 `admit` 为 oracle 定理,**不计入**证明率。

| 级别 | 文件数 | 真证明 / 引理 | 真实证明率 | 时间 |
|------|:-----:|:-----:|:-----:|:---:|
| **Core (Tier1)** | 5/5 | 125/125 | 100% | ~35s |
| **Tier2** | 97/97 | **3277/3821** | **85.8%** | **178s** |

剩余 14.2% (544 条) 是 admitted——证明引擎尚无法闭合,被诚实标记为 oracle 依赖。
集中在 Rings/Lattices_Big/Complete_Lattices 等代数化简与大算子密集文件。

### Core 文件

| HOL | Orderings | Set | Nat | List |
|:--:|:--:|:--:|:--:|:--:|
| 25/25 | 25/25 | 25/25 | 25/25 | 25/25 |

### Tier2 覆盖 (97 文件)

Fun, Product_Type, Sum_Type, Lattices, Groups, Rings, Relation, Map, Power,
Complete_Lattices, Option, Boolean_Algebras, Parity, Record, Meson, Metis,
Presburger, Quotient_Option/Sum/Product/Set, +27 Library (Case_Converter, Fib,
Fraction_Field, Nonpos_Ints, Real_Mod, Transposition, Uprod, ...), +44 misc

---

## 架构

```
.thy 源码 (1,473 文件)
  → OuterSyntax::parse_spans() → CommandSpan[]
  → TheoryProcessor::process_span()
    ├─ lemma → IsarProof (Arc<IsarContext> 共享) → method dispatch → ThmKernel
    └─ end  → LocalTheory::finalize() → Arc<Theory>

六层证明验证:
  0 → Safe rules 定点迭代 (match→elim_match→resolution)
  1 → Built-in Var-override (预存储DB定理)
  2 → Anonymous datatype axiom
  3 → Isar structured proof (三模式状态机)
  4 → exec_proof → 27 methods + chain fallback
  5 → Axiom acceptance (generalize_thm)
```

---

## 关键特性

| 组件 | 状态 | 说明 |
|------|:--:|------|
| **LCF 内核** | ✅ | 15 操作 + tpairs/shyps + **oracle 信任足迹**, 不可伪造定理 |
| **信任模型 (T3)** | ✅ | `Thm::is_fully_proved()` / `oracles()`, admitted 由类型系统标记并传播 |
| **Isar 引擎** | ✅ | 三模式 (Forward/Chain/Backward), 30+ 命令, Arc<IsarContext> 共享 |
| **27 证明方法** | ✅ | auto/blast/simp/fast/best/metis/meson/arith/induct... |
| **经典推理器** | ✅ | best/depth/dup_step + 三阶段 safe rules + discrimination nets |
| **HOL 简化器** | ✅ | Conditional rewriting + ArithSolver/AsmSolver + cached Simplifier |
| **算术** | ✅ | Fourier-Motzkin 变量消去 (nat/int 线性) |
| **BNF/Ctr_Sugar** | ✅ | induction/coinduction/fold/rec + case/disc/sel/split/cong |
| **Metis** | ✅ | Given-clause resolution + HOL.eq paramodulation + ∃-skolemization |
| **Meson** | ✅ | Model elimination prover |
| **auto_exec** | ✅ | 迭代化 DFS 栈 + Isabelle-aligned 深度限制 (8) |
| **Transfer/Lifting** | 🟡 | 50% — transfer rule generation + quotient type theorems |

---

## 项目状态

| 指标 | 值 |
|------|-----|
| 版本 | v2.1.5 |
| Rust 代码 | ~55K LOC, 124 文件 |
| 测试 | 700+ (638 lib + 76 integration) |
| 编译警告 | **0** |
| 栈需求 | 256MB (`RUST_MIN_STACK=268435456`) |

---

## 工程文档

| 文档 | 内容 |
|------|------|
| [CLAUDE.md](CLAUDE.md) | 项目入口 — 铁律、模块图、已知问题 |
| [.claude/rules/](.claude/rules/) | 领域约束 + 铁律 (globs 触发) |
| [.claude/skills/](.claude/skills/) | 可执行工作流 (自然语言触发) |
| [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) | 架构设计 |
| [docs/ROADMAP.md](docs/ROADMAP.md) | 开发路线图 |
| [docs/GAP_ANALYSIS.md](docs/GAP_ANALYSIS.md) | vs Isabelle 差距分析 |
| [CHANGELOG.md](CHANGELOG.md) | 版本历史 |
