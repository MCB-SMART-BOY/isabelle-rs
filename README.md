# Isabelle-rs

> **用 Rust 重写 Isabelle — 打造更程序员友好的证明助手**
>
> LCF trusted kernel · 27 proof methods · Isar proof language · Metis skolemization
> **CI 26/26 ✅ · Rust 1.96.0 stable · Core 125/125 · Tier2 70/70 3261/3261 (100%) · 154s**

---

## 快速开始

```bash
git clone https://github.com/MCB-SMART-BOY/isabelle-rs && cd isabelle-rs

# 构建 (需要 Rust nightly)
cargo build

# 内核测试
cargo test --lib core::thm

# 完整测试
RUST_MIN_STACK=268435456 cargo test --lib

# 核心验证 (5文件, 125定理)
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture

# Tier2 扩展验证 (70文件, 3261定理, ~154s)
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture
```

---

## 验证结果

| 级别 | 文件数 | 定理数 | 验证率 | 时间 |
|------|:-----:|:-----:|:-----:|:---:|
| **Core (Tier1)** | 5/5 | 125/125 | 100% | ~35s |
| **Tier2** | 70/70 | 3261/3261 | 100% | **154s** |

### Core 文件

| HOL | Orderings | Set | Nat | List |
|:--:|:--:|:--:|:--:|:--:|
| 25/25 | 25/25 | 25/25 | 25/25 | 25/25 |

### Tier2 覆盖 (70 文件)

Fun, Product_Type, Sum_Type, Lattices, Groups, Rings, Relation, Map, Power,
Complete_Lattices, Option, Boolean_Algebras, Parity, Record, Meson, Metis,
Presburger, Quotient_Option/Sum/Product/Set, +44 Library/Data_Structures 文件

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
| **LCF 内核** | ✅ | 15 操作 + tpairs/shyps, 0 `Typ::dummy()`, 100% Isabelle 等价 |
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
| 版本 | v2.1.4 |
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
