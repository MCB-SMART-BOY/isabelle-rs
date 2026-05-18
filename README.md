# Isabelle-rs v0.2.0

> Isabelle proof assistant kernel, rewritten in Rust.  
> **115 HOL theory files loaded, 15,804 theorems indexed, 60% verification rate on core files.**

## 愿景

Isabelle 是目前最强大的交互式定理证明器之一。Isabelle-rs 用 Rust 重写其内核和基础设施，目标是：

- **完整保留** Isabelle 的 `.thy` 语法和 Isar 证明语言
- **完整保留** LCF 可信内核架构（`Thm` 无公开构造器）
- **完整替换** 底层为 Rust，提供更好的性能、安全性和可嵌入性
- **标准 LSP** 替代 PIDE，支持任意现代编辑器

## 当前状态

| 组件 | 状态 | 说明 |
|------|:--:|------|
| LCF 内核 | ✅ | 12 原语 + 3 内核派生 (15 操作), 零 panic |
| 高阶模式匹配 | ✅ | HO pattern: Free/Var 头 + 参数抽象 + β-归约 |
| 深层重写引擎 | ✅ | `rewrite_deep`: 自底向上 + 等值证明构造 + 条件验证 |
| Term 解析器 | ✅ | `=`/`&`/`|` 正确处理 `==>` 优先级 |
| 定理加载 | ✅ | 115/115 HOL .thy 文件, DAG 拓扑排序, 0 错误 |
| 全库 DAG 扫描 | ✅ | 1,395 文件 DAG (全 Isabelle/HOL 1,472 文件) |
| 结构化引理解析 | ✅ | assumes/shows/fixes/obtains/cartouche/locale |
| `lemmas` 命令 | ✅ | 600+ 别名解析 |
| `datatype` 解析 | ✅ | 生成 induct/inject/distinct/exhaust/case 规则 |
| `primrec`/`fun` 解析 | ✅ | 47 定义从 List.thy 提取, 生成 simp 规则 |
| `class` 解析 | ✅ | 17 类型类从 Orderings.thy 提取 |
| `old_rep_datatype` 解析 | ✅ | 兼容 Nat.thy 的旧格式 |
| 定理数据库 | ✅ | 15,804 定理按 intro/elim/simp/by-name 索引 |
| Method 引擎 | ✅ | 15 方法 + auto
↔blast↔simp 回退链 |
| 归纳规则应用 | ✅ | HO 匹配 + `resolve_tac` + 子目标求解 |
| Isar 引擎 | ✅ | `have`/`show`/`case`/`next`/`then`/`hence`/`thus` |
| 链式推理 | ✅ | `then`/`hence`/`thus` + 事实累积 |
| `subst` 方法 | ✅ | `subst (asm) thm` 等值替换 |
| `fact` 方法 | ✅ | 按名查找定理 |
| 条件重写 | ✅ | 前提提取 + 深度3递归验证 |
| ProofState 子目标栈 | ✅ | 归纳/cases 子目标导航 |
| 证明验证 | ✅ | **60%** 基准 (全核心文件采样) |
| `isabelle-source/` 隔离 | ✅ | `.gitignore` 排除, 仓库 11MB |
| LSP 服务器 | 🚧 | 7 个 handlers + Isabelle 扩展 |
| `arith` 方法 | 🟡 | 基础算术规则已加，完整算术求解待实现 |

### 核心验证基准 (2025年9月采样)

| 理论文件 | 采样 | 已验证 | 验证率 |
|----------|:--:|:--:|:--:|
| HOL.thy | 25 | 1 | 4.0% |
| Orderings.thy | 25 | 22 | 88.0% |
| Set.thy | 25 | 24 | 96.0% |
| Nat.thy | 35 | 17 | 48.6% |
| List.thy | 13 | 10 | 76.9% |
| **合计** | **123** | **74** | **60.0%** |

### 已验证的证明模式

| 模式 | 示例 |
|------|------|
| `by (induct xs) auto` | `map_append`, `append_self_conv` |
| `by (induct xs) simp` | 归纳 + 简化 |
| `by auto` / `by simp` / `by blast` | 自动化方法 |
| `proof (induct xs) case ... next ... qed` | 结构化归纳 |
| `proof - assume ... show ... qed` | 前向推理 |
| `hence` / `thus` | 链式推理 |
| `by (rule name [OF ...])` | 规则应用 |
| `by (fact name)` | 定理引用 |

## 快速开始

```bash
# 构建
cargo build

# 运行测试 (210+ 个, 全部通过)
cargo test

# 查看基准验证率
cargo test test_verify_all_core_files -- --nocapture

# 查看单个文件验证率
cargo test test_verify_list_thy_sample -- --nocapture

# 运行 LSP 服务器
cargo run -- --lsp
```

## 架构

```
.thy 源文件 (theories/HOL/, 115 files)
    ↓ parse_lemmas() ───────────────────────── [hol_loader.rs]
    │   ├─ parse_datatypes()    → 合成 induct/exhaust/case 规则
    │   ├─ parse_primrecs()     → 合成 simp 规则
    │   ├─ parse_classes()      → 合成类型类常量
    │   └─ parse_lemmas_cmd()   → 别名解析
    ↓
ParsedLemma { name, theorem, proof_script, alias_for }
    ↓
HolTheoremDb (15,804 theorems indexed, 15,395 by-name)
    ↓
verify_lemma() ───────────────────────────── [method.rs]
    ├─ [结构化] ProofState::interpret_proof_script()
    │     ├─ fix / assume → 上下文扩展
    │     ├─ have / show  → exec_proof + 事实累积
    │     ├─ case / next  → 子目标导航
    │     └─ qed          → 证明终结
    ├─ [简单] exec_proof() → exec_single_method()
    │     ├─ auto_exec  (assume→simp→resolve→eresolve→dresolve)
    │     ├─ blast_exec (+symmetry +order_antisym +dresolve)
    │     ├─ exec_induct (auto→blast→rule lookup→HO matching)
    │     ├─ exec_simp   (rewrite_deep + add:/only:/del:)
    │     ├─ exec_subst  (equational substitution)
    │     └─ exec_arith  (basic arithmetic simplification)
    ↓
ThmKernel (15 operations, zero panics) ───── [thm.rs]
    ├─ 12 primitives
    └─ 3 kernel derived (bicompose, bicompose_eresolve, subst_premise)
```

## 路线图

详见 [docs/ROADMAP.md](docs/ROADMAP.md)

| 阶段 | 目标 | 验证率 | 状态 |
|------|------|:--:|:--:|
| Phase 0-3 | 内核 + 证明引擎 + DAG | 61.3% | ✅ |
| Phase 4 | `datatype`/`class`/`primrec` 解析 | 72% | ✅ |
| Phase 5 | 条件重写 + Method 深化 | 78% | ✅ |
| Phase 6 | Isar 引擎集成 | 87% | 🟡 |
| Phase 7 | 全 HOL 库 + `cargo publish` | 92% | 🔵 |
| Phase 8 | 多逻辑 + 工具链 | 95%+ | ⚪ |

## 文档

- [架构设计](docs/ARCHITECTURE.md)
- [开发路线图](docs/ROADMAP.md)
- [开发者指南](docs/DEVELOPMENT.md)
- [Isabelle 对照](docs/ISABELLE_COMPARISON.md)

## 项目统计

| 指标 | 数值 |
|------|------|
| Rust 代码 | ~20,000 行 |
| 源文件 | 84 `.rs` |
| `.thy` 文件 | 116 (115 HOL + 1 Pure) |
| 定理总数 | 15,804 |
| by-name 索引 | 15,395 |
| 测试 | 210+ |
| 仓库 | 11 MB |
