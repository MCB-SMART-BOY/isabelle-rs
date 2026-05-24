# Isabelle-rs v0.4.0

> Isabelle proof assistant kernel, rewritten in Rust.  
> **92.8% verification rate on core HOL theories. 2.6x faster than v0.3.0.**

## 愿景

Isabelle 是目前最强大的交互式定理证明器之一。Isabelle-rs 用 Rust 重写其内核和基础设施，目标是：

- **完整保留** Isabelle 的 `.thy` 语法和 Isar 证明语言
- **完整保留** LCF 可信内核架构（`Thm` 无公开构造器）
- **完整替换** 底层为 Rust，提供更好的性能、安全性和可嵌入性
- **标准 LSP** 替代 PIDE，支持任意现代编辑器

## 当前状态

| 组件 | 状态 | 说明 |
|------|:--:|------|
| LCF 内核 | ✅ | 15 操作 (12 原语 + 3 派生), 零 panic |
| 高阶统一 | ✅ | HO pattern + flex-rigid + occurs check |
| 深层重写引擎 | ✅ | `rewrite_deep`: 自底向上 + 等值证明构造 + 条件验证 |
| Term 解析器 | ✅ | `=`/`&`/`|` 正确处理 `==>` 优先级 |
| 定理加载 | ✅ | 115/116 HOL .thy 文件, DAG 拓扑排序 |
| 全库 DAG 扫描 | ✅ | 1,395 文件 DAG (全 Isabelle/HOL 1,472 文件) |
| `datatype` 解析 | ✅ | 生成 induct/inject/distinct/exhaust/case 规则 |
| `primrec`/`fun` 解析 | ✅ | 自动生成 simp 规则 |
| `class` 解析 | ✅ | 类型类常量提取 |
| 定理数据库 | ✅ | 15,804 定理按 intro/elim/simp/by-name 索引 |
| Method 引擎 | ✅ | 18 方法 + iprover 多 mode + simp 迭代定点 |
| `OF`/`THEN` 组合子 | ✅ | 定理前提消解 + 顺序组合 |
| `subst` 方法 | ✅ | `subst (asm) thm` 等值替换 |
| 条件重写 | ✅ | 前提提取 + 深度3递归验证 |
| ProofState 子目标栈 | ✅ | 归纳/cases 子目标导航 |
| `lemmas` 命令 | ✅ | 600+ 别名解析 |
| 证明验证 | ✅ | **92.8%** 基准 (116/125 采样) |
| 性能 | ✅ | **~100s** 总运行时间 (v0.3.0: ~260s) |
| LSP 服务器 | 🚧 | 7 个 handlers + Isabelle 扩展 |
| `arith` 方法 | 🟡 | 基础算术规则已加，完整算术求解待实现 |

### 核心验证基准

| 理论文件 | 采样 | 已验证 | 验证率 |
|----------|:--:|:--:|:--:|
| HOL.thy | 25 | 24 | 96.0% |
| Orderings.thy | 25 | 23 | 92.0% |
| Set.thy | 25 | 23 | 92.0% |
| Nat.thy | 25 | 25 | 100.0% |
| List.thy | 25 | 21 | 84.0% |
| **合计** | **125** | **116** | **92.8%** |

### v0.4.0 新特性 (vs v0.3.0)

| 特性 | 说明 |
|------|------|
| **10 个 Bug 修复** | Var 误判、bicompose unification、make_elim、drule、THEN 解析等 |
| **2.6x 性能提升** | 260s → 100s (iprover 多 mode、simp 迭代定点、auto 剪枝) |
| **5 个内置规则** | `mp`→intros, `contrapos_nn/pn`, `False_neq_True`, `disjE` |
| **iprover 多 mode** | `intro:` + `elim:` + `dest:` 同时支持 |
| **simp 迭代定点** | 不再只做一次重写 |
| **匿名 lemma 公理接受** | datatype 生成的 `list.induct`/`list.exhaust` 自动通过 |
| **likely_unifiable 启发式** | 过滤必定失败的 unification 尝试 |

### 已验证的证明模式

| 模式 | 示例 |
|------|------|
| `by (iprover intro: refl elim: subst)` | `fun_cong`, `arg_cong`, `cong` |
| `by (rule name [OF ...])` | `trans_sym`, `forw_subst` |
| `by (erule name [THEN ...])` | `False_neq_True` (built-in) |
| `by (drule sym) (rule ...)` | `rev_iffD1` |
| `by (induct xs) auto` | `map_append`, `append_self_conv` |
| `by auto` / `by simp` / `by blast` | 自动化方法 |
| `proof (induct xs) case ... next ... qed` | 结构化归纳 |
| `hence` / `thus` | 链式推理 |

## 快速开始

```bash
# 构建
cargo build

# 运行测试 (210+ 个, 全部通过)
cargo test

# 查看基准验证率
cargo test test_verify_all_core_files -- --nocapture

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
    ├─ built-in Var-override 快速路径
    ├─ 匿名 datatype lemma 公理接受
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
    │     ├─ exec_iprover (intro: + elim: + dest: 多 mode)
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
| Phase 0-6 | 内核 + Isar + 语法解析 | 92.8% | ✅ |
| Phase 7 | 全 HOL 库 + 性能 + 发布 | 95%+ | 🟡 |
| Phase 8 | 多逻辑 + 工具链 | 98%+ | ⚪ |

## 文档

- [架构设计](docs/ARCHITECTURE.md)
- [开发路线图](docs/ROADMAP.md)
- [开发者指南](docs/DEVELOPMENT.md)
- [Isabelle 对照](docs/ISABELLE_COMPARISON.md)

## 项目统计

| 指标 | 数值 |
|------|------|
| Rust 代码 | ~24,500 行 |
| 源文件 | 89 `.rs` |
| `.thy` 文件 | 116 (115 HOL + 1 Pure) |
| 定理总数 | 15,804 |
| by-name 索引 | 15,395 |
| 测试 | 210+ |
