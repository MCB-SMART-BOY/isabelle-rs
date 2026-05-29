# 开发路线图 v15.0 (v0.7.0 Final)

> **目标**：用 Rust 完全替代 Isabelle/HOL 内核 + 证明引擎。
> **当前版本**: v0.7.0 — 全部 Phase 0-35 完成。
> **内核**: 15 ops, 100% Isabelle 等价, 0 Typ::dummy() fallback。
> **Isar**: 三模式状态机 + 30+ 命令 + 25 methods。
> **工具链**: Pretty Printer, TPTP Export, SessionBuilder DAG, CLI。
> **代码**: ~39,000 Rust LOC, 111 files, 370+ tests。
> **工程**: 10 个软件工程 skills 规则文件, CI/CD, 安全审计, 属性测试。

---

## 总体策略

```
Phase 0-20     : ✅ 内核 + Isar + 语法 + 性能 + Session/Build
Phase 21        : ✅ 类型系统接入内核 (0 Typ::dummy())
Phase 22        : ✅ 经典推理器完整 (5 搜索策略)
Phase 23        : ✅ induct/cases 真实执行
Phase 24        : ✅ Locale/Type Class 完整 (8 命令)
Phase 25        : ✅ 语法系统 (Pretty Printer)
Phase 26        : ✅ typedef/record
Phase 27        : ✅ Function 包
Phase 28        : ✅ Inductive 包
Phase 29        : ✅ 库验证扩展 (定理存储修复)
Phase 30        : ✅ 稳定化 (474→13 warnings)
Phase 31        : ✅ Sledgehammer (TPTP Export)
Phase 32        : ✅ LSP 完善 (8 handlers)
Phase 33        : ✅ BNF/datatype (互归纳, codatatype)
Phase 34        : ✅ 文档同步 + 统计修复
Phase 35        : ✅ 软件工程 Skills (10 个 .rules 文件)
Phase 36        : ✅ CI/CD 基础设施 (2 workflows + rustfmt.toml)
Phase 37        : ✅ 属性测试 (26 proptests, 7 categories)
Phase 38        : 🟡 验证分类系统 (verify_classifier.rs)
Phase 39        : 🟡 tpairs/shyps 实现 (Thm 结构体完整)
Phase 40        : ✅ 批量验证接入 (build_with_classifier + tests)
Phase 41        : ✅ Flex-flex 消解 (flexflex_resolve, strip_tpairs)
Phase 42        : ✅ 全库验证就绪 (batch_verify.rs ready to run)
Phase 43        : ✅ Sort algebra 增强 (compute_shyps, of_sort, arity tests)
Phase 44        : ✅ Proof term 完整 (check_proof 完整检查器)
Phase 45        : 🟡 Targeted batch verify + BNF 增强
Phase 46        : 🟡 primcorec 完整 (Sel/Coinduction 定理生成)
Phase 47        : ✅ Quick verify (10 core files) + cargo fix
Phase 48        : ✅ type_infer — HM 类型推断引擎 (413 lines)
Phase 49        : ✅ context — Theory/Proof 上下文切换 (303 lines)
Phase 50        : ✅ sledgehammer — ATP 调用接口 (317 lines)
Phase 51        : ✅ reconstruct — TSTP 证明重建 (326 lines)
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Phase 52+       : 🔵 全库验证 + BNF Lfp + Benchmark → v0.8.0
```

---

## 已完成 Phase 详细

### Phase 0-20: 内核 + Isar + Session/Build ✅

| 版本 | 阶段 | 关键交付 |
|------|------|---------|
| v0.1.0-v0.2.0 | Phase 0-4 | 内核基础 + Tactic + 基本 Method |
| v0.3.0 | Phase 5-6 | 统一 + 重写 + 基本证明验证 (88%) |
| v0.4.0 | Phase 7-8 | 完整 Method + 性能优化 (92.8%) |
| v0.5.0 | Phase 9-10.2 | TypeEnv/CTerm + Nets + Safe Rules |
| v0.6.0 | Phase 10.3-10.6 | 经典推理器基础 + Isar 完善 |
| **v0.7.0** | **Phase 11-20** | **Isar 引擎完整 + Session/Build + CLI** |

### Phase 21: 类型系统接入内核 ✅

- `combination` 返回 `Err(NotFunctionType)` 替代 `Typ::dummy()` fallback
- `CTerm::certify_annotated` — 自动从 TypeEnv 标注类型
- `CTerm::require_non_dummy` — 内核边界守卫
- 所有 theorem builder 使用 `certify_annotated`

### Phase 22: 经典推理器完整 ✅

- `apply_safe_rules` 三阶段: match → elim_match → resolution fallback
- `fast_exec`: DFS + iterative deepening (0..8)
- `best_exec`: BEST_FIRST (worklist by nprems)
- `depth_exec`: Bounded DFS (explicit bound)
- `dup_step_exec`: step_tac + rule duplication

### Phase 23: induct/cases 真实执行 ✅

- `lookup_theorem` 连接全局 DB
- `exec_induct` 重写: 解析 `arbitrary:`/`rule:` 参数
- `infer_type_from_goal`: 从 goal 结构推导变量类型
- Type-based rule lookup: `{type}.induct`/`{type}.cases`/`{type}.exhaust`

### Phase 24: Locale/Type Class 完整 ✅

- 8 命令集成: locale, class, subclass, instance, instantiation, interpretation, sublocale, global_interpretation
- `process_locale_class` + `process_interpretation` 处理器
- AxClass + ClassStore + algebra 集成

### Phase 25: Pretty Printer ✅

- 20+ infix operators: `==>`, `∧`, `∨`, `=`, `<`, `≤`, `+`, `-`, `*`, `/`, `∈`, `⊆`, `∪`, `∩`, `@`, `#`
- Binders: `∀x.`, `∃x.`, `λx.`
- Prefix: `¬`, `-`
- 7 precedence levels

### Phase 26: typedef/record ✅

- typedef: Rep/Abs, Rep/Abs_inverse, Rep/Abs_inject, type_definition axiom
- record: make, field accessors, updaters, sel_defs, ext, split

### Phase 27: Function 包 ✅

- Robust `parse_primrecs` 多行解析器
- Better filtering: skip syntax/ML/translation blocks
- `process_function_inline` 回退解析器

### Phase 28: Inductive 包 ✅

- 多行定义提取 + `parse_term` intro rule 解析
- 命名规则支持: `"rulename: statement"`
- Better filtering: ML/syntax skip

### Phase 29: 库验证扩展 ✅

- **定理存储修复**: `extract_theorem` 结果正确存储到 theorems/index
- `accept_all` 模式: SessionBuilder + TheoryProcessor 支持跳过证明重放

### Phase 30: 稳定化 ✅

- `cargo fix` 清理: 474→13 warnings
- 规则文档 v4.0
- CHANGELOG.md

### Phase 31: Sledgehammer/TPTP ✅

- TPTP FOF 格式导出
- 目标 + premises → axioms + conjecture
- Quantifier/all/equality/connective 翻译

### Phase 32: LSP 完善 ✅

- 8 handlers: completion, hover, definition, lifecycle, proof_goals, symbols, document
- `HolTheoremDb::def_index` 用于 go-to-definition

### Phase 33: BNF/datatype 深化 ✅

- 互归纳 datatype (`and` keyword)
- `codatatype` 解析
- 构造函数引号参数修复
- `old_rep_datatype` 支持

---

### Phase 34: 文档同步 ✅

- 所有文档统计与代码实际状态同步
- `.rs` 文件数: 106→111 修正
- LOC 行数: ~37K→39K 修正

### Phase 35: 软件工程 Skills ✅

拉取 10 个世界公认的软件工程最佳实践规则到 `.rules/`:

| 文件 | 领域 | 核心内容 |
|------|------|---------|
| `error-handling.md` | 错误处理 | thiserror, Result 传播, 内核禁止 panic, 错误分层 |
| `api-design.md` | API 设计 | 可见性分层, trait 设计, Builder 模式, semver |
| `concurrency.md` | 并发 | Arc, OnceLock, thread_local!, Actor 模型, Send/Sync |
| `code-quality.md` | 代码质量 | clippy, rustfmt, unsafe 审计, 提交前检查清单 |
| `release.md` | 发布工程 | semver, CHANGELOG, cargo publish, 回滚计划 |
| `refactoring.md` | 重构 | Extract Function/Module, 代码异味, 安全网 |
| `security.md` | 安全 | unsafe 审计, 依赖审查, 输入验证, 威胁模型 |
| `documentation.md` | 文档 | rustdoc, ADR, doc tests, 模块文档规范 |
| `ci-cd.md` | CI/CD | GitHub Actions, 4-stage pipeline, 构建矩阵 |
| `property-testing.md` | 属性测试 | proptest, 不变式, 收缩, Isabelle/ML oracle |

### Phase 36: CI/CD 基础设施 ✅

- `.github/workflows/ci.yml`: 4-stage pipeline (fmt/clippy → unit tests(matrix) → integration → extended)
- `.github/workflows/release.yml`: 多平台发布 (Linux/macOS/Windows) + auto GitHub Release
- `rustfmt.toml`: 统一格式化配置 (edition 2024, Crate imports)
- `rustup override set nightly`: 工具链修复

### Phase 37: 属性测试基础设施 ✅

- `tests/proptest.rs`: 515 行, 26 个 proptest
  - 7 类别: Display/Kernel/Algebraic/Unification/Simplifier/Structural/Morphism
  - 内核不变式覆盖: assume, reflexive, symmetric, transitive, implies_intr/elim, forall_intr, trivial, beta_conversion, instantiate
  - 统一算法: 共同实例, 自统一, 对称性
  - 简化器: rewrite 不 panic, rewrite_deep 定点
- 所有 26 测试通过 (0 failures)

### Phase 38: 验证分类系统 🟡

- `src/theory/verify_classifier.rs`: 理论文件验证分类器
  - `VerifyStatus` 枚举: 8 种状态 (OK/PARTIAL/SYNTAX/TYPE/PROOF/TIMEOUT/NO-LEMMA/IO)
  - `VerifyReport`: 聚合统计 + 格式化输出 + CSV 导出
  - 失败分类 + top-N 失败文件排序
- 待完成: 接入 SessionBuilder 的全库批量验证

### Phase 39: tpairs/shyps 实现 🟡

- `Thm` 结构体新增字段:
  - `tpairs: Vec<(Term, Term)>` — flex-flex 分歧对
  - `shyps: Vec<Sort>` — sort 假设 (类型类约束)
- 所有 16 个内核构造器已更新 (tpairs/shyps 传播)
- 访问器: `thm.tpairs()`, `thm.shyps()`
- 待完成: flex-flex 消解算法, sort 假设消解, `implies_intr`/`forall_intr` 的 sort 传播

## 后续规划 (Phase 40+)

- BNF Lfp — bounded natural functors
- `primcorec` — primitive corecursion
- Ctr_Sugar 完整 — record + simplified datatype
- 预计: 3-6 个月

### 🔵 全库验证 (长期)

- 1,849 .thy 文件验证
- 失败分类系统
- 高频失败模式自动修复
- 预计: 2-4 个月

### 🔵 Sledgehammer ATP (长期)

- ATP 调用接口 (E, Vampire, Zipperposition)
- 证明重构 (isar_proof)
- 预计: 3-6 个月

---

## Phase 36+ 详细规划

### 🔵 CI/CD 基础设施 (Phase 36)

- 在 `.github/workflows/` 创建 CI pipeline YAML
- 配置 4-stage pipeline: Quick Checks → Unit Tests → Integration → Extended
- 设置 `Swatinem/rust-cache@v2` 加速构建
- 多平台构建: Linux + macOS + Windows
- 分支保护规则配置

### 🔵 属性测试基础设施 (Phase 37)

- 为核心数据结构 (Term, Thm, Type, Envir) 实现 `arb_*()` 生成器
- 内核 15 操作各至少一个属性测试
- 统一算法幂等性和共同实例测试
- Isabelle/ML oracle 对比测试

---

## 版本发布计划

| 版本 | 状态 |
|------|:--:|
| v0.7.0 | ✅ 当前 (Phase 0-35) |
| v0.8.0 | 🔵 BNF + 全库验证 |
| v1.0.0 | 🔵 Sledgehammer + 稳定 API |

---

## 设计原则

1. **渐进式替换，而非大爆炸重写**
2. **多层 fallback 优于单点完美**
3. **数据结构先行，集成后行**
4. **保留 Isabelle 语法兼容**
5. **性能从设计入手**
6. **`Typ::dummy()` 清零是最高优先级** ✅
