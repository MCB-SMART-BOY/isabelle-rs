# isabelle-rs v1.8.1+ → v1.9.0 移交提示词

> Archive note: this is a historical v1.9.0 handoff snapshot. Its percentages,
> method counts, and “complete” labels are not current trust or compatibility
> claims. Read root [AGENTS.md](../AGENTS.md),
> [PROJECT_STATUS.md](PROJECT_STATUS.md), [TRUST.md](TRUST.md), and
> [ROADMAP.md](ROADMAP.md) instead.

> 本会话：2026-06-04 | 主要成果：完成 Phases 49-54，v1.9.0 基础设施全部交付

---

## 一、你在接手的项目

isabelle-rs — Isabelle 证明助手内核的 Rust 移植。本会话完成了 v1.9.0 的 6 个 Phase，交付了 HOL 基础设施现代化。

### 历史状态快照（不可作为当前状态）

| 指标 | 值 |
|------|-----|
| 内核 | 15 ops + tpairs/shyps, 0 Typ::dummy() ✅ |
| 证明方法 | 27 (含 Meson) |
| 核心验证 | **5/5 files 125/125 (100%)** 26s |
| Tier2 验证 | **6/20 files 100%** (Fun, Product_Type, Sum_Type, Lattices, Groups, Rings) |
| 编译警告 | **0** |
| 代码量 | ~48K Rust LOC, 127 files |
| 测试 | 780+ |

### 本次会话新增模块

| 文件 | 行数 | 测试 | 对应 Isabelle 源 |
|------|:---:|:---:|------|
| `src/hol/hologic.rs` | 580 | 21 | `HOL/Tools/hologic.ML` (23K) |
| `src/hol/simpdata.rs` | 290 | 3 | `HOL/Tools/simpdata.ML` (7K) |
| `src/isar/args.rs` | 310 | 18 | `Pure/Isar/args.ML` (7K) |
| `src/hol/defs.rs` | 275 | 6 | `Pure/defs.ML` (9K) |
| `src/isar/spec.rs` 增强 | +340 | 19 | `Pure/Isar/specification.ML` (19K) |

### 文档整合结果

- 根目录：README.md, CLAUDE.md, CHANGELOG.md（3 个）
- docs/：ARCHITECTURE.md, DEVELOPMENT.md, GAP_ANALYSIS.md, ROADMAP.md, SESSION_TRANSFER.md, SESSION_TRANSFER_v1.9.0.md
- `ISABELLE_COMPARISON.md` → 合并到 `GAP_ANALYSIS.md`
- `PLAN_v1.9.0.md` → 合并到 `ROADMAP.md`
- 0 个死链接，0 冗余

---

## 二、本会话的关键发现

### 2.1 hologic.rs 是最大的单一价值交付

Isabelle 的 `hologic.ML` 有 23K 行，而 isabelle-rs 之前只有 43 行的 `term_builder.rs`（还是死代码——未注册到 mod.rs）。HOL 项操作（Trueprop/eq/conj/disj/imp/Not/All/Ex 等）散落在 25+ 文件中使用 ad-hoc pattern matching。

**解决方案**：`src/hol/hologic.rs` — 580 行，40+ mk_*/dest_*/is_* API，21 个测试。所有 HOL 常量和类型集中在一个地方。

### 2.2 simpdata 统一了 simp 规则初始化

之前 `exec_simp` 和 `exec_auto` 各自构建临时的 simp 规则列表。现在 `simpdata.rs` 提供 `init_hol_simpset()` 统一入口，`exec_simp` 自动包含 builtin HOL 连接词重写规则。

### 2.3 属性系统已经完整

审计发现 attrib.rs（323 行）已经完整实现：属性解析、分类、DB 类别计算。管道已连接：`parse_attrs → classify → compute_db_categories → DB分发`。CLAUDE.md 中 "属性系统不完整" 的已知问题已过时。

### 2.4 `depth -= 1` 溢出修复

Tier2 验证时 `method.rs:2916` panic（attempt to subtract with overflow），修复为 `depth.saturating_sub(1)`。这个模式要记住——所有减法都应该用 saturating_sub。

---

## 三、已知问题（更新后）

| 优先级 | 问题 | 状态 |
|:--:|------|:--:|
| 🟡 | `test_batch_scan_theories` 256MB 栈溢出 | 根因待定 |
| 🟡 | `test_batch_verify_all` timeout/slow | accept_all 可用 |
| 🟡 | Tier2/Tier3 验证不完整 | 6/20 Tier2 100%，其余待测 |
| 🟡 | Metis 方法 → auto fallback | metis.rs 存在但 dispatch 用 auto 兜底 |
| 🟢 | `simp` pass rate limited | ✅ simpdata.rs 已改善 |
| 🟢 | Method argument parsing | ✅ args.rs 已实现 |
| 🟢 | 属性系统集成不完整 | ✅ 审计确认管道完整 |

---

## 四、历史会话当时的优先级（已废止）

当时的建议依次是扩大 Tier2/Tier3 验证、连接 Metis，以及深化
ATP/Sledgehammer。它们仅记录 v1.9.0 交接时的方向，现已被
[`ROADMAP.md`](ROADMAP.md) 中以不可变 theory/signature identity 和唯一
`KernelTrustedClosed` 接收入口为先的依赖顺序取代。
---

## 五、关键文件和命令

### 验证命令

核心、lib、Tier2 与快速检查命令现分别由
`scripts/dev-check.sh core`、`lib`、`tier2` 和 `fast` 维护。该归档保留
历史结果，但不再复制可能失效的命令行。

### 新增模块速查

| 模块 | 用途 |
|------|------|
| `hol::hologic` | mk_Trueprop / dest_Trueprop / mk_eq / dest_eq / mk_conj / dest_conj / conjuncts / mk_imp / dest_imp / mk_not / dest_not / mk_all / mk_exists / mk_mem / dest_mem / mk_set / mk_prod / dest_prod / mk_nat / dest_nat / mk_numeral / dest_numeral / mk_list / dest_list / mk_if / dest_if / mk_Let |
| `hol::simpdata` | init_hol_simpset() / mksimps_pairs() / mk_meta_eq() / mk_eq_True() |
| `isar::args` | Args::parse_modifiers() / Args::parse_goal_spec() / Args::extract_clause() / MethodArgs struct |
| `hol::defs` | Defs::empty() / define() / merge() / get_deps() / cycle detection |
| `isar::spec` | Typedecl / Specification / LocalDef / Definition / Axiomatization / Abbreviation / TypeAbbrev |

### 核心源码参考

- `src/hol/hologic.rs` — 580 行，HOL 项操作
- `src/hol/simpdata.rs` — 290 行，simp 初始化
- `src/isar/args.rs` — 310 行，方法参数解析
- `src/hol/defs.rs` — 275 行，定义一致性检查
- `src/isar/spec.rs` — ~500 行，规范命令解析
- `src/isar/method.rs` — 4262 行，27 方法 + verify_lemma
- `src/hol/hol_loader.rs` — 4584 行，.thy 解析 + HolTheoremDb
- `src/core/simplifier.rs` — 540 行，⚠️ prove_condition 不能递归重写
- `src/core/thm.rs` — 1444 行，LCF 内核（只有这里能构造 Thm）

### Isabelle 参考源

- `isabelle-source/src/HOL/Tools/hologic.ML` — hologic.rs 的参考
- `isabelle-source/src/HOL/Tools/simpdata.ML` — simpdata.rs 的参考
- `isabelle-source/src/Pure/Isar/args.ML` — args.rs 的参考
- `isabelle-source/src/Pure/defs.ML` — defs.rs 的参考
- `isabelle-source/src/Pure/Isar/specification.ML` — spec.rs 的参考
- `isabelle-source/src/Pure/Isar/typedecl.ML` — TypeAbbrev 的参考

---

## 六、架构和设计原则

1. **对照 Isabelle 源码写，不要自己发明** — hologic/simpdata/args/defs 都是先读 Isabelle 源再写 Rust

2. **prove_condition 铁律** — 绝不能在里面调 `self.rewrite()` 或 `self.rewrite_deep()`。只允许 trivial True + condition_solver。见 `src/core/simplifier.rs:317-340`

3. **栈溢出调试方法** — thread_local 计数器 + eprintln probe，不要盲猜

4. **新模块必加 tests** — 本会话新增 86 个测试，全部通过

5. **验证是 3 阶段 pipeline**: 解析(空DB) → 构建本地DB → 逐lemma证明重放

6. **Thm 只能从 src/core/thm.rs 构造** — 外部用 ThmKernel

7. **改动后跑 `test_verify_all_core_files`** — 5 files 125 lemmas，不能有退化

8. **所有 `depth -= 1` 都要用 `saturating_sub(1)`** — 本会话修了一个溢出

---

## 七、当前工作入口

不要从本归档选择下一项任务。先阅读根
[`AGENTS.md`](../AGENTS.md)、[`PROJECT_STATUS.md`](PROJECT_STATUS.md)、
[`TRUST.md`](TRUST.md) 和 [`ROADMAP.md`](ROADMAP.md)，并按其中当前的
可信主线和验证要求执行。
