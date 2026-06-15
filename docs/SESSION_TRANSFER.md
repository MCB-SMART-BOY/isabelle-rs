# isabelle-rs v1.8.1 → v1.9.0 移交提示词

> 前一会话：2026-06-04 | 主要成果：修复 List.thy 栈溢出，解锁 5/5 core files 100% 验证

---

## 一、你在接手的项目

isabelle-rs v1.8.1 — Isabelle 证明助手内核的 Rust 移植。LCF 可信内核 + 高阶合一 + Isar 证明语言 + theory 加载管线。

### 当前状态速览

| 指标 | 值 |
|------|-----|
| 内核 | 15 ops + tpairs/shyps, 0 `Typ::dummy()` ✅ |
| 证明方法 | 27 个 (含 Meson) |
| 核心验证 | **5/5 files 125/125 (100%)** ← 本次会话达成 |
| HOL/HOL.thy | 25/25 ✅ |
| HOL/Orderings.thy | 25/25 ✅ |
| HOL/Set.thy | 25/25 ✅ |
| HOL/Nat.thy | 25/25 ✅ |
| HOL/List.thy | 25/25 ✅ ← **刚修复，之前即使 256MB 栈也溢出** |
| 编译警告 | 0 ✅ |
| 代码量 | ~46K Rust LOC, 121 files |

### 待解决的已知问题

| 优先级 | 问题 | 描述 |
|:--:|------|------|
| P0 | `hologic.ML` 缺失 | HOL 项操作 (`dest_Trueprop`, `mk_eq`, `dest_conj` 等) 散落各处 ad-hoc pattern matching，边缘情况静默失败 |
| P0 | `simpdata.ML` 缺失 | `by simp` 是最常用方法但初始 simp 规则集不完整 |
| P0 | `args.ML` 方法参数解析 | `simp add: foo del: bar` / `induct rule: baz` 语法不完整 |
| P0 | `specification.ML` | `fun`/`function`/`inductive` 命令的底层基础设施 |
| P1 | `test_batch_scan_theories` | 扫描 115 个 HOL theories 时栈溢出（根因待定，已排除 prove_condition） |
| P1 | `defs.ML` | 定义一致性检查缺失，威胁 LCF 可信性 |
| P1 | `typedecl.ML` | 非定义性类型引入 |
| P1 | `local_defs.ML` | Isar 证明中 `def`/`define` 局部缩写 |
| P1 | ATP 桥接 | Sledgehammer 真正调用外部求解器 (E/Vampire) |
| P2 | Metis 真正集成 | 当前 metis → auto fallback |
| P2 | 属性系统完整 | `[simp]`/`[intro!]`/`[elim!]` 全 pipeline |

---

## 二、本次会话的关键发现

### 2.1 List.thy 栈溢出的真正根因（重要！）

**不是你预期的 auto_exec 深递归。** 是 `src/core/simplifier.rs` 里的 `prove_condition` 无限相互递归：

```
prove_condition(cond, depth=0)
  → self.rewrite(cond)          # 遍历全部 134 条 simp 规则
    → try_rule(rule_N)           # 匹配到有条件规则
      → prove_condition(cond2, 0)  # depth 又回到 0！永远不增长！
        → self.rewrite(cond2)
          → ... 无限循环 → 栈溢出
```

**Isabelle 源码对照** (`isabelle-source/src/Pure/raw_simplifier.ML:1480`):
```ml
val simple_prover =
  SINGLE o (fn ctxt => ALLGOALS (resolve_tac ctxt (prems_of ctxt)));
```
Isabelle 只用假设消解条件前提，绝不递归重写条件本身。

### 2.2 修复方案（v1.8.1）

`prove_condition` 简化为：
1. 检查条件是否 trivially `True`
2. 委托给外部 `condition_solver`（ArithSolver/AsmSolver）
3. 返回 `false` — 不再调用 `self.rewrite()`/`self.rewrite_deep()`

**修改文件**: 只有 `src/core/simplifier.rs` 一个函数

**结果**: List.thy 从溢出 → 25/25 (100%) 0.8s。全 5 个核心文件 125/125 (100%)。

### 2.3 新增 Iron Law（CLAUDE.md 第 12 条）

```
12. prove_condition 绝不能调用 self.rewrite() 或 self.rewrite_deep()
   — 这会通过 rewrite → try_rule → prove_condition 产生无界相互递归。
   Isabelle 的 simple_prover 只做 ALLGOALS (resolve_tac ctxt (prems_of ctxt))。
   只有 trivial True + condition_solver 是安全的。
```

### 2.4 不需要做的事

以下函数**不需要**迭代化（本次会话已验证它们不是溢出根因）：
- `auto_exec` (depth cap 15, 工作正常)
- `blast_exec` (depth cap 15)
- `dfs_search`/`dfs_subgoals` (bound cap 7)
- `step_exec` (depth cap 10)
- `dup_step_exec` (depth cap 12)

`depth_search` 已加了 `bound > 20` 安全帽。

---

## 三、优先级排序的下一步工作

按影响力从高到低：

### 🥇 第一优先：hologic.ML 移植
- **为什么**: HOL.thy 本身依赖。`dest_Trueprop`/`mk_eq`/`dest_conj`/`mk_imp` 等操作散落在各处 pattern matching，边缘情况静默失败。几乎所有 HOL .thy 文件都受影响。
- **Isabelle 源**: `isabelle-source/src/HOL/Tools/hologic.ML` (23K ML)
- **新建文件**: `src/hol/hologic.rs`
- **关键 API**:
  - `dest_Trueprop(t)` — 剥掉 Trueprop 包装
  - `mk_eq(lhs, rhs)` — 构造等式
  - `dest_eq(t)` — 解构等式
  - `mk_imp(prem, concl)` — 构造蕴含
  - `dest_imp(t)` — 解构蕴含
  - `mk_conj(a, b)` / `dest_conj(t)`
  - `mk_disj(a, b)` / `dest_disj(t)`
  - `mk_All(var, body)` / `dest_All(t)`
  - `mk_Ex(var, body)` / `dest_Ex(t)`
  - numeral/if/let 处理

### 🥈 第二优先：simpdata.ML 移植
- **为什么**: `by simp` 是最常用的证明方法。正确初始化 simp 规则集直接提升验证成功率。
- **Isabelle 源**: `isabelle-source/src/HOL/Tools/simpdata.ML` (7K ML)
- **需要**: 在 `hol_loader.rs` 或新建 `src/hol/simpdata.rs` 中正确初始化 HOL simpset

### 🥉 第三优先：args.ML 方法参数解析
- **为什么**: `simp add: foo del: bar`、`induct rule: baz`、`auto simp: thm` 等大量证明方法依赖参数解析
- **当前状态**: method.rs 有 165K 但参数解析不完整

### 第四优先：specification.ML 基础设施
- 解锁 `fun`/`function`/`inductive`/`primrec` 命令的正确解析

### 后续：defs.ML / typedecl.ML / local_defs.ML
- 补全 Isar 证明语言的语法支持

---

## 四、关键文件和命令

### 验证命令
```bash
# 核心 5 文件验证（每次改动后必跑）
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files --lib -- --nocapture

# 全量 lib 测试（慢，但全面）
RUST_MIN_STACK=268435456 cargo test --lib

# 快速编译检查
cargo build && cargo clippy -- -D warnings
```

### 项目入口
- `CLAUDE.md` — 项目全貌 + Iron Laws + 架构
- `.claude/rules/` — 领域规则触发文件
- `docs/ROADMAP.md` — 版本路线图
- `docs/GAP_ANALYSIS.md` — Isabelle 差距分析
- `docs/ARCHITECTURE.md` — 架构文档
- `CHANGELOG.md` — 版本变更记录

### 核心源码
- `src/core/simplifier.rs` — **刚修改过**，prove_condition 不能递归重写
- `src/isar/method.rs` — 165K，25 个证明方法 + verify_file/verify_lemma
- `src/hol/hol_loader.rs` — 174K，theory 解析 + HolTheoremDb
- `src/core/thm.rs` — LCF 内核（只有这里能构造 Thm）
- `src/core/unify.rs` — 高阶合一（已迭代化）
- `src/core/tactic.rs` — 策略和组合子

### Isabelle 参考源
- `isabelle-source/src/Pure/raw_simplifier.ML` — 简化器（刚用来验证 prove_condition 设计）
- `isabelle-source/src/Pure/Isar/method.ML` — 方法系统
- `isabelle-source/src/HOL/Tools/hologic.ML` — HOL 项操作（下一步要移植）
- `isabelle-source/src/HOL/Tools/simpdata.ML` — simp 规则数据库
- `isabelle-source/src/Pure/Isar/args.ML` — 方法参数解析

---

## 五、架构和设计原则（不要重蹈覆辙）

1. **对照 Isabelle 源码写，不要自己发明** — 本次会话证明：如果我一开始就查 `raw_simplifier.ML` 里的 `simple_prover`，半小时就能定位问题。下一会话的 hologic/simpdata/args 移植也必须**先读 Isabelle 源码再写代码**。

2. **prove_condition 铁律** — 绝对不能在里面调 `self.rewrite()` 或 `self.rewrite_deep()`。这会产生 rewrite → try_rule → prove_condition 无限相互递归。只允许 trivial True + condition_solver。

3. **栈溢出调试方法** — 加 thread_local 计数器 + eprintln 比盲猜快 100 倍。先用 probe 定位精确溢出点，再修。

4. **所有新方法遵循 4 步模式**: enum variant → execute_depth → impl → exec_single_method

5. **验证是 3 阶段 pipeline**: 解析(空 DB) → 构建本地 DB → 逐 lemma 证明重放

6. **Thm 只能从 src/core/thm.rs 构造** — 外部用 ThmKernel

7. **改动后跑 `test_verify_all_core_files`** — 5 files 125 lemmas，不能有退化

---

## 六、实用技巧

- `cargo fmt -- src/core/simplifier.rs` — 只格式化你改的文件
- `timeout 60 cargo test <test_name> --lib -- --nocapture` — 限制运行时间
- 运行 `cargo test` 在后台用 `run_in_background: true` — 跑全量测试时不阻塞
- 用 `Explore` agent 扫描 Isabelle 源码和 Rust 代码 — 比手动 grep 快
- 用 `Plan` agent 设计移植方案 — 确保对照 Isabelle 源

---

## 七、开始工作

请先阅读 CLAUDE.md 了解项目全貌，然后从你觉得最有效的方向开始推进。

建议顺序（按我的分析）：
1. **hologic.ML → hologic.rs** — 收益最大，所有 HOL 文件都依赖
2. **simpdata.ML → simpdata.rs** — `by simp` 成功率直接提升
3. **args.ML 解析完善** — 解锁大量证明方法的正确参数解析
4. **然后跑 Tier2 验证** — 看 Fun/Product_Type/Sum_Type 等文件验证率提升多少

每个任务前先查 Isabelle 源码，对照着写。
