# 开发路线图

## 总体路线：现代化重写策略

Isabelle-rs 不追求 1:1 移植 Isabelle 40 年的全部架构。采用**价值优先、逐步净化**策略：

1. 先让已加载定理产生实际证明能力
2. 再用原始 proof 脚本自我验证
3. 扩展理论覆盖，最终达到完全替代

---

## ✅ 已完成：定理表示层

| 组件 | 说明 |
|------|------|
| LCF 内核 | `ThmKernel`: assume/reflexive/beta/forall_intr/forall_elim 等 |
| Term 解析器 | 完整 Isabelle 语法：量词、case、if、let、集合、列表、范围 |
| Tokenizer | 原生 `\<...>` 符号 + 全部 ASCII 操作符 + cartouche |
| 引理解析 | 多行 assumes/shows/fixes/obtains、匿名引理、多结论 |
| 定理加载 | 5 个核心 .thy 文件，**2,436/2,436 源声明 100% 覆盖** |
| 定理数据库 | 2,548 条已索引（intro/elim/simp/by-name/by-root-symbol） |
| 文档模型 | Snapshot-based incremental checking |
| LSP 服务器 | 7 个 handlers + Isabelle 自定义扩展 |

---

## Phase 1：证明引擎 MVP

**目标**：利用已加载的 2,548 条定理，能够自动证明新目标。

### ✅ Phase 1a 已完成：内核基础设施

- [x] `ThmKernel::instantiate(env, thm) -> Thm` — 将 Envir 应用到 Thm
- [x] `ThmKernel::bicompose(thm1, thm2, i) -> Option<Thm>` — 核心 resolution 操作
- [x] `Thm::nprems()`, `Thm::prem(i)`, `Thm::concl()` — 目标状态访问
- [x] 所有 13 个内核操作返回 `Result` — 零 panic
- [x] 全部副作用检查已强制（abstraction free_in, transitive alpha_eq, etc.）
- [x] 314 测试通过，零 warning

### 🔵 Phase 1b 当前：Tactic 层重写

### 架构根基：为什么不是直接写 auto/simp

在 Isabelle 中，**所有** tactic（assume_tac, resolve_tac, eresolve_tac, ...）最终都调用
同一个内核操作：`bicompose`。这不是 `implies_elim`（modus ponens）能做到的——
`bicompose` 在嵌套蕴含链的任意位置做替换，而 `implies_elim` 只能处理第一个前提。

当前我们有：
- `ThmKernel` 11 条原语 ✅
- `unify::matchers` 统一 ✅
- `Envir::norm_term` 环境归一化 ✅

但我们缺少：
- `ThmKernel::instantiate(env, thm)` — 将统一结果应用到定理
- `ThmKernel::bicompose(thm1, thm2, i)` — 将定理注入目标状态
- `Thm::nprems()`, `Thm::prem(i)`, `Thm::concl()` — 访问目标状态

**没有这三个基础设施，所有 tactic 都无法正确实现。**

### 1.1 内核基础设施（第一优先）

```rust
// 在 thm.rs 中新增：
impl ThmKernel {
    /// 将 Envir（统一结果）应用到定理，产生新定理
    pub fn instantiate(env: &Envir, thm: &Thm) -> Thm;
    
    /// 核心 resolution 操作：将 thm1 注入 thm2 的第 i 个子目标位置
    pub fn bicompose(thm1: &Thm, thm2: &Thm, i: usize) -> Option<Thm>;
}

impl Thm {
    fn nprems(&self) -> usize;    // 子目标数量
    fn prem(&self, i: usize) -> Term;  // 第 i 个子目标（1-indexed）
    fn concl(&self) -> Term;      // 主结论
}
```

### 1.2 Tactic 层重写

基于 `bicompose` + `instantiate`，重写 `core/tactic.rs`：

```rust
// 目标状态就是 Thm，不再需要 Goal 结构体
// tactic = Thm -> Vec<Thm> （对齐 Isabelle 的 thm -> thm Seq.seq）
pub type Tactic = Box<dyn Fn(&Thm) -> Vec<Thm>>;

// 基础 tactic
fn all_tac() -> Tactic;    // |state| vec![state.clone()]
fn no_tac() -> Tactic;     // |_| vec![]
fn assume_tac(i: usize) -> Tactic;   // 用 bicompose + Thm.assume 消去子目标 i
fn resolve_tac(thms: &[Thm], i: usize) -> Tactic;  // 用 bicompose 将定理注入子目标 i

// 组合子（保留现有结构，只改类型）
fn then_tac(t1: Tactic, t2: Tactic) -> Tactic;     // THEN: 函数复合
fn orelse_tac(t1: Tactic, t2: Tactic) -> Tactic;   // ORELSE: 回溯
fn repeat_tac(t: Tactic) -> Tactic;                 // REPEAT
fn every_tac(ts: Vec<Tactic>) -> Tactic;            // EVERY
fn first_tac(ts: Vec<Tactic>) -> Tactic;            // FIRST
```

### 1.3 Method 层

基于新 Tactic 重写 `isar/method.rs`：

```rust
impl Method {
    /// 将方法转换为 tactic（查询 HolTheoremDb）
    fn to_tactic(&self, db: &HolTheoremDb) -> Tactic {
        match self {
            Method::Assumption => assume_tac(1),
            Method::Rule(thms) => resolve_tac(thms, 1),
            Method::Simp => simp_tac(&db.simps),
            Method::Auto => auto_tac(db),
        }
    }
}
```

### 1.4 Isar 集成

更新 `isar/proof.rs`：`Proving` 状态持有 `Thm` 作为目标状态。

### Phase 1 完成标准

- [ ] `prove("A & B --> B & A")` 返回 `Ok(Thm)` — 通过内核原语构建
- [ ] `prove("(A = B) & (B = C) --> A = C")` 返回 `Ok(Thm)`
- [ ] `Thm` 的 derivation 是 `Derivation::Rule { ... }` 不是 `Derivation::Axiom`
- [ ] 100+ 个命题逻辑 + 等式 + 量词测试用例通过

---

## Phase 2：自我验证（2-3 周）

**目标**：用 .thy 文件中的原始 proof 脚本重新验证已加载定理。

### 数据流

```
.thy 源文件
    ↓ parse_lemmas()         ← Phase 0 已完成
    ↓ extract_proof()        ← Phase 2 新增：提取 "by auto" 等 proof 脚本
    ↓ exec_proof()           ← 用 Phase 1 的引擎执行
    ↓
Verified → 替换原 assume() 版本
Failed   → 保留原 assume() 版本（标记 unchecked）
```

### proof 脚本解析

支持的 proof 方法：
- `by auto` / `by simp` / `by blast` / `by iprover`
- `by (rule name)` / `by (erule name)` / `by (drule name)`
- `by (simp add: thm1 thm2)`
- `by (blast intro: A elim: B)`

暂不支持的（保留 unchecked）：
- `by (induct ...)` / `proof ... qed` / `apply ... done`
- `by induction_schema` / `pat_completeness`

### 预期验证率

| 文件 | 定理数 | 可验证 proof | 预计验证率 |
|------|--------|-------------|:--:|
| HOL.thy | 254 | by auto/simp/rule/blast | ~70% |
| Orderings.thy | 153 | by auto/simp/iprover/rule | ~75% |
| Nat.thy | 360 | by auto/simp/induct | ~55% |
| Set.thy | 412 | by auto/simp/blast/iprover | ~70% |
| List.thy | 1,257 | by auto/simp/induct/iprover | ~60% |
| **合计** | **2,436** | | **~65%** |

### Phase 2 完成标准

- [ ] ~1,600 条定理被重新验证（带上 `Derivation::Verified`）
- [ ] 验证报告：每条定理的 proof 方法 + 验证状态

---

## Phase 3：理论 DAG + 增量加载（2 周）

**目标**：加载全部 100+ 个 .thy 文件，按理论依赖图拓扑排序。

```rust
struct TheoryGraph {
    nodes: HashMap<String, TheoryNode>,
    load_order: Vec<String>,  // 拓扑排序
}

struct TheoryNode {
    name: String,
    imports: Vec<String>,     // 依赖
    theorems: Vec<Arc<Thm>>,
}
```

### 加载流程

1. 扫描 `isabelle-source/src/HOL/` 下所有 .thy 文件
2. 解析 `theory Foo imports Bar Baz begin`
3. 构建 DAG，检测循环依赖
4. 拓扑排序，继承父理论的定理数据库
5. 增量加载：每个理论扩展定理索引

---

## Phase 4：库化 + FFI（1-2 周）

**目标**：isabelle-rs 成为真正的 Rust crate。

```rust
// Cargo.toml
[lib]
name = "isabelle_rs"
crate-type = ["lib", "cdylib"]

// 公共 API
pub fn prove(goal: &str, context: &[String]) -> Result<Thm, Error>;
pub fn load_theory(path: &str) -> Result<Theory, Error>;
pub fn check_proof(source: &str) -> Result<Vec<Diagnostic>, Error>;
```

```c
// C FFI
IsabelleCtx* isabelle_new(void);
const char* isabelle_prove(IsabelleCtx* ctx, const char* goal);
void isabelle_free(IsabelleCtx* ctx);
```

---

## 时间线总览

| 阶段 | 时间 | 可交付 |
|------|------|--------|
| ✅ Phase 0 | — | 2,548 条定理，100% 源覆盖 |
| ✅ Phase 1a | 已完成 | `instantiate` + `bicompose` 内核基础设施 |
| 🔵 Phase 1b | 1 周 | Tactic 层重写（`Thm -> Vec<Thm>`） |
| 🔵 Phase 1c | 1-2 周 | simp + auto 可用 |
| Phase 2 | 2-3 周 | ~65% 定理重新验证 |
| Phase 3 | 2 周 | 100+ 理论文件加载 |
| Phase 4 | 1-2 周 | `cargo add isabelle-rs` |
| **合计** | **8-11 周** | **可嵌入的、自验证的证明助手库** |
