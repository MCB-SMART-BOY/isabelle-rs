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

## Phase 1：证明引擎 MVP（3-4 周）

**目标**：利用已加载的 2,548 条定理，能够自动证明新目标。

### 1.1 目标状态机

```rust
struct ProofState {
    main_goal: Term,
    subgoals: VecDeque<Goal>,
    proved: Vec<Thm>,
    depth: u32,
    trace: Vec<ProofStep>,  // 可回溯
}

enum TacticResult {
    Proved(Thm),
    Reduced(Vec<Goal>),
    NotApplicable,
    Failed(ProofError),
}
```

### 1.2 定理索引

- 按结论根符号索引（eq → [sym, trans, refl, ...]）
- 重写规则提取（`[simp]` 定理 → `RewriteRule { lhs, rhs, conds }`）
- intro/elim 规则分类

### 1.3 核心 Tactic

| Tactic | 说明 |
|--------|------|
| `rule` | 用单个定理匹配目标结论 |
| `erule` | 用消除规则析构假设 |
| `assumption` | 检查目标是否在假设中 |
| `simp` | 用重写规则化简目标 |
| `auto` | 经典推理器（安全规则优先 + 有限回溯） |

### 1.4 `simp` 重写引擎

- 从最内层子项开始匹配 LHS
- 前提条件递归验证
- 重写直到不动点

### 1.5 `auto` 经典推理器

```
1. assumption    ← 安全（不增加子目标）
2. simp          ← 安全（重写不改变可证明性）
3. rule (intro)  ← 将目标分解为子目标（通常更简单）
4. erule         ← 从假设中提取信息
5. 有限回溯      ← 防止组合爆炸
```

### Phase 1 完成标准

- [ ] `prove("A & B --> B & A")` 返回 `Ok(Thm)`
- [ ] `prove("(A = B) & (B = C) --> A = C")` 返回 `Ok(Thm)`  
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
| ✅ 已完成 | - | 2,548 条定理，100% 源覆盖 |
| Phase 1 | 3-4 周 | simp + auto 可用 |
| Phase 2 | 2-3 周 | ~65% 定理重新验证 |
| Phase 3 | 2 周 | 100+ 理论文件加载 |
| Phase 4 | 1-2 周 | `cargo add isabelle-rs` |
| **合计** | **8-11 周** | **可嵌入的、自验证的证明助手库** |
