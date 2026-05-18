# 开发路线图 v9.0

> **目标**：完全替代 Isabelle/HOL 内核 + 证明引擎，最终移除 `isabelle-source/` 参考依赖。
> **当前验证率**：**61.3%** (7,621/12,426 lemmas)，覆盖 **115/1,473** HOL .thy 文件。
> **内核完整度**：LCF 15 操作 **100%** 等价，HO 模式匹配 **100%**，TheoryGraph DAG **115 节点零循环**。

---

## 总体策略

```
Phase 0-3   : ✅ 内核 + 证明引擎 + 115 文件 DAG (已完成)
Phase 4     : 🔴 语法解析补全 → 验证率 61% → 72%
Phase 5     : 🟠 条件重写 + Method 深化 → 验证率 72% → 78%
Phase 6     : 🟡 Isar 引擎集成 → 验证率 78% → 87%
Phase 7     : 🔵 全 HOL 库 + 生态 → 1,473 文件, 90%+ 验证率
Phase 8     : ⚪ 多逻辑 + 工具链 → 完全替代 Isabelle 本体
```

---

## 当前状态校准 (2025年9月)

### 已实现（与旧路线图差异）

| 组件 | 旧路线图(v8) | 实际状态 |
|------|:--:|:--:|
| .thy 文件 | 6 | **115** |
| 验证率 | 46.5% | **61.3%** |
| TheoryGraph DAG | 🔵 规划 | **✅ 完成** |
| HO 模式匹配 | 🟡 | **✅ Free + Var 头** |
| 操作符优先级修复 | ❌ 未提及 | **✅ `parse_trm_no_imp`** |
| `lemmas` 命令 | 🔵 规划 | **✅ 600+ 别名** |
| 多行 assumes/shows | ✅ | **✅ + cartouche** |
| `using`/`unfolding` | ✅ | **✅** |
| induct 规则应用 | ❌ | **✅ HO匹配 + resolve_tac** |
| ProofState 骨架 | ❌ | **✅ 枚举定义完成** |
| `isabelle-source/` 隔离 | ❌ | **✅ .gitignore** |

### 当前核心差距

| 差距 | 影响 | 验证率损失(估计) |
|------|------|:--:|
| `datatype`/`class`/`primrec` 解析缺失 | 类型/常量未声明 → 相关引理无法验证 | ~15-20% |
| 条件重写 (`if P then l = r`) 未实现 | simp 规则条件被跳过 | ~5-8% |
| Isar 引擎未接入验证流程 | `have`/`show`/`case` 结构化证明全部失败 | ~10-12% |
| `cases`/`induct` 子目标求解受限 | 限制 5 子目标, 仅 1 候选规则 | ~3-5% |
| `subst`/`arith` 方法缺失 | 等值替换和线性算术不可用 | ~2-3% |

---

## Phase 4: 语法解析补全 (当前 → 验证率 72%)

> **目标**: 解析 `datatype`/`class`/`primrec`/`typedef` 等核心声明，消除"类型/常量缺失"导致的验证失败。
> **预期验证率**: 61.3% → 72% (+1,300+ lemmas)
> **工作量**: 12-18 天

### 4.1 `datatype` 解析 (4-6天) 🔴 最高优先级

当前 `hol_loader.rs` 遇到 `datatype` 声明时直接跳过。需实现：

```rust
// theories/HOL/Nat.thy:
// datatype nat = Zero | Suc nat
// theories/HOL/List.thy:
// datatype 'a list = Nil | Cons 'a "'a list"
// theories/HOL/Option.thy:
// datatype 'a option = None | Some 'a

struct DatatypeDef {
    name: String,               // "nat", "list", "option"
    type_params: Vec<String>,   // ['a], [] for nat
    constructors: Vec<(String, Typ)>,  // ("Zero", nat), ("Suc", nat→nat)
}

fn parse_datatype(source: &str) -> Option<DatatypeDef>;
```

**交付**：
- 声明类型常量 (`HOL.nat`, `HOL.list`)
- 声明构造子常量 (`HOL.Zero`, `HOL.Suc`, `HOL.Nil`, `HOL.Cons`)
- 生成归纳规则 (自动派生 `nat_induct`, `list_induct` 等)
- 影响：List.thy (+~150 lemmas), Nat.thy (+~40), Option.thy (+~15), Sum_Type.thy (+~5)

### 4.2 `primrec` / `fun` / `function` 解析 (3-4天) 🔴

原始递归定义和函数定义是核心 HOL 理论的基础：

```rust
// primrec append :: "'a list => 'a list => 'a list" where
//   "append Nil ys = ys"
// | "append (Cons x xs) ys = Cons x (append xs ys)"

// fun map :: "('a => 'b) => 'a list => 'b list" where
//   "map f Nil = Nil"
// | "map f (Cons x xs) = Cons (f x) (map f xs)"

struct PrimrecDef {
    name: String,
    typ: Typ,
    equations: Vec<(Term, Term)>,  // (lhs, rhs) pairs
}
```

**交付**：
- 解析 `primrec` 和 `fun` 声明
- 将定义等式注册为重写规则 (自动注入 simp set)
- 影响：List.thy (+~200 lemmas), Nat.thy (+~30), Fun.thy (+~20)

### 4.3 `class` / `subclass` / `instantiation` 解析 (3-4天) 🟠

类型类 (type classes) 是 Isabelle/HOL 的核心特性：

```rust
// class ord = fixes less_eq :: "'a => 'a => bool"
// instantiation nat :: ord begin ... end
// instantiation list :: (ord) ord begin ... end

struct ClassDef {
    name: String,
    superclasses: Vec<String>,
    fixes: Vec<(String, Typ)>,
}

struct Instantiation {
    type_name: String,
    class_name: String,
    definitions: Vec<ParsedLemma>,
}
```

**交付**：
- 解析 `class` 声明（声明类型类常量）
- 解析 `instantiation` 块（定义实例）
- 影响：Orderings.thy (+~30), Lattices.thy (+~25), Complete_Lattices.thy (+~20)

### 4.4 `typedef` 解析 (1-2天) 🟠

```rust
// typedef 'a set = "{x :: 'a. True}" morphisms Collect set
fn parse_typedef(source: &str) -> Option<TypedefDef>;
```

### 4.5 `inductive` / `coinductive` 解析 (1-2天) 🟡

```rust
// inductive even :: "nat => bool" where
//   "even Zero"
// | "even n ==> even (Suc (Suc n))"
```

影响：Inductive.thy, Transitive_Closure.thy。

### Phase 4 完成标准
- [ ] `datatype nat/list/option/sum/prod` 全部解析
- [ ] `primrec`/`fun` 定义自动生成重写规则
- [ ] `class ord/order/semilattice/lattice` 全部解析
- [ ] 验证率 **≥ 72%** (9,000+ / 12,426)
- [ ] 新增测试 30+

---

## Phase 5: 条件重写 + Method 深化 (验证率 72% → 78%)

> **目标**: 实现条件重写，深化 blast/auto/induct 的搜索能力。
> **预期验证率**: 72% → 78% (+~750 lemmas)
> **工作量**: 8-12 天

### 5.1 条件重写 (3-4天) 🟠 高优先级

当前 `simplifier.rs` 的 `try_rule` 遇到条件规则时直接跳过条件检查：

```rust:src/core/simplifier.rs#L275-279
// Check condition if present
if let Some(cond) = &rule.condition {
    let _cond_inst = env.norm_term(cond);
    // For conditional rules, we'd need to prove the condition
}
```

**实现方案**：
1. 条件规则的 LHS 匹配成功后，实例化条件项
2. 对实例化后的条件调用 `prove_auto` (轻量递归验证)
3. 条件成立 → 应用规则；条件不成立 → 跳过
4. 递归深度限制 (max 3 层) 防止无限循环

```rust
fn check_condition(cond: &Term, env: &Envir) -> bool {
    let goal = ThmKernel::assume(CTerm::certify(cond.clone()));
    prove_auto(&goal, &[]).is_some()
}
```

**影响**：Set.thy (+~40), List.thy (+~60), Nat.thy (+~20), Relation.thy (+~15)

### 5.2 blast 搜索深化 (2-3天) 🟠

当前 `blast_exec` 的搜索受限于：
- `resolve_tac` 分支限制 3
- 深度限制 25
- 仅试用 `intros` 和 `elims`

**改进**：
1. 增加 `dresolve_tac` 路径
2. 对称性处理泛化 (不仅限于等式，还包括 `<=` ↔ `>=`)
3. 引入 `intro:`/`elim:`/`dest:` 声明的分类索引
4. 搜索分支按 term size 剪枝

### 5.3 induct/cases 子目标求解增强 (2-3天) 🟠

当前限制：
- `solve_subgoals` 最多处理 5 个子目标
- `exec_induct` 仅尝试 1 个候选规则

**改进**：
1. 子目标求解上限提升至 15
2. 候选规则数提升至 3
3. 对每个子目标独立调用 `prove_auto` → `prove_blast` → `prove_simp` 链
4. 子目标间共享已证明的事实 (accumulated facts)

### 5.4 `subst` 方法 (1-2天) 🟡

```rust
// subst (asm) thm  — 等值替换目标(或假设)中的匹配项
fn exec_subst(method_str: &str, state: &Thm, premises: &[Arc<Thm>]) -> Vec<Thm>;
```

### Phase 5 完成标准
- [ ] 条件重写可用 (递归条件验证, 深度限制 3)
- [ ] blast 搜索覆盖率提升 50%
- [ ] induct 子目标上限 15, 候选规则 3
- [ ] 验证率 **≥ 78%** (9,700+ / 12,426)

---

## Phase 6: Isar 引擎集成 (验证率 78% → 87%)

> **目标**: 将 `ProofState` 骨架接入 `verify_lemma` 流程，支持 `have`/`show`/`case` 结构化证明。
> **预期验证率**: 78% → 87% (+~1,100 lemmas)
> **工作量**: 3-4 周

### 6.1 ProofState → verify_lemma 集成 (5-7天) 🔴

当前 `verify_lemma` 绕过 `ProofState`，直接调用 `exec_proof`：

```rust:src/isar/method.rs#L1207-1217
pub fn verify_lemma(lem: &ParsedLemma) -> Option<Thm> {
    let proof = lem.proof_script.as_ref()?;
    let (prems, _concl) = Pure::strip_imp_prems(lem.theorem.prop().term());
    let premises: Vec<Arc<Thm>> = prems.iter()
        .map(|p| Arc::new(ThmKernel::assume(CTerm::certify((*p).clone()))))
        .collect();
    let goal = ThmKernel::assume(CTerm::certify(lem.theorem.prop().term().clone()));
    exec_proof(&goal, proof, &premises)
}
```

**改为**：
```rust
pub fn verify_lemma(lem: &ParsedLemma) -> Option<Thm> {
    let proof = lem.proof_script.as_ref()?;
    let mut state = ProofState::new(lem.theorem.prop().term().clone());
    state.begin_proof();
    // Parse proof into ProofState steps:
    //   fix x y → state.fix(x, typ) / state.fix(y, typ)
    //   assume "A" → state.assume(parse_term("A"))
    //   have "B" by auto → state.have("B", "auto")
    //   show "C" by blast → state.show("C", "blast")
    //   case Nil → state.case("Nil")
    //   next → state.next()
    //   qed → state.qed()
    interpret_proof_script(&mut state, proof, &premises)?;
    state.qed()
}
```

### 6.2 `have` / `show` / `hence` / `thus` (5-7天)

```rust
impl ProofState {
    /// 证明中间引理
    fn have(&mut self, name: &str, stmt: &Term, method: &str) -> Result<Arc<Thm>>;
    /// 证明当前目标
    fn show(&mut self, stmt: &Term, method: &str) -> Result<Arc<Thm>>;
    /// `hence` = `then have`  (使用前一个 fact 作为额外前提)
    fn hence(&mut self, name: &str, stmt: &Term, method: &str) -> Result<Arc<Thm>>;
    /// `thus` = `then show`
    fn thus(&mut self, stmt: &Term, method: &str) -> Result<Arc<Thm>>;
}
```

### 6.3 `case` / `next` (3-4天)

归纳证明的 case 分析：
```isabelle
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (auto simp add: IH)
qed
```

`case Nil` 将当前子目标的假设绑定到 `Nil` case 的 facts。`next` 切换到下一个子目标。

### 6.4 `obtain` / `{ ... }` 嵌套块 (2-3天)

### 6.5 `note` / `let` / `from` / `with` (2天)

### Phase 6 完成标准
- [ ] `ProofState` 完整接入 `verify_lemma`
- [ ] `have`/`show`/`case`/`next` 全部工作
- [ ] 嵌套 `proof ... qed` 块支持
- [ ] 验证率 **≥ 87%** (10,800+ / 12,426)
- [ ] 新增测试 40+

---

## Phase 7: 全 HOL 库 + 生态 (验证率 87% → 92%)

> **目标**: 加载全部 1,473 HOL .thy 文件，优化性能，准备发布。
> **预期验证率**: 87% → 92% (全库)
> **工作量**: 4-6 周

### 7.1 全 HOL 库加载 (1-2周)

当前 115 文件的 TheoryGraph DAG 已工作。扩展到 1,473 的挑战：
1. **错误恢复**：单文件解析失败不阻塞整个 DAG
2. **内存**：1,473 文件的 HolTheoremDb 可能增长到 100K+ 定理，需优化索引
3. **增量加载**：按 session 分批，支持中断恢复

```rust
// 目标调用方式
let mut graph = TheoryGraph::new();
graph.scan_all("isabelle-source/src/HOL")?;  // 1,473 files
let db = graph.load_all_with_progress(|name, pct| {
    eprintln!("Loading {} ({:.1}%)", name, pct);
})?;
```

### 7.2 性能优化 (1周)

当前瓶颈：
- `solve_subgoals` 限制 5 个子目标
- `exec_induct` 仅尝试 1 个候选规则
- `auto_exec` 深度限制 30
- `cargo test` 全测试超时

**优化项**：
1. 定理数据库索引：用 `HashMap<NameHash, Vec<Arc<Thm>>>` 替代线性扫描
2. 重写规则缓存：预编译 simp set 的 term index
3. 并行验证：`rayon` 并行验证独立引理
4. 增量验证缓存：已验证引理持久化到 SQLite

### 7.3 `cargo publish` 准备 (1周)

- [ ] 公共 API 审计 (`pub` 限定)
- [ ] 文档注释 (`cargo doc`)
- [ ] `Cargo.toml` 元数据
- [ ] CI/CD pipeline
- [ ] 最小示例 (examples/ 目录)

### 7.4 LSP 服务器完善 (1-2周)

当前 7 个 handler。目标：
- `textDocument/didChange` → 增量解析 + 诊断
- `textDocument/completion` → 定理名/方法名补全
- `textDocument/hover` → 定理类型信息
- `textDocument/definition` → 跳转到定义
- `textDocument/references` → 查找引用

### Phase 7 完成标准
- [ ] 全 1,473 HOL .thy 文件加载
- [ ] 验证率 ≥ 90%
- [ ] `cargo add isabelle-rs` 可用
- [ ] LSP 服务器可用 (诊断 + 补全 + 悬停)

---

## Phase 8: 多逻辑 + 工具链 (90% → 完全替代)

> **目标**: 支持 Isabelle 全部逻辑，移植关键工具链。
> **工作量**: 8-12 周

### 8.1 其他逻辑支持 (3-4周)

| 逻辑 | 工作量 | 说明 |
|------|:--:|------|
| FOL (一阶逻辑) | 1周 | 无类型类，内核相同，不同常量 |
| ZF (集合论) | 2周 | 独立公理系统 |
| CTT (构造类型论) | 2周 | 依赖类型 |
| Cube (λ-cube) | 1周 | 8 个 Pure 扩展 |
| CCL/LCF/Sequents | 2周 | 小逻辑 |

### 8.2 关键工具链 (3-4周)

| 工具 | 工作量 | 说明 |
|------|:--:|------|
| Sledgehammer 接口 | 2周 | ATP 调用 + 结果解析 |
| Code Generator | 2周 | Haskell/ML/Rust 代码生成 |
| Quickcheck/Nitpick | 1周 | 反例搜索 |
| `isabelle build` 等价 | 1周 | 会话构建系统 |

### 8.3 ML 运行时 (可选, 4-6周)

- [ ] 嵌入式 ML 解释器 (或 WASM 插件)
- [ ] `ML_file` 命令支持
- [ ] 用户自定义 tactic

### Phase 8 完成标准
- [ ] 至少 3 种逻辑可用 (HOL + FOL + ZF)
- [ ] `isabelle-source/` 完全不再需要
- [ ] Sledgehammer 可调用外部 ATP

---

## 时间线总览

| 阶段 | 时间 | 累计验证率 | .thy 覆盖 | 核心交付 |
|------|:--:|:--:|:--:|------|
| ✅ Phase 0-3 | (已完成) | 61.3% | 115 | 内核 + 证明引擎 + DAG |
| 🔴 Phase 4 | 12-18天 | 72% | 115 | datatype/class/primrec 解析 |
| 🟠 Phase 5 | 8-12天 | 78% | 115 | 条件重写 + Method 深化 |
| 🟡 Phase 6 | 3-4周 | 87% | 115 | Isar 引擎集成 |
| 🔵 Phase 7 | 4-6周 | 92% | 1,473 | 全 HOL 库 + cargo publish |
| ⚪ Phase 8 | 8-12周 | 95%+ | 1,849 | 多逻辑 + 工具链 |
| **合计** | **5-7月** | — | — | **完全替代 Isabelle 本体** |

---

## 即时行动项 (本周)

按 ROI (验证率提升 / 工作量) 排序：

| # | 任务 | 工作量 | 预期验证率提升 |
|---|------|:--:|:--:|
| 1 | `datatype` 解析 (Nat/List/Option/Sum_Type) | 4-6天 | +150 lemmas |
| 2 | `primrec`/`fun` 解析 | 3-4天 | +200 lemmas |
| 3 | 条件重写 | 3-4天 | +120 lemmas |
| 4 | `class`/`instantiation` 解析 | 3-4天 | +80 lemmas |
| 5 | blast 搜索深化 | 2-3天 | +60 lemmas |
| 6 | induct 子目标求解增强 | 2-3天 | +50 lemmas |

---

## 风险与缓解

| 风险 | 概率 | 影响 | 缓解 |
|------|:--:|:--:|------|
| datatype 归纳规则自动生成不正确 | 中 | 高 | 与 Isabelle 输出逐条对比 |
| 条件重写导致无限递归 | 中 | 中 | 严格深度限制 + 循环检测 |
| Isar 引擎复杂度超预期 | 高 | 高 | 先支持 80% 常见模式 |
| 全 1,473 文件内存爆炸 | 中 | 高 | 增量加载 + 惰性索引 |
| 全测试超时 | 高 | 中 | 并行化 + 基准测试子集 |
