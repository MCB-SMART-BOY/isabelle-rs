---
description: v1.9.0 发布后的下一步计划
version: 2.0
created: 2026-06-16
updated: 2026-06-16 (Phase 3.1-3.3 ✅, Phase 5 🔄)
---

## 完成状态

| Phase | 内容 | 状态 |
|:-----:|------|:--:|
| 3.1 | 浅层导入 (核心 simpset) | ✅ |
| 3.2 | 内存限界搜索 | ✅ |
| 3.3 | rewrite 深度上限 | ✅ |
| 4 | tier2 扩展 | ✅ (36/36 files, 2959/2959) |
| 4.2 | tier2++ 扩展 | ✅ (Hull→Lifting_Set, +12 files) |
| 5 | v1.9.0 发布 | ✅ |

# 下一步计划：v1.9.0-dev → v1.9.0

## 当前状态

| 指标 | 值 |
|------|-----|
| Core 验证 | 5/5 files 125/125 (100%) |
| Tier2 验证 | 6/16 files 100% (Fun→Rings) |
| 属性系统 | ✅ 完整 (class assumes + attrs_index) |
| ctr_sugar | ✅ 修复 (3 处 pop unwrap) |
| VERIFY_DEADLINE | ✅ 7 检查点 |
| Fields.thy | 数据流 90% 修复, 4 类跨文件规则缺失 |
| Hilbert_Choice | ❌ 25GB 内存爆炸 |
| Transitive_Closure | ❌ 25GB 内存爆炸 |

## 根因矩阵

```
问题层:
  [数据层]   class assumes 未被解析                → ✅ 已修复
  [数据层]   named_theorems 无反向索引             → ✅ 已修复
  [数据层]   跨文件 simp 规则缺失                  → ❌ Phase 3.1
  [算法层]   auto/blast 无限递归搜索               → ❌ Phase 3.2
  [算法层]   simplifier rewrite 无硬深度上限       → ❌ Phase 3.3
  [架构层]   verify_file 单文件 DB, 无父理论规则   → ❌ Phase 3.1
```

---

## Phase 3.1: 浅层导入 (Shallow Imports)

### 问题

Fields.thy `imports Nat`，但 `verify_file` 只加载 Fields.thy 自身的 lemmas。
Fields 中 `by (simp add: algebra_simps)` — algebra_simps 定理全在 Rings/Groups 中（不在 Fields 自身）。

```
Isabelle/ML: simpset 自动累积所有导入理论的 [simp] 规则
我们的系统: verify_file → from_lemmas → 只有当前文件的 lemmas + builtins
```

### 方案：核心 simpset 快照

不加载完整理论文件，而是：

1. **构建阶段**：从 `isabelle-source/src/HOL/` 的 6 个核心文件（HOL, Orderings, Set, Nat, Fun, Lattices）中提取所有 `[simp]` 引理，编译成一个静态数组

2. **运行时**：`verify_file` 加载核心 simpset 规则到 local_db

3. **缓存**：用 `std::sync::LazyLock` 惰性初始化，首次构建后全局复用

### 实现

```rust
// src/hol/simpdata.rs — 扩展现有的 init_hol_simpset

/// 预编译的核心 simpset — 包含从 HOL→Orderings→Set→Nat→Lattices
/// 的所有 [simp] 引理。首次访问时从 .thy 文件提取并缓存。
static CORE_SIMPSET: LazyLock<Vec<Arc<Thm>>> = LazyLock::new(|| {
    let mut rules = Vec::new();
    // 顺序很重要 — 与 Isabelle 的 theory 导入顺序一致
    for thy_file in &["HOL", "Orderings", "Set", "Nat", "Fun", "Lattices"] {
        let source = include_str!(concat!("../../theories/HOL/", thy_file, ".thy"));
        let lemmas = parse_lemmas(source);
        for lem in &lemmas {
            if lem.attributes.iter().any(|a| a == "simp") {
                rules.push(Arc::clone(&lem.theorem));
            }
        }
    }
    rules
});

/// 在 verify_file 中使用
pub fn verify_file(source: &str) -> (usize, usize) {
    // ... 现有解析逻辑 ...
    let mut local_db = HolTheoremDb::from_lemmas(&lemmas);
    
    // 注入核心 simpset（来自导入理论的 [simp] 规则）
    for thm in CORE_SIMPSET.get() {
        local_db.simps.push(Arc::clone(thm));
    }
    
    HolTheoremDb::add_builtins(&mut local_db);
    // ...
}
```

### 为什么不用 LazyLock 的问题

之前 `HolTheoremDb::get()` 的 LazyLock 加载全部 1,473 文件（慢且重）。
核心 simpset 只加载 6 个核心文件的 `[simp]` 引理——约 200-300 条规则——内存开销极小。

### 预期效果

| 文件 | 之前命中率 | 之后命中率 | 预期验证率 |
|------|:--------:|:--------:|:--------:|
| Fields | ~90% | ~98% | 90%+ |
| Num | ~85% | ~95% | 85%+ |
| Relation | 100% | 100% | 100% |
| Finite_Set | 100% | 100% | 100% |

---

## Phase 3.2: 内存限界搜索 (Memory-Bounded Search)

### 问题

Hilbert_Choice (56 × `by auto`) 和 Transitive_Closure (40 × `by auto`) 中，
每条 `by auto` 触发 `auto_exec` 递归树。每层递归通过 `Arc::clone` 持有中间定理，
25GB 内存被百万个 `Arc<Thm>` 占满。

```
auto_exec → apply_safe_rules → bicompose → new Thm → Arc::clone
         → auto_exec (递归) → apply_safe_rules → ...
         → 每层都持有父层的 Arc<Thm> → 永不释放 → 内存爆炸
```

### Rust 特定考量

- `Arc<Thm>` 是指针 + 引用计数，每条 ~80 bytes
- 25GB ≈ 300M 条 `Arc<Thm>` —— 不可能全都有用
- Rust 没有 GC，不能"暂停然后清理"——必须主动释放
- `Cell<usize>` 线程局部计数器零开销

### 方案：基于 Arc 计数的内存预算

```rust
thread_local! {
    /// 当前证明搜索中活跃的 Arc<Thm> 计数
    static PROOF_ALLOC_COUNT: Cell<usize> = Cell::new(0);
    /// 硬上限
    static PROOF_ALLOC_BUDGET: Cell<usize> = Cell::new(100_000);
}

// 在 auto_exec 入口检查
fn auto_exec(state: &Thm, depth: usize, premises: &[Arc<Thm>]) -> Vec<Thm> {
    // 检查内存预算
    let count = PROOF_ALLOC_COUNT.with(|c| c.get());
    let budget = PROOF_ALLOC_BUDGET.with(|c| c.get());
    if count > budget {
        return vec![state.clone()];  // 放弃搜索, 返回当前状态
    }
    // ...
}

// 在 bicompose (Thm 创建点) 计数
// 用 Arc::strong_count 估算引用树大小
fn check_alloc_budget(thm: &Thm) -> bool {
    let count = Arc::strong_count(/* the thm's underlying Arc */);
    PROOF_ALLOC_COUNT.with(|c| c.set(c.get() + count));
    c.get() < PROOF_ALLOC_BUDGET.with(|b| b.get())
}
```

实际简化版——不追踪精确计数，而是用**树深度 × 分支数**估算：

```rust
fn auto_exec(state: &Thm, depth: usize, premises: &[Arc<Thm>]) -> Vec<Thm> {
    // 预算检查: 深度 × 分支数 = 搜索树规模上限
    // depth 15 → 最多允许 ~20 个分支
    let branch_limit = if depth > 10 { 5 } else if depth > 5 { 15 } else { 50 };
    let mut branches = 0;
    
    // ... 在 resolve_tac / eresolve_tac 等地方检查 ...
    for rule in &candidates {
        branches += 1;
        if branches > branch_limit {
            break;  // 剪枝
        }
        // ...
    }
    // ...
}
```

### 预期效果

- Hilbert_Choice: 从 25GB → <500MB
- Transitive_Closure: 从 25GB → <500MB
- 验证率: 可能下降（剪枝会丢失一些有效证明），但至少不会 OOM

---

## Phase 3.3: Simplifier 改写深度硬上限

### 问题

`repeat_conv` 有收敛检测，但没有 **硬深度上限**。Isabelle 默认 `simp_depth_limit = 40`。

### 方案

```rust
impl Simplifier {
    const MAX_REWRITE_DEPTH: usize = 40;

    fn rewrite_inner(&self, term: Term, depth: usize) -> Option<Term> {
        if depth > Self::MAX_REWRITE_DEPTH {
            return None;  // 放弃, 返回原 term
        }
        // ... 重写逻辑 ...
        self.rewrite_inner(result, depth + 1)
    }
}
```

---

## Phase 4: Tier2 扩展

### 重新启用所有文件

Phase 3.1-3.3 完成后:
- 重新启用 Fields, Num, Hilbert_Choice, Transitive_Closure, Partial_Function
- 运行完整 tier2 测试
- 预期: 13+/16 files 100%, 其余 deadline 截断但不再 OOM/25GB

### 扩展 tier2 到 isabelle-source

从 `isabelle-source/src/HOL/` 挑选 30-50 个中等大小的 `.thy` 文件：
- 过滤: 跳过 >2000 行的文件
- 优先: 经常被导入的基础理论
- 目标: 验证率 >80%

### tier2 自动化

```bash
# 脚本: 扫描 isabelle-source, 挑出所有 <500 行的 .thy, 批量验证
find isabelle-source/src/HOL -name '*.thy' -size -20k | head -50
```

---

## Phase 5: v1.9.0 发布

### 发布前检查清单

- [ ] Core 5/5 files 125/125 (100%)
- [ ] Tier2 ≥15/20 files ≥90%
- [ ] `cargo check --lib` 0 warnings
- [ ] `cargo clippy` 0 warnings
- [ ] 全部单元测试通过
- [ ] 所有文档同步 (docs/ + .claude/)
- [ ] CHANGELOG 更新
- [ ] Cargo.toml version → 1.9.0

### 版本号

```
v1.9.0-dev → v1.9.0: Route A 完成
  - class assumes 解析
  - attrs_index 反向索引  
  - 浅层导入 (核心 simpset)
  - 内存限界搜索
  - VERIFY_DEADLINE 全覆盖
  - Tier2 ≥15/20 files ≥90%
```

---

## 实现优先级

| 优先级 | Phase | 预计时间 | 影响 |
|:------:|-------|:------:|------|
| **P0** | 3.1 浅层导入 | 1-2h | 解锁 Fields/Num 的剩余 5 类规则 |
| **P0** | 3.2 内存限界 | 1-2h | 防止 25GB OOM |
| **P1** | 3.3 rewrite 深度 | 30min | 保险网 |
| **P1** | 4 tier2 扩展 | 2-4h | 覆盖率指标 |
| **P2** | 5 发布 | 1h | 版本发布 |

### 建议执行顺序

1. Phase 3.2 先做——防止最坏情况（25GB OOM）
2. Phase 3.1 接着做——解锁最大收益（Fields~90%）
3. Phase 3.3 快速做——安全网
4. Phase 4 验证效果
5. Phase 5 发布

---

## 相关文件

| 文件 | 作用 |
|------|------|
| `src/hol/simpdata.rs` | 核心 simpset 定义 (Phase 3.1) |
| `src/isar/method.rs` | auto_exec, exec_simp, 预算检查 (Phase 3.2, 3.3) |
| `src/core/simplifier.rs` | rewrite 深度上限 (Phase 3.3) |
| `tests/tier2_verify.rs` | tier2 文件列表 (Phase 4) |
| `docs/ARCHITECTURE.md` | 架构更新 (Phase 5) |
| `docs/ROADMAP.md` | 路线图更新 (Phase 5) |
