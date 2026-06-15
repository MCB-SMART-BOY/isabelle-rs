---
description: 性能优化规则。Nets, safe rules, 惰性初始化, 24×加速历史。
globs: src/core/net.rs, src/hol/hol_loader.rs, src/isar/method.rs
alwaysApply: false
version: 2.0
updated: 2026-05-27
---

# 性能规则

## 触发条件

性能优化, 修改 nets/DB/方法搜索时应用。

## 优化历史 (24× total)

| 优化 | 加速 | 阶段 |
|------|:---:|------|
| auto_exec depth 30→15 | 4.2× | v0.5.0 |
| Discrimination Nets | 1000× (搜索) | Phase 10.1 |
| Safe Rules 定点迭代 | 5.8× | Phase 10.2 |
| 迭代化统一/匹配 | — | Phase 10.6 |
| 迭代深化 DFS | — | Phase 10.4d |

## 模式 1: Nets

```rust
// ✅ O(log n) net lookup → ~10-50 候选 (vs 15,000+)
let candidates = db.intro_net().lookup(&subgoal);
// ❌ O(n) 线性扫描
for thm in &db.intros { ... }
```

## 模式 2: Safe Rules First

```rust
// ✅ 先做廉价搜索
let current = apply_safe_rules(state, premises);
if current.nprems() == 0 { return vec![current]; }
// 再做昂贵搜索
```

## 模式 3: OnceLock 惰性

```rust
// ✅ 首次 lookup 才构建
intro_net: OnceLock<Net<Thm>>,
pub fn intro_net(&self) -> &Net<Thm> {
    self.intro_net.get_or_init(|| { /* 构建 */ })
}
```

## 模式 4: Safe/Unsafe 分离

```rust
// [intro!] → safe, [intro] → unsafe, 回退启发式
fn classify_intro_safe(thm, attrs) -> bool {
    if has_safe_intro_attr(attrs) { true }
    else if has_unsafe_intro_attr(attrs) { false }
    else { is_safe_intro(thm) }  // 不含 disjI/exI 即为安全
}
```

## 模式 5: 迭代深化

```rust
fn fast_exec(state, premises) -> Vec<Thm> {
    for bound in 0..8 {
        if let Some(r) = dfs_search(state, bound, premises) { return vec![r]; }
    }
    auto_exec(state, 0, premises)
}
```

## 分文件性能

| 文件 | v0.4.0 | Phase 10.2 | 关键 |
|------|:-----:|:---------:|------|
| HOL.thy | 50s | 2.3s | Safe rules + nets |
| Orderings.thy | 4.5s | 0.03s | Nets (150×) |
| Set.thy | 27s | 1.7s | Safe rules + depth |
| Nat.thy | 7s | 0.08s | Nets (88×) |
| List.thy | 1s | 0.01s | Induction |

## DO / DON'T

| ✅ | ❌ |
|----|----|
| `intro_net().lookup()` | `db.intros` 线性 |
| `apply_safe_rules` 第一步 | 直接 auto/blast |
| OnceLock 惰性 | 加载时构建 nets |
| 分类 safe/unsafe | 盲目应用所有规则 |
| 深层递归→迭代 | 增大栈 workaround |
| bound < 8 | 无限 DFS |
