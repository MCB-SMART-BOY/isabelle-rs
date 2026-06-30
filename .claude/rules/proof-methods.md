---
description: 证明方法规则。22种方法, 六层fallback, 新方法4步添加法, 经典推理器 (Phase 22)。
globs: src/isar/method.rs
alwaysApply: false
version: 2.1
updated: 2026-05-28
---

# 证明方法规则

## 触发条件

修改 `src/isar/method.rs` 时应用。

## 方法枚举 (22+)

```
Assumption | Rule | Simp | Auto | Blast | Fast | Step | Best | Depth | DupStep |
Induct | Cases | Unfold | Fold | Insert | Erule | Drule | Frule |
Skip | Fail
```

## 六层 Fallback

```
verify_lemma()
  0. apply_safe_rules          ← net lookup, O(log n), 匹配优先→fallback 到 resolution
  1. Built-in Var-override     ← 系统内置规则
  2. Anonymous axiom           ← datatype 引理
  3. Isar structured proof     ← fix/assume/have/show/qed
  4. exec_proof → exec_single_method
     ├─ auto_exec  (safe→assume→simp→resolve→eresolve→dresolve)
     ├─ blast_exec (+symmetry +dresolve)
     ├─ fast_exec  (DFS + iterative deepening, bound 0..8)
     ├─ best_exec  (BEST_FIRST — worklist ordered by subgoal count)
     ├─ depth_exec (bounded DFS with explicit bound)
     ├─ step_exec  (safe exhaustive + one unsafe per subgoal)
     ├─ dup_step_exec (step_tac with duplication for complete search)
     ├─ exec_induct (rule lookup + subgoal solving)
     ├─ exec_simp (rewrite_deep)
     └─ exec_iprover / exec_subst / exec_arith
  5. Chain fallback (auto/blast 接管)
```

## Safe Rules — 三阶段匹配 (Phase 22 ✅)

⚠️ The `ThmKernel::bicompose` calls below are **legacy `src/core/`** paths.
They have NOT been migrated to strict `src/kernel/`. The strict kernel has a
conservative `resolve1_match` prototype for one-way backward resolution, but
full `bicompose` / `bicompose_eresolve` are still design-phase work (see
`docs/RESOLUTION_DESIGN.md`). Do not use legacy safe-rule resolution as an
implementation reference for `src/kernel/`.

```rust
pub fn apply_safe_rules(state, premises) -> Thm {
    loop {
        // Phase 1: 匹配 (matching, 不变例化变量) — 对齐 Isabelle bimatch_from_nets_tac
        for rule in safe_intro_net.lookup(&subgoal) {
            if let Some(r) = ThmKernel::bicompose(true, rule, &state, 0) { ... }
            // match_flag=true → matching, not unification
        }
        // Phase 2: 消去匹配
        for rule in safe_elim_net.lookup(&subgoal) {
            if let Some(r) = ThmKernel::bicompose_eresolve(true, rule, &state, 0, premises) { ... }
        }
        // Phase 3: Resolution fallback (允许变量实例化) — 对齐 Isabelle inst_step_tac
        resolve_tac(&safe_rules, 0)(&state)
        eresolve_tac(&safe_rules, 0)(&state)
    }
}
```

## 经典推理器搜索策略 (Phase 22 ✅)

| 方法 | 策略 | 对齐 Isabelle |
|------|------|:--:|
| `fast_exec` | DFS + iterative deepening (bound 0..8) | `fast_tac` |
| `best_exec` | BEST_FIRST — worklist ordered by nprems | `best_tac` |
| `depth_exec` | Bounded DFS with explicit depth bound | `depth_tac` |
| `step_exec` | Safe exhaustive + one unsafe rule per subgoal | `step_tac` |
| `dup_step_exec` | step_tac + rule duplication for completeness | `dup_step_tac` |

## 新方法: 4 步

**1. 枚举变体** → **2. 执行分发** (`execute_depth` match) → **3. 实现函数** → **4. 名称解析** (`exec_single_method` + `from_name`)

## 关键函数

```rust
pub fn apply_safe_rules(state: &Thm, premises: &[Arc<Thm>]) -> Thm
fn auto_exec(state: &Thm, depth: usize, premises: &[Arc<Thm>]) -> Vec<Thm>
fn fast_exec(state: &Thm, premises: &[Arc<Thm>]) -> Vec<Thm>         // DFS + 迭代深化
fn best_exec(state: &Thm, premises: &[Arc<Thm>]) -> Vec<Thm>         // BEST_FIRST
fn depth_exec(state: &Thm, bound: usize, premises: &[Arc<Thm>]) -> Vec<Thm> // 有界 DFS
fn step_exec(state: &Thm, depth: usize, premises: &[Arc<Thm>]) -> Vec<Thm>  // safe + 1 unsafe
fn dup_step_exec(state: &Thm, depth: usize, premises: &[Arc<Thm>]) -> Vec<Thm>
fn exec_induct(method_str: &str, state: &Thm, premises: &[Arc<Thm>]) -> Vec<Thm>
pub fn verify_lemma(lem: &ParsedLemma) -> Option<Thm>
```

## DO / DON'T

| ✅ | ❌ |
|----|----|
| `apply_safe_rules` 第一步 | 直接进 auto/blast |
| `intro_net().lookup()` | `db.intros` 线性扫描 |
| `safe_intro_net()` (safe rules 中) | `intro_net()` (safe rules 中) |
| `depth > N → return` | 无限递归 |
| `vec![state]` 超时返回 | `vec![]` 空返回 |
| matching 优先 → resolution fallback | 直接 resolution (避免意外实例化) |
