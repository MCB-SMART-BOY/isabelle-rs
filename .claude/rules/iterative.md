---
description: 递归→迭代转换规则。四种模式: 简单栈,工作列表,continuation,DFS。深层嵌套项必须迭代化。
globs: "**/*.rs"
alwaysApply: false
version: 2.0
updated: 2026-05-27
---

# 迭代化规则

## 触发条件

栈溢出 < 256MB, 或处理深层嵌套项 (inductive/fixpoint) 时应用。

## 决策: 转换 vs 保留

| 转换 | 保留递归 |
|------|---------|
| 深层嵌套项处理 | 浅层 (term 深度 only) |
| DB 加载时调用 (`extend`, `CTerm::certify`) | 调用频率低 |
| Debug mode 栈溢出 | 状态复杂的树折叠 |

## 模式 1: 简单工作栈

遍历树，收集信息，不需重建。

```rust
// ✅
fn compute_maxidx(t: &Term) -> usize {
    let mut maxidx = 0;
    let mut stack = vec![t];
    while let Some(term) = stack.pop() {
        match term {
            Term::App { func, arg } => { stack.push(arg); stack.push(func); }
            Term::Abs { body, .. } => stack.push(body);
            Term::Var { index, .. } => maxidx = maxidx.max(*index);
            _ => {}
        }
    }
    maxidx
}
```

## 模式 2: 可变状态工作列表

处理中修改共享状态，不需重建树。

```rust
// ✅ env 原地修改 (不 clone per frame)
fn unify_dpairs_iter(mut env: Envir, pairs: Vec<DPair>, config: &UnifyConfig) -> Option<Envir> {
    let mut stack = pairs;
    stack.reverse();
    while let Some((rbinder, t, u)) = stack.pop() {
        let t = env.norm_term(&t);
        let u = env.norm_term(&u);
        if t == u { continue; }
        match (&t, &u) {
            (Term::App { .. }, Term::App { .. }) => {
                stack.push((.., a1, a2));  // 分解
                stack.push((.., f1, f2));
            }
            (Term::Var { name, index, typ }, rigid) => {
                if !occurs_check(name, *index, rigid) {
                    env.update(name.clone(), *index, typ.clone(), rigid.clone());  // 原地改!
                } else { return None; }
            }
            _ => return None,
        }
    }
    Some(env)
}
```

## 模式 3: Continuation 帧

需自底向上重建树结构。

```rust
// ✅
enum StackItem { Process(Term), BuildAbs(Symbol, Typ), BuildApp }
let mut stack = vec![StackItem::Process(term)];
let mut results = vec![];

while let Some(item) = stack.pop() {
    match item {
        StackItem::Process(t) => match &t {
            Term::App { func, arg } => {
                stack.push(StackItem::BuildApp);
                stack.push(StackItem::Process(arg));   // 后处理
                stack.push(StackItem::Process(func));  // 先处理
            }
            other => results.push(other),
        },
        StackItem::BuildApp => {
            let arg = results.pop().unwrap();
            let func = results.pop().unwrap();
            // Beta-reduce: re-process
            if let Term::Abs { body, .. } = &func {
                stack.push(StackItem::Process(subst_bounds(&[arg], body)));
            } else {
                results.push(Term::app(func, arg));
            }
        }
    }
}
```

## 模式 4: 迭代深化 DFS

```rust
// ✅
fn fast_exec(state, premises) -> Vec<Thm> {
    for bound in 0..8 {
        if let Some(r) = dfs_search(state, bound, premises) { return vec![r]; }
    }
    auto_exec(state, 0, premises)
}
```

## 检查清单

- [ ] 识别所有递归调用点
- [ ] 选模式 (栈/工作列表/continuation/DFS)
- [ ] 加步骤计数器 + 安全上限
- [ ] 保持状态传播
- [ ] 处理 re-process (beta-reduction, 已绑定变量)
- [ ] `cargo test test_verify_all_core_files` (125/125)
- [ ] `RUST_MIN_STACK=134217728 cargo test test_verify_beyond_core --lib` (128/128)

## 已完成

| 函数 | 文件 | 模式 | 之前 | 之后 |
|------|------|------|:--:|:--:|
| `unify_dpairs` | `unify.rs` | 工作列表 | 512MB | 32MB |
| `match_pattern` | `unify.rs` | Continuation | 512MB | 32MB |
| `norm_term` | `envir.rs` | Continuation | 256MB | 32MB |
| `compute_maxidx` | `thm.rs` | 栈 | 128MB | 32MB |
| `subst_bounds` | `term_subst.rs` | Continuation | 128MB | 32MB |
| `incr_bound` | `term.rs` | Continuation | 256MB | 32MB |
| `subst_var_bound` | `term.rs` | Continuation | 256MB | 32MB |
| `occurs_check` | `unify.rs` | 栈 | 128MB | 32MB |
| `free_in` | `thm.rs` | 栈 | 128MB | 32MB |
| `term_eq_notypes` | `unify.rs` | 栈 | 128MB | 32MB |
| `prove_condition` | `simplifier.rs` | **删除递归调用** | 256MB | 32MB |
