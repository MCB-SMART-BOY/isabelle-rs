---
description: LCF 内核规则。ThmKernel 15操作, CTerm, tpairs, shyps, 类型感知等值构造。
globs: src/core/thm.rs, src/core/logic.rs, src/core/drule.rs, src/core/more_thm.rs
alwaysApply: false
version: 3.0
updated: 2026-05-29
---

# 内核规则

## 触发条件

修改 `thm.rs`, `logic.rs`, `drule.rs`, `more_thm.rs` 时应用。

## 15 操作 + tpairs/shyps

```
原语 (12): assume, reflexive, symmetric, transitive, combination, abstraction,
           beta_conversion, implies_intr, implies_elim, forall_intr, forall_elim, instantiate
内核派生 (3): bicompose, bicompose_eresolve, subst_premise
推导 (1): trivial
```

## Thm 结构体完整字段 (Phase 39)

```rust
pub struct Thm {
    hyps: Hyps,                    // 假设集 (α-equivalence)
    prop: CTerm,                   // 命题
    maxidx: usize,                 // 最大 schematic 索引
    tpairs: Vec<(Term, Term)>,     // flex-flex 分歧对 (Phase 39)
    shyps: Vec<Sort>,              // sort 假设 (Phase 39)
    derivation: Derivation,        // 推导历史
    serial: u64,                   // 唯一序列号
}
```

## 模式: 类型感知等值

```rust
// ✅ reflexive: CTerm 类型
let typ = ct.term_type().clone();
let eq = Pure::mk_equals(typ, t.clone(), t);

// ✅ symmetric/transitive: 从命题提取
let (t, u, eq_typ) = Pure::dest_equals_with_type(thm.prop.term())?;
let new_prop = Pure::mk_equals(eq_typ, u.clone(), t.clone());

// ✅ combination: 函数类型的 codomain
let (_, _, fn_typ) = Pure::dest_equals_with_type(thm_f.prop.term())?;
let result_typ = fn_typ.dest_fun().map(|(_, cod)| cod.clone()).unwrap_or_else(Typ::dummy);

// ✅ abstraction: x_typ → eq_typ
let fn_typ = Typ::arrow(x_typ.clone(), eq_typ);

// ❌ 禁止
let eq = Pure::mk_equals(Typ::dummy(), t, u);
```

## Pure 工具函数 (logic.rs)

```rust
Pure::mk_implies(a, b)             // a ==> b
Pure::dest_implies(term)           // → Some((a, b))
Pure::mk_equals(typ, t, u)         // t ≡ u
Pure::dest_equals_with_type(term)  // → Some((t, u, typ))  ← 优先
Pure::mk_all(name, typ, body)      // ⋀x. body
Pure::strip_imp_prems(term)        // → (Vec<prem>, concl)
Pure::extract_eq_type(const_typ)   // 从 Pure.eq 类型提取参数类型
```

## Bicompose

```rust
ThmKernel::bicompose(true, rule, goal, i)              // 反向消解
ThmKernel::bicompose(false, goal, rule, 0)             // 正向
ThmKernel::bicompose_eresolve(true, rule, goal, 0, premises) // 消去消解
```

## CTerm

```rust
CTerm::certify(term)          // 自动推断类型
CTerm::certify_typed(term, t) // 显式类型
ct.term_type()                // &Typ
```

## DO / DON'T

| ✅ | ❌ |
|----|----|
| `CTerm::term_type()` | `Typ::dummy()` |
| `dest_equals_with_type()` | `dest_equals()` + `Typ::dummy()` |
| `ThmKernel::*` | 直接构造 `Thm { .. }` |
| `occurs_check` 在绑定前 | 跳过 occurs check |
| `free_in` 在 `forall_intr` 前 | 跳过 free_in |

## 文件

| 文件 | Isabelle 对应 | 完成度 |
|------|:----------:|:-----:|
| `core/thm.rs` | `thm.ML` (2752) | 95% |
| `core/logic.rs` | `logic.ML` (693) | 80% |
| `core/drule.rs` | `drule.ML` (839) | 75% |
| `core/envir.rs` | `envir.ML` | 80% |
| `core/unify.rs` | `unify.ML` (668) | 85% |
| `core/name.rs` | `name.ML` | ✅ 100% |
| `core/term_ord.rs` | `term_ord.ML` | ✅ 100% |
| `core/morphism.rs` | `morphism.ML` | ✅ 90% |
| `core/conv.rs` | `conv.ML` | ✅ 80% |
| `core/tactic.rs` | `tactic.ML` + `tactical.ML` | ✅ 90% |
| `core/sign.rs` | `sign.ML` | 80% |
| `core/simplifier.rs` | `raw_simplifier.ML` | 70% |
| `core/sorts.rs` | `sorts.ML` | 70% |
| `core/proofterm.rs` | `proofterm.ML` | 50% |
| `core/net.rs` | `net.ML` | 80% |
| `core/pattern.rs` | `pattern.ML` | 70% |
| `core/term_subst.rs` | `term_subst.ML` | 80% |
| `core/variable.rs` | `variable.ML` | 60% |
| `core/axclass.rs` | `axclass.ML` | 15% |
