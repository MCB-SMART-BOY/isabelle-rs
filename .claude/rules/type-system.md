---
description: 类型系统规则。TypeEnv, CTerm, Typ::dummy()修复状态, 路线图。
globs: src/core/types.rs, src/core/thm.rs, src/core/sign.rs
alwaysApply: false
version: 2.1
updated: 2026-05-28
---

# 类型系统规则

## 触发条件

修改 `types.rs`, CTerm, `sign.rs`, `axclass.rs` 时应用。

## 架构

```
TypeEnv { consts, types, frees, algebra }
  ├── Algebra { class_graph, arities } ← sorts.rs ✅
  └── CTerm { term, maxidx, term_type }
Type / Sort / ClassAlgebra              ← types.rs
```

## Sort Algebra (Phase 14 ✅)

```rust
let mut alg = Algebra::pure();
alg.add_class(&ord, &[type_class]);
alg.add_class(&order, &[ord.clone()]);
alg.add_arity(&sym("list"), &sym("type"), vec![Sort::top()]);

alg.class_le(&order, &ord)    // true: order ⊆ ord
alg.sort_le(&s1, &s2)          // sort comparison
alg.of_sort(&typ, &sort)       // key operation: type checking
```

## Typ::dummy() 修复状态

| 位置 | 优先级 | 状态 |
|------|:-----:|:----:|
| Kernel rules (6处) | 🔴 P0 | ✅ Phase 10.3 (大部分已完成) |
| `Term::free("x", Typ::dummy())` | 🟠 P1 | ❌ 待修复 (Phase 21) |
| `lambda(..., Typ::dummy())` | 🟡 P2 | ❌ 待修复 (Phase 21) |
| 测试代码 | 🔵 P3 | ❌ 低优先级 |

## 已完成修复 (Phase 10.3-20)

```rust
// reflexive: ct.term_type()
// symmetric/transitive: dest_equals_with_type
// combination: fn_typ → codomain
// abstraction: x_typ → eq_typ
// beta_conversion: ct.term_type()
```

## 下一步 (Phase 21)

1. **审查所有 Typ::dummy() 调用点** — 在 thm.rs, logic.rs, term.rs 中
2. **从 .thy 解析类型** — `Term::free("x", Typ::base("nat"))` 而非 `Typ::dummy()`
3. **`CTerm::certify_with_env`** — 类型检查版本
4. **类型统一** — `unify_types(env, t1, t2)`

## TypeEnv 用法

```rust
let mut env = TypeEnv::new();
env.declare_type("list", 1);       // 'a list
env.declare_type("fun", 2);        // 'a => 'b
env.declare_const("HOL.eq",        // 'a => 'a => bool
    Typ::arrows(vec![a.clone(), a], Typ::base("bool")));

env.type_arity("list")      // Some(1)
env.const_type("HOL.eq")    // Some('a => 'a => bool)
env.lookup_const("eq")      // → "HOL.eq"
```

## 文件

| 文件 | 内容 | 完成度 |
|------|------|:-----:|
| `core/types.rs` | Type/Sort/ClassAlgebra/TypeEnv | 60% |
| `core/thm.rs` | CTerm + infer_type + kernel 类型感知 | 95% |
| `core/logic.rs` | mk_equals(typ, ...) — 已类型感知 | 80% |
| `core/sign.rs` | 签名 | 40% |
| `core/sorts.rs` | Sort algebra | 70% |
| `core/axclass.rs` | 类型类 (stub) | 15% |
