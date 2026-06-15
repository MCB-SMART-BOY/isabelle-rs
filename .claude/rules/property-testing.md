---
description: Property-based testing with proptest. Invariant testing, fuzzing, shrinking, test oracle design for theorem proving.
globs: tests/proptest.rs, "**/test*.rs"
alwaysApply: false
version: 1.0
updated: 2026-05-29
---

# Property-Based Testing Rules

> "Don't write tests. Write properties." — Property-based testing philosophy.

## 触发条件

编写测试、添加新数据类型、或修改内核/统一算法时应用。

## 铁律

1. **每个核心数据结构必须有属性测试** — Term, Thm, Type, Envir
2. **属性优于示例** — 测试不变式而非具体输入输出
3. **收缩 (Shrinking) 是关键** — 最小的反例最有价值
4. **Oracle 可来自参考实现** — Isabelle/ML 作为 oracle
5. **不变量必须显式声明** — 明确什么是 "正确行为"

## proptest 基础

```rust
use proptest::prelude::*;

// 策略: 生成随机 Term
fn arb_term() -> impl Strategy<Value = Term> {
    let leaf = prop_oneof![
        any::<String>().prop_map(|s| Term::free(&s, Typ::base("bool"))),
        any::<usize>().prop_map(|i| Term::bound(i)),
    ];
    leaf.prop_recursive(
        8,   // 最大深度
        256, // 最大分叉数
        10,  // 每层分支数
        |inner| {
            prop_oneof![
                // App
                (inner.clone(), inner.clone())
                    .prop_map(|(f, a)| Term::app(f, a)),
                // Abs
                (any::<String>(), inner)
                    .prop_map(|(n, b)| Term::abs(&n, Typ::base("bool"), b)),
            ]
        },
    )
}
```

## 模式 1: 内核不变量测试

```rust
proptest! {
    /// reflexive: A ≡ A, 且返回的定理无前提
    #[test]
    fn prop_reflexive_no_premises(t in arb_term()) {
        let ct = CTerm::certify_typed(t, Typ::base("bool")).unwrap();
        let thm = ThmKernel::reflexive(&ct).unwrap();
        prop_assert_eq!(thm.nprems(), 0);  // 无反前提
    }

    /// assume: hyp1 ==> hyp1, 结果的 prop 等于输入
    #[test]
    fn prop_assume_prop_equals_input(t in arb_bool_term()) {
        let ct = CTerm::certify_annotated(t.clone()).unwrap();
        let thm = ThmKernel::assume(&ct).unwrap();
        prop_assert!(thm.prop.term().alpha_equivalent(&t));
    }

    /// symmetric(symmetric(thm)) == thm (对合性)
    #[test]
    fn prop_symmetric_involution(eq_thm in arb_equality()) {
        let sym1 = ThmKernel::symmetric(&eq_thm).unwrap();
        let sym2 = ThmKernel::symmetric(&sym1).unwrap();
        prop_assert!(sym2.prop.term().alpha_equivalent(eq_thm.prop.term()));
    }

    /// beta_conversion: (λx. t) x ≡ t 是定理 (无前提)
    #[test]
    fn prop_beta_conversion_is_theorem(
        (var_name, t) in (any::<String>(), arb_term())
    ) {
        let abs = Term::abs(&var_name, Typ::base("bool"), t.clone());
        let var = Term::free(&var_name, Typ::base("bool"));
        let app = Term::app(abs, var);
        let ct = CTerm::certify_annotated(app).unwrap();
        let thm = ThmKernel::beta_conversion(&ct).unwrap();
        prop_assert_eq!(thm.nprems(), 0);
    }
}
```

## 模式 2: 统一算法不变量

```rust
proptest! {
    /// 成功的统一产生同时是 t 和 u 实例的 env
    #[test]
    fn prop_unify_produces_common_instance(
        (t, u) in (arb_term(), arb_term())
    ) {
        let env = Envir::empty();
        if let Some(env) = unify(&env, &t, &u, &UnifyConfig::default()) {
            let t_norm = env.norm_term(&t);
            let u_norm = env.norm_term(&u);
            // 归一化后相等
            prop_assert!(t_norm.alpha_equivalent(&u_norm));
        }
        // 如果 unify 返回 None, 那没问题 — 不可统一
    }

    /// 统一是幂等的: 对统一后的 env 再次统一 t 和 u 应该在原地成功
    #[test]
    fn prop_unify_idempotent(
        (t, u) in (arb_term(), arb_term())
    ) {
        let env = Envir::empty();
        if let Some(env1) = unify(&env, &t, &u, &UnifyConfig::default()) {
            let t_norm = env1.norm_term(&t);
            let u_norm = env1.norm_term(&u);
            let env2 = unify(&env1, &t_norm, &u_norm, &UnifyConfig::default());
            prop_assert!(env2.is_some());
        }
    }
}
```

## 模式 3: 简化器不变量

```rust
proptest! {
    /// rewrite 产生等价定理: lhs ≡ rhs
    #[test]
    fn prop_rewrite_is_equality(t in arb_term()) {
        let simps = load_simp_rules();
        if let Some(thm) = Simplifier::rewrite_term(&t, &simps) {
            let (lhs, rhs, _) = Pure::dest_equals_with_type(thm.prop.term()).unwrap();
            // lhs 是原始项, rhs 是简化结果
            prop_assert!(lhs.alpha_equivalent(&t));
        }
    }

    /// 深层重写是定点: 重写结果不可再重写
    #[test]
    fn prop_rewrite_deep_fixpoint(t in arb_term()) {
        let simps = load_simp_rules();
        if let Some((rewritten, _)) = Simplifier::rewrite_deep(&t, &simps) {
            // 再次重写结果不变
            let again = Simplifier::rewrite_deep(&rewritten, &simps);
            match again {
                None => {} // 好: 无法再简化
                Some((r2, _)) => prop_assert!(r2.alpha_equivalent(&rewritten)),
            }
        }
    }
}
```

## 模式 4: Isabelle/ML Oracle 测试

```rust
/// 用 Isabelle/ML 版本作为 oracle 验证 isabelle-rs 结果
#[test]
fn prop_compare_with_isabelle_ml(t in arb_bool_term()) {
    let ct = CTerm::certify_annotated(t.clone()).unwrap();
    let ours = ThmKernel::assume(&ct).unwrap();

    // 调用 Isabelle/ML 进程 (如果可用)
    if let Some(oracle) = oracle_isabelle_ml_assume(&t) {
        prop_assert!(ours.prop.term().alpha_equivalent(&oracle));
    }
}
```

## 模式 5: 解析器往返测试

```rust
proptest! {
    /// Pretty print → Parse → 原项 (往返)
    #[test]
    fn prop_pretty_print_roundtrip(t in arb_term()) {
        let printed = pretty_print(&t);
        let parsed = parse_term(&printed);
        // 如果解析成功, 应该等于原项
        if let Some(parsed) = parsed {
            prop_assert!(parsed.alpha_equivalent(&t),
                "roundtrip failed: {} -> {} -> {:?}", t, printed, parsed);
        }
    }
}
```

## 测试配置

```rust
// 默认 proptest 配置
proptest! {
    #![proptest_config(ProptestConfig {
        cases: 256,           // 每次测试运行 256 个案例
        max_shrink_time: 1000, // 收缩时间 1 秒
        max_shrink_iters: 100, // 收缩迭代 100 次
        ..ProptestConfig::default()
    })]
    #[test]
    fn prop_my_test(...) { ... }
}
```

## 属性分类

| 类别 | 示例属性 |
|------|---------|
| 不变式 | `thm.nprems() == 0` (无前提定理) |
| 往返 | `parse(print(t)) == t` |
| 幂等性 | `simplify(simplify(t)) == simplify(t)` |
| 对合性 | `symmetric(symmetric(thm)) == thm` |
| 单调性 | `nprems(simplify(t)) <= nprems(t)` |
| 等价性 | `ours == oracle` (vs Isabelle/ML) |
| 无崩溃 | 所有公共 API 在任意输入上不 panic |

## 检查清单

- [ ] 每个核心类型有 `arb_*()` 生成器
- [ ] 内核 15 操作至少有一个属性测试
- [ ] 统一算法有幂等性和共同实例测试
- [ ] 简化器有定点和不改变语义测试
- [ ] proptest 在 CI 中运行 (非仅本地)
- [ ] 失败案例有最小反例 (收缩)
- [ ] 测试配置合理 (cases ≥ 256)

## 反模式

| ❌ | ✅ |
|----|----|
| 仅测试 happy path | 测试边界和错误路径 |
| 硬编码测试输入 | 生成多样化的随机输入 |
| 忽略收缩 | 确保最小反例 |
| 属性过于宽泛 | 精确的不变量 |
| 无 oracle | Isabelle/ML 作为参考 |
| proptest 仅在本地运行 | CI 中运行 |
