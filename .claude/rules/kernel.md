---
description: LCF 内核规则。KernelRules 15原语 + resolve1_match prototype, CTerm, invariant replay, pub(in crate::kernel) visibility firewall。
globs: src/core/thm.rs, src/core/logic.rs, src/core/drule.rs, src/core/more_thm.rs, src/kernel/rules.rs, src/kernel/thm.rs, src/kernel/cterm.rs, src/kernel/unify.rs, src/kernel/term.rs, src/kernel/typ.rs, src/kernel/invariant.rs, src/kernel/derivation.rs, src/kernel/context.rs
alwaysApply: false
version: 4.0
updated: 2026-07-02
---

# 内核规则

## 触发条件

修改 `src/core/thm.rs`, `src/core/logic.rs`, `src/core/drule.rs`, `src/core/more_thm.rs`,
以及 `src/kernel/rules.rs`, `src/kernel/thm.rs`, `src/kernel/cterm.rs`,
`src/kernel/unify.rs`, `src/kernel/invariant.rs` 时应用。

## 操作总览

```
Strict kernel primitives (15):
  assume, reflexive, symmetric, transitive, combination, abstraction,
  beta_conversion, implies_intr, implies_elim, forall_intr, forall_elim,
  equal_intr, equal_elim, generalize, instantiate

Strict kernel derived (1, prototype):
  resolve1_match — conservative one-way matching, no lifting/freshening,
  no full unification, no flex-flex. Returns RequiresLifting on Free-variable
  collision. NOT full bicompose. See docs/RESOLUTION_DESIGN.md.

Legacy core only (3): bicompose, bicompose_eresolve, subst_premise

Utility (1): trivial
```

**Note**: The three legacy rules (`bicompose`, `bicompose_eresolve`, `subst_premise`)
are **legacy `src/core/` only**. They have NOT been migrated to the strict
`src/kernel/`. The strict kernel's `resolve1_match` is a conservative prototype
backed by strict matching and invariant replay; full `bicompose` /
`bicompose_eresolve` remain design-phase work tracked in
`docs/RESOLUTION_DESIGN.md`. Do not implement strict-kernel resolution by
copying legacy `ThmKernel::bicompose`.

## Thm 结构体完整字段 (Phase 39 + T3 信任足迹)

```rust
pub struct Thm {
    hyps: Hyps,                    // 假设集 (α-equivalence)
    prop: CTerm,                   // 命题
    maxidx: usize,                 // 最大 schematic 索引
    tpairs: Vec<(Term, Term)>,     // flex-flex 分歧对 (Phase 39)
    shyps: Vec<Sort>,              // sort 假设 (Phase 39)
    oracles: Vec<Arc<str>>,        // 信任足迹 (T3): 依赖的未证明断言, 像 hyps 一样并集传播
    derivation: Derivation,        // 推导历史
    serial: u64,                   // 唯一序列号
}
```

## T3 信任足迹 — 铁律

- **真证明 ⟺ `oracles` 为空 ⟺ `is_fully_proved()`**
- `ThmKernel::admit(ct, name)` 是内核**唯一**"接受命题而不证明"入口 (对应 sorry/oracle)
- 每条规则必须传播 `oracles`:公理类 `vec![]`;单前提 `thm.oracles.clone()`;
  多前提 `Self::union_oracles(&a.oracles, &b.oracles)`
- **新增 Thm 构造点必须设置 `oracles`** (铁律 #7 + #21)
- 禁止用 `ThmKernel::assume` 把未证明的命题伪装成已证 — 用 `admit`
- 详见 [docs/TRUST.md](../../docs/TRUST.md)

## T2 规则可靠 — 铁律 (v2.3.0)

- **`tpairs`/`shyps` 必须并集传播** — 多前提规则用 `union_tpairs`/`union_shyps`,
  单前提 `clone`。当前恒空,但接入完整高阶合一后丢弃会不可靠。
- **`alpha_eq` Branch A/B 是承重的真实可靠性洞,禁止在内核直接收紧**:
  - Branch A `Free≡Const` 后缀匹配 (`thm.rs:219`) — 弥合 parser/loader 表示鸿沟
  - Branch B `Var≡Free` (`thm.rs:225`) — DB schematic 定理靠此匹配 parser 的 Free
  - **正确修复在解析边界** (certify_annotated 把 Free 解析为 Const + hol_loader
    mk_var→Term::free),不在内核。直接收紧会击穿算术证明链 → Tier2 暴跌。见 T2-4。
- **`alpha_eq` Branch C 已加 binder 类型守卫** (`thm.rs:231`) — dummy 容忍,
  已知不同类型拒绝。`λ(x:nat).x ≢ λ(x:bool).x`。
- **`combination` 是 congruence 规则** — 对任意类型逻辑可靠;dummy 时跳过类型检查
  是 well-formedness 取舍,非 bug。类型已知时拒绝不匹配。

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

## Bicompose — ⚠️ LEGACY CORE ONLY

These are the **legacy `src/core/`** bicompose signatures. They have NOT been
migrated to the strict `src/kernel/`. Do NOT use these as implementation
reference for strict-kernel resolution rules. See `docs/RESOLUTION_DESIGN.md`
for the strict-kernel design.

```rust
// LEGACY src/core/ — not available in src/kernel/
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
