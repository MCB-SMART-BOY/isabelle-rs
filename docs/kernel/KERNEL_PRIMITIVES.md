# Strict Kernel Primitive Contracts

This document describes the `crates/kernel/src/` nucleus rules (re-exported by
`src/kernel/mod.rs`). It is a contract for the strict TCB, not for the legacy
`src/core` implementation.

局部原语及 replay 的实现不表示原生 Isabelle2025 兼容验收。
P2/P3/P4 已按批准的 P1 设计恢复实施；两个 Rust THM consumer 的局部
实际闭环、失败与运行范围见 [首个闭环](../status/PROJECT_STATUS.md#first-native-rust-thm-closure-2026-10-18)
和 [变量闭环](../status/PROJECT_STATUS.md#rust-thm-type-and-variable-transformations-2026-10-19)。
旧 bundled 125-case 计数不是本轮重跑结果；本文末尾的 P1 合同是整体目标，
其中部分窄项已实施，不能据此认定完整 ML THM 或全部规则已经验收。

## Global Invariants

- There is no dummy type in the strict kernel type language.
- `Signature` starts with `prop/0` and `fun/2`; every other type constructor
  must be declared with its exact arity before using it in an annotation,
  scheme, or constant declaration. Supported type-variable sorts and indices
  are checked recursively.
- Constants must be declared in `Signature`.
- `CTerm` and `CProp` are produced only by strict certification.
- `CTerm`、`CProp` 和 theorem 使用精确 `ContextStamp`，包含
  `TheoryId`、`SignatureId`、`logic_basis` 与内核分配的 `local_type_scope`；
  多输入规则在逻辑匹配前拒绝 stamp 不同的输入。当前 domain 为
  `signature/v4`、`theory/v4`、`context/v3`、`theorem/v8`；
  完整类型/class/arity/常量方案及 proof payload 的准确编码以
  [`identity.rs`](../../crates/kernel/src/identity.rs) 和
  [`theory.rs`](../../crates/kernel/src/theory.rs) 为准。
- Theorem fields are private.
- Pure primitive theorem values are produced by `KernelRules`; checked axiom
  instances use `theorem_builder::axiom_theorem`, and conservative definitions
  use the internal definition builder. None of these constructs an accepted
  token without exact-owner `accept_closed_theorem`.
- `ProofObligation` is not a theorem.
- `ClosedThm` is a wrapper for a checked theorem whose closure obligations
  have passed; it is not itself a trusted accepted token.
- `KernelThm::try_close` 与 `theorem_builder::close_thm` 拒绝局部类型作用域、
  未解 C/F/pending 及额外 shyps；实际出现在 P/H/F 的 schema sorts 保留。
  `ClosedThm` 本身不是 accepted seal，接受端再次完整 replay 和检查负载。
- `TrustedTheorem` is a private accepted seal over a replayed `ClosedThm`,
  canonical logical `TheoremId`, exact proof/acceptance theory identities, and
  replay-derived dependencies. The dependency set does not itself grant
  theorem-reference authority.
- `TrustedTheory` is immutable owner/fact ancestry. `accept_closed_theorem` is
  the only token constructor and atomically returns the fact child plus token;
  duplicate names and owner/store mismatches fail closed.
- Every accepting replay recursively recertifies theorem fields and all checked
  derivation payloads under the exact owner.
- Ancestor theorem reuse records an exact theorem dependency. Installed
  logic-basis declarations and all axiom schemas are validated against the
  immutable signature before installation; axiom instances and conservative
  monomorphic definitions are also checked on owner replay. The two bounded
  standalone HOL/Pure fixtures and the audited sampled `HOL::TrueI` projection
  use this boundary, not general HOL source loading.
- `SearchFactDb` facts are proof-erased and not trusted theorem-table entries.

## Accepted theorem reference

```text
input:  owner : TrustedTheory, theorem : TrustedTheorem in owner ancestry
output: ClosedThm in the owner's current context
```

This is fact reuse, not a new logical axiom. Construction and replay both check
the exact non-forgeable token (`id`, `name`, and `accepted_in`) against theory
ancestry, recertify the proposition in the descendant signature, and only then
record the referenced logical `TheoremId`. Equal-content sibling tokens may
share that ID but are not interchangeable; a sibling or stale token is
rejected.

## `assume`

```text
input:  A : CProp
output: OpenThm, A |- A
```

Side conditions:

- `A` must be a certified proposition.

Result:

- hypothesis set is `{A}`;
- proposition is `A`;
- the theorem is open and cannot become a `ClosedThm`.

## `reflexive`

```text
input:  t : CTerm
output: ClosedThm, |- t == t
```

Side conditions:

- `t` must be certified.
- the object type of both sides is exactly `type_of(t)`.

Result:

- no hypotheses;
- exact-context invariant replay succeeds; the result becomes trusted only
  after `accept_closed_theorem`.

## `symmetric`

```text
input:  Γ |- t == u
output: Γ |- u == t
```

Side conditions:

- premise proposition must be equality.

Propagation:

- hypotheses are preserved.

## `transitive`

```text
input:  Γ |- t == u
        Δ |- u == v
output: Γ ∪ Δ |- t == v
```

Side conditions:

- both premises must be equality propositions;
- equality object types must be identical;
- middle terms must be strict alpha-equivalent;
- Free/Const and Var/Free compatibility are rejected.

Propagation:

- hypotheses are unioned modulo strict alpha-equivalence.

## `implies_intr`

```text
input:  Γ ∪ {A} |- B
output: Γ |- A ==> B
```

Side conditions:

- `A` must occur in the theorem hypotheses modulo strict alpha-equivalence.

Propagation:

- exactly one matching hypothesis is discharged.

## `implies_elim`

```text
input:  Γ |- A ==> B
        Δ |- A
output: Γ ∪ Δ |- B
```

Side conditions:

- major premise proposition must be implication;
- minor conclusion must be strict alpha-equivalent to the antecedent.

Propagation:

- hypotheses are unioned modulo strict alpha-equivalence.

## `beta_conversion`

```text
input:  redex : CTerm, shape ((λx:τ. body) arg)
output: ClosedThm, |- ((λx:τ. body) arg) == body[arg/x]
```

Side conditions:

- `redex` term must be an `App` whose `func` is an `Abs`.
- `arg` type must match the binder parameter type `τ`.
- Bound substitution is strict de Bruijn `instantiate_bound0(body, arg)`.

Result:

- no hypotheses;
- exact-context invariant replay succeeds; the result becomes trusted only
  after `accept_closed_theorem`.

Attack tests cover:

- identity reduction: `(λx:nat. x) a ≡ a`;
- non-application CTerm rejected;
- non-lambda `App` (Const function) rejected;
- inner bound variables preserved under substitution;
- invariant check passes on valid output;
- closed theorem accepted only through the separate exact-owner trust gate;
- function application substitution `(λx:nat. f x) a ≡ f a`;
- nested lambda capture avoidance: `(λx:nat. (λy:nat. x)) a ≡ (λy:nat. a)`;
- argument with bound variable lifted correctly: `(λf. f a) (λx. x) ≡ (λx. x) a`;
- triple-nested lambda substitution;
- invariant replay catches tampered proposition;
- invariant replay catches tampered hypotheses.

## `forall_intr`

```text
input:  variable : CTerm, free variable x : τ
        theorem  : Γ |- P
output: Γ |- ⋀x:τ. P[x → Bound(0)]
```

Side conditions:

- `variable` must be a `Free` term (Var not yet supported);
- `x` must not occur free in any hypothesis in Γ.
- The free variable is abstracted from the conclusion using de Bruijn
  abstraction: every `Free(x, τ)` becomes `Bound(depth, τ)` where `depth`
  counts enclosing Abs/Forall binders. Existing `Bound` indices are unchanged.

Propagation:

- hypotheses are preserved.

Attack tests cover:

- generalises free variable in conclusion: `|- (x == a) ⇒ (x == a)` → `|- ⋀x. ((x == a) ⇒ (x == a))`;
- rejects variable with same name free in hypotheses;
- rejects non-Free variable (Const, App, Abs);
- produces closed theorem from closed input;
- invariant check passes on valid output;
- hypotheses are preserved through generalisation.

## `forall_elim`

```text
input:  Γ |- ⋀x:τ. P(x)
        t : CTerm with type τ
output: Γ |- P(t)
```

Side conditions:

- Theorem proposition must be a `Forall` (⋀x:τ. body).
- Argument type must exactly match the binder parameter type τ.
- Substitution uses strict de Bruijn `instantiate_bound0(body, arg)` — the
  inverse of the `abstract_over` used in `forall_intr`.

Propagation:

- Hypotheses are preserved.

Attack tests cover:

- instantiates bound variable correctly: `⋀x:nat. (x==a)⇒(x==a)` with `a` → `(a==a)⇒(a==a)`;
- rejects non-Forall input with `NotForall`;
- rejects binder/argument type mismatch with `ForallBinderMismatch`;
- preserves hypotheses through elimination;
- invariant check passes on valid output;
- nested Forall: eliminates only the outermost binder, preserves inner structure;
- `forall_intr`/`forall_elim` round-trip: `forall_elim(forall_intr(thm), x) ≡ thm`;
- invariant replay catches tampered proposition (unreduced forall body).

Substitution-depth stress tests cover:

- `forall_elim` does not replace `Bound(1)` when eliminating the outer binder;
- multiple `Bound(0)` occurrences all replaced;
- consecutive nested forall elimination (outer then inner);
- `forall_elim` with `Abs` argument substitutes correctly;
- `beta_conversion` then `forall_elim` without de Bruijn interference.

## `combination`

```text
input:  Γ |- f == g       (f, g : τ → σ)
        Δ |- x == y       (x, y : τ)
output: Γ ∪ Δ |- f x == g y
```

Side conditions:

- Both premises must be equality propositions.
- `f` and `g` must be function types; the equality object type `τ → σ` is
  destructured via `dest_arrow` to extract domain `τ` and codomain `σ`.
- The argument equality object type must match the function domain exactly.
- The result application terms `f x` and `g y` share the codomain `σ`.

Propagation:

- Hypotheses are unioned modulo strict alpha-equivalence.

Attack tests cover:

- basic function-congruence application: `f == g`, `a == b` → `f a == g b`;
- rejects non-equality function premise with `NotEquality`;
- rejects non-equality argument premise with `NotEquality`;
- rejects non-function `f`/`g` with `NotFunctionType`;
- rejects domain/argument type mismatch with `TypeMismatch`;
- preserves open hypotheses through union;
- invariant check passes on valid output;
- invariant replay catches tampered proposition (swapped argument order);
- composition with `reflexive` produces closed theorem.

## `abstraction`

```text
input:  Γ |- t == u              (t, u : β)
        variable name x, type α
output: Γ |- (λx:α. t[x→Bound(depth)]) == (λx:α. u[x→Bound(depth)])   (λx..., λx... : α → β)
```

Side conditions:

- Premise proposition must be equality.
- `x` must not be free in any hypothesis in Γ.

Propagation:

- Hypotheses are preserved.
- `t` and `u` are abstracted via `Term::abstract_over`:
  every `Free(x, α)` in the body is replaced with `Bound(depth, α)`, where
  `depth` counts enclosing Abs/Forall binders in that body. Only occurrences
  at depth zero become `Bound(0, α)`; other frees remain unchanged.

Attack tests cover:

- basic lambda introduction: `a==b ⊢ (λx. a)==(λx. b)`;
- rejects abstraction when `x` is free in hypotheses;
- preserves hypotheses through abstraction;
- rejects non-equality premise with `NotEquality`;
- invariant check passes on valid output;
- produces closed theorem from closed input;
- nested abstraction preserves binder structure;
- composes with `forall_elim` + `combination` + `abstraction`;
- invariant replay catches tampered proposition (wrong binder name);
- `Free(x)` replaced by `Bound(0)` in body (critical binding-correctness);
- only target variable abstracted — other `Free`s preserved;
- `Free(x)` replaced within application terms.

## `equal_intr`

```text
input:  Γ |- A ==> B
        Δ |- B ==> A
output: Γ ∪ Δ |- A == B
```

Side conditions:

- Both premises must be implication propositions.
- The antecedent of the first must be strict alpha-equivalent to the
  consequent of the second (`A == A`), and vice versa (`B == B`).

Propagation:

- Hypotheses are unioned modulo strict alpha-equivalence.

Attack tests cover:

- mutual implications `A==>B, B==>A` yield `A==B`;
- rejects non-implication left premise with `NotImplication`;
- rejects non-implication right premise with `NotImplication`;
- rejects mismatched pairs with `AntecedentMismatch`;
- preserves distinct open hypotheses through union;
- round-trip with `equal_elim`: `equal_elim(equal_intr(…), A) → B`;
- invariant replay catches tampered proposition.

## `equal_elim`

```text
input:  Γ |- A == B
        Δ |- A
output: Γ ∪ Δ |- B
```

Side conditions:

- Major premise must be an equality proposition.
- The equality must be **propositional**: `A == B` where `A, B : prop`.
  Object equality (`x == y` where `x, y : nat`) is rejected with
  `NotProposition`.
- Minor premise must be strict alpha-equivalent to the left-hand side `A`.

Propagation:

- Hypotheses are unioned modulo strict alpha-equivalence.

Attack tests cover:

- `A==B, A ⊢ B` elimination;
- rejects non-equality major premise with `NotEquality`;
- rejects object equality with `NotProposition`;
- rejects minor-premise mismatch with `AntecedentMismatch`;
- round-trip: `equal_elim(equal_intr(A==>B, B==>A), A) → B`;
- preserves open minor hypothesis through union;
- invariant replay catches tampered proposition.

## First Attack-Test Set

The independent test file `tests/kernel_rewrite_soundness.rs` covers:

- undeclared constants rejected;
- undeclared frees rejected;
- dummy type construction rejected;
- ill-typed application rejected;
- Free/Const middle-term mismatch rejected;
- Var/Free middle-term mismatch rejected;
- `assume(A)` creates an open theorem;
- `reflexive(t)` creates a closed theorem; only owner acceptance seals it;
- implication introduction discharges hypotheses;
- implication elimination requires exact antecedent;
- transitivity requires typed middle equality;
- beta conversion reduces identity applications;
- beta conversion rejects non-lambda applications;
- beta conversion preserves inner bound variables;
- beta conversion produces closed trusted theorems;
- beta conversion substitution is correct;
- beta conversion nested lambda capture avoidance;
- beta conversion argument bound lift;
- beta conversion triple nested substitution;
- `forall_intr` generalises a free variable in the conclusion;
- `forall_intr` rejects a variable free in hypotheses;
- `forall_intr` rejects non-Free terms;
- `forall_intr` produces closed theorems from closed input;
- `forall_elim` instantiates bound variable with matching argument;
- `forall_elim` rejects non-Forall input;
- `forall_elim` rejects binder/argument type mismatch;
- `forall_elim` preserves hypotheses;
- `forall_elim` handles nested Forall (outer-only elimination);
- `forall_intr`/`forall_elim` round-trips;
- `combination` basic function-congruence;
- `combination` rejects non-equality premises;
- `combination` rejects non-function `f`/`g`;
- `combination` rejects domain/argument type mismatch;
- `combination` preserves open hypotheses;
- `combination` invariant passes and catches tampering;
- `combination` composes with `reflexive` for closed theorems;
- `abstraction` introduces lambda binders on both sides of equality;
- `abstraction` rejects `x` free in hypotheses;
- `abstraction` preserves hypotheses;
- `abstraction` rejects non-equality premise;
- `abstraction` invariant passes and catches tampering;
- `abstraction` produces closed theorem from closed input;
- `abstraction` nested supports two binders;
- `abstraction` composes with `forall_elim` + `combination`;
- `abstraction` replaces `Free(x)` with `Bound(0)` (binding semantics);
- `abstraction` only abstracts target variable — other Frees preserved;
- `abstraction` replaces `Free(x)` within application terms;
- `equal_intr` mutual implications yield equality;
- `equal_intr` rejects non-implication premises;
- `equal_intr` rejects mismatched implication pairs;
- `equal_intr` preserves hypotheses;
- `equal_intr`/`equal_elim` round-trip;
- `equal_elim` A==B, A → B;
- `equal_elim` rejects non-equality major premise;
- `equal_elim` rejects minor mismatch;
- `equal_elim` preserves open minor hypotheses;
- `equal_elim` rejects object (non-prop) equality;
- `ProofObligation` is not a theorem;
- `SearchFact` cannot become `TrustedTheorem`;
- `generalize` basic free→var transformation;
- `generalize` preserves hypotheses;
- `generalize` selected term names share one explicit index;
- `generalize` transforms every selected TFree annotation, including cached types;
- `generalize` selects Free names across distinct types, with checked trailing `_` cleanup;
- `generalize` closed/open theorem status preserved;
- `generalize` invariant check passes;
- `generalize` empty selections are identity, including at the largest index;
- `generalize` nonempty unmatched selections still require a fresh index;
- `generalize` checks the full input maxidx and recomputes output P/H/F/C maxidx;
- `generalize` preserves S/C/pending/mode and transforms, but never drops, F;
- `generalize` rejects selected term or fixed-type parameters in H;
- `generalize` round-trip records derivation for future instantiate;
- `instantiate` basic Var→Term replacement;
- `instantiate` rejects type mismatch;
- `instantiate` respects Var index (Var(x,0) ≠ Var(x,1));
- `instantiate` type-sensitive name+index matching;
- `instantiate` rejects duplicate (name,idx) entries;
- `instantiate` rejects Bound in replacement;
- `instantiate` partial substitution keeps unmatched Vars;
- `instantiate` preserves hypotheses;
- `instantiate` invariant check passes;
- `instantiate` closed theorem stays closed;
- `instantiate` does not affect Const/Free nodes;
- `instantiate` empty subst is identity;
- `instantiate` multiple Vars with different replacements;
- `instantiate` all occurrences of same Var replaced;
- `instantiate` round-trip with generalize.

## `generalize` — 固定类型与项的统一泛化

`KernelRules::generalize(thm, type_names, term_names, index)` 接收两个
`BTreeSet<Name>` 和显式 `usize` 索引。选中的 TFree 变为同名、同 sort
的 TVar；选中的 Free 按名字（不是 `(name, type)`）变为 Var。
普通项名共用 `index`，项名每个尾部 `_` 被移除并 checked 增加一次索引；
类型名不清洗。所有 Bound/App/Abs 等类型注解与缓存类型同时转换，
已有 Var/TVar 身份不变。

- 两集合为空时原样返回；非空但未命中仍要求 `index > thm.max_var_index()`。
  冲突返回 `GeneralizeIndexNotFresh`，算术溢出返回
  `GeneralizeIndexOverflow`，TVar 超过 u32 表示域返回
  `TypeVariableIndexOutOfRange`。
- H 保持不变。H 中出现选中项名或选中 TFree 的任何注解分别返回
  `FreeVarInHypotheses` / `TypeFreeInHypotheses`；不允许把 H 泛化成 schematic。
- P/F 转换，S/C/pending/mode 精确保留；相等 F 端点也不自动删除。
  结果 maxidx 从当前 P/H/F/C 重算，不继承已经消失的历史 premise 索引。
- `Derivation::Generalize` 记录名称集合、索引及词法未绑定的 typed source frees。
  接受时先在来源类型域完整回放，再从已验证来源产生结果授权环境；
  同名不同类型以精确 typed key 区分，不能向 owner 加声明或覆盖声明规避冲突。
  binder 授权保留词法来源，类型变换和已验证 RHS 复制都传播该来源；
  退出 binder 撤销该层全部派生授权，同 key 的独立外层来源仍保留。
- 泛化不改变 local stamp，也不等于 `forall_intr` 或 scope 导出。

### 认证对象与 scope 导出

`ProofContext::generalize_type` 返回 CType；`generalize_term` 返回
`(ProofContext, CTerm)`，派生 context 同步剩余 Free 的类型，原 context
保持不变。非空选择的认证对象索引缓存保留
`max(old, requested, actual)`；这是安全下界强化，不声称等同于官方缓存数值。
这些 API 保留 local scope，不授予定理权限。

`KernelRules::export_scope(owner, source_context, theorem)` 保存私有构造的
`ProofScope`，在原 owner 恢复原 kernel-issued stamp，完整回放来源并重建依赖，
然后在没有 local 声明的 owner 重认证 P/H/F/C。剩余 Free/TFree 拒绝；
义务不丢弃，local theorem 仍不能直接关闭。后代 transfer 先在实际祖先回放，
不能以新 owner snapshot 配旧 scope stamp。

导出进入 bound proof 时，先 lower 内层 scope，再对仅存在于历史 proof 的
本 scope 参数做确定性泛化；fresh 索引覆盖完整 lowered proof，保留 Bound 深度、
leaf source keys、occurrence 身份及依赖。所有转换后 operand 仍由 owner checker
认证，没有“已回放所以免检查”的叶子。

`KernelRules::incr_indexes(owner, context, theorem, increment)` 在零增量时也
检查 owner/context 并回放来源；正增量复用 SourceRenameIndex 与 AdjustMaxIndex，
变换 P/F/proof operands，保留 H/S/C/pending/mode。局部 theorem 必须先导出，
usize/u32 边界 checked，不提供负数索引或 ML adapter。

跨步骤消费见 `native_thm_variables` 示例及 `variable_transformations`、
`scope_export`、`binder_replay` 回归。实例化后消失的空 sort 仍可能阻止关闭；
consumer 必须用已有受检 `strip_shyps` 解除，而不是删除 payload 字段。

## `strip_shyps` — 当前空 sort 路径

当前入口为 `KernelRules::strip_shyps(owner, context, theorem)`，不是下文
完整 C4 class/export 设计的实现声明。原 source 必须先在准确 owner/context
重放全部字段、操作数和依赖；class constraints、flex pairs、pending 与
没有 witness 的非空 extra sort 保持拒绝。

现有 Pure derivation 按源操作顺序降低为私有 bound proof；proof hypothesis
slot 不是真实 H。resolution 先拆原 rule 的准确前提，再分别实例化，不能将
实例化后结论中的 implication 当成新前提。已绑定的证明中，仅不在最终 P/H
的空-sort type atom 可替换；proof-only Free 在类型映射前按原 typed identity
转为超过完整 bound proof 索引上界的新 Var，原 leaf keys 与调用方 context 不变。

保存的 source 用已有受检 `Generalize` 显式导出其消失的 Free 参数。
收集覆盖 source 的实际操作数，包括未使用的 axiom 参数和 substitution RHS；
原 `ForallIntr`、`Abstraction`、`Generalize` binder 仅作用于其自己的 premise，
不扩展兄弟分支。接受时仍完整重放该 source，再在未扩充的 owner context
独立检查 bound proof；只有 binder 全闭且精确保持 H/P 才物化普通 theorem。
关闭与唯一 `accept_closed_theorem` 仍分别检查完整负载；此路径不清空义务
冒充证明，也不授权任意 class、非空 sort 导出或 typedef。

## `instantiate` (Schematic Var → Certified Term)

```text
input:  H |- P
        types: finite TVar substitution
        subst: [InstEntry{name₁, idx₁, τ₁, replacement₁}, ...]
output: H |- (P[type_inst])[subst]
        term keys use the exact type after the complete type pass
```

### Trust boundary

Every replacement must be a certified `CTerm`, passed via `InstEntry`:
`InstEntry { name, index, var_ty, replacement: CTerm }`. This enforces the
kernel certification boundary:

```text
RawTerm → Signature/ProofContext certification → CTerm → InstEntry → KernelRules::instantiate
```

Bare `Term` values cannot be passed as replacements.

### Design decisions

- **顺序**：先对类型做有限一次替换，再匹配完整类型化 term key；
  RHS 不递归重新代入。递归 unifier 的 occurs-check 不是本 API 的规则。
- **Exact match**: Var matching is on **all three** of `(name, index, type)`.
  `Var("x", 0, nat)` ≠ `Var("x", 1, nat)` ≠ `Var("x", 0, bool)`.
- **完整键去重**：按 type pass 之后的 `(name, index, var_ty)` 去重；
  同名、同 index、不同类型是不同项，只有完整键重复才报
  `DuplicateSubstitution`。
- **Partial substitution**: Unmatched Vars remain unchanged. Valid if the
  theorem contains Vars not listed in the substitution.
- **Type check (defense-in-depth)**: `replacement.ty() == var_ty` for every
  entry. While `InstEntry` construction should preserve this invariant, the
  kernel performs a runtime check.
- **Simultaneous substitution**: The replacement is a single-pass traversal
  over the original theorem. Var nodes inside replacement terms are NOT
  substituted even if they match another entry. Substitution order does not
  matter — the result is deterministic and independent of entry ordering.
- **捕获检查**：replacement 不得有逃逸的 loose `Bound`；
  自身 `Abs`/`Forall` 内合法绑定的 `Bound` 不受此限制。
- **作用域与负载**：真实 H 必须不含 Var/TVar，替换精确保留 H；
  P/F 和 C 中的类型按各自规则处理。所有 RHS（即使未命中）及被消去的
  forall/axiom 参数仍贡献 sort 负载，不得由最终 P 反推并丢弃。

### Implementation outline (already implemented)

1. `InstEntry { name, index, var_ty, replacement: CTerm }` — typed substitution
   entry enforcing the certification boundary at the Rust type level.
2. `Term::instantiate_vars(&self, subst: &[InstEntry]) -> Term` — iterative
   continuation-frame traversal replacing `Var(name, idx, ty)` with
   `entry.replacement.term().clone()` when all three fields match.
3. `KernelRules::instantiate(context, thm, type_inst, subst)` 核 owner、
   全部类型 RHS、完整键重复、replacement 类型及 Bound 作用域；先 types、
   后 terms，构造可 replay 的 `Derivation::Instantiate` 并保留完整负载。

### Contract

Side conditions:
- Every replacement is a certified `CTerm` (enforced by `InstEntry` type).
- `replacement.ty() == var_ty` for every entry (type match) → `TypeMismatch`.
- No duplicate `(name, idx, var_ty)` entries → `DuplicateSubstitution`.
- No escaping loose `Bound` in a replacement → `BoundInSubstitution`.
- No dummy type in replacements (enforced by CTerm certification).
- Partial substitution is valid: unmatched `Var`s remain unchanged.

Propagation:
- H 精确保留；输入 H 中的 Var/TVar 直接拒绝，不能靠替换修补。
- S/C/F/pending 保留或按显式变换处理；实例化成功不保证可关闭。

### Round-trip guarantee

```text
generalize(thm, empty_type_names, term_names, index)
  then instantiate(context, result, empty_types, original_terms)
  preserves the proposition and real hypotheses; closure still checks all obligations
```

这是仅泛化项的往返。替换键使用调用者提供的显式 `index`；原名字尾部
每个 `_` 被删除并增加一位索引，必须使用清洗后的名字与实际索引。

And:

```text
instantiate(context, thm, type_inst, subst), then generalize(result, ...)
  is NOT guaranteed to round-trip, because instantiate may replace Vars
  with terms that contain Frees different from the original schematic
  representation.
```

## Historical Initial Attack Checklist (generalize)

This is the earlier checklist of intended behaviors, not current case names
or a fresh run. The typed-name implementation and executable examples are
indexed in the [2026-10-19 delivery record](../status/PROJECT_STATUS.md#rust-thm-type-and-variable-transformations-2026-10-19).

| Test | What it checks |
|------|----------------|
| `generalize_basic` | Free(nat) → Var(start, nat) in closed reflexive theorem |
| `generalize_free_in_real_hypothesis_rejects` | Selected Free in a real hypothesis is rejected; H is never rewritten |
| `generalize_multiple_frees` | Selected ordinary names share one explicit fresh index |
| `generalize_non_free_unchanged` | Const and Bound nodes unchanged |
| `generalize_only_target_free` | Only named frees replaced; different-name frees preserved |
| `generalize_closed_remains_closed` | Closed theorem stays closed |
| `generalize_open_hypothesis_with_target_free_rejects` | Open H cannot authorize generalization of its fixed parameter |
| `generalize_invariant_check_passes` | check_kernel_thm succeeds |
| `generalize_empty_frees_noop` | Empty type and term name sets are identity |
| `generalize_ignores_unmatched_free` | Unmatched names preserve content but still require a fresh index |
| `generalize_explicit_fresh_index_avoids_existing_var` | Caller-selected fresh index leaves existing Vars unchanged |
| `generalize_name_selection_preserves_other_atom_kinds` | Name-based Free selection leaves Const and Bound atoms unchanged |
| `generalize_roundtrip_with_instantiate` | generalize then instantiate = original |
| `generalize_tampered_prop_fails_invariant` | Wrong Var index |

## Historical Initial Attack Checklist (instantiate; 18 cases at that checkpoint)

The case labels below preserve the earlier test-planning snapshot; they are
not current test names or fresh execution results. The current typed-key,
real-H and explicit-index behavior is specified above and exercised by
[`variable_transformations.rs`](../../crates/kernel/tests/variable_transformations.rs)
and [`theorem_instantiation.rs`](../../crates/kernel/tests/theorem_instantiation.rs).

| Test | What it checks |
|------|----------------|
| `instantiate_basic` | Var(name,idx,τ) → Certified Term, matching type |
| `instantiate_rejects_type_mismatch` | Var(nat) := prop_term → TypeMismatch |
| `instantiate_respects_index` | Var(x,0) and Var(x,1) not confused |
| `instantiate_rejects_duplicate_substitution` | Duplicate complete `(name,index,type)` keys reject; different types are distinct keys. |
| `instantiate_rejects_duplicate_same_name_index_different_type` | Historical same-name/index expectation; superseded by typed keys, so distinct types are distinct entries. |
| `instantiate_rejects_bound_in_replacement` | Escaping Bound is rejected; an internally bound index remains legal. |
| `instantiate_is_simultaneous_not_sequential` | Single-pass traversal; order-independent result |
| `instantiate_type_sensitive_same_name_index` | Var(x,0,nat) not matched by prop term |
| `instantiate_multiple_vars` | Multiple different Vars with different replacements |
| `instantiate_partial_substitution_keeps_unmatched_var` | Var not in subst remains as-is |
| `instantiate_same_var_all_occurrences` | All occurrences of same Var replaced |
| `instantiate_preserves_hypotheses` | Historical plan to instantiate H; current real H is preserved unchanged and schematic Var/TVar in H is rejected. |
| `instantiate_invariant_check_passes` | check_kernel_thm succeeds |
| `instantiate_closed_remains_closed` | Closed theorem stays closed |
| `instantiate_does_not_affect_const_or_free` | Only Vars replaced |
| `instantiate_empty_subst_noop` | Empty subst = identity |
| `instantiate_roundtrip_with_generalize` | generalize→instantiate = original |
| `instantiate_invariant_catches_tampered_result` | Tampered result caught by invariant (inline test) |

---

# Resolution / Bicompose Family

**Design tracked in [RESOLUTION_DESIGN.md](../design/RESOLUTION_DESIGN.md).**

The early resolution design in [RESOLUTION_DESIGN.md](../design/RESOLUTION_DESIGN.md)
distinguishes current conservative `resolve1_match` / `subst_premise` from full
Isabelle-style resolution. Implication-chain utilities, the strict matcher and
these two operations are implemented; the historical `bicompose` alias is not
exported by the current crate. The newer separately named
`bicompose_candidate`, `lift_rule`, `assumption_candidate`,
`eq_assumption`, `rotate_rule` and `permute_prems` use checked bound-proof
paths with owner/payload replay; see the
[fixed THM interface inventory](../status/NATIVE_THM_INTERFACE_INVENTORY.md).
They are narrow Rust capabilities, not complete `Thm: THM` / ML `Seq` or
general unification. The historical sample's `HOL::TrueI` remains `1/125`
and does not authorize broader HOL proof rules.

**Conservative operation status**: `resolve1_match` uses the shared
`replace_subgoal_with_premises` helper, records `Resolve1Match` and rejects
namespace collisions requiring lifting. The conservative `subst_premise` is
propositional equality only, fixed lhs→rhs and without full unification or
object-equality rewriting. The distinct, later
`bicompose_candidate` uses its own checked bound-proof derivation and retains
unresolved flex burdens instead of turning a search candidate into a closed
proof. Neither interface implies complete Isabelle `bicompose_eresolve`,
higher-order matching or ML observable effects.

# P1 Native Closure Kernel Contract Design

本节是固定 Isabelle2025 `765fb2460a57eb46e8490283241ad46f1fac857f` 九根及完整依赖闭包的**已批准整体设计**，不是上文所有窄项的当前状态：上文已按源码描述部分 Rust payload、class/sort、ordered owner DAG、checked bound proof 与变量变换，但不代表 ML THM、typedef、ROOT 或完整闭包验收。Rust kernel 是唯一 theorem authority；官方源码/运行结果、ML `Thm`、P0 探针与报告均不是证书。下述尚未闭合的合同仍须迁移受影响 API、逐节点 replay、独立攻击审查并实际运行完整闭包；具体已实现项以 [THM 逐项清单](../status/NATIVE_THM_INTERFACE_INVENTORY.md) 和 [最新交付记录](../status/PROJECT_STATUS.md#rust-thm-type-and-variable-transformations-2026-10-19) 为准。目标权限、逻辑基础和验收边界见 [TRUST.md 的 P1 设计](../status/TRUST.md#p1-native-trust-design) 与 [验收差距](KERNEL_TRUSTED_ACCEPTANCE_GAPS.md#p1-design-and-implementation-gap)。固定源以仓库内 [Pure type/sort](../../isabelle-source/src/Pure/type.ML)、[Thm](../../isabelle-source/src/Pure/thm.ML)、[Context](../../isabelle-source/src/Pure/context.ML)、[Proofterm](../../isabelle-source/src/Pure/proofterm.ML)、[Theory](../../isabelle-source/src/Pure/theory.ML)、[Defs](../../isabelle-source/src/Pure/defs.ML) 和 [typedef](../../isabelle-source/src/HOL/Tools/typedef.ML) 等真实文件核对，不依赖会话附件。

## P1 Type, sort and complete theorem payload

`RawType = Type(qualified_tycon,args) | TFree(name,sort) | TVar(name,index,sort)`；`Sort` 是全限定 class 名按稳定类名次序排序、去重的集合；sort 集合之间按 `Term_Ord.sort_ord` 比较。`[]` 与 `[HOL.type]` 不同；`TFree` 和 `TVar` 不能互换，TFree 的固定参数作用域由 context stamp 单独参与身份，同一固定/示意 identity 的 sort 必须一致，index 非负，scheme 的 `(identity,sort)` 表有稳定参数顺序。声明与认证检查 tycon 元数、常量完整类型方案、class 可达与 sort、binder/Bound 及作用域。`Signature` 同时保存 class 直接父图、经 proof 授权的 classrel 和 `(tycon,arg_sorts,result_class)` arity；声明和合并均查无环、元数、coregularity。布尔 `Sign.of_sort`、`sort_le` 仅可用于搜索或预检，非 class proof。

目标完整负载为 `KernelThm{owner,hyps:H,prop:P,shyps:S,sort_obligations:C,tpairs:F,local_frees,local_tfrees,derivation,dependencies,pending,mode}`；`maxidx` 根据实项重算并审核合法上界。每条规则将前提 H/C/S/F/deps/pending 全量合并，只有明确的证据转换可消除义务。**真实 H 的每个项与每处类型注解均不得含 Var/TVar**（重算 `maxidx=-1`）；assume、weaken、合并、replay 都查，不能靠实例化 H 修补：从 `Q(?'a)` 假设推演后把 prop 中 `?'a` 换成另一类型不合法。合法受控 Free/TFree 可存在于开放证明，闭合边界不得泄漏局部作用域。

`present_shyps` 是 P/H/F 中实际 atomic type 注解的 sorts，作为参数化 theorem schema 保留；`extra_shyps = S − present_shyps` 按 sort **结构相等**计算，不能直接删除，也不因 S 非空拒绝合法 schema。关闭前 H/C/F、未消去 extra shyps、局部逃逸、oracle/admit/skip、未完成 future/promise、pending 均为空；接受时再 replay 完整 P/H/C/S/F、owner、依赖与 mode，而非仅比命题。`instantiate` 为 types-before-terms **有限一次**替换：TVar 键含 name/index/sort，Var 键为 type pass 后的精确型别；命中 RHS 不递归再代入，合法 `?'a ↦ ?'a list` 和 `?x ↦ f ?x` 不用 occurs-check；递归 unifier 环境才需无环检查。仍须核对 sort 证据、Bound 捕获、owner、C/S/F 和 H 不变量。

## P1 Ordered owner DAG and joint dependency validation

目标 `TheoryNode` 绑定真实不可变父节点及 `ordered_canonical_parents`、共享祖先、完整 signature、`LogicPolicyId`、extension、联合 dependency graph、accepted facts；proof context 另绑定局部固定变量及参数作用域。`Context.make_parents` 保留输入**首次**顺序、按身份去重、删去被其他输入覆盖的祖先，不按名字或字典排序；diamond 共祖先只计一次，同 basename 异身份冲突。规范 domain-separated 编码覆盖 class/arity、定义/typedef、父顺序、约束、basis 和 fact 更新；拟迁移至 `signature/v3`、`theory/v2`、`context/v2`、`theorem/v3`、`extension/v2` 域（统一实际版本由集成确定），旧 digest/token 不能兼容授权。

K 在发布 child **之前**从真实已提交父节点按规范顺序展开联合扩展，同一祖先身份复用、同名不同结构/来源拒绝；同一 `LogicPolicyId` 下实际引入的 approved axiom 集可以各异并作精确联合，policy 不兼容拒绝。`DefinitionSpec` 保存 `(Const|Type,qualified_name,instance_type_args)` lhs/rhs 实例、参数/sort、原 owner、重载实例、restriction pattern 和全部 RHS 项/类型依赖（含注解、Rep/Abs）。认证 lhs 参数包住 RHS 全部自由变量与类型变量，RHS 在父 owner 中认证；核实例类型、严格分离的不可统一重载区域及 `Theory.check_overloading` 的 sort 限制。每次引入和父合并重算联合 `Defs` 归约、模式重叠、coregularity、混合 type→const→type 与 const→const cycle；不能左右 map 覆盖、等事后 `Theory.add_deps` 才检查，`c=¬d` 与 `d=c` 分支合并必须失败。失败不生成半个 child/registry。

`TheoremRef` 查找当前 owner 或可达已提交祖先的封闭 token，核 `(id,name,accepted_in,full_payload,dependencies)`；同 theorem ID 的 sibling/旧 owner、provisional 与候选自引不能通过。接受 A 返回的**新 owner**才可立即引用 A。只有 `accept_closed_theorem` 重放并原子创建 child/token；图身份与 source hash 都不是证明。

## P1 Pure rules and shared bound proof IR

以下是目标契约而非上文窄规则的宣告：`assume/assume_cterm(A)` 要求 A:prop 且 H 不含 Var/TVar，得 `{A}⊢A`；`weaken` 加受检 A 不删除旧负载。`implies_intr(A,p)` 即使 A 未在 H 也生成 `A ==> P`，仅删除匹配的 H；`implies_elim` 精确 alpha/type 匹配并合并。`forall_intr` 在 H/F/开放 scope 中核自由出现后用 de Bruijn 引入，`forall_elim` 有类型匹配和捕获避免；`reflexive/symmetric/transitive`、beta/eta、`abstract_rule/combination`、`equal_intr/equal_elim` 各自重算准确 redex、相等中项、型别/作用域及全量负载，不能以对象层 `=` 代替 Pure `==`。`generalize` 的新 index 严格超过所有已有使用及证明上界，不改 H，不让局部变量逃入 H/C/F；`instantiate` 遵上节有限一次。`solve_constraints` 每个 `(T,S)` 使用已重放 classrel/arity 证据；`of_class` 用下面的独立证明树。调用方构造的最终 record、搜索成功和未知 `Derivation` variant 一律不能作规则。

**唯一私有 core IR**：`Hyp(j)`、`ImpliesIntro/Elim`、`ForallIntro/Elim`、已列 Pure equality/conversion (`EqRefl/Sym/Trans/Cong/Abs/BetaEta`、`EqualIntr/Elim`、受限制的 `EqFlex(j)`)、`AuthorizedLeaf(exact cert/token,local instance)`、`ClosedExportTransport(checked inner root,capture-free instance)`。判断 `Γp;Γt;H;C;S;F;deps;pending ⊢ P @ owner` 中 `Γp` 是有序 proof-binder 假设（最近为 `Hyp(0)`）、`Γt` 是 term/type de Bruijn binder；两者都**不是**真实 H。`Hyp` 核 slot/depth，只在私有 scoped proof 中生成 `H=[]` 的局部命题；`ImpliesIntro` 仅关闭自己的 proof slot，不删除合法 H；`ForallIntro/EqAbs` 在 H/C/F 和所有开放 Γp 声明及 const coverage 中检查 freshness，跨 binder 对旧声明 lift 索引。开放 Γp/Γt 或 `EqFlex` 不得物化普通 theorem、外传或 seal。只有逐 slot/term binder 关闭并核完整负载，才可成为普通 theorem。

非 TCB 生成器按**源操作顺序**先用原 typed identity 验证每个 source `H/C/S/F/P/owner/deps/pending`、有限一次 type→term 替换和 proof/term binder index，再生成有限 bound DAG；K 对每个节点重算，不靠结论相等。source `Generalize` 不能把替换向下穿透到 `Assume` 再产生 schematic H；非单射 type map 也不能在 term substitution 或 `ForallIntro` 后按合并的新名字重跑捕获。源 H 中若需临时 schematic，先 scope-private rigidify，明确 discharge 后才于受检闭合边界恢复 schema。无可分解节点时返回 `UnsupportedSortExportVariant`，不引入泛化 `Resolve`/“proof valid”节点。

### P1 Composition lowering

所有 `bicompose`、`lift_rule`、`assumption/eq_assumption`、`rotate_rule`、`permute_prems` 共用上述 IR。选 state 外层第 `i` 个 premise（`1≤i≤n`）时分为 `Bs,Bi,C`；rule 剥准确 `m` 个前提 `As`，未剥 remainder B **完整保留**，不能把 Bi 内部的 `!!`/`==>` 算成外层 Bs。ordinary resolution 由 `Intro(Bs@As)`、受检 rule 消 As、等式 DAG 将 B 接 Bi、消 state、逆序关 binder，输出 `Bs @ As ==> C`；后续旧 state tail 留在 C。lift 先以 `state.maxidx+1` freshen rule index，沿 Bi 的 interleaved implication/forall **结论脊柱**提升 As/B 和旧 F；`flatten=true` 才重排剩余参数并用 binder adapter 证明原 lifted premises。eres `m≥1`，从 A1 的第 j 个已证明 assumption 导出 A1，仅删**剩余前提**原链中的所选第 j 项；`flatten=false` 剩余 As 原样，不能删其内部条件。

`incremented=false` 须先统一同名 schematic Var 的类型；`match=true` 不得赋值给 state 任意 Var/TVar 或改变 state 的 P/H/C/S/F/scope 投影。非 TCB unifier 提供有限无环环境与 ordered residual U；K 对 `BBi :: rule.F @ state.F` 中每对旧/新等式构造精确 Eq DAG，`EqFlex(j)` **仅**引用输出 `F=norm(U)` 的第 j 对同型开放等式，不能把 flex pair 当真；只有实际证明消去才能减少旧 F，F 非空永不得 close。输出 H/C/S/deps/pending 全量联合，fresh index、scope、owner join、`maxidx` 上界及顺序均重查。`assumption` 可给残余 F，`eq_assumption` 仅第一 alpha/η 相等项、空 env 且保持旧负载；rotate 的目标仍在 `Bs` 后、旧 tail 保留，负数 k 按 `n+k` 计算；permute 固定前 j 项，尾 `V` 旋转 `m=k<0 ? |V|+k : k`，结果 `fixed @ V[m..] @ V[..m]`，不按多重集合比较。公开 `permute_prems` 的 `List.drop` 可先抛 `General.Subscript`，宿主不得把所有非法索引统变 THM 或空 Seq。搜索的 lazy Seq 和异常由 [TRUST.md 的 THM 合同](../status/TRUST.md#p1-native-trust-design) 保持；K 只接受逐节点推导。

具体 source 顺序不能省略：`lift_rule` 使用 `cprem_of(state,i)` 原 `maxidx`（即使最大索引未出现）、`inc=maxidx+1`，先把 rule Var/TVar index 上移；Bi 结论脊柱的 `H ==> rest` 插同一 H，`!!x.rest` 插同一 binder，并将 lifted schematic Var 在各 Bound 上应用，F pair 只经 forall 抽象。`lifted=true` 的 `strip_assums2(B,Bi)` 生成核心 DP；`flatten=true` 对剩余 A' 按源参数出现次序外提参数，eres 在每个剩余前提的**原 implication 链**删所选第 j 项，其适配证明先引入被删的旧前提并忽略那个 Hyp，再用新目标的其余 proof/term bounds 逐层消去。eres 的 `Logic.assum_problems(nlift+1,A1)` 先剥 A1 最外 forall，再至多取 `nlift+1` 个前提，依顺序尝试 `j=1..k` 的 `(close(h_j),close(concl)) :: BBi :: rule.F @ state.F`；`k=0` 无候选。`flatten=false` 只删已由 A1 证明的**整个 A1**，其他 A2..Am 原形保留；`m=0` 的 eres 非法。`assumption/eq_assumption` 对 Bi 用 `Logic.assum_problems(~1,Bi)` 收全体前提，前者按 j 搜索与旧 F 联合，后者只取第一 `aeconv`、不改原 F/C/S/H/maxidx。rotate 仅读 Bi 最外 forall 后连续 implication，要求 `0≤m≤n`；permute 固定首 j 项要求 `0≤j≤n` 且 `0≤m≤|V|`，不窥探各前提内部 binder。每个 adapter 都要显式 `ForallIntro/Elim`、`ImpliesIntro/Elim` 与 de Bruijn shift，不能仅凭字符串相同。

`Envir.norm_type/norm_term` 是递归归约并可能 β 收缩，不等于普通 `Thm.instantiate` 一次替换；合一候选的 tyenv/tenv 必须单一、无递归 assignment 环、有限、型别/sort/scope 受检，先按源 typed keys 正规化两个**完整证明 DAG**，再 rigidify/materialize（绝不修改真实 H）。对输入的每对旧 F，K 检查它在 env 后从新 residual F 的 `EqFlex` 或具体反身/conversion/equality DAG 可证；被跳过的 lifted 前缀也要逐层 EqAbs/EqCong 证明，不能因为核心 B/Bi 看起来可统一就忽略它们。`match=true` 连较低索引同名 state assignment 也拒绝；rename_bvars 只能全 DAG 同身份捕获避免改名，不能仅重命名 As。完整输出 `F=norm(U)`，`H=union(rule.H,state.H)`、`C=union(C)+env 的受检约束`、`S=Envir.insert_sorts(env,union(S))`，`deps` 包含所有 Eq/class/leaf 的证据，`pending` 取兼容并集；输入声明的 freshness 上界及全 payload 均由 K 复查。

### Composition replay maintenance exceptions (2026-10-19)

本轮质量修复显式保留以下超过 60 行的现有函数作为受审阅例外。行数从
多行签名首行计至结束括号，不含外部注释。它们集中呈现一次构造或回放的
源数据、推导和最终 payload；本轮不为行数引入可复用的半验证中间结果。
这不是通用长度豁免，也不减少攻击测试或 exact-owner replay 要求。

路径均相对于 `crates/kernel/src/bound_proof/`：

|文件 / 函数|行数|保留完整流程的具体理由|
|---|---:|---|
|`composition.rs::build_exact_resolution`|77|同一前提排列决定输出命题、binder depth、假设 offset 和最终 introduction；集中核对这些索引的对应关系。|
|`composition.rs::replay_exact_resolution`|90|residual 认证、canonical proof 对比、闭合证明检查、两源 F 负担与 sort 检查全部先于唯一输出 theorem 构造出口。|
|`composition.rs::bicompose_candidate`|79|源 premise/assumption 上限必须在候选正规化与实例化之前保存；完整源回放和最终 resolution 回放夹住该有序流程。|
|`composition_assumption.rs::replay_assumption`|90|记录的源 assumption 上限、canonical proof、完整结论与旧 F/sort 负担一起约束同一输出，不能单凭结论匹配构造结果。|
|`composition_assumption.rs::assumption_candidate`|76|先记录原目标的 assumption 数，再在正规化前后校验赋值成员；不能用实例化后新增的 premise 扩大可选范围。|
|`composition_index.rs::replay_index_rename`|75|统一处理源变量、命题、F 和 proof-only 索引，同时拒绝改变 H，再以完整 proof 与 sort 检查约束 payload。|
|`composition_lift.rs::replay_lift_rule`|66|goal 与 lifted F 认证、canonical proof 对比、完整命题和 sort 检查必须全部完成后才构造 lifted theorem。|
|`source_instantiate.rs::replay_source_instantiation`|75|按源顺序变换完整证明与 F，保留 H；正规化证明、完整命题与 payload sort 检查集中在同一回放边界。|

## P1 C4 sort proof, strip and export

`ClosedOfClassProof(T,c)` 按 goal 驱动：`AnnotatedAtomLeaf` 仅用 TFree/TVar 自身 sort 明列的 class；`ExportPremiseLeaf` 仅在同一 `SortScoped(plan,scope)` 的 `Γp` 中取准确 `Hyp(slot)`，真实 H 永远为空；`ClassWeaken` 引用非反身 classrel 的 exact proof；`TypeConstructor` 引用可达已重放 `ArityCert` 并按其 `premise_slots` 逐 class 检查参数；`SemanticArity` 仅从下述四类完整模型证书构造首次证明，不读待安装候选 arity。scoped H=[]、`Gamma_used` 为 Hyp 与 const coverage 实际使用 slot 的并集，未关闭不能物化普通 theorem。独立公开 `of_class` 只接受 closed judgment、H/C/F=[]，并保留 T 的真实 present shyps。候选 classrel/arity 在**尚未安装候选**的 parent owner 完成证明变换与 exact shape 检查，然后才原子入图；复合 classrel/arity 也要 replay proof，不能只有图边。

`strip_shyps(K)` 先完整 replay K 并完成 promise，拒绝 oracle/skip；扫描 F 两侧、P、H 的 atomic types，按 `Term_Ord.typ_ord` 排序；`present=[(A,sort(A))]`，`extra=S−{sort(A)}` 按 sort **精确相等**计算。witness 按 present/solved 先选满足 `S1≤target` 的第一个，再按 signature 稳定 logical tycon 顺序与 `mg_domain` 递归找 ground witness（`[]` 用 `prop`，有路径上 stronger-sort 终止保护）。不能 witness 的每个原 S2 得 `(S1=minimize(S2),S2)`；`extra'` 仅保留无严格更强代表的 S1。从 extra' 取首个 `S0≤S1`，分别证明 `rel(S0,S1)`、`rel(S1,S2)`，相等段为空；proof-only `ProofOnlyWitness` 只能以 extra' 的代表进入替换候选 `present ++ witnessed ++ dummy(extra')`，不能把每个原 extra 的 dummy 也放入。每个原约束与新增 `(T,S)` 均用完整 classrel/arity proof discharge。先按源次序生成 binder/一次替换，后仅在已绑定 core 内将**不在 present** 的 proof-only atom 映为候选中首个 `S'≤S` 类型；源 P/H/F 不变。materialized H 使用新私有 rigid identity，待 H 无待恢复 rigid 且 C=[] 后 `CloseStripSchema` 恢复原 schema；F 保留，不可借 strip 消失。输出 `S'=sorts(present)∪extra'`、重算负载与依赖，没有 witness/转换证据则拒绝。

`unconstrainT` 必须先 strip，源 H=C=F=[]、P 无 TFree、完整 derivation/owner 已 replay。`O_export` **是 strip 后 source 的真实受检 owner**：普通 classrel/arity 使用尚无候选的 committed parent；conditional/staged 只可用同 tx provisional lineage，保持 `pending={tx}`，不能 seal/供 parent witness；提交后才在新 owner 用最终 cert 重放。P 的每个 distinct present atom 按 `typ_ord` 映射到互异私有 `κ_i::[]`，extra sort 按 `sort_ord` 分配其余 κ；即便 present 同 sort 也不可合并。输出 `constraint_map=present ++ extra`，每项按其原 sort class 次序生成 `OFCLASS(κ_i,c)`；仅 proof-only atom 可按**exact source sort**选第一映射，不能按 subsort 近似。源 core binding/leaf local instance 完成后才 materialize κ；每个局部 OFCLASS 经同一 Γp 的 `ClosedOfClassProof` 用 `ImpliesElim` 按 slot 顺序消去（相同命题也逐 slot 消费）。所有 Γp slot 包括未使用的，按逆序逐个 `ImpliesIntro` 关闭并保存确切 discharged binder path。仅 Γp 全闭、H=C=F=[]、无私有 identity 逃逸时 `CloseSortScope` 将 κ **仅在已检最终 P 中**同时替成 canonical index-0 空-sort TVar；不在内层证明物化 schematic H，不假冒普通 `generalize(idx)`。普通输出 `P=OFCLASS* ==> erase(P0)`、`S={[]}`、`mode=SortErased(plan)`、pending 空；staged 保留准确 singleton tx；全量 deps、owner、maxidx 重新算。

对每个映射后的 const occurrence，私有 `certify_sort_erased_use` 保存 `(source path,decl_id,source sorted instance,erased instance,exact class evidence,coverage binder)`；K 从 scheme 重配所有所需 class 证明，连 `reflexive`/conversion 内常量也不豁免。新 occurrence 在当前 Γp 要证明，已闭合 nested `SortErased` 则通过 `ClosedExportTransport` 完整检查 inner const path、证据和**已 discharge 的 inner binder**，把其前提作为外层命题 binder 传输，不能要求外层 Γp 无条件证明，也不能把内层已消前提当外层 H。每个 `AuthorizedLeaf` 用**同一**已接受完整原证书、source sorted schema 与精确 leaf-local type→term instance 计算唯一 `LeafExportView`；依 source derivation variant/term 先序 path 记录每一 occurrence，不按名字去重。先得到私有 `ExportHead(OFCLASS* ==> Q)`，按局部 class slots 逐项 `ImpliesElim` 才成为 `SortScoped`；不可把 head 直接 seal。叶分别覆盖 approved axiom、保守定义、同 tx conditional typedef、提交后 typedef、可达 token、class proof 和四类模型 arity；oracle/仅 hash/名称无 view。C2 wrapper 的 `build_rev(Term.add_tfrees prop)` OFCLASS slots 与 C4 present-atom export slots **分阶段分别核对**，不能复用一份位置表。

四个语义 arity 根仅为 `FunctionTypeArityCert`（`fun` 的非空函数空间，两个 `type` 参数）、`ItselfArityCert`（单元素标签，一个 `type` 参数）、`FreshNonemptyTyconCert`（fresh tycon 元数 n、每参数 `type` 的非空模型）、`TypedefArityProjection`（完整最终 typedef 证书）。各自从完整声明/模型/owner/参数 class 证据生成**唯一** sorted schema 和 export view，物理 OFCLASS 次序按 present atoms，语义 `arg_sorts` 按 tycon 参数索引并存对应 slots。首次 fun/itself/base-sort leaf 不读取待安装 ArityCert，随后 replay 完成才能登记；staged 叶在同 tx 传播 `PENDING(tx)`，最终重新投影 TypedefCert，绝非第十四条公理。

## P1 C2 conservative definitions and staged typedef

`ConstDefCert` 精确编码声明 scheme/实例、合法 lhs 参数、parent owner、已认证 RHS 完整 tree/依赖实例、sort、overload/restriction、生成的 Pure.eq；定义实例引入前即检查 fresh/交叠、自引用、归约循环和参数闭合，每次 DAG merge 复检。`ClassDeclCert` 的定义型 class 从保守定义和已审规则推得 `OFCLASS`，`ClassRelCert/ArityCert` 含准确目标、已 replay 证明、owner 与参数 class slots；`axclass` 的任意 axiomatization 是新增公理申请而非自动批准。

`HOL.type` 基础 class 无 superclass/操作/局部公理，意思仅为已授权 object-type carrier 非空。条件 typedef 的 `Q(A)=∃x::oldT. x∈A`、`TD=Trueprop(type_definition Rep Abs A)`；K 必须核真实 parent 可达的 `Typedef.type_definition` 保守定义 RHS，逐节点核 `Rep x∈A`、`Abs(Rep x)=x`、`y∈A ⟹ Rep(Abs y)=y` 及 connective/binder/type，不认名字/哈希。对每个满足参数 sorts 的赋值 ρ：若 Qρ 真，carrier 取 Aρ、Rep 为包含、Abs 在 Aρ 上为恒等、其余映入所选 a0；若 Qρ 假，任取非空 carrier 并解释 Rep/Abs，条件式为真。后者**不能**反推出 Q 假或发布无条件 TD；只有父 owner replay 精确 Q witness 才能 commit。

`Sign.add_type(binding,n,mixfix)` 起始只保留 fresh tycon、arity n、provisional lineage 的 reservation，**不臆造 type parameter/sort**；Rep/Abs 等声明进入不可变 ledger。原样 `more_thm.ML` 向 `Theory.add_axiom` 提供的是 `OFCLASS* ==> stripped(Q ==> TD)`：解析前导 slots 与 active reservation、Rep/Abs type shape、parent-language A/Q、locale predicate；形成 `RawConditionalCandidate(tx)`，并不按 binding/file/caller 授权。按原样 `cert_axm/varify_global` 后，通过真实 `Thm.instantiate` 的精确双射 recover map（仅 stored TVars、对应原 TVars/sorts，一次替换）及 `unvarify_global/of_sorts` 逐项消**全部且仅有** wrapper OFCLASS，保留 Q；与 recovered Rep/Abs、新型参数位置及 A/oldT 逐节点一致，才形成 `PendingTypedef(tx)` 并取得有序参数身份/sort。原始 `source_dep_calls` 必须核三次官方 `Theory.add_deps`：`type_dep(newT) -> A_consts @ A_types`（官方 fold 遍历、头插去重次序）、`const_dep(Rep) -> [type_dep(newT)]`、`const_dep(Abs) -> [type_dep(newT)]`；不要求原始 Rep/Abs 调用带独立 oldT 边。K **另**从 A/oldT/Q、Rep/Abs 声明及受检 instances 构造完整语义依赖图，补齐 newT→A/oldT/Q、Rep/Abs→newT+oldT 的边，并在初始与每次合并核归约、restrictions、重载分离/混合循环；从 Defs 算 `has_open_dependencies`，不猜不可见 caller `overloaded`。三次调用只是与预检图核对，不可迟到后补授权。

条件规则只产生 `PENDING(tx) ⊢ Q ==> TD`，staged base arity 同 tx 可见且 taint 传播。parent witness 证明精确 Q 必须在**事务前已提交父语言**独立 replay，不用 newT/Rep/Abs/staged arity、pending、额外局部参数或未解 C/F；由原样 `inhabited RS typedef` 的完整 core DAG 消去唯一 Q 才到 `CommitReady`，pending 必须**恰为 `{tx}`**。`RS` 不创建新 owner。Context 的新 `Theory_Data.put` 输入可沿不可变 tuple/list/datatype/已完成 `Lazy.Value` 中的真实 theorem 引用交 K，核 ledger、conditional root、witness、依赖图/arity 后原子生成**新** owner/context；不强制 lazy、不读 ref/closure/别的 context 或凭 metadata 授权。旧 aliases 不变；旧 pending proof 仅显式 transfer 到新 owner 后逐节点使用最终 TypedefCert 重放，才能清 taint，closed theorem 仍经唯一 acceptance。普通 `typedecl` 在 `Theory.end_theory` 需精确空 RHS marker 与 fresh 非空模型才可提交；`bool/ind/set` 是指定 basis 声明序列，不能误落普通分支。十二个真实 typedef 的 parent A/Q、阶段及 witness 源级对应和 13+2+17 项授权类别见 [TRUST.md 的 P1 基础政策](../status/TRUST.md#p1-holbasisv1-policy)；每项 Rust 实际 witness replay 尚待验证。
