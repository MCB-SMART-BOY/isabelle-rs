# 信任模型 (Trust Model) — Isabelle-rs

> **核心承诺:系统永不说谎。** 一个定理要么被真正证明(信任足迹为空),要么诚实地
> 标记它依赖了哪些未经证明的假设(oracle / sorry / admitted)。可信性不等于"证明
> 一切",而等于"对自己证明了什么,绝不撒谎"。

本文件定义 Isabelle-rs 的可信性目标,并**诚实记录**当前达成度。它是项目可信工程的
单一事实来源 (single source of truth)。

---

## 一、为什么需要这份文件

定理证明器的全部价值建立在一个前提上:**它说"证明了 P",P 就真的被证明了。**
如果系统在证不出来时偷偷把 P 当公理接受、却仍报告"已验证",那么它的每一个结论都
不可信。

历史教训(本项目自身):v2.1.5 对外宣称 "Tier2 3821/3821 100% verified",但
`verify_lemma` 的最后一行是 `Some(generalize_thm(...))` —— 证明引擎失败时把命题
当公理接受,且**计数时不加区分**。仪表化测量后,真实证明率是 **85.8%**,有 14.2%
(544 条)是 admitted 而非 proved。这正是本信任模型要从根上杜绝的失信模式。

---

## 二、de Bruijn 准则与四条性质

业界对"可信"的黄金标准是 **de Bruijn 准则**:

> 系统产出可被一个**小的、独立的、可审计的检查器**复核的证明对象;于是对整个系统的
> 信任,坍缩为对那一个小检查器的信任。

我们把它拆成 4 条可独立审计的性质。`Thm` 类型必须满足:

| 性质 | 含义 | 达成度 |
|:--:|------|:--:|
| **T1 不可伪造** | 获得 `Thm` 的唯一途径是内核推理规则;无 `pub` 后门、无 `unsafe` 伪造 | ✅ ~98% (后门已收口) |
| **T2 规则可靠** | 15 条内核规则各自正确执行推理,强制全部边条件 | 🟡 部分 (tpairs/shyps+Branch C 已修, A/B 延后) |
| **T3 信任可追溯** | 任何未经证明就接受的东西(oracle/sorry/admitted)记录在 `Thm` 的信任足迹中,并随推导传播 | ✅ **已达成** |
| **T4 可独立复检** | 独立最小检查器能重放证明项、确认定理 | 🔴 ~30% (死代码) |

**完全可信 = T1 ∧ T2 ∧ T3 ∧ T4。** 当前重点:**T3 已落地**,T2 进行中,T4 为北极星。

---

## 三、T3 信任足迹 — 已实现 (v2.2.0)

### 机制

`Thm` 结构体携带一个 oracle 足迹字段:

```rust
pub struct Thm {
    hyps: Hyps,
    prop: CTerm,
    // ...
    /// 此定理最终依赖的"未证明断言"集合 (Isabelle 的 oracles_of)。
    /// 像 hyps 一样,通过每条推理规则做并集传播。
    oracles: Vec<Arc<str>>,
    // ...
}
```

**核心不变式:`thm.is_fully_proved() ⟺ thm.oracles().is_empty()`**

- 真证明 → 足迹为空 → `is_fully_proved() == true`
- admitted/oracle → 足迹含标记(如 `"admitted"`)→ `is_fully_proved() == false`

### 传播规则(与 `hyps` 一致)

| 规则种类 | oracle 传播 |
|------|------|
| 公理类 (`assume`/`reflexive`/`beta_conversion`) | 空 |
| 单前提 (`symmetric`/`abstraction`/`forall_*`/`implies_intr`/`instantiate`) | 克隆前提足迹 |
| 多前提 (`transitive`/`combination`/`implies_elim`/`bicompose*`/`subst_premise`) | `union_oracles(前提1, 前提2)` |
| oracle 入口 (`ThmKernel::admit`) | 注入指定 oracle 名 |

**关键性质:传染性。** 任何用到 admitted 定理的推导,结果也被标记。一个链式证明若
中途依赖了 admitted 引理,最终定理诚实地 `!is_fully_proved()`。

### 唯一的失信入口被收口

`ThmKernel::admit(ct, name)` 是内核**唯一**的"接受命题而不证明"的入口,对应 Isabelle
的 `sorry`/oracle。`verify_lemma` 证明失败时的 fallback(`generalize_thm`)现在全部
路由经此,因此 544 条 admitted 引理由**类型系统**标记,而非靠外部统计脚本。

### 验证

- `src/core/thm.rs` 单元测试:`test_admit_is_not_fully_proved`、
  `test_oracle_footprint_propagates_through_rules`、
  `test_union_of_proved_and_admitted_is_tainted` —— 故意构造"用 admitted 前提走真规则",
  断言结果被污染。
- Tier2 harness 打印 `REAL PROOF RATE`,由 `Thm::is_fully_proved()` 派生,与独立的
  exit-site 仪表交叉验证。

---

## 四、真实证明率(诚实指标)

> **Tier2:97 文件,3821 条引理 —— 3277 真证明 (85.8%),544 admitted (14.2%),178s**

"100% verified" 的旧口径含义是"引擎跑完没崩溃 + 产出了 `Some(Thm)`"。真实的"证明"
口径是 `is_fully_proved()`。两者差 14.2%,即下表的攻坚目标。

### admitted 集中分布(prover 最弱处)

| 文件 | admitted | 真证明 | 性质 |
|------|:--:|:--:|------|
| Rings | 80 | 196 | `algebra_simps`/`field_simps` 密集 |
| Lattices_Big | 63 | 44 | 大算子 SUP/INF/Max/Min |
| Parity | 27 | 140 | even/odd 同余 |
| Complete_Lattices | 25 | 155 | 完备格 Sup/Inf |
| Order_Relation | 23 | 30 | 序关系 |
| Map / Power | 19 / 18 | 120 / 124 | 有限映射 / 幂 |

规律:**代数化简 + 大算子**是两大软肋,根因是 named_theorems 重写集 (`field_simps`
等) 接入不全。缩小 544 = 提升真实证明率。

---

## 五、T1 / T2 / T4 现状与计划

### T1 不可伪造 (~98% — v2.2.0 后门已收口)

✅ `Thm` 字段私有,`PartialEq/Eq` derive,无 `pub` 字段后门。
✅ **假定理后门已收口**:`hol_rules.rs`(11 个连接词 stub)、`hol_consts.rs`(3 个)、
`core/conjunction.rs`(2 个)中那些"产出结论形状却不从前提推导"的函数,过去用
`ThmKernel::assume` 伪装成已证。现已:(1) 全部改用 `ThmKernel::admit(ct, "...:STUB")`,
使结果 `!is_fully_proved()` 且污点传播;(2) 降为 `pub(crate)`,无法泄漏出 crate。
真实推导(`mp`/`all_intr`/`all_elim`/`true_intr` 委托内核)保持 `pub`。
全 src 扫描确认:**无任何 `pub fn` 返回 `assume(结论)` 伪装成已推导的定理**。
机器可检不变式:`test_stubs_are_admitted_not_proved` 等断言 stub 输出带 oracle 标记。

🟡 剩余 ~2%:`assume` 在证明引擎里仍广泛用于**合法**的目标/前提初始化(`P ⊢ P` 正是
待证目标的形态),这是正确的 LCF 惯用法,非伪造。

### T2 规则可靠(进行中 — v2.2.0 部分达成)

内核审计 + kernel-reviewer 复核发现的可靠性缺口,逐条修复 + 回归测试:

| 缺口 | 位置 | 真实性质 | 状态 |
|------|------|------|:--:|
| `tpairs`/`shyps` 被 12 条规则丢弃 | `thm.rs` | **潜在**:当前引擎不产生 flex-flex/sort 约束 (恒空), 故无现行不可靠; 接入完整高阶合一后会咬人 | ✅ **已修** (并集传播, 零行为风险) |
| `combination` 在 `Typ::dummy()` 时跳过类型检查 | `thm.rs:669` | **非 bug**:combination 是 congruence 规则, 对任意类型逻辑可靠; 类型检查只是 well-formedness 守卫, dummy 时无从检查 | ✅ **已澄清+测试** (类型已知时拒绝不匹配) |
| `alpha_eq` Branch C — `Abs` 忽略 binder 类型 | `thm.rs:231` | **潜在真洞**:`λ(x:nat).x ≡ λ(x:bool).x` 一旦 type_annotate 标注 binder 即可被误同一 | ✅ **已修** (binder 类型守卫, dummy 容忍) |
| `alpha_eq` Branch A — `Free≡Const` 后缀匹配 | `thm.rs:219` | **真洞但承重**:弥合 parser (`Free("zero")`) 与 loader (`Const("Groups.zero")`) 表示鸿沟; 直接收紧会击穿算术证明链 | 🔴 **延后 (T2-4)** |
| `alpha_eq` Branch B — `Var≡Free` 忽略 index | `thm.rs:225` | **真洞但承重**:DB 全部 schematic 定理用 `Term::var`, 靠此匹配 parser 的 `Free`; 直接移除会击穿整个证明管线 | 🔴 **延后 (T2-4)** |

**关键认知(kernel-reviewer 复核结论):** Branch A/B 是真实可靠性洞,但**正确的修复在解析边界,不在内核** —— 应在 `CTerm::certify_annotated` / parser 把 `Free("zero")` 解析为 `Const("Groups.zero")`,并把 hol_loader 的 `mk_var` 改为 `Term::free`(对齐已正确的 `nat.induct` 设计),然后才能安全收紧 `alpha_eq`。直接在内核收紧会让 Tier2 真实证明率暴跌。这是 T2-4 的独立工程(数天),不是内核小改。

**v2.2.0 已修:** tpairs/shyps 并集传播 + Branch C binder 类型守卫 + combination 文档化/测试。每项配回归测试(`test_shyps_*`、`test_alpha_eq_*`、`test_combination_*`),core 125/125 不回退。

### T4 可独立复检(北极星,~30%)

`src/core/proofterm.rs` 的 `check_proof` 已存在但**从未在生产路径调用**,且多前提规则
退化为 `PAxm`、接受 `PMin` 占位。目标:补完为 < 500 行的独立检查器,验证后真正调用它
复核;故意篡改一步,checker 能抓出。

---

## 六、可信工程路线:A 先行,B 为北极星

- **(A) 务实可信** = T1 + T2 + T3:系统永不说谎,每个定理可查信任足迹,admitted 显式
  可见。数周内可达。差异化卖点:"Rust 写的、内存安全、诚实的 HOL 核"。
- **(B) 完全可信 (de Bruijn)** = A + T4:独立证明项复检,信任坍缩到一个小检查器,达
  Isabelle/Coq 级别。数月目标。

**当前位置:T3 已达成,A 完成约 2/3。** 下一步 T2 内核加固,然后 T1 收口后门。

---

## 七、如何使用信任足迹

```rust
let thm = verify_lemma(&lemma)?;

if thm.is_fully_proved() {
    // 真证明:Γ ⊢ φ,无任何 oracle 依赖
} else {
    // admitted/oracle:诚实告知依赖了什么
    eprintln!("⚠ depends on: {:?}", thm.oracles());  // 如 ["admitted"]
}
```

**铁律:对外报告能力时,引用 `is_fully_proved()` 派生的真实证明率,绝不引用"已处理 /
verified"计数。**
