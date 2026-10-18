# Kernel-Trusted Acceptance Gaps

## Status

Immutable context identity, declaration-aware certification, an installed
`refl` basis, conservative definitions, and exact-owner acceptance now
support two standalone source fixtures and one audited sampled HOL `TrueI`
projection. The latter is not whole-theory HOL compilation.

这是已实现的窄信任边界，不是原生 Isabelle2025 闭包验收。
P2/P3/P4 已按批准设计恢复实施，局部 Rust THM consumer 已有实际闭环，
但完整 ML THM、ROOT、HOL 和九根兼容仍未验收。下方 `0/125`、`1/125`
是 cutover 前的 bundled sample，不是本轮重跑；当前局部修复、失败及阻塞见
[最新 Rust 变量闭环记录](../status/PROJECT_STATUS.md#rust-thm-type-and-variable-transformations-2026-10-19)
与 [ML/evidence 修复记录](../status/PROJECT_STATUS.md#ml-runtime-and-evidence-semantic-repairs-2026-10-19)。

Read root [AGENTS.md](../../AGENTS.md), then
[PROJECT_STATUS.md](../status/PROJECT_STATUS.md) and [TRUST.md](../status/TRUST.md), before using
this audit as an implementation plan.

Last recorded bundled-source sampled status (not a fresh run):

```text
TransitionalStrictClosed: 0/125
KernelTrustedClosed:      1/125
```

`KernelTrustedClosed` is mutually exclusive and owns a replayed accepted
token. Only the exact source-backed `HOL::TrueI` candidate in the five-file
sample reaches this bucket; other candidates remain legacy/diagnostic.


## Checkpoint (2026-07-21)

Branch `wip/kernel-trusted-slice` merged at `03d28a6` closed two previously
open gaps:

| Gap | Status | Resolution |
| --- | ------ | ---------- |
| Axiom-schema instance trust (derivation trusts stored prop) | **Closed** | `AxiomInstance` replay reconstructs from basis schema; see `AxiomDependencyId` |
| Dual-entry axiom dependency (AxiomBasis + Axiom) | **Closed** | Single atomic `AxiomDependencyId::compute(basis_id, schema_id)` |
| Polymorphic constant instance matching (always-true) | **Closed** | `is_monomorphic_instance_of` with `BTreeMap<TypeVarId,Ty>` + concrete check |

**Closed (2026-07-22):**
- `ConservativeDefinition` is certificate-backed (atomic `DefinitionId` in `TheoryExtension::DefineConst`, replay walks owner ancestry)
- `PolyType::new` validates param sort consistency and requires every declared param appears in the body

**Remaining open gaps:**
- Other sampled HOL lemmas and runtime callers have no source-to-kernel bridge.
- The sampled projection does not execute unrelated HOL/ML commands, verify
  the complete theory, or provide an Isabelle runtime differential.

## Scope

This audit covers the strict path:

```text
RawTerm
  -> immutable Signature + TheorySnapshot + ProofContext
  -> CTerm / CProp
  -> KernelRules
  -> KernelThm
  -> ClosedThm
  -> accept_closed_theorem(owner, name, candidate)
  -> (child TrustedTheory, TrustedTheorem)
  -> ProofOutcome::KernelTrustedClosed
```

It distinguishes the standalone HOL/Pure fixtures from the sampled
`TrueI` source projection and broad source declaration loading.

## Current Certification Boundary

### What `ProofContext::certify_prop` checks

`crates/kernel/src/context.rs::ProofContext::certify_prop` recursively certifies a
`RawTerm` and then calls the private `CProp::new` constructor. The current checks
are:

- every type constructor must be declared with the exact arity; type variables
  have the supported sort and a representable index;
- a `Const` name must exist in the context's `Signature`, with the declared
  monomorphic type or a checked concrete instance of its polymorphic scheme;
- a `Free` name must exist in the `ProofContext`, with exactly the declared
  `Ty`;
- a `Bound` index must be in scope;
- an application head must have an arrow type and its argument type must match
  exactly;
- a `Forall` body must have type `prop`;
- both operands of a Pure equality must have the same type;
- both operands of a Pure implication must have type `prop`;
- the final certified term must have type `prop`.

`crates/kernel/src/typ.rs::Ty` has no dummy constructor, and the reserved
concrete type name `dummy` is rejected. `CProp` fields and constructors remain
private to the standalone kernel crate, re-exported by `src/kernel`.

The attack tests in `tests/kernel_rewrite_soundness.rs` therefore establish the
following type-level boundary:

```text
b : bool                         -> rejected as CProp
HOL.True : bool                  -> rejected as CProp
HOL.eq a b : bool                -> rejected as CProp
HOL.Trueprop HOL.True : prop     -> accepted after local declaration
```

This is a real `CProp : prop` defense. The immutable-identity foundation now
also establishes:

- a deterministic, domain-separated `SignatureId` v4 over checked type,
  class/arity and constant declarations; current identity encodings live in
  [`identity.rs`](../../crates/kernel/src/identity.rs) and the accepted theorem
  domain in [`theory.rs`](../../crates/kernel/src/theory.rs);
- an ancestry-sensitive `TheoryId` v4 over ordered checked parents, extension
  and resulting signature;
- immutable signature/theory extension with checked conflict rejection;
- a `ContextStamp` with theory, signature, optional logic basis and kernel-issued
  local type scope on certified objects and theorem values;
- exact-stamp propagation through current rule construction and owner replay,
  with incompatible contexts rejected before logical matching.

### What certification does not check

Certification alone does not authorize an object-logic basis or prove a source
theorem. `LogicBasisId`, checked axiom schemas, definition certificates, and
typed scheme instantiation now exist; their authorization is enforced by
installation and owner replay, not by the diagnostic source AST.

`LogicBasis::validate_against` validates every complete schema before
installation using the same signature. Its private schema mode permits
consistent type-variable substitutions. Public instantiation of polymorphic
constant schemes requires concrete types; ordinary constant instances must
exactly match their declared type, which may contain validated type variables.
Judgment declarations separately require concrete types. Definitions require
a closed, monomorphic RHS in every annotation, including annotations hidden
below binders. Entry and replay share the same certificate validator.

Accepted dependencies identify installed axiom/definition certificates and
logical IDs of ancestor theorems after exact-token authorization. Descendants
cannot retroactively authorize an ancestor declaration or replace its payload.

`RawTerm::Var` is checked for valid type annotations but is not resolved against
a general schematic-variable/sort context. A concrete name such as
`Ty::base("'a")` is not a type variable and still requires a type declaration.

`Signature::extend_const` returns a fresh immutable signature and rejects both
identical and conflicting duplicates. `Signature::from_untrusted_snapshot`
recomputes the canonical digest and rejects a claimed-ID mismatch. This fixes
identity drift for the declarations the strict signature currently represents;
it does not make an ad hoc locally declared `HOL.Trueprop` an authorized HOL
judgment.

The `declared_trueprop_wraps_hol_true_as_cprop` regression still manually
installs `HOL.Trueprop : bool => prop`. It proves the type and context gates,
not production HOL declaration loading or logic-basis provenance.

## Current Theorem Acceptance

### Unique gate and token

`KernelThm` stores an exact `ContextStamp`, real hypotheses, a `CProp`
conclusion, replayable `Derivation`, and a private complete `ProofPayload`.
`KernelThm::try_close` rejects local type scope, nonempty hypotheses, invalid
index bounds, unresolved sort constraints/flex pairs/pending transactions and
extra sort hypotheses. It does not itself create a trusted value.

`TrustedTheorem` is now a private `Arc`-backed seal containing:

```text
TheoremId
fact name
ClosedThm
replay-derived DependencySet
proved-in TheoryId
accepted-in TheoryId
```

No public constructor, deserializer, raw-part assembler, or
`ClosedThm::trust` operation can create it. The only production constructor is
`accept_closed_theorem`.

### Immutable owner and fact ancestry

`TrustedTheory` has immutable `Arc`-backed checked owner ancestry, including
ordered canonical multi-parent merges. Each owner node records its exact
`TheorySnapshot`, actual parents and at most one local accepted fact.
`begin_child`, checked extension, merge, and accepted-fact insertion
return new values; existing parents and siblings remain unchanged.

Before acceptance, the owner DAG and joint declarations/dependencies are
rechecked against the committed snapshots. A stored theorem must match its
`StoreTheorem { name, theorem_id }` extension, proof context, dependencies
and `accepted_in` child ID. Lookup searches authorized ancestry and duplicate
names are rejected rather than replaced.

### Acceptance checks and ordering

`accept_closed_theorem(&TrustedTheory, name, ClosedThm)` performs:

1. exact candidate `TheoryId` / `SignatureId` comparison;
2. immutable owner-chain consistency validation;
3. duplicate-name rejection;
4. owner-parameterized recursive replay and recertification;
5. exact replayed context, hypotheses, and conclusion comparison;
6. closedness validation on the replayed result;
7. dependency resolution against owner ancestry;
8. canonical theorem-ID computation and atomic child/token construction.

The function returns `(child_theory, accepted_token)`. This tuple is necessary:
the fact name and theorem ID are part of the immutable child `TheoryId`.

### Logical identity versus token authority

`TheoremId` and `DependencySet` are canonical logical identity data.
`DependencySet` intentionally stores a referenced theorem's `TheoremId`, not
its `accepted_in` child. This does not collapse authorization:

- `KernelRules::theorem_ref` requires the exact sealed token's `id`, fact
  `name`, and `accepted_in` value in the supplied owner ancestry;
- accepting replay repeats that exact-token check before inserting the logical
  dependency ID;
- equal theorem content accepted under different names may share a
  `TheoremId`, but the tokens are not interchangeable across sibling branches;
- a dependent theorem ID includes its own exact `ContextStamp`, so proofs built
  in distinct sibling branches remain distinct.

The digest-only `TrustedTheory::resolves` check is post-replay consistency, not
proof authority. A future persistence format must serialize and revalidate
accepted-token provenance; it must never reconstruct authority from a
`DependencySet` alone.

Unlike the legacy `src/core::Thm`, strict `KernelThm` has a private
`ProofPayload` retaining sort hypotheses, sort obligations, flex pairs,
pending transactions and proof mode; closure/replay checks rather than
silently discards them. It has no implicit legacy admit/oracle route.
There is still no production legacy-to-kernel conversion proving all legacy
burdens discharged. A future adapter must check rather than erase them.

## Replay Inventory

`check_kernel_thm` remains a structural diagnostic only. Trusted acceptance
uses `replay_closed_theorem_in(owner, candidate)`, constructs a fresh
`ProofContext` from the supplied immutable owner, and recursively validates:

- every theorem conclusion and hypothesis;
- every `CProp` and `CTerm` derivation payload;
- every substitution replacement;
- cached application, abstraction, equality, and bound-variable types;
- every nested theorem before applying its logical rule.

This rejects same-stamp payloads created under a larger local-free map,
malformed cached checked terms, stale contexts, and mixed siblings.
The following historical narrow inventory predates the later native Rust
THM variable/scope and bound-proof extensions. It is **not** an exhaustive
list of today's [`Derivation`](../../crates/kernel/src/derivation.rs) variants:
```text
TheoremRef
Assume
Reflexive
Symmetric
Transitive
BetaConversion
ForallIntr
ForallElim
ImpliesIntr
ImpliesElim
Combination
Abstraction
EqualIntr
EqualElim
SubstPremise
Generalize
Instantiate
Resolve1Match
AxiomInstance
ConservativeDefinition
```

The conservative `bicompose` wrapper recorded `Resolve1Match` at that
checkpoint. Current source also contains `ExportScope`, transfer, index,
class/sort and bound-proof composition derivations; accepting replay handles
the actual variants in [`invariant/`](../../crates/kernel/src/invariant/).
Unsupported or mismatched derivations fail closed. A derivation record alone
is never an accepted token.

`TheoremRef` accepts only a non-forgeable token installed in the current
trusted ancestry, recertifies its proposition into the descendant context, and
adds its `TheoremId` to the replay-derived dependency set. Search facts carry
no proof object and cannot manufacture this derivation.

Replay validates conservative definitions via `DefinitionCertificate` in owner
ancestry and axiom instances against their installed basis. The bounded
standalone/sampled `TrueI` path uses only `refl`; this is not a statement that
the separately approved `HOLBasisV1` policy has only one slot, nor that a
general Isabelle/HOL bootstrap is implemented.

## Bypass Audit

### Boundaries that are closed

- `CProp`, `CTerm`, `KernelThm`, `OpenThm`, and `ClosedThm` constructors remain
  private to `crates/kernel`; `src/kernel/mod.rs` only re-exports its API.
- `TrustedTheorem` has one private seal operation, called only after accepting
  replay; its private `Arc` state has no deserializer or public parts API.
- `TrustedTheory` has no public mutation or unchecked theorem insertion.
- `SearchFact::Kernel` retains only a proposition; proof extraction and
  conversion to `TrustedTheorem` are absent.
- `ProofObligation`, parser values, legacy `core::Thm`, compatibility results,
  admissions, and oracles have no conversion into the accepted token.
- The accepted classifier takes a real `TrustedTheorem`; it does not accept a
  Boolean, enum tag, theorem name, or caller-provided digest.

### Remaining authorization boundary

An upper layer may construct a content-addressed synthetic Pure root, declare
monomorphic constants, derive Pure tautologies, and submit them to acceptance.
The returned token is valid only for that exact content-addressed theory. It
does not claim that the root is the authorized Isabelle/Pure or HOL bootstrap,
and it cannot prove an arbitrary declared proposition without an axiom or
assumption.

Public source-shape metadata remains only a transitional rejection gate. It
establishes neither name resolution nor trusted provenance and cannot authorize
`KernelTrustedClosed`.

## Remaining Minimal Components

The strict signature now validates type constructors/arity, supported sorts and
type-variable indices; installation validates every complete axiom schema under
that signature. Axiom instances and conservative monomorphic definitions carry
replay-checked dependencies. The bounded source parser/elaborator and minimal
HOL `refl` basis produce accepted tokens for standalone `TrustedTrueI.thy` and
`TrustedPureIdentity.thy` (`!!P::prop. PROP P ==> PROP P`, `by assumption`).

The **sampled** HOL verifier now accepts only `HOL::TrueI` through an audited
projection of the bundled source: it checks the exact required declaration
shapes, binding/scope, source `True` RHS, and complete proof before replaying
under its immutable owner. Other source commands (including ML) are not
executed or included in that owner. Broader HOL declarations and proof
methods, whole-theory compilation, and a Rust-to-official structured
differential remain open. The official-only reference baseline below does not
close these gaps. Neither standalone fixture contributes to the sampled
`KernelTrustedClosed: 1/125` count.

None of the remaining work may be replaced by theorem names, source-shape
metadata, executable HOL validators, or caller-provided identity strings.

### P1 Design and Implementation Gap

固定 Isabelle2025 `765fb2460a57eb46e8490283241ad46f1fac857f` 的九根/完整依赖闭包已有 [2026-10-12 官方 reference 记录](../status/PROJECT_STATUS.md#isabelle2025-reference-observations-2026-10-12) 与 [reference-only snapshot](../../tests/fixtures/isabelle2025/closure.json)；它们不是 native loader、逻辑公理清单或 Rust proof。P1 C1–C7 已报告的设计 Major/Blocker 经独立定向复审收敛，C4 最后 `O_export`、Γp evidence、四种 `SemanticArity` 的 `SortCoreRevisionReview` / `SortCoreAuthorityReview` 和 composition no-flatten/`General.Subscript` 的 `CompositionRuleReview` / `CompositionTrustReview` 仅在明确审查范围内 **APPROVED**。这仍不是九根闭包验收。当前 Rust 内核已分段实现 payload、ordered parent merge、owner replay、部分 class/sort、composition 与变量变换，并完成两个外部 Rust consumer 的局部闭环；逐项能力以 [THM 清单](../status/NATIVE_THM_INTERFACE_INVENTORY.md) 和 [2026-10-19 交付记录](../status/PROJECT_STATUS.md#rust-thm-type-and-variable-transformations-2026-10-19) 为准。不能将局部结果倒填为 2026-10-12 设计审查时的运行证据，亦不得用 P0 官方探针代替新增证据。

P1 的已审可实施合同分别持久化为 [type/sort、完整负载、DAG、规则、C4 sort/组合、C2 typedef](KERNEL_PRIMITIVES.md#p1-native-closure-kernel-contract-design) 与 [13 条 `HOLBasisV1`、THM/Context/权限/运行屏障/solver](../status/TRUST.md#p1-native-trust-design)。目标是原样执行官方输入而只用 Rust kernel `accept_closed_theorem` 作 theorem seal；官方堆、源码名称/hash、proof hash、ML 句柄、solver 返回均不授信。尚未实现的具体 Pure rule 无法在已审 core IR 逐节点展开，或新效果/公理必须引入时，应报告精确源码、负载差异和最小反例，审查批准前阻断，不加 fallback、假返回值、按目标名特判或缩根。P1 设计已批准，P2–P5 实施及独立审查分段取证；完整闭包仍须整合验证。

#### Native closure differential schema (diagnostic only)

`NativeClosureReport` 目标顶层结构为 `schema_version=1, purpose=native_closure_diagnostics, source_commit, source_files:[{path,sha256}], requested_roots, theories, execution, effects, result`。报告只描述活 runtime 中真实 replay 并持有的 token，compare 工具**不能反序列化或返回 `TrustedTheorem`**。每个 theory 保留限定名、源 hash、source imports、按 `Context.make_parents` 的规范父序、带类别的完整声明、fact groups 及**各组有序成员**。声明记录 tycon/arity、class/superclass/classrel、常量 scheme、definition/typedef/instance 证书类别及规范 goal；成员 key `(theory, fact_group_name, member_index)`，保存来源 owner、完整 P/H/shyps/tpairs/未解 C、oracle/skip、Rust 授权类别与可追溯依赖，别名/shadow 是名字语义不覆盖 token。只对齐总数不算比对。

结构化外部项/type 只允许 `Type{name,args}`、`TFree{name,sort}`、`TVar{name,index,sort}`、`Const{name,type}`、`Free{name,type}`、`Var{name,index,type}`、`Bound{index}`、`Abs{binder_type,body}`、`App{function,argument}`；完整 tag 和字段、声明 arity、非负 index、Bound 作用域、同 identity sort、qualified class/const/tycon 和固定参数 scope 必须验证，无 dummy/未标类型的捷径。保留原 sort 集合，另报告用同一有证据 class 图得出的规范集合；不能靠 pretty/Debug/hash 比公式。Abs 展示名可忽略；Var/TVar 仅在**同一 theorem 的全部 P/H/F/C 间**作 kind-preserving、一致双射的 alpha rename，Free/TFree 名与 scope 保留（除非有明确受检 schema export）；构造子/常量/class 限定名不改。先构造结构命题/类型的统一双射，再以同一映射核 H/F 集合及 C，歧义作有限显式匹配，不能分别正规化各字段。shyps 同时保留原值与有 witness 的规范结果；只有确切证据才消 extra。

每项参考字段采用 `Available(value,evidence,completeness)` 或 `Unavailable(reason[,evidence])`，**缺失不能填 `[]`、false、0 或从相似字段臆测**。现有 reference-v1 的官方 `owner` 是 `Thm.transfer` 后 `observed_in`；`declaration_origin` 与 Rust `accepted_in` 是另外两个字段，前者未知即 Unavailable，后者只能来自活 accepted token。P0 仅观测静态命名事实的 P/H/shyps/F 与传递 oracle footprint；内部 constraints/未解 sort obligations 未导出；`Thm_Deps.thm_deps` 在命名节点止步，不能推出完整公理/保守扩展依赖。当前 reference adapter 对 `full_axiom_extension_dependencies`、`unresolved_sort_obligations`、未知的 `declaration_origin`、匿名中间事实和动态 ML 求值标记 `Unavailable`。不把 18,895 个静态命名记录（其中 16,490 含 shyps）误称完整匿名闭包；缺受检观察器之前最终完整差分门是 `BlockedPrerequisite`，局部 P/H 匹配不是 Pass。

官方 `official_storage_kind` 和 Rust `rust_authorization_kind` 分列：13 个 approved logic slot、2 个显式 object arity、17 个 base-sort arity、12 个 conditional typedef、1,267 个 definition-associated 和 7 个 Pure equality mirror **逐项**按结构命题、type/sort、owner、证书映射，不按前缀/计数授权；两边 proof DAG 允许不同，但 Rust 终点依赖必须完整、只含精确批准的初始基础、已检扩展和可达 accepted facts。官方全局 fallback namespace 不是各理论的历史执行态，注册效果须按具体时点执行额外同版程序；`type_text` 也无法证明 opaque/generative identity。

#### P1 acceptance routing

1. **来源与完整执行**：绑定固定 commit/真实源文件、九根及所有 imports（P0 观察到 67 imports 节点/66 个实际目标理论，仅供 reference）、每理论命令和 ML 源加载；未识别、跳过、异常、超时、缺 end、未排空任务均 fail/blocked，不以官方成功或单个 `TrueI` 顶替。
2. **授权/闭合**：在每个声明、父 DAG 合并、rule leaf 与 `TheoremRef` 核确切 owner、HOLBasisV1、联合 type/const 依赖、C4 class 证据及 C2 parent witness，H/C/F/extra shyps、oracle/skip/future/pending 不得流入 closed theorem。每一 accepted 事实必须在准确已提交 proof owner 上完整 replay，再由唯一 acceptance 原子生成新 owner/token；查 13+2+17+12 的逐项证书以及十二个 parent-language witness，而不是将官方 axiom 表作为 Rust basis。
3. **运行/效果**：完整 SML VM/THM/Context 的真实签名、异常/Seq、data-carried immutable commit、旧 aliases 和显式 transfer；同一 capability gate 和 lifecycle barrier；固定 veriT 仅在强制隔离内产生不可信文本，经原样 proof reconstruction + Rust replay。官方探针只作 source/reference 对照，不是 native 成功。
4. **比较与发布**：逐 theory 对比完整声明/fact group 成员、结构 P/H/S/F/C/owner/依赖、注册效果与已执行程序；所有 `Unavailable` 中影响最终契约的字段必须先由有来源的实际观察补齐。报告 `Succeeded | Failed | BlockedPrerequisite`；`Succeeded` 仅全部可达依赖、受管任务/证明排空、证据完整、报告及 registry 原子发布成功，compare 没有 token 构造能力。失败载阶段、源码 span/理论、操作和输入 identity、原始 cause，分别区分 recoverable（可重试但本次不发布）、user-fixable（报告修正输入）及 fatal（停止并撤权）；未运行检查不写成通过。

`List.thy` 的 veriT 能力与完整 THM、Context 替换和 `HOLBasisV1` 的精确范围已单独批准，[TRUST.md](../status/TRUST.md#p1-effects-runtime-barrier-and-fixed-solver) 列出严格边界；没有授权任意 subprocess/shell、oracle、额外公理、增大效果或改官方输入。当前局部 Rust consumer 的实际闭环不能代替 ML facade、完整九根闭包与独立完整差分字段；solver cleanup blocker 仍在，不启动新 solver。

## Implemented Acceptance API

The kernel produces both the immutable child theory and the trusted value; the
reporting layer only classifies the token:

```rust
pub fn accept_closed_theorem(
    theory: &TrustedTheory,
    name: impl Into<Name>,
    theorem: ClosedThm,
) -> Result<(TrustedTheory, TrustedTheorem), KernelError>;
```

The theorem identity is a versioned, domain-separated SHA-256 digest over:

```text
exact ContextStamp
proposition role
burden tags
alpha-canonical checked proposition
sorted replay-derived dependencies
```

Binder display names and proof derivation structure are omitted. Constructor
tags, constant/free/variable namespaces, variable indices, all checked types,
and dependency kinds are included. A fixed-width big-endian encoder is used;
`Debug` output and platform-native integer layout are not hash inputs.

Accepted ancestor facts are reused only through:

```rust
KernelRules::theorem_ref(&TrustedTheory, &TrustedTheorem)
    -> Result<ClosedThm, KernelError>
```

The rule requires the token in the supplied owner ancestry. Accepting replay
revalidates that ancestry, recertifies the proposition in the descendant
signature, and reconstructs the theorem dependency.

Reporting now uses one exclusive outcome:

```rust
pub enum ProofOutcome {
    KernelTrustedClosed { theorem: TrustedTheorem },
    TransitionalStrictClosed { summary: TheoremSummary },
    CompatClosedOracleFree { summary: TheoremSummary },
    OpenOracleFree { reason: OpenReason, summary: TheoremSummary },
    Admitted { reason: AdmitReason, summary: TheoremSummary },
    Failed { reason: ProofFailure, name: String },
}
```

`verify_lemma` returns `LemmaVerification`, which carries an explicit optional
accepted token and optional `(legacy theorem, exit)` evidence. No thread-local
or global value participates in classification. `classify_proof_outcome` gives
an accepted token precedence over any legacy result, and
`ProofOutcomeStats::record` increments exactly one bucket.
`ProofOutcomeStats::total()` includes the kernel bucket. The bundled
five-file sampled path supplies one source-backed `HOL::TrueI` token and
`0/125` transitional results.

The acceptance attack suite covers wrong theory/signature, stale parents,
sibling tokens, duplicate names, tampered derivations/conclusions, same-stamp
undeclared frees, malformed checked-term caches, owner/store mismatches,
search-fact erasure, alpha-canonical IDs, dependency ordering/kinds, an
independent golden theorem-ID vector, and the distinction between equal logical
theorem IDs and non-interchangeable sibling acceptance tokens.

### Historical post-commit verification audit

The immutable-context baseline `38c5f14` (then `origin/dev`) and all five
candidate commits independently pass `cargo +stable check --locked` and
`scripts/check-strict-kernel.sh` when built with isolated Cargo targets.
`cargo +stable check --locked --all-targets` fails at that baseline and every
candidate with the same four pre-existing benchmark errors: two private
`Result<Thm>` argument mismatches in `benches/kernel_benchmarks.rs`. The
issues are now fixed (commit `878d8ae`); `--all-targets` passes.

The `scripts/check-strict-kernel.sh` path above is a removed historical entry
point, not a present command. Current focused checks run via
`cargo +stable xtask strict`; complete repository checks use
`cargo +stable xtask verify`. Neither command was rerun for this document.

## Required Implementation Order

### 1. Immutable `SignatureId` / `TheoryId` — implemented

- private, deterministic, domain-separated IDs commit to the complete checked
  type/constant signature and immutable theory ancestry;
- checked extension rejects declaration conflicts and preserves parents and
  siblings;
- exact identity propagates through certification, theorem construction, and
  replay;
- mixed contexts fail before logical matching.

### 2. Mutually exclusive kernel acceptance — implemented

- one context-bound acceptance API owns replay, dependency reconstruction,
  duplicate-safe immutable insertion, and token sealing;
- the existing Pure `A ==> A` test exercises acceptance without entering the
  HOL benchmark;
- `KernelTrustedClosed` is a real exclusive outcome, last recorded at `1/125`
  in the bundled five-file sample; standalone fixtures and later Rust THM
  consumers are counted separately.

### 3. Source-aware proposition AST — data model implemented

- `src/isar/source_ast.rs` provides `SourceProposition`, `SourceExpr`,
  `SourceType`, and `SourceSyntax` as unresolved source-level data;
- `SourceName` retains exact spelling without a parser-time qualified-name,
  `Const`, `Free`, `Var`, or `Bound` classification;
- binder/operator syntax remains a raw `SourceSyntax` spelling plus span, not a
  fixed Pure/HOL semantic enum;
- `SourceSpan` is a half-open byte range `[start, end)`, while `SourceId` is a
  caller-supplied label; both are forgeable diagnostics and confer no trust;
- no `ContextStamp`, `SignatureId`, `TheoryId`, `CProp`, `ClosedThm`, or
  `TrustedTheorem` appears in the module or its public API;
- compile-fail doc-tests enforce the absence of conversions into `Term`,
  `CProp`, `ClosedThm`, `TrustedTheorem`, and `DependencySet`;
- the bounded strict parser and checked elaborator now consume this model for
  the two standalone fixtures; broad Isabelle source coverage remains absent.

### 4. Checked judgment / constant / type-scheme elaboration — narrow path implemented

The standalone HOL path elaborates `HOL.Trueprop HOL.True : prop` against
explicit declarations and checked schemes. General source commands for
`typedecl`, `judgment`, `axiomatization`, and `definition` are not compiled by
this path. The separate legacy loader's declarations confer no kernel authority.

### 5. Data-only HOL logic-basis manifest — narrow fixture uses refl only

The bounded standalone/sampled `TrueI` path installed only `refl`. This
historical source path must not be conflated with the separately approved
13-slot `HOLBasisV1` policy or assume all its slots have been exercised by the
sample. Installation validates complete schemas and owner origin; generic
replay checks instances, context identity and dependencies. Neither a
theorem name nor an executable HOL validator creates authority.

### 6. Generic conservative definition extension — implemented

Immutable `define_const` validates freshness, closed and entirely monomorphic
RHS, parent declarations, self-reference, type agreement, and certificate
identity. Owner replay uses the same validator. Legacy `true_def_transport`
is not a certificate.

### 7. Re-derive `HOL::TrueI` — Sampled Projection Implemented

The standalone fixture and audited sampled source share the narrow rule chain:

```text
source-aware proposition
  -> checked CProp: HOL.Trueprop HOL.True
  -> installed refl schema
  -> conservative True_def theorem
  -> ordinary Pure transport
  -> accept_closed_theorem
  -> KernelTrustedClosed
```

The sampled verifier routes its exact `HOL::TrueI` candidate through
this chain, with the source-bound parent command, checked required
declarations, definition, and proof. This does not by itself prove
`HOL::trans`, authorize `HOL.subst` for the sampled path, or supply a second
adapter, general simplifier, or HOL-specific kernel primitive.
The Pure fixture still requires
`!!P::prop. PROP P ==> PROP P` with `by assumption`; `ForallIntr` and
`Abstraction` scope replay variables only within their premises.

## Audit Conclusion

The strict nucleus now has a non-forgeable, immutable, dependency-aware
acceptance boundary for its current Pure derivations. It recursively
recertifies replay payloads, binds accepted facts to exact theory ancestry,
stores them conflict-safely, and exposes a token-backed mutually exclusive
`KernelTrustedClosed` outcome.

Among sampled theorems only `HOL::TrueI` traverses the source-to-acceptance
chain. The standalone fixtures use separate narrow paths; other sampled and
runtime callers have not been migrated:

```text
required source proposition and declarations
  -> checked declaration-aware CProp
  -> authorized immutable HOL basis
  -> axiom and conservative-definition dependencies
  -> accepted TrustedTheorem
```

Standalone fixtures must not be counted in the 125; neither their success nor
this single sampled token establishes general Isabelle/HOL acceptance.
