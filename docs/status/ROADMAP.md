# Roadmap

This is the current dependency-ordered roadmap. Root
[AGENTS.md](../../AGENTS.md), [PROJECT_STATUS.md](PROJECT_STATUS.md), and
[TRUST.md](TRUST.md) define the authoritative position; historical phase plans
and transfer notes do not override them.

## Approved Native Compatibility Program

The long-term target is full **native Rust** functionality against Isabelle2025,
fixed at `765fb2460a57eb46e8490283241ad46f1fac857f`. This is a target, not
the current prototype's capability claim. Official reference evidence is never
a production backend, fallback or source of Rust accepted tokens. The JVM-free
policy disables local official reference execution; comparison uses separately
approved offline evidence. AFP requires a separately pinned corpus.

| Package | Deliverable and exit evidence |
|---|---|
| A — Automation | Independent `xtask`, migrated CI/install calls, retained gates, actual artifact-bound supervised smoke. No proof or parser changes. |
| B — Capability baseline | Source-backed matrix of commands, sessions, logics, ML interfaces and tools; historical fixed official observations and independently approved offline differential evidence. Local reference execution is disabled; missing observations remain blocked. |
| C — Pure closure | General declaration/elaboration, type inference/classes, multi-parent contexts, scope and replay semantics; positive, rejection, diamond-import and owner-attack evidence. |
| D — ML compatibility | Native Standard ML execution and Isabelle host interfaces, including user `ML_file`, modules, exceptions, mutable state and extension registration. No unchecked theorem authority. |
| E — Isar/basic HOL | Real declaration and transaction semantics, structured proofs, nine official HOL files **and their dependency closure**, stronger semantic/accepted-token checks without weakening existing compatibility tests. |
| F — Logics and tools | Pure, HOL, FOL/FOLP, ZF, CTT, CCL, LCF, Sequents, Cube and the fixed official sessions; datatype/BNF/inductive, automation, codegen and external corpus evidence. |
| G — Product runtime | Session/build, incremental documents, cancellation/recovery, official PIDE/editor functionality, document outputs and supported-platform interaction evidence. ISIP is not a substitute. |
| H — Performance/delivery | Same-input semantic comparisons, unchanged proof/dependency results, reproducible resource budgets and complete versioned capability/corpus/platform evidence. |

Packages B–H need separately reviewed executable designs; this program does
not authorize unknown axioms or kernel APIs. The trusted milestones below
remain prerequisites. C and D may overlap only where contracts are independent.
Performance investigation may begin early, but cannot omit proofs or inputs.
External ATP, OS and document tools may remain explicit untrusted dependencies.
Translating bundled ML code alone is not compatibility with user ML extensions.

Completion requires a versioned capability matrix with unsupported, unrun and
failed items distinguished; actual source/dependency execution and differential
semantics; Rust owner-bound replay; honest axiom/oracle/sorry dependencies; and
passing behavioral, resource and quality gates. Finite tests do not establish
universal equivalence. Nine parser tests or the `1/125` sample cannot discharge
this program. No broad semantic or runtime implementation is delivered by A.

### Package Status and Handoffs

**Earlier package A has scoped evidence, not full-project acceptance.** See
[its dated record](PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11).
The all-Rust automation migration and integrated quality repairs have their own
[delivery evidence](PROJECT_STATUS.md#current-delivery-state); old xtask passes
do not verify today's tree. Source-quality repairs do not expand proof
capabilities or establish native kernel/ML compatibility acceptance.
**B has a historical reference-side baseline, not full compatibility
acceptance.** The prior isolated reference run rebuilt Pure/HOL and executed
the nine-root closure; its frozen observations, remaining gaps and production
`veriT` permission boundary are recorded in
[PROJECT_STATUS.md](PROJECT_STATUS.md#isabelle2025-reference-observations-2026-10-12).
Registered interfaces are not executed Rust capabilities or approved axioms.

C–H are not accepted. The user has approved resuming native P2/P3/P4 closure
implementation under the reviewed P1 contracts; this is not compatibility
acceptance. The later JVM-free architecture separates native publication from
independently approved offline reference comparison, without weakening Rust
replay or authorizing solver launches. See the
[current delivery record](PROJECT_STATUS.md#current-delivery-state), including
the scoped Rust THM consumers and ML/evidence repairs.
Each package still needs its own inputs, owned paths, non-goals, failure semantics, review,
reproducible behavior evidence and applicable quality gates. Use the shared
[engineering workflow](../guides/DEVELOPMENT.md#engineering-workflow); its six
stages are distinct from A–H and the trust milestones below. Do not silently
change either the original nine-file compatibility requirement or the
strict-token acceptance criterion to make progress appear complete.

## Current State

The last source-backed bundled five-file sample, before the automation
migration, reported the following. These are dated sampled observations, not
a new run or a measure of complete native closure:

```text
TransitionalStrictClosed: 0/125
KernelTrustedClosed:      1/125
```

The isolated `crates/kernel/` TCB, re-exported by `src/kernel/`, has checked `CProp : prop`, private theorem
construction, the base Pure rule set, conservative resolution prototypes,
immutable content-addressed signature/theory and accepted-fact ancestry,
owner-parameterized recursive recertification/replay, theorem-reference
dependency reconstruction, and non-forgeable accepted tokens for targeted
standalone paths.

The sampled `HOL::TrueI` now passes a narrowly audited projection of the
bundled `theories/HOL/HOL.thy`: required declarations, the actual `True`
definition RHS, and the exact source proof are checked before immutable owner
replay. Unrelated HOL declarations and ML are neither executed nor authorized.
The separate `isabelle-build` fixtures `TrustedTrueI.thy` and
`TrustedPureIdentity.thy` remain outside the sampled 125-lemma metric.

声明与成功契约已收紧：strict signature 记录类型 arity，basis 安装前验证完整
schema，定义和 owner replay 共用验证。legacy 完整 loader 按文件事务发布，
拒绝未实现命令和多 imports；proof 结案与自动化最终出口核对完整目标及真实
证据。这些属于边界修复，不是 sampled 迁移或一般 Isar/HOL 功能完成。

The separate `native_thm` and `native_thm_variables` Rust consumers exercise
checked transformations, explicit scope/owner replay, closure, acceptance and
reference reuse. They are not additional sampled HOL adapters or the complete
ML `Thm: THM` interface. The
[fixed THM inventory](NATIVE_THM_INTERFACE_INVENTORY.md) distinguishes native
kernel support from missing ML interfaces; complete ROOT/HOL remains unaccepted.

## Next Delivery Plan (2026-10-19)

下一阶段先恢复可信的工程反馈，再贯通**真实 ML 源码消费 Rust 内核**的路径，
不以增加 theorem-specific adapter、扩大 parser 统计或启动新平台项目代替闭包。
以下是对既有 A–H / P1 的执行顺序细化，不是新增公理、宿主权限、依赖升级、
solver 启动或发布授权；各包进入实施时仍须按工作流确认具体范围。

### 现状与关键依赖

现有两个 Rust THM consumer 已覆盖局部接受和引用，不应重新造一套内核入口。
但 [THM 清单](NATIVE_THM_INTERFACE_INVENTORY.md) 仍有 ML 表示、异常与回调
接口缺口。当前 [`evaluate_root_with_context`](../../src/ml/bootstrap.rs)
成功返回也只覆盖 ROOT 前缀和已批准的 Context 替换；固定
[`ROOT.ML`](../../isabelle-source/src/Pure/ROOT.ML) 在 Context 后首先加载
`config.ML`，其后还有大量文件。本次实际 smoke 更早停在
`src/Pure/ML/ml_heap.ML`：`unbound value PolyML.objSize`，尚未到达 Context。
详见 [本次源码核对证据](PROJECT_STATUS.md#source-backed-documentation-audit-and-delivery-plan-2026-10-19)；
后续必须从实际错误推进，不能直接假定已执行到 `config.ML`。

|阶段|直接依赖|可交付结果|进入下一阶段的条件|
|---|---|---|---|
|N0 — 工程基线|当前 checkout 与已有失败日志|分开修复源码质量、测试前置条件和依赖漏洞；得到稳定树的完整门结果|相关行为证明、`verify`、`selftest` 与全局门全部通过；不靠删断言或忽略失败|
|N1 — 原样 ROOT 推进|N0；已批准的 ML/Context/效果合同|从实际最早失败文件继续，记录每个已执行文件和精确未执行后缀|修复首个语义缺口并通过同一路径；新边界可复现、失败不发布部分构建|
|N2 — ML THM 消费闭环|N1 的类型/模块/Context 前置；现有 Rust 内核 API|真实 ML 签名、句柄和操作调用 Rust checker，而非另造 theorem 构造器|ML 消费者实际得到经 owner 接受的结果；错误身份、scope、异常及撤权攻击被拒绝|
|N3 — Pure/Isar 源执行|N1 全部 Pure ROOT 依赖及 N2 所需接口|完成真实 Pure bootstrap、声明/证明事务和源级扩展注册|未执行后缀为空；受支持源码从读取到接受/拒绝及排空形成完整闭环|
|N4 — 九根 HOL 闭包|N3；P1 basis/class/typedef 证书；需要时恢复 solver 宿主前置|执行固定九根和其完整依赖，不跳过普通 ML/HOL 包|逐根真实执行、完整 replay、失败不发布、任务排空；无 admit/legacy 重分类|
|N5 — 独立兼容与交付|N4 原生结果；另行提供并批准的官方离线材料|分别报告 native build 与官方语义差分；完成产物再分发清单|缺失证据仍阻塞兼容；版本/平台/许可和质量门齐备后才申请发布|
|N6 — 产品与规模化|相应 Pure/HOL 闭包及独立产品设计|共享文档 runtime、交互取消/恢复、多逻辑和有依据的性能工作|端到端用户流程、同输入语义及资源证明；ISIP/AFP 各自验收，不外推覆盖|

N1 与 N2 可在已固定且互不冲突的接口上并行；N3 必须等待它们收敛。
文档、拒绝路径和受限性能调查可以并行，但不增加证明权限或改变验收分母。
N0 未完成时可继续已授权的局部诊断，不能将其交付为完整里程碑或提交放行。

### 工程基线包的验收条件

本节保留 N0 的验收条件，不把已修复问题重复列为未实施。已授权的
ZIP 升级、fixture、Clippy 与诊断修复及其验证见
[工程修复记录](PROJECT_STATUS.md#engineering-quality-repair-2026-10-19)。

- 按 [当前交付记录](PROJECT_STATUS.md#current-delivery-state) 分类已知失败，
  不把旧失败重新当成未知问题，也不以单个绿色工具覆盖另一道失败门。
  格式修复与语义修复分开审查，避免全库自动重写掩盖已有用户成果。
- 测试中的 `/bin/cat`、`/bin/true` 前置条件应改为项目支持的可定位输入或
  独立受控 fixture；必须仍覆盖真实 launcher、流和清理行为，不能改成
  不启动进程的 mock 或隐藏跳过。测试前置修复不解除真实 solver 的阻塞。
- `zip` 漏洞按单独依赖/安全包评估实际调用和修复版本，审阅 API/锁文件变化，
  保留压缩归档行为测试和 license 检查；本计划不直接指定未经验证的升级版本。
- 冻结源码、配置和文档后跑最终门。输出分类为 passed、failed、blocked、
  unrun；完整工作树验证戳缺失时不提交，不以文档更正作为失败豁免。

紧随 N0 的首个语义包应核对 `ML_Heap` 实际消费的 `PolyML.objSize`、
GC、统计与共享/heap 接口，明确 Rust VM 对象图、字大小、共享和可观察效果的
真实实现。此轮只复现了首个未绑定值，不代表其余接口均缺失；逐项以代码与
源码消费验证，不用常数、空操作或假 heap 保存让 ROOT 越过加载检查。

### 原生语义推进方式

1. 用 [`native_root_smoke`](../../examples/native_root_smoke.rs) 的实际错误定位
   首个缺失行为；它只验证前缀/Context，不能把退出 0 当完整 Pure 构建。
   对照固定 Isabelle/ML 与同版运行时语义，先写最窄行为复现，再做通用修复；
   不按文件名、函数名或值形状硬编码通过。
2. 在 [171 项 THM 清单](NATIVE_THM_INTERFACE_INVENTORY.md) 中分别记录 Rust
   kernel 能力、ML adapter、真实 consumer 和已运行证据。优先补原样源码当前
   实际消费的接口，再覆盖完整公开签名；不能以少数 Rust 示例宣布 THM 完成。
3. 复用 `accept_closed_theorem`、既有 composition candidate checker 和显式
   scope/owner replay。搜索只生产有限候选；开放 `thm`、`ClosedThm`、
   结构/hash 或 ML 返回值都不是 accepted token。缺少 kernel 能力时另定窄包、
   独立审查侧条件和 replay，不绕过 checker 在 Host 补造定理。
4. 每个推进包保留完整原异常和已有 ref 副作用，区分可捕获 ML 异常与不可恢复
   permission/fatal/cancel；失败撤权后旧句柄和二次调用不能恢复。
   成功须排空 callback、future、流与任务；无真实 Closed 屏障不发布 registry。
5. Context/Thm 与 SHA1 仅采用已批准替换；其余固定源码顺序和字节保持原样。
   确需新增替换、宿主服务、类型证书或 basis slot 时先独立批准，绝不静默跳过
   当前不支持的文件、命令或服务。

### HOL、兼容与产品的停止条件

P1 的 class/arity、conditional typedef、sort export 和 13 条 HOLBasisV1
合同继续生效；完整代码存在或局部 attack tests 通过，都不能代替
九根源执行的 witness、owner replay 和完整依赖闭包。`core` 的 125 项统计
仍单独记账，不把新 consumer 或原生构建计入旧采样。

solver cleanup 的宿主问题没有解除前，不启动新的 solver，也不以删除
`List.thy` 的调用、宽松隔离或假结果闭合 HOL。若原生执行推进到该依赖，
记录精确阻塞并停止受影响闭包；其他独立的纯 Rust 工作可以继续。
本地官方 JVM/Scala runtime 继续禁用。官方来源审批和离线差分独立于原生
接受；`Matched` 不产生 Rust 定理，缺材料不是兼容成功。

产品工作后置，先固定 CLI/loader 的成功失败语义和文档 worker 的生命周期，
再考虑共享 runtime 与新协议。现有 WASM tactic 通道未实现，fuel 也不提供
内存/墙钟保障；编译期链接的原生 Rust 插件则是受信任进程内代码。
不能为了“统一插件”把两者权限模型合并，或将当前 LSP 称为完整 PIDE。

### 证据、回退与发布

每包记录固定源码身份、实际输入、toolchain、可观察停止点、owner/依赖、
预算、原始日志和独立审查结论。源码/依赖/宿主修复各自保持可审查边界；
失败不发布构建，继续保留现有可用窄路径与失败证据，不静默 fallback。
需恢复代码时只处理明确授权的本包改动，绝不整树 reset 用户成果。

源码提交与二进制发布分开。现有 Apache-2.0/Isabelle BSD 声明记录许可范围，
不构成全库原创性、权利归属或合规保证。源码提交、上传须满足所分发源码的
适用许可条件，以及约定的质量门和用户授权条件。二进制发布还须按实际构建
纳入的锁定依赖、链接的原生库及复制材料，核对并履行相应再分发义务，
补齐许可文本、版权/NOTICE 等声明。`cargo deny` 通过不完成这项工作；
完成源码检查也不等于完成二进制发布检查。

## Trusted Main Line

The phases below describe the narrow source-to-kernel migration path. They are
not a complete inventory of the native Pure/ML implementation or its approved
[P1 contracts](TRUST.md#p1-native-trust-design).

```text
immutable SignatureId / TheoryId [implemented]
  -> unique context-bound acceptance [implemented]
  -> data-only source proposition AST [implemented]
  -> bounded source parser + checked TrueI and typed Pure identity elaboration [narrow slices]
  -> minimal HOL refl basis + generic True_def [narrow slice]
  -> source-backed TrueI and Pure identity CLI acceptance [narrow slices]
  -> sampled HOL TrueI acceptance [audited source projection; 1/125]
  -> staged, per-caller replacement of legacy theorem producers [not implemented]
  -> HOL::trans and broader coverage [deferred]
```

These trust dependencies remain mandatory within the A–H delivery program.
One sampled accepted token does not turn the legacy theory batch compiler,
Isar or other runtime frontends into trusted theorem producers, nor validate
the full HOL theory.

The legacy engine stays available as an explicitly untrusted search and
experimentation path during this migration. Each proof-producing caller is
cut over only with a replayable strict contract; no bulk deletion of its
compatibility API or relabeling of legacy facts is implied.

## Phase 1: Immutable Context Identity — Implemented

### Goal

Make it impossible to combine certified terms or theorems from unrelated
signatures by accident.

### Minimum implementation

1. Add private, opaque `SignatureId` and `TheoryId` types.
2. Replace silent declaration overwrite with checked monotonic extension.
3. Define canonical, domain-separated identity input for validated
   declarations and parent identity.
4. Bind `ProofContext`, `CTerm`, `CProp`, `KernelThm`, `ClosedThm`, and
   `TrustedTheorem` to the relevant context identity.
5. Reject mixed-context inputs in every strict rule before theorem
   construction.
6. Preserve parent contexts unchanged when creating an extension.

Do not add a hashing dependency merely to make the type look content-addressed.
First specify and test canonical declaration encoding, domain separation, and
collision/error behavior. Any dependency and `Cargo.lock` change needs a
separate rationale.

### Required attacks

- equal canonical signatures produce equal IDs;
- declaration order has the documented deterministic meaning;
- a conflicting constant declaration is rejected, not overwritten;
- extending a signature does not mutate the parent;
- a `CProp` certified under signature A cannot be used with signature B;
- two contexts with the same surface names but different declarations do not
  interoperate;
- callers cannot construct or spoof identity values.

### Exit condition

Focused identity tests and the existing strict gate pass. No proof outcome or
sampled HOL count changes.

Implemented with the repository's existing `sha2` dependency; `Cargo.lock` did
not change.

## Phase 2: Unique Context-Bound Acceptance — Implemented

The implemented operation is:

```rust
pub fn accept_closed_theorem(
    theory: &TrustedTheory,
    name: impl Into<Name>,
    theorem: ClosedThm,
) -> Result<(TrustedTheory, TrustedTheorem), KernelError>;
```

It:

- checks exact theory/signature identity and immutable owner-chain integrity;
- recursively recertifies every checked theorem and derivation payload under
  the supplied owner;
- requires a proposition-valued, replay-equal, closed result;
- reconstructs and authorizes ancestor-theorem dependencies;
- validates installed axiom dependencies and conservative-definition certificates;
- rejects duplicate theorem names without mutation or overwrite;
- atomically returns the immutable fact child and sealed token;
- accepts no compat, admitted, search-fact, or legacy input.

`ClosedThm::trust` is removed, `SearchFact` carries no extractable proof,
and `KernelTrustedClosed` is a mutually exclusive token-owning
`ProofOutcome`. `ProofOutcomeStats::total()` includes that bucket.

Synthetic Pure `A ==> A` tests exercise correct/wrong context, dependency,
duplicate, tampering, malformed-term, owner/store, canonical-ID, and classifier
attacks without changing the 125-theorem HOL benchmark.

Detailed audit:
[KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](../kernel/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md).

## Phase 3: Source-Aware Proposition AST — Data Model Implemented

`src/isar/source_ast.rs` now preserves source structure before any trusted
elaboration:

```text
SourceProposition { SourceId, SourceSpan, SourceExpr }
SourceExpr::{Name, Application, Binder, SyntaxApplication, TypeAscription, Group}
SourceType::{Name, Application, Arrow}
```

`SourceName` stores exact spelling without preclassifying dotted text as a
qualified constant. `SourceSyntax` stores raw binder/operator spelling and its
span instead of hard-coding Pure/HOL binder meaning. `SourceSpan` is a
half-open byte range `[start, end)` and `SourceId` is a caller-supplied label;
both are forgeable diagnostic metadata, not trusted provenance.

The model has no `ContextStamp`, `SignatureId`, `TheoryId`, `CProp`,
`ClosedThm`, or `TrustedTheorem`, and compile-fail tests forbid direct
conversion into kernel or legacy theorem authority.

The data model itself carries no authority. The separate `source_parser`
and `elaborator` consume the two supported TrueI and explicit-PROP Pure identity
source slices with file-byte spans, declaration-aware resolution and checked
`CProp : prop`. General Pure/HOL syntax, polymorphic source annotations, local
declarations, and broader Isar commands remain outside this trusted path.
Transitional source status/shape metadata remains confined to legacy search.

Do not repair a damaged legacy `CTerm` by guessing what the source meant.

## Phase 4: Checked Declarations And Proposition Elaboration — Narrow Slice

The current narrow strict elaborator resolves checked HOL.Trueprop and HOL.eq
declarations from a `ProofContext`. Its supported fixtures/projection do not
provide a general implementation of `typedecl`, `judgment`, `consts` or
`axiomatization` for arbitrary theory source.

The first required judgment is:

```text
HOL.Trueprop : bool => prop
```

The elaborator must resolve checked polymorphic schemes and sorts, preserve the
source skeleton, insert `Trueprop` only at recorded judgment positions, and
return a checked `CProp` without constructing a theorem.

Do not add a `HOL.Trueprop` string special case to legacy
`HolTheoremDb::build_type_env`.

## Phase 5: Data-Only HOL Logic Basis — Minimal Refl Slice

The source-backed TrueI path installs bool/fun, HOL.Trueprop, HOL.eq and one
replayable `HOL.refl` schema. Its former malformed `HOL.subst` schema was removed.
This narrow path is distinct from the approved native HOLBasisV1 policy and
its source/owner checks in [TRUST.md](TRUST.md#p1-holbasisv1-policy).
It does not imply that broader HOL source compilation has been delivered.

Generic kernel code validates declaration schemes, installs the basis,
instantiates axioms, and replays derivations. Structural validation of the
manifest does not independently verify agreement with Isabelle/HOL sources.
Do not add `ThmKernel::hol_*` or `KernelRules::hol_*` proof shortcuts.

## Phase 6: Generic Conservative Definition Extension — Kernel Implemented

The kernel provides atomic checked conservative definition extensions,
including a replayable Pure equality theorem and owner checks. The
standalone TrueI compiler defines HOL.True via this extension. Legacy
`CheckedDefinitionSource` remains a non-theorem migration input. The former
`true_def_transport` bridge was removed, not promoted into a kernel certificate.

## Phase 7: First Source-Backed HOL Theorem — Sampled Projection Implemented

The standalone `TrustedTrueI.thy` fixture and sampled HOL source projection share the narrow kernel rule chain:

```text
source-aware TrueI
  -> checked HOL.Trueprop HOL.True : prop
  -> immutable HOL theory with HOL.refl
  -> conservative True_def theorem
  -> Pure equality/congruence transport
  -> exact-owner TrustedTheorem acceptance
```

The sampled five-file verifier now routes only the actual `HOL::TrueI`
candidate through this chain and reports `KernelTrustedClosed: 1/125`;
all other theorem-producing legacy callers remain outside this path.

## Phase 8: Reuse Consumer

`HOL::trans` would require its own source/owner and proof contract. No
`hol_subst`, second adapter, general simplifier, or HOL-specific kernel
primitive is authorized by the `TrueI` milestone; any needed axiom schema,
including `subst`, requires separate soundness review.

## Parallel Maintenance

Allowed when it does not delay or weaken the main line:

- strict-kernel attack-test and replay hardening;
- classified admitted/compat diagnostics;
- documentation and agent-rule synchronization;
- design-only deterministic CPU symbolic-compute work.

Compute remains an untrusted candidate producer. Burn/CubeCL/GPU work, if ever
added, stays outside the kernel and cannot produce theorem values.

## Phase 9+: ISIP Platform

ISIP (Isabelle Structured Interaction and Proof) is a family of standards
for editor-agnostic, model-agnostic proof interaction. See
[docs/isip/ISIP.md](../isip/ISIP.md). **Design-only until TCB closes.**

The existing sampled `1/125` milestone does not by itself close the complete
trusted source/runtime loop. These ISIP design stages are not A–H packages,
and ISIP cannot substitute for native ML or official PIDE compatibility.

ISIP implementation stages:

| Stage | Name | Prerequisite | Key Deliverables |
|-------|------|-------------|-----------------|
| 0 | Design | None (now) | Existing overview/ISIP-000; ISIP-100 and ISIP-300 drafts remain planned |
| 1 | Observable | TCB closed | `getSnapshot`, `getGoals`, `getContext`, diagnostics |
| 2 | Transactional | Stage 1 | `LogicalAction`, `StateTransition`, `StateDiff` |
| 3 | Branching + Agent | Stage 2 | `fork`, `moveHead`, `tryBatch`, budget, MCP Profile |
| 4 | Evidence-Aware | Stage 3 | Replay, certificate check, artifact persist, theory extend |
| 5 | Multi-Logic | Stage 4 | Second logic backend, TranslationEvidence, A2A Profile |

## Deferred Platform Work

Defer until the trusted HOL loop closes:

- broader runtime/session extraction (the current workspace contains the root product, `isabelle-kernel`, `isabelle-evidence`, and `xtask`);
- ISIP Stage 1+ runtime implementation;
- session snapshot/rollback engine;
- `isabelle.toml` project system;
- broad LSP/PIDE/WASM/plugin expansion beyond the separately approved compiler-linked native Rust plugin and host-service contracts;
- broad HOL/Isar/tool coverage;
- AFP-scale claims.

## Standing Verification Policy

- Documentation/agent changes: `cargo +stable xtask docs`.
- Kernel or trust-boundary changes: `cargo +stable xtask strict`.
- Sampled HOL metric changes: `cargo +stable xtask core`.
- Integrated delivery: `cargo +stable xtask verify`, then independent security/
  global gates; Tier diagnostics remain opt-in and local official reference
  execution remains disabled.
- Broader theory statistics: run the exact relevant supervised `tier2`, `tier3`,
  or `broad` mode; these are opt-in diagnostics, not default proof regressions.
  The default suite still covers the 125 sample, global HOL database,
  functional/trust contracts, and nine official files' no-`SyntaxError` checks.
  See [diagnostic modes](../../scripts/README.md#report-only-scale-workloads)
  for budgets and output logs; completion is not a theory build or proof.

Report observed results only. Do not infer project API correctness from a
standalone template compile, mathematical trust from an oracle-free count, or
dependency intent from a successful locked metadata command.

The earlier [A-package record](PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11)
reports workspace tests completed but failed official-source compatibility,
and the global gate also failed strict Clippy. This is historical evidence, not
the current all-Rust migration's gate result; see
[current delivery evidence](PROJECT_STATUS.md#current-delivery-state).
Older lint/scanner/OOM/timeout records remain dated history. Apply project
gates first and the complete `~/.omp/agent/validate.sh` separately; no `all`
or narrow success waives a known failure or authorizes release.
