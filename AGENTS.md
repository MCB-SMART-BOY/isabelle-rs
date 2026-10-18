# Isabelle-rs Agent Guide

This file is the versioned, harness-neutral entry point for coding agents working
in this repository. Oh My Pi, Codex, Claude Code, and other tools must apply the
same trust boundary. A stronger harness or model does not make a theorem more
trusted.

## Authority Order

Resolve conflicts in this order:

1. source code and tests in the current checkout;
2. `docs/status/PROJECT_STATUS.md` and `docs/status/TRUST.md`;
3. accepted ADRs and trusted-boundary design documents;
4. `docs/status/ROADMAP.md` and other current repository documentation;
5. `.claude/`, `~/.codex/`, agent memory, and archived session notes.

Always obtain repository state from a fresh status/log inspection. Documentation
must not freeze a clean-worktree claim or assume that an unpublished commit is
still present.

## Project Position

Isabelle-rs is a Rust research prototype of an Isabelle/Pure-inspired LCF
kernel. It is not a full Rust rewrite of Isabelle and does not have
Isabelle/HOL, Isar, PIDE, or AFP feature parity.

The approved long-term program targets native Rust compatibility with the
fixed Isabelle2025 baseline, including user Isabelle/ML extensions. The official
runtime's nine-root observation is a frozen differential reference, never a
production backend or Rust theorem authority. The JVM-free policy disables local
`cargo +stable xtask reference prepare/build/inventory` before workspace access;
only `reference compare` remains available for offline evidence comparison.
Do not launch the official runtime or a solver to refresh historical evidence.
See [JVM-free direction](docs/status/PROJECT_STATUS.md#jvm-free-architecture-direction-2026-10-16)
and [the command catalog](scripts/README.md#verification).

The workspace has four members: root `isabelle-rs` (the sole default member and
product), `isabelle-kernel` (the isolated accepted-theorem TCB),
`isabelle-evidence` (offline evidence data, not theorem authority), and `xtask`
(product-independent automation). Its membership does not expand the trusted
kernel or authorize runtime extraction. Native P2/P3/P4 closure work has resumed
under the approved [P1 contracts](docs/status/TRUST.md#p1-native-trust-design);
local Rust `native_thm` and `native_thm_variables` consumer evidence is not a
complete ML `Thm: THM`, ROOT/HOL or nine-root compatibility acceptance. Consult
the [THM inventory](docs/status/NATIVE_THM_INTERFACE_INVENTORY.md) and
[current delivery record](docs/status/PROJECT_STATUS.md#current-delivery-state)
for dated evidence and blockers. The earlier package-A xtask migration and
package-B nine-root reference snapshot remain distinct historical results.
Automation and quality checks do not authorize additional proof rules or
production effects. The [engineering workflow](docs/guides/DEVELOPMENT.md#engineering-workflow)
governs each task; A–H packages and numbered trust milestones describe
deliverables, not permission to skip that workflow.

Use the [next delivery plan](docs/status/ROADMAP.md#next-delivery-plan-2026-10-19)
for dependency order and exit evidence, not as new implementation or release
authorization. The current native ROOT stopping point is owned by the
[source-backed audit record](docs/status/PROJECT_STATUS.md#source-backed-documentation-audit-and-delivery-plan-2026-10-19),
not inferred from a successful Rust THM consumer or the presence of Context APIs.

Historical sampled trust metrics from 2026-10-03 (before the source-backed
sampled cutover) were `TransitionalStrictClosed: 1/125` and
`KernelTrustedClosed: 0/125`. The last source-backed run before this automation
migration sampled bundled `theories/HOL/{HOL,Orderings,Set,Nat,List}.thy` and reported:

```text
TransitionalStrictClosed: 0/125
KernelTrustedClosed:      1/125
```

The sampled `HOL::TrueI` now uses a checked projection of its real source:
explicit bool/Trueprop/equality declarations, `refl`, the actual `True`
definition RHS, and the complete `unfolding True_def by (rule refl)` proof.
It builds an immutable owner and a replayed `HOL.Trueprop HOL.True : prop`
token, not a reclassified legacy `Thm`. Its projection does not execute
unrelated HOL commands or ML and does not compile the whole theory.
`isabelle-build tests/fixtures/TrustedTrueI.thy` remains a separate
source-backed fixture and is not counted in the sampled 125.

The separate `tests/fixtures/TrustedPureIdentity.thy` now has a checked
`imports Pure` path: `!!P::prop. PROP P ==> PROP P` with `by assumption` is
elaborated, proved by Pure `assume`/`implies_intr`/`forall_intr`, and accepted
by owner replay. The former `(rule impI)` spelling is rejected. Replay scopes
Free variables only within binder premises, including `Abstraction`, without
adding them to the owner. This fixture remains
outside the sampled 125-theorem verifier. The legacy Isar/HOL loader still
does not return accepted tokens.

`KernelTrustedClosed` is a mutually exclusive `ProofOutcome` backed by a
real accepted token. Only the sampled `HOL::TrueI` candidate has been
migrated; other legacy HOL verification remains transitional or diagnostic.

## Two-Kernel Boundary

```text
crates/kernel/  candidate target TCB nucleus (src/kernel/ re-exports its API)
src/core/    legacy quarantine and migration source
```

For `crates/kernel/` (and its `src/kernel/` re-export):

- no dummy type or compatibility certification;
- no `admit`, fallback `assume`, or theorem construction from failed search;
- no dependency on `core`, Isar, HOL, tools, theory/session, LSP, server, WASM,
  or compute backends;
- undeclared or wrong-arity types, undeclared constants, and local frees are rejected;
- `ProofObligation` and `SearchFact` are not theorems;
- unchecked certified-term and theorem constructors remain `pub(crate)` or
  narrower inside the isolated `isabelle-kernel` crate, never public frontend APIs;
- every trusted rule requires explicit side conditions, replay, and attack tests.
- `accept_closed_theorem` is the only trusted-token constructor; it owns exact
  owner replay, recursive recertification, dependency reconstruction, duplicate
  rejection, and immutable accepted-fact insertion;
- ancestor theorem reuse requires `KernelRules::theorem_ref`; replay checks the
  exact sealed token (`id`, `name`, and `accepted_in`) in owner ancestry before
  recording its logical `TheoremId` dependency;
- a canonical `DependencySet` is theorem identity data, never proof authority.

For `src/core/`:

- do not add new trusted HOL proof power;
- changes are limited to bug fixes, boundary hardening, diagnostics, and explicit
  migration adapters;
- compatibility constructors and `Typ::dummy()` remain debt, not precedents;
- `is_strict_closed_proved()` authorizes only
  `TransitionalStrictClosed` reporting.
- `src/core/kernel_convert.rs` is a compatibility-only translation out of the
  strict kernel; its legacy output cannot authorize an accepted theorem.

`HolTheoremDb` and other search indexes may contain open, admitted, generated,
compatibility, and transitional facts. They are not trusted theorem tables.

Legacy HOL/Isar search takes an explicit borrowed `&HolTheoremDb`; local
verification, theory transactions and diagnostic runs own their own search
database. The immutable `HolTheoremDb::global()` is for application roots,
not an ambient lookup inside proof methods or term certification. Named facts
proved during a theory transaction are added only to that transaction's
database; its failure does not publish them. Simplification rules are cached
per database. This search-scoping repair does not change theorem authority or
the sampled trusted count.

Search-rule collections are still public legacy fields. After a DB has been
queried, do not edit those collections directly: use `extend`,
`add_builtins`, or `insert_named_fact`, which invalidate its derived caches.
Direct mutation can leave search results stale; this is remaining legacy
API debt and must not be interpreted as accepted proof evidence.

## Platform Architecture

The target architecture is a layered proof engineering platform:

| Layer | Crate(s) | Responsibility |
|-------|----------|---------------|
| 0 — TCB | `isabelle-kernel` | Immutable theorem construction, acceptance, replay. Zero warnings, no async, dependencies limited to `sha2` + `thiserror`. |
| 1 — Logic | `src/hol/`, future `src/pure/` | Declaration-aware elaboration, checked judgments, logic-basis manifests, axiom/definition replay. |
| 2 — Runtime | Future `isabelle-session` | Headless document engine, snapshot/fork/rollback, diagnostics, proof-state transactions. |
| 3 — Adapters | CLI, LSP, Agent | No theorem authority. Share a single document/proof runtime via versioned protocols. |

Target architectural invariants (not yet general runtime capabilities):
- explicit logic identity in theorem, session, and diagnostic protocols;
- `stable` vs `experimental` separation; experimental code cannot enter the TCB dependency graph.
- `KernelTrustedClosed` is the only final trust token; all other outcomes are transitional or diagnostics.

Experimental built-in LSP/Session checks and LSP definition lookups execute
in a reusable `--compute-worker` child, with bounded diagnostic/proof-state
IPC. Embedded `IsabelleServer::new` needs a trusted worker executable;
`Session::new_with_worker` is required for built-in `RealExecutor`, while
`Session::new` only accepts cooperative custom executors. This is direct-child
failure isolation, not an OS resource, privilege, or process-tree sandbox.
No process-produced snapshot carries theorem acceptance authority.

Native ML callbacks consume compiler-certified types by argument position and
record/tuple field, never by the first matching closure pointer. Public untyped
`Vm::apply` checks foreign callable/argument ownership before type lookup and
does not infer polymorphic or opaque identities. A FileHostBridge VM mismatch
revokes both runtime domains. Ordinary exception packets and prior ref effects
remain observable; permission, cancellation and fatal failures remain uncatchable.
Bootstrap registrations use source-bound `observer/event` records; valid empty
source reads do not waive hashes or sealing. See the scoped
[semantic repair evidence](docs/status/PROJECT_STATUS.md#ml-runtime-and-evidence-semantic-repairs-2026-10-19);
offline checks do not establish a new official reference run or theorem authority.

### Checkpoint (2026-07-21)

Commit `03d28a6` from `wip/kernel-trusted-slice`, integrated by merge `bc056ed`, delivered:
- `TypeVarId { name, index }`, recursive `is_concrete_type`, `is_monomorphic_instance_of` with `BTreeMap`.
- Atomic `AxiomDependencyId` replacing dual-entry axiom dependency.
- 10 TCB attack tests.
- `prove_true_i` via accepted `True_def` + `theorem_ref` + `Combination + Symmetric + EqualElim` chain.

**Completed (2026-07-22):**
- `ConservativeDefinition` is atomic via `DefinitionId` in `TheoryExtension::DefineConst`. Replay walks owner ancestry to find the certificate, validates parent, freshness, and concrete types.
- `PolyType::new` validates param sort consistency and requires every declared param appears in the body. `monomorphic_instance_matches` authorizes instances against params.

**Still incomplete:**
- Kernel -> legacy conversion in `src/core/kernel_convert.rs` still uses Debug strings (untrusted path).
- Apart from sampled `HOL::TrueI`, legacy `src/core` and other runtime
  frontends have not migrated to the source-to-kernel compiler.
- A single accepted sampled token does not imply broader HOL/Isar acceptance.


## ISIP Vision

The project's long-term interaction model is defined by the **ISIP** (Isabelle
Structured Interaction and Proof) standard suite. ISIP is a family of
specifications for editor-agnostic, model-agnostic, transport-agnostic proof
interaction. See `docs/isip/ISIP.md` for the full overview.

ISIP is currently **design-only**. The sampled `KernelTrustedClosed: 1/125`
milestone is narrow prerequisite evidence, not closure of the full TCB/frontend
loop or authorization to implement ISIP runtime, wire protocols or adapters.
Future implementation requires the relevant reviewed runtime design and gates.

The planned suite has seven specifications. Only the overview and ISIP-000
architecture draft currently exist; ISIP-100 through ISIP-600 are planned:

| Spec | Scope |
|------|-------|
| ISIP-000 | Architecture and Trust Boundary |
| ISIP-100 | Semantic Model (DocumentRevision, ProofSnapshot, Goal, Fact) |
| ISIP-200 | Runtime Model (branches, speculative execution, leases) |
| ISIP-300 | Evidence and Trust Model (certificates, replay, oracle/admit) |
| ISIP-400 | Wire Protocol (JSON-RPC 2.0, capability negotiation) |
| ISIP-500 | Integration Profiles (LSP, MCP, A2A, Native SDK, CLI) |
| ISIP-600 | Security and Conformance (permissions, audit, threat model) |

Six normative requirements govern all ISIP specs; the first and most important
is: **the kernel MUST NOT depend on ISIP, MCP, LSP, A2A, or AI.**
## Current Trusted Main Line

The implemented narrow path is:

```text
whole-file TrueI source -> bounded source AST -> declaration-aware CProp
  -> refl basis instance -> generic conservative True_def
  -> Pure transport -> close_thm -> accept_closed_theorem
```

`src/isar/source_ast.rs` remains data only; the strict parser and elaborator
consume it without granting SourceId or spans theorem authority. The two
standalone supported source proofs are the HOL `TrueI` fixture and the Pure
identity fixture. A separate audited projection accepts the sampled HOL
`TrueI` source without interpreting unrelated commands or adding their
declarations to the owner. Other declarations, proof methods, and broad
HOL/Isar commands remain outside this acceptance path.

Further trusted migration replaces theorem-producing callers individually
when the strict kernel can replay their full source/owner/proof contract.
The approved Pure/ML, owner, class/arity and effect contracts now govern native
implementation; the [progress record](docs/status/PROJECT_STATUS.md#native-kernel-and-ml-progress-2026-10-15)
separates local behavior evidence from unresolved closure gates.
The legacy engine remains available for experiments and
search; no legacy `Thm` may be reclassified as a trusted token.

Read `docs/kernel/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md` before changing this chain.

### 声明与证明成功契约

- strict `SignatureId` 覆盖类型构造器及 arity；snapshot 必须按声明重建，
  不兼容旧 digest。当前身份版本见
  [严格内核不变量](docs/kernel/KERNEL_PRIMITIVES.md#global-invariants)；
  basis 安装前在同一 signature 下校验全部 schema。
- 定义入口与 owner replay 共用完整 RHS 单态检查；后代不能补授权祖先公理，
  theorem reference 必须匹配祖先保存的规范 token 及负载。
- legacy `TheoryProcessor` 按文件事务发布，支持一个或多个可用且能无冲突合并的
  import、实际 `typedecl`、已实现证明命令与文档命令；必须有最终 `end`。
  缺失或冲突 import、未实现声明、`sorry`、`accept_all` 和未闭合证明均失败，
  不发布 partial Theory；legacy 合并不授予 kernel accepted 权力。
- `SessionBuilder` 每轮重建 registry；缺失、冲突、成环和失败父项阻断后代，
  独立合法文件仍可发布。不是整个 session 的原子提交。
- `parse_term` 和类型 parser 必须完整消费；局部 binder 使用 Bound，错误
  注解不得覆盖原类型。仅搜索诊断可使用明确标记的 Incomplete 项。
- 两套 legacy proof 状态都要求实际 Strict/checked 证明、完整目标匹配及合法
  作用域导出。synthetic goal、Compat fact、未完成 `have` 不能用于结案。
- rewrite 返回覆盖全部端点的证书；ATP reconstruction 消费真实步骤，
  未知规则、名称冲突或错误公式直接失败，不回退本地搜索冒充 replay。
- `ArithSolver` 从 checked 目标创建待证状态，返回前校验完整命题及显式
  context 授权的假设。`arith_tac` 非空或零子目标不构成成功；无算术 basis
  的六类回归保持未证明，默认全局数据库集成覆盖另行保留。
- 上述 legacy 成功仍不是 `TrustedTheorem`，不得增加 sampled kernel 计数。

Rust THM 的类型/变量变换使用显式名称集合与 fresh index；旧 `(Name, Ty)` 列表
及连续分配索引 API 已移除。局部固定类型证明必须通过
`KernelRules::export_scope` 的原 scope 完整回放和空 local owner 重认证，
不能只改 stamp。回放的 typed-Free 授权及 bound checker 私有 context view
不是 owner 声明，不能从候选结果补授权。`generalize`、`incr_indexes`
不清除 S/C/F/pending；具体实例化遗留的 extra sort 仍须受检 `strip_shyps`。
`native_thm_variables` 是独立的双类型 Rust consumer，不增加 sampled 125 计数；
接口/验证边界见 [THM 清单](docs/status/NATIVE_THM_INTERFACE_INVENTORY.md)。

工程质量修复使用 `CompositionOptions` 汇集 composition 参数，subgoal index
仍为 1-based；`ObserverHostInputs` 只是证据输入数据，不授予认证权力。
import 阻塞采用 `DependencyError`，仍失败且不发布 theory。
ML/host 错误的紧凑存储必须保留异常身份、诊断和取消语义。
本轮质量门与剩余兼容性边界见
[工程修复记录](docs/status/PROJECT_STATUS.md#engineering-quality-repair-2026-10-19)。

## Explicit Near-Term Exclusions

`KernelTrustedClosed: 1/125` is a narrow sampled milestone, not authorization
for general HOL/Isar acceptance or unrestricted platform claims.

- `HOL::trans`, `hol_subst`, or a second theorem adapter;
- theorem-specific `ThmKernel::hol_*` or `KernelRules::hol_*` constructors;
- general simp/unfolding as a shortcut for `TrueI`;
- promotion of `hol_object_refl` or `true_def_transport` into the final TCB;
- broad HOL/Isar command coverage, further workspace/session extraction, APP, LSP, WASM, or PIDE work;
- Burn, CubeCL, GPU, or multi-backend dependencies in the kernel.

Source-shape metadata remains a transitional guard for the legacy loader.
The strict source parser and elaborator use explicit declarations and
`CProp` certification instead; `SourceId` and spans remain diagnostic only.
Independent legacy lemma statements retain raw proposition text in
`DefLocation`; truncated quoted statements and contextual/compound propositions
cannot supply a complete source proposition to checked elaboration. This is
provenance, not accepted proof authority.

## Warning Policy

- `isabelle-kernel` (TCB): **zero warnings** enforced by `RUSTFLAGS="-D warnings"` in the strict gate.
- Root crate: warnings tracked as baseline; no net-new warnings per commit.
- Never restore `#![allow(warnings)]` crate-wide. Use targeted `#[allow(dead_code)]` with reason comments.

## Agent and Review Workflow

Apply [SCOPE → DESIGN → IMPLEMENT → REVIEW → VERIFY → DELIVER](docs/guides/DEVELOPMENT.md#engineering-workflow).
That guide owns task planning, review triggers, evidence selection and
confirmation boundaries; `.claude/` routes to it instead of defining another
lifecycle. Preserve user work and obtain explicit approval for destructive
operations or material changes in scope/risk. Parsed adapter metadata is not
proof that a harness loaded or enforced its configuration.

Use a hybrid workflow where useful:

- Oh My Pi may be the primary harness for long-lived context, LSP, structured
  edits, independent worktrees, and read-only audit fan-out.
- Codex-compatible models or CLI sessions remain useful for bounded
  implementation slices, adversarial review, and independent reproduction.
- High-risk TCB changes should not rely on the implementer as the only reviewer.
- Parallel agents may inspect independent areas, but shared TCB contracts are
  decided before parallel edits. Do not create worktrees without user authorization.
- The parent agent fixes shared interfaces and invariants before delegation,
  then fans out genuinely independent slices in one batch; do not serialize a
  lone subagent while the parent waits idle.
- Parallel workers must not edit the same trust-sensitive files. Give each
  worker explicit, disjoint paths and acceptance criteria.
- Workers skip builds, tests, linters, and formatters while edits are in flight.
  The parent integrates the results and owns verification of the final tree.
- Repository code, tests, and ADRs remain authoritative over harness memory.

### Cross-Harness Data Handoffs

Independent review is not authorization to send data to another provider.
Prefer the currently authorized environment. Before introducing an external
provider outside that authorization, identify the recipient, data scope,
retention and permission boundary, and obtain explicit approval.
Send only task-required, redacted material; exclude credentials, environment
secrets, full session transcripts and unrelated user work. Ignored files and
harness metadata are not access controls or data-transfer permission.

Never commit, amend, rebase, push, or rewrite history automatically unless the
user explicitly requests it. Preserve unrelated work and report dirty state.

## Dependency and Commit Hygiene

Project-authored code, tests, automation, documentation and templates use
Apache-2.0 except where a file or component states otherwise. See root
[NOTICE](NOTICE) and [THIRD_PARTY_LICENSES](THIRD_PARTY_LICENSES): actual upstream
materials retain their applicable terms. Record sources and attribution without
inferring project-wide originality, derivative-work status or legal compliance
from implementation language, API use, license metadata or passing checks.
Keep the two library crates' `LICENSE`/`NOTICE` copies synchronized with the root
files. Release `package` embeds the root legal texts at xtask build time;
dependency notice obligations remain separate.

`Cargo.lock` and `isabelle-source` are never incidental changes.

- Modify them only when explicitly in scope.
- A lock-only dependency refresh needs an explicit dependency/security rationale
  and must pass locked metadata/build checks.
- If no manifest or intentional dependency update explains lockfile drift, drop
  it rather than mixing it into trust-boundary work.
- Keep dependency/vendor changes separate from kernel, parser, metrics, tests,
  and documentation commits.

The `isabelle-source` Gitlink is rebaselined to the official Isabelle2025
Git mirror release commit `765fb2460a57eb46e8490283241ad46f1fac857f`
via `.gitmodules`. Initialize it for Gitlink-based diagnostics and upstream
source checks, not for the bundled five-file `core` sampler; the former
`c8d07caca5f6b9dd351de18a7ee25d2fa0e61ab8` checkout is unavailable.
The 2026-10-03 core run reproduced `1/125` transitional and `0/125`
kernel-trusted totals against the then-pinned source. The current sampled
test instead reads bundled `theories/HOL/` and records `0/125` transitional,
`1/125` kernel-trusted after the source-backed TrueI cutover. The separate
Tier2 run returned green while reporting `0/3872` proved, 3872 axiom-accepted
and four timeouts; it is not a successful theory build. The bundled
`theories/` files are a different snapshot, not a replacement for the Gitlink.

For trusted-boundary work, prefer reviewable responsibility splits:

1. parser/dispatcher boundary hardening;
2. outcome model and reporting;
3. attack/regression tests;
4. architecture, status, and agent documentation.

## Documentation and Templates

Short explanatory Rust, TOML, JSON and command examples are allowed when
they clarify a local contract. Do not duplicate runnable scripts in Markdown.

- all maintained automation, including audits and script tests, lives in `xtask/`;
- `scripts/` retains official reference probe inputs and classified templates;
- every template is classified in `scripts/templates/README.md`;
- standalone template compilation proves only local syntactic/type
  self-consistency, not compatibility with the production project API;
- `cargo +stable xtask snippets` enforces size and duplication limits, not
  semantic correctness.

Update code, tests, trust/status docs, ADRs, and agent guidance together when a
trusted boundary changes. Historical snapshots and changelog entries should be
marked historical rather than rewritten as current status.

## Verification

Use repository-owned entry points:

- docs or agent guidance: `cargo +stable xtask docs`;
- kernel, theorem acceptance, replay, or trust semantics:
  `cargo +stable xtask strict`;
- sampled HOL regression: `cargo +stable xtask core`;
- integrated delivery: `cargo +stable xtask verify` for the complete repository
  code/test matrix, followed by independent security/global gates;
- broader theory statistics: explicitly run `tier2`, `tier3`, or `broad`
  under supervision, not as default regression tests.

`xtask/` owns typed orchestration without depending on the product or kernel.
The four-member workspace defaults to the root product; explicitly run
`cargo +stable xtask selftest` and `cargo +stable xtask test` for tool and workspace tests.
Use outer `+stable` for canonical gates; leaf Cargo inherits `CARGO`.
`all` remains scoped and includes expensive tier diagnostics, not full validation.
Only supervisor-directed INT/TERM or its timeout promises existing cleanup;
termination of the Cargo/xtask parent alone does not promise signal cascading.

Run the task-matched behavior proof, project gates and then the complete
`~/.omp/agent/validate.sh` from the repository root; `--quick` is not delivery
evidence. The strict gate includes wrong-context and deterministic-identity
attacks, but does not replace workspace regression or the global gate.

The [current delivery record](docs/status/PROJECT_STATUS.md#current-delivery-state)
separates automation, product, trust and global-gate evidence. Native P2/P3/P4
implementation has explicit authorization but still requires complete replay,
independent review and closure verification. The known solver cleanup blocker
prohibits further solver launches until the host prerequisite is recovered;
do not weaken its isolation or claim a successful cleanup.
Older failures and OOM/timeout results remain dated history, not current
full-gate evidence.

Eight report-only HOL workloads now use the explicit, bounded
`isabelle-scale-hol` modes documented in `scripts/README.md` (the previous six
plus Tier 2/3; not all scale modes). `cargo +stable xtask tier2`/`tier3`
builds the locked worker and runs with a default 600-second wall deadline and
4096 MiB per-process address-space limit, overridable via
`HOL_DIAGNOSTIC_TIMEOUT_SECS` / `HOL_DIAGNOSTIC_MEMORY_MIB`. Each invocation
prints its new output directory; read `stderr.log` and `supervisor.json`.
No new ignores replace tests. The 125-theorem sampler, global HOL database,
functional/trust assertions, and nine official HOL files' no-`SyntaxError`
compatibility checks remain in the default suite. Report regression results
and opt-in diagnostic outcomes separately; completion is not a theory build
or proof, and timeout is not completion.

The earlier targeted `benches/kernel_benchmarks.rs` fix enabled an
all-targets check at that historical checkpoint; see `docs/kernel/BASELINE.md`.
It is not evidence that the current checkout builds. Current results belong
in [Project Status](docs/status/PROJECT_STATUS.md#current-delivery-state).

