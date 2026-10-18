# Changelog

Notable changes to isabelle-rs. Entries below tagged releases are historical
claims made at that time, not current proof metrics or compatibility promises.
Current outcomes and verification limits are maintained in
[Project Status](docs/status/PROJECT_STATUS.md).

## [Unreleased]

### Stable dependencies and CI repair (2026-10-19)
- Update all direct registry dependencies to the reviewed latest stable
  releases, including Wasmtime 49.0.3, rusqlite 0.40.2, Rowan 0.17.0,
  RustCrypto SHA-1/SHA-2 0.11, Criterion 0.8.2, signal-hook 0.4.5,
  lzma-rust2 0.23.0 and zstd 0.14.3. Preserve the fixed Isabelle2025 source.
- Preserve digest encodings with `base16ct` outside the TCB and retain checked
  unsigned SQLite conversions through `fallible_uint`.
- Optimize only development-profile SHA-256 after measuring executable
  hashing as the worker startup bottleneck; retain identity checks and deadlines.
- Repair Linux/Unix reference compilation boundaries and reject unsupported
  secure offline imports without a less-safe file-access fallback.
- Update CI action and security-tool versions, retain full advisory scope,
  and share a fail-closed Linux namespace prerequisite check.
- Read launcher diagnostics through a retained descriptor so worker log
  replacement cannot block supervision or disclose a symlink target.
  Local, remote and compatibility results remain separate in Project Status.

### Engineering quality repair (2026-10-19)
- Upgrade the xtask ZIP dependency to locked `9.0.5` for
  RUSTSEC-2026-0367, RUSTSEC-2026-0368 and RUSTSEC-2026-0369; retain
  existing archive contents, permissions, features and no-overwrite behavior.
- Group composition and observer inputs without changing proof replay or
  evidence authority; migrate every caller to the new public input types.
- Reduce ML and nested host-error payload sizes while retaining exception,
  source, cancellation and failure information.
- Classify blocked theory imports as dependency failures instead of syntax
  errors, retaining fail-closed loading and the official-source parser checks.
- Use PATH-resolved tools in supervision fixtures; repair workspace formatting,
  strict lints and unused code without adding suppression or ignoring tests.
  Actual delivery results remain in Project Status; native compatibility and
  the real solver cleanup prerequisite are separate gates.

### Legal wording clarification (2026-10-19)
- Separate project maintenance and license declarations from legal conclusions
  about originality, ownership, derivative-work status or non-infringement.
- Align English/Chinese reader guidance and all three project NOTICE copies;
  retain license texts, copyright notices and third-party terms unchanged.
- Clarify that ISIP is a project proposal, without claiming external standards
  adoption or official Isabelle endorsement; retain its name and design goals.
- Distinguish source and binary redistribution checks; packaging and quality
  gates are not legal-compliance certification. No dependency, product behavior,
  release permission or license selection changes.

### Documentation and workflow refresh (2026-10-19)
- Align English/Chinese entrypoints, current status, roadmap and agent routing
  with resumed-but-unaccepted native Pure/ML work, scoped Rust THM consumers
  and the four-package workspace.
- Mark local official reference preparation/build/inventory as disabled by the
  JVM-free policy; preserve offline comparison and the solver cleanup blocker.
- Keep the existing native Rust xtask workflow, distinguish executable
  orchestration from short examples, design templates and upstream ML probes,
  and document the actual limits of snippet/link/template checks.
- Record the actual native ROOT stop at `PolyML.objSize` in `ml_heap.ML`,
  separate Rust THM mappings from ML acceptance, and delimit the old resolution
  wrapper and WASM resource/proposal claims.
- Add dependency-ordered delivery stages with explicit quality, source execution,
  replay, offline compatibility, solver and redistribution exit conditions.
- Correct the demo's stale TCB description without changing proof or execution
  semantics. Keep historical results separate from current verification;
  dependencies and CI release gates are unchanged.

The earlier unreleased entries below retain their original checkpoint scope.
They may describe subsequently disabled commands or then-paused work; current
execution policy and gate results are owned by Project Status, not those entries.

### Project licensing and distribution notices
- Apply shared Apache-2.0 Cargo metadata to all four workspace packages,
  including xtask, and ship portable LICENSE/NOTICE files with both libraries.
- Record the project's Apache declaration separately from bundled Isabelle
  sources and copied upstream excerpts, whose applicable terms are retained.
  This is not a project-wide originality or ownership determination.
- Include project and identified Isabelle legal texts in release archives,
  preserving their exact bytes and non-executable permissions. This is not
  a complete dependency notice inventory or redistribution compliance claim.
- Align the two zstd dependency license exceptions with the existing lockfile;
  dependency versions and the global license/advisory policy remain unchanged.

### Native ML semantic and offline evidence repairs
- Bind internal callback type evidence to its certified argument position,
  including distinct polymorphic uses of the same closure; preserve the public
  untyped-call rejection boundary.
- Revoke foreign callable invocations before type lookup and both FileHostBridge
  runtime domains on a binding mismatch. Preserve ordinary exception packets,
  reporter results and ref effects without making fatal/permission stops catchable.
- Align bootstrap frame/load decoding and registration verification with the
  producer, accept hash-checked empty source reads, and retain incomplete results
  for unsealed loads or missing named members. These are native/offline repairs,
  not new official reference or theorem acceptance evidence.

### Integrated verification and source-quality repairs
- Added `cargo +stable xtask verify` as the complete repository matrix, including
  strict workspace/all-targets lint, locked compilation, TCB checks, documentation
  gates and the full workspace regression suite with failure aggregation.
  CI uses this matrix and independent required security scans; `release-check`
  now checks the version then runs `verify`, not Tier diagnostics.
- Repaired missing `Sort` imports and kernel Clippy issues without adding proof
  rules. `KernelError::MixedContext` retains complete expected/actual context
  stamps in boxed error-only payloads.
- Fixed theory-header handling of leading document headings and nested
  cartouches; executable preambles remain rejected. Unsupported theory
  declarations/imports/proofs still fail closed.
- Refreshed the documentation and harness routes around one workflow and test
  ownership model. Quality verification does not accept paused P2/P3 native
  compatibility; actual outcomes remain in Project Status.

### Native Rust maintenance automation
- Replaced maintained Shell/PowerShell/Python automation and script tests with
  Rust `cargo +stable xtask` commands: documentation checks, firewall and compat
  audits, `fix`, local `install`, supervised diagnostics, reference preparation/
  observation, editor reminder hooks, and release `package`. The existing
  checkout and Rust/Cargo are prerequisites; installation does not
  download/upgrade Rust, pull sources or copy binaries onto PATH.
- Official reference Isabelle/ML observer input is still executed only by the
  official runtime. Design templates and reference inputs remain in `scripts/`,
  not as alternative runnable project scripts.
- Re-executed the pinned official Pure/HOL build and nine-root inventory through
  the migrated Rust commands. Both exited successfully with zero trace-decoder
  errors; unresolved observations remain explicit and the original frozen
  reference snapshot is unchanged. This is not native Rust HOL acceptance.
- The initial automation-only verification passed independent selftests and
  strict xtask Clippy, frozen reference decoding/comparison and real trace/hook
  smokes. Full-project compilation, formatting, strict Clippy and regression
  were blocked at that stage; see the dated
  [migration record](docs/status/PROJECT_STATUS.md#native-rust-automation-verification-2026-10-14).
  Earlier sampled and official reference results remain separate evidence.

### Isolated Isabelle2025 Reference Baseline
- Added `xtask reference prepare|build|inventory` with a pinned distribution,
  fixed-source copy, private environment, no-network namespace, explicit build
  artifact selection and bounded subprocess lifecycle.
- Actually rebuilt Pure/HOL and executed the nine-root observer session.
  Exported structured declarations/facts, source-bound command and ML inputs,
  axiom provenance, public interface declarations and bootstrap requirements.
  The frozen reference snapshot preserves gaps and grants no Rust authority.
- Recorded real `veriT` use as a production permission/design gate. Official
  success does not fix the existing compatibility/Clippy failures, complete
  native closure execution or change the sampled `KernelTrustedClosed: 1/125`.

### Documentation and Workflow Synchronization
- Unified first-party documentation and `.claude/` routing around the
  SCOPE → DESIGN → IMPLEMENT → REVIEW → VERIFY → DELIVER lifecycle.
  A–H delivery packages and historical trust phases remain separate.
- Corrected stale sampled counts, legacy-versus-strict admission language,
  already-implemented search/process repairs and the post-xtask status.
  A is implemented; B's capability/reference baseline is next, not delivered.
- Distinguished scoped `strict`/`all`/CI lint, workspace regression and the
  complete global validator. Known compatibility and strict-Clippy failures
  remain blockers; historical evidence is preserved with its original scope.
- Updated skill/configuration descriptions and reader routes without changing
  product proof behavior, dependency versions, CI execution policy or hook
  implementation. Parsing harness metadata does not prove runtime enforcement.

### Typed Build Automation
- Added an independent `xtask` workspace member with locked build/check/test,
  strict/core/docs gates, explicit selftests, audits, and version/release checks.
  The workspace still defaults to the root product; kernel dependencies are
  unchanged. This does not add proof rules or official Isabelle compatibility.
- Migrated CI, installers and active command guidance; removed the two replaced
  Shell orchestration scripts. Historical verification records retain the
  commands used at the time.
- Independent steps now aggregate failures; successful Cargo artifact records,
  not guessed target paths, bind supervised workers. The single-lemma `profile`
  entry supports the existing manifest workflow and paths containing spaces.
  Existing supervisor cancellation boundaries remain unchanged; killing the
  Cargo/xtask parent alone does not guarantee descendant cancellation.
- Fixed the kernel firewall's false-clean result on `rg` execution errors.
  Missing tools, scan errors, failed builds and blocked dependents fail visibly.

### Diagnostic and Regression Boundaries
- Moved eight report-only HOL workloads from default tests to explicit
  `isabelle-scale-hol` modes (six earlier migrations plus Tier 2/3, not all
  available scale modes). Tier 2 retains its active file sequence, per-file
  deadlines, adaptive `AUTO_LIMIT`, trust classifications and statistics;
  Tier 3 retains its 30 paths and aggregate statistics without a new per-file
  budget. Kept the 125-theorem core, global HOL database, functional/trust
  assertions and nine official HOL files' no-`SyntaxError` compatibility
  checks in the regression suite. No new ignores were added.
- `cargo +stable xtask tier2`/`tier3` builds the locked worker, then supervises
  each diagnostic with a default 600-second wall deadline and 4096 MiB
  per-process address-space limit, overridable with
  `HOL_DIAGNOSTIC_TIMEOUT_SECS` / `HOL_DIAGNOSTIC_MEMORY_MIB`. Each run prints
  its fresh output directory for `stderr.log` and `supervisor.json`; `broad`
  runs `core`, `tier2`, `tier3` in order and aggregates independent failures.
  At the time, direct `scripts/profile-hol.sh --scale-mode` required explicit
  budgets and provided namespace cleanup; this historical script was replaced
  by native Rust `cargo +stable xtask supervise --worker PATH ...`. Completion
  is not a theory build or proof; timeout is incomplete.
- Avoided redundant formal-comment prefix scans on ordinary source
  characters, preserving all existing ASCII/Unicode masking behavior.
- Replaced six nonempty-result arithmetic tests with checked, isolated
  proof-contract regressions while retaining default global HOL DB coverage.
  `ArithSolver` now starts from a checked obligation and validates the complete
  result and authorized hypotheses, rather than returning a self-assumption as
  a proof. No arithmetic basis, search-budget cut, or accepted token was added.
- Kept malformed lexical suffix checks at the span layer and moved `end ?`
  rejection coverage to strict whole-file acceptance and legacy transaction
  rollback. Method punctuation remains lexically valid; production parsing
  and theorem authority are unchanged.
- Fixed public Rust doctest imports and marked six Isabelle formula examples as
  `text`, preserving their documentation without compiling them as Rust. Added
  no `ignore` or `no_run` workaround.

### Experimental Process Isolation
- Moved built-in LSP and Session document checks and LSP definition lookups
  into one supervised, reusable compute child; bounded and versioned IPC
  carries diagnostics and proof-state display data only.
- Required an explicit trusted worker executable from embedded LSP/Session
  callers. Cancellation and shutdown reap the direct child and report cleanup
  failures; fatal worker failure ends pending definition requests with errors.
  Timed-out Session checks do not expose stale proof state. Serialize shared
  snapshot goals without pre-frame duplication, returning an unavailable
  diagnostic when the bounded response is too large.
- Preserved Session cleanup failures across cancelled replies and shutdown
  join timeouts. Record worker-side failures even if the owning pool detached.
- Custom executors remain cooperative; the child is not an OS memory or
  privilege sandbox.

### Earlier Engineering Changes
- Removed global `#![allow(dead_code, unused_variables, unused_imports,
  unreachable_patterns, unused_comparisons)]` from `src/lib.rs`. Dead code in
  intentionally stubbed modules (HOL inference rules, BNF infrastructure,
  ATP proof reconstruction, linear arithmetic) now carries targeted
  `#![allow(dead_code)]` with rationale comments. Test-only imports use
  `#[cfg(test)]`.
- Fixed CI self-consistency: 14 known-failure tests marked `#[ignore]` with
  reason strings, advisory `cargo test -- --ignored` step added to CI,
  `--all-targets` compilation gate added to CI.
- Moved `proptest` from `[dependencies]` to `[dev-dependencies]`.

### Quality Gate Remediation
- Removed unused first-party paths and corrected linted ownership, parsing,
  error-size, and public module-export shapes without promoting legacy proofs
  to trusted tokens; `SessionError` remains publicly matchable.
- Added a repository-local single-thread/stack default for Cargo tests, keeping
  all library and integration tests in the quality gate.
- Scoped a gitleaks function-text false positive and accepted 13 vulnerable
  upstream editor-lockfile entries for Rust verification only. The latter are
  still vulnerabilities; both exceptions require review by 2026-11-03 or on
  upstream Gitlink change and are invalid for editor/VSIX delivery.

### Trust Boundary
- Added explicit strict type-constructor declarations and arity validation to
  certification and `SignatureId` v2 snapshots; old digests do not authorize
  reconstructed signatures.
- Validate all basis axiom schemas before installation and share conservative
  definition checks between construction and exact-owner replay. Binder replay
  scopes Free variables in premises only; ancestor token payloads are checked.
- Support the standalone Pure source `!!P::prop. PROP P ==> PROP P` with
  `by assumption`; reject the old `impI` spelling. Both this fixture and HOL
  `TrueI` return accepted tokens, outside the sampled 125-theorem batch.
- Make complete legacy theory loading a fail-closed file transaction. Real type
  declarations persist; unsupported commands, missing/failed imports, unfinished
  proofs, and trailing input cannot publish partial theories.
- Require full term consumption and correct binder indices; proof completion
  validates actual Strict/checked results, complete goals and scoped assumptions.
- Require full rewrite certificates and validated automation/ATP steps; malformed
  replay cannot fall back to local search and claim successful reconstruction.
- Renamed the sampled legacy strict metric to `TransitionalStrictClosed` and
  introduced the separate `KernelTrustedClosed` metric. The bundled five-file
  sampler currently reports `0/125` transitional and `1/125` kernel-trusted:
  the audited real-source `HOL::TrueI` projection, not a general HOL compiler.
- Hardened the registered `HOL::TrueI` path so explicit strict adapters run
  before compatibility parser-gap fallbacks and reject free, dummy-typed,
  malformed, contextual, or unverifiable source propositions without legacy
  fallback.
- Added attack coverage for the existing new-kernel `CProp : prop` boundary;
  HOL `bool` terms are not valid theorem propositions without `HOL.Trueprop`.
- Added deterministic, domain-separated `SignatureId` and ancestry-sensitive
  `TheoryId` values. Immutable context stamps now propagate through strict
  certification, theorem construction, every current kernel rule, and replay;
  mixed signatures/theories and stale certified objects fail before logical
  matching.
- Replaced mutable strict signature declaration with checked immutable
  extension, including duplicate/conflict rejection, parent/sibling isolation,
  and digest verification for untrusted signature snapshots.
- Added one context-bound `accept_closed_theorem` gate with recursive
  owner-parameterized replay, replay-derived theorem dependencies,
  duplicate-safe immutable fact insertion, and a sealed `TrustedTheorem`.
  Ancestor facts are reusable only through the checked theorem-reference rule.
- Clarified that replay-derived `DependencySet` entries are logical theorem
  identities, not authority. Exact `(id, name, accepted_in)` tokens remain
  ancestry-checked, including equal-content sibling facts.
- Added a parser-independent source proposition AST with raw unresolved names
  and syntax, grouping, binders, source type annotations, half-open byte spans,
  and compile-fail barriers against trusted-context or theorem conversion.
- Made `KernelTrustedClosed` a mutually exclusive token-owning `ProofOutcome`.
  `verify_lemma` now returns explicit accepted/legacy evidence; classification
  no longer reads ambient thread-local outcome state.
- Routed theory-scan diagnostics through `ProofOutcome`, so admitted or
  axiom-accepted theorem-shaped values no longer display as transitional
  successes.
- Split registered document commands and keep experimental LSP theorem
  declarations pending; the document layer does not classify a declaration as
  verified before it can retain and check the complete proof block.

### Experimental LSP
- Bounded open-document, command, diagnostic, snapshot and response admission;
  one shared CPU worker handles document checks and HOL definition lookups
  without blocking protocol dispatch. Revision replacement, invalidation,
  close and shutdown cancel queued queries; an outstanding duplicate request
  ID ends the original query with one error.
- Bounded the per-thread symbol cache and moved production HOL loading progress
  to best-effort nonblocking logging. At this pre-process-cutover checkpoint,
  running legacy commands and global HOL DB initialization could not be
  preempted; quotas did not provide a hard CPU/RSS budget or a trusted runtime.

### Scripts (Earlier Unreleased Steps)
- Added a separate manifest-replay HOL diagnostic worker and Linux/GNU
  supervisor with explicit wall/CPU/address-space/file-size limits, flushed
  stage events, private output directories, and namespace descendant reaping.
  Replay captures the full bootstrap context and legacy first-200 source
  selection; it adds neither proof authority nor a full-suite success claim.
- Previously added `scripts/dev-check.sh` as the shared verification entry.
  It was subsequently removed by the xtask cutover above; this is historical,
  not the current command.
- Added Markdown size/duplication auditing, standalone compilation checks for
  explicitly design-only Rust templates, and a compatibility-callsite audit.
  Short explanatory blocks remain allowed; template compilation does not prove
  production API compatibility.
- Centralized reusable commands under `scripts/` and reusable design/examples
  under classified `scripts/templates/`.
- Kept all build/check/install paths on the committed lockfile. Local installer
  runs now use the current checkout without pulling another branch.
- Added the immutable context-identity attack suite to the strict kernel gate.
- Added the trusted-acceptance attack suite and strict public-boundary
  compile-fail doctests to the strict kernel gate.
- Audited baseline `38c5f14` and every candidate commit independently. Normal
  locked checks and strict gates pass; `--all-targets` had four pre-existing
  benchmark compile errors at every revision. Those are now fixed
  (`ThmKernel::assume` unwrap, `pub(crate)` `check_proof` → public
  `replay_proof`); the gate is green.
- GitHub releases require a tag matching `Cargo.toml` and the scoped
  repository-owned release matrix before platform artifacts are built.
  That workflow is not the complete local quality gate.

### Verification Limits (Historical 2026-10-07 Checkpoint)
- The 2026-10-07 strict gate passed 615 tests and 11 effective doctests, with
  one existing ignored example. The five-theory sampler reported `0/125`
  transitional and `1/125` kernel-trusted; no broader HOL acceptance follows.
- Scoped secrets and dependency audits passed in a bounded shared-validator
  attempt. A separate locked root Clippy run passed after six lint fixes; the
  shared validator at that checkpoint still lacked a full test result. Prior
  full tests were OOM-killed, a single-thread run timed out after 3600 seconds,
  and the 2026-10-07 attempt exceeded a 900-second wall limit. The later
  [A-package run](docs/status/PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11)
  completed workspace testing with the official-source regression failure.
  Neither record establishes full-suite success or an official runtime differential.

### Docs
- Repositioned the project as a Rust research prototype of an
  Isabelle/Pure-inspired LCF kernel with explicit oracle footprints,
  closed-theorem acceptance, and minimal proofterm replay.
- Established `docs/status/PROJECT_STATUS.md` as the canonical high-level status.
- Rewrote README, architecture, trust, gap-analysis, development, roadmap, and
  session-transfer docs to distinguish full Isabelle parity from the narrower
  trusted-kernel research slice.
- Separated measured trust outcomes from subjective historical completion
  estimates. Later narrow source elaboration, logic-basis, conservative-definition
  and acceptance paths are implemented; sampled integration and broad coverage
  remain incomplete.
- Added root `AGENTS.md` as the harness-neutral authority and
  `docs/kernel/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md` as the source-audited acceptance
  inventory and remaining sampled-integration plan.
- Added the repository-root Apache-2.0 license declared by `Cargo.toml`; bundled
  Isabelle theory sources retain their separate upstream license.
- Added the checked HOL proposition normalization contract and proposed HOL
  logic trusted-extension ADR. No `HOL::trans` adapter or HOL substitution
  primitive was added.
- Updated Isabelle-rs-specific `~/.codex` references, rules, and skills to use
  the corrected metrics, priorities, and centralized scripts.
- Synchronized first-party English/Chinese summaries, kernel/design/ADR/ISIP
  status, contributor workflows, and relocated links. Historical releases and
  archived assessments are retained as history, not rewritten as current results.

## [2.2.1] — 2026-06-21

### Docs
- **全项目文档审计 + 同步** —— 修正残留的过时引用,统一证明率口径:
  - `docs/ARCHITECTURE.md`:删除残留的 "Tier2 97/97 3821/3821 (100%)" 虚高声明,
    改为真实证明率 85.8% (3277/3821);header v25.0→v26.0;LCF 内核加 oracle 信任足迹。
  - `README.md`:项目状态版本 v2.1.5→v2.2.0,加真实证明率/信任模型行,链接 TRUST.md。
  - `.claude/skills/bench.md`:frontmatter + Expected Results 版本 → v2.2.0。
- 全 doc 扫描确认:无任何**当前状态**仍宣称 "100% verified"(历史记录如实保留)。
- 纯文档变更,零代码改动;kernel/trust 22/22、fmt、clippy 0 errors 全通过。

---

## [2.2.0] — 2026-06-21

### 🔒 信任工程 (Trust Engineering) — 本版本主题

诚实化:把"Tier2 100% verified"的虚高指标,变成由类型系统保证的**真实证明率**。

### Added
- **T3 信任足迹 (oracle tracking)** — `Thm` 新增 `oracles: Vec<Arc<str>>` 字段,
  像 `hyps` 一样通过全部 15 条内核规则**并集传播**。真证明 → 足迹空;admitted → 含标记。
- **`ThmKernel::admit(ct, name)`** — 内核唯一的"接受命题而不证明"入口(对应 Isabelle
  `sorry`/oracle)。返回的定理 `!is_fully_proved()`,且污点随推导传染。
- **`Thm::is_fully_proved()` / `Thm::oracles()`** — 判定与查询信任足迹的公开 API。
- **`docs/TRUST.md`** — 完整信任模型:de Bruijn T1-T4 性质、达成度、可信路线 A/B。
- **`verify_file_diagnostic`** — 暴露每条引理 (name, proof_script, is_proved),
  由 T3 足迹派生;用于分析 admitted 引理的真实瓶颈。
- 14 个内核/信任单元测试(T3 footprint ×4、T2 shyps/alpha_eq/combination ×6、
  T1 stub-admitted ×2、capture 等)。
- Tier2 harness 打印 `REAL PROOF RATE`(由 `is_fully_proved()` 派生)。

### Changed
- **T2 内核可靠性加固**(每项配回归测试,core 125/125 + Tier2 85.8% 不回退):
  - `tpairs`/`shyps` 改为并集传播(`union_tpairs`/`union_shyps`)——修 12 条规则的
    静默丢弃。当前恒空无现行不可靠,接入完整高阶合一后才咬人;零行为风险预防。
  - `alpha_eq` Branch C:`Abs` 加 binder 类型守卫——`λ(x:nat).x ≢ λ(x:bool).x`,
    dummy 容忍(parser 现状),已知不同类型拒绝。
  - `combination` 澄清+测试:congruence 规则对任意类型逻辑可靠,dummy 跳过非 bug。
- **T1 不可伪造:假定理后门收口** —— `hol_rules`(11 连接词 stub)、`hol_consts`(3)、
  `core/conjunction`(2)中"产出结论形状却不从前提推导"的函数,过去用
  `ThmKernel::assume` 伪装成已证。现全部改用 `ThmKernel::admit(_, "*:STUB")`
  (输出 `!is_fully_proved()`,污点传播)并降为 `pub(crate)`。真实规则
  (mp/all_intr/all_elim/true_intr)保持 `pub`。全 src 扫描确认无 `pub` 伪造后门。
- **`verify_lemma` 的 axiom-accept fallback 改用 `admit`** — 旧版用 `ThmKernel::assume`
  把失败的引理伪装成 `P ⊢ P` 已证。现在路由经 `admit`,admitted 由类型系统标记。
- **`capture_proof` 修复**:`proof...qed` 块之前只捕获首行(`proof -`),丢弃整个 body;
  现在捕获完整平衡块(跟踪 proof/qed 嵌套)——结构化 Isar 回放的前提。
- **真实证明率公开:Tier2 = 85.8% (3277/3821 proved, 544 admitted)**,不再宣称 100%。
- 所有文档(README/CLAUDE/GAP_ANALYSIS/ROADMAP/DEVELOPMENT)证明率口径统一为
  `is_fully_proved()`。新增铁律 #20/#21:永不谎称证明;新路径不得绕过信任足迹。

### Fixed
- **指标失信根因** — `verify_lemma` 结构上对任何有证明脚本的引理恒返回 `Some`,导致
  "100%" 是数学保证而非测量结果。现已由 oracle 足迹如实区分 proved vs admitted。

### 诊断结论(指导后续)
- 544 admitted 的瓶颈是**结构性**的:结构化 `proof...qed` 回放(51%)、locale 上下文、
  `obtains` 语句——**不是缺 simp 规则集**。85.8% 是当前引擎的诚实平台期;推高需要
  结构化 Isar / locale / obtains 的独立工程(数天,可靠性敏感)。

### 战略
- 确立定位:**放弃追赶 Isabelle 广度(138 万行,97% 是 30 年理论库),押注「内核可信
  + 片段深度」**。Sledgehammer/CodeGen/SMT 战略上不追。
- **路线 A 务实可信(T1+T2部分+T3)基本完成:系统由类型系统保证永不说谎。**

---

## [2.1.5] — 2026-06-17

### Added
- **Phase 17: Tier2 Library expansion** — 27 new Library files verified at 100%
- 31 candidate files copied to `theories/HOL/Library/`, 27 verified (3821/3821 lemmas)
- Library coverage: Case_Converter, Centered_Division, Code_Bit_Shifts_for_Arithmetic,
  Code_Target_Int, Conditional_Parametricity, Confluence, Debug, Fraction_Field,
  Group_Closure, Groups_Big_Fun, ListVector, Order_Relation_More, Order_Union,
  Parallel, Rewrite, Signed_Division, Stirling, Transposition, Uprod,
  Diagonal_Subsequence, Fib, Going_To_Filter, Infinite_Typeclass, Nonpos_Ints,
  Periodic_Fun, Real_Mod, Code_Abstract_Char
- Tier2: 70→97 files, 3261→3821 lemmas, 154s→178s, 100% verified

### Known Issues
- 4 Library files pending: Product_Order (instantiation hang), Quotient_List,
  Sorted_Less (antiquotation), State_Monad (datatype hang)

## [1.8.1] — 2026-06-04

### Added
- **Phase 49: hologic.rs** — HOL abstract syntax operations, corresponds to Isabelle's `src/HOL/Tools/hologic.ML` (23K ML → ~580 lines Rust). Centralized: Trueprop/eq/conj/disj/imp/Not/All/Ex/mem/set/prod/nat/numeral/list/if/let constants + mk_*/dest_*/is_* API. 21 tests, all passing.
- **Phase 50: simpdata.rs** — HOL simplification data, corresponds to Isabelle's `src/HOL/Tools/simpdata.ML`. `init_hol_simpset()`, `mksimps_pairs()`, `mk_meta_eq()`, `mk_eq_True()`. Integrated built-in HOL connective rules into `exec_simp` method dispatch. 3 tests.
- `src/hol/hologic.rs` — 580 lines, 21 tests (Trueprop roundtrip, conj/disj/imp/not/eq/all/exists/nat/numeral/list/set/prod)
- `src/hol/simpdata.rs` — 290 lines, 3 tests (simp rules init, mksimps pairs, meta_eq)
- **Phase 51: args.rs** — method argument parsing, corresponds to Isabelle's `src/Pure/Isar/args.ML` (6.8K ML → ~310 lines Rust). `MethodArgs` struct, `Args` parser combinators: goal_spec parsing `[1]`/`[2-4]`/`[!]`, modifier clause extraction `add:`/`del:`/`only:`/`rule:`/`arbitrary:`/`intro:`/`elim:`/`dest:`/`simp:`, theorem name resolution. 18 tests, all passing.
- `src/isar/args.rs` — 310 lines, 18 tests
- **Phase 52: spec.rs enhanced** — `Definition`, `Axiomatization`, `Abbreviation` command parsers matching Isabelle's `specification.ML`. `is_new_command()` keyword detection. 18 tests, all passing.
- Tier2 verification: 6/20 files **100% verified** (Fun 190/190, Product_Type 166/166, Sum_Type 22/22, Lattices 91/91, Groups 157/157, Rings 276/276) — previously accept_all mode
- Fixed `depth -= 1` overflow in method.rs parse_method_list → `depth.saturating_sub(1)`
- `src/hol/defs.rs` — 275 lines, 6 tests (Phase 53: definition consistency checking)
- `src/isar/spec.rs` enhanced with `TypeAbbrev` parser (Phase 54: type_synonym support)

### Documentation
- **Consolidated all docs into `docs/`**: removed scattered root-level docs, merged redundant files
- `docs/ISABELLE_COMPARISON.md` merged into `docs/GAP_ANALYSIS.md` (now single source for Isabelle comparison)
- `PLAN_v1.9.0.md` merged into `docs/ROADMAP.md` (now contains detailed Phase 49-60 planning)
- `SESSION_TRANSFER.md` moved from root to `docs/SESSION_TRANSFER.md`
- `docs/DEVELOPMENT.md` trimmed — removed architecture/state redundancy (→ ARCHITECTURE.md)
- `docs/ARCHITECTURE.md` updated to v1.8.1 stats (5/5 core files, 27 methods, removed kernel/ refs)
- `README.md` updated from v1.2.0 to v1.8.1
- Skills updated: bench.md (v1.7.0→v1.8.1), verify.md (25→27 methods, overflow→passing), release.md (doc refs)
- Verified: 0 broken cross-references across all 20+ markdown files

### Fixed
- **🔴 List.thy stack overflow — ROOT CAUSE FIXED**: `prove_condition` in `src/core/simplifier.rs` had unbounded mutual recursion through `prove_condition → rewrite → try_rule → prove_condition`. Each `try_rule` call passed `depth=0`, bypassing the depth guard. Fixed by removing recursive `self.rewrite(cond)`/`self.rewrite_deep(cond)` calls from `prove_condition`, matching Isabelle's `simple_prover` design: `SINGLE o (fn ctxt => ALLGOALS (resolve_tac ctxt (prems_of ctxt)))` — only trivial `True` + external solver, no recursive conditional rewriting.
- `depth_search` safety cap: `bound > 20` returns None (was unbounded, only `bound == 0` terminated)

### Verification
- **All 5 core files 100% verified**: HOL (25/25), Orderings (25/25), Set (25/25), Nat (25/25), List (25/25). **125/125 total, previously List.thy overflowed even at 256MB stack.**
- List.thy verification: overflow → 25/25 in 0.8s (38x faster than the interim total-cap approach)

### Changed
- `prove_condition` simplified: no longer calls `self.rewrite()`/`self.rewrite_deep()` for conditional rule premises. Only checks trivial `True` and delegates to `condition_solver` (ArithSolver/AsmSolver/etc.)

### Unchanged
- `auto_exec`, `blast_exec`, `dfs_search`, `dfs_subgoals`, `step_exec`, `dup_step_exec` — confirmed NOT the root cause; these remain recursive with their existing depth caps (15, 15, 7, 7, 10, 12 respectively)

## [1.8.0] — 2026-06-04

### Added
- Meson model elimination prover for classical logic (275 lines, 4 tests)
- Method combinators: THEN, ORELSE (`|`), REPEAT (参考 Isabelle Seq.EVERY/FIRST/REPEAT1)
- Attribute application chain: [symmetric], [simplified], [folded def], [unfolded def], [rule_format]
- `verify_file()` — reusable 3-phase verification function (local DB, no global LazyLock init)
- Tier 2 verification: 20 files (Fun 190/190, Product_Type 166/166, Sum_Type 22/22)
- Tier 3 verification: 30 files ready
- `apply_attributes()` — unified attribute chaining
- `parse_single_method()` — method string parser for combinators
- Auto directive parser extended: `simp:`, `elim:`, `dest:`, `iff:`, `add:`, `del:` support
- Adaptive AUTO_LIMIT (50/80/200 per file size)

### Changed
- `bench_file()` — 3-phase local DB approach (no global LazyLock init)
- `parse_of_and_then_suffix()` — returns 4-tuple with other_attrs
- `exec_single_method()` — global SINGLE_METHOD_DEPTH guard (200 limit)
- `exec_proof_script()` — PROOF_SCRIPT_DEPTH guard (50 limit)
- `Term::Display` + `Term::Debug` — iterative, depth-limited (64)
- `auto`/`blast` execution bounded by adaptive AUTO_LIMIT

### Fixed
- `parse_attrs()` — bracket-aware splitting for compound attributes
- `auto simp: thm` directive — previously ignored, now resolves and applies
- `depth.saturating_sub(1)` — prevents subtraction underflow
- `ctr_sugar.rs` — `theorems.exhaust` move-after-use
- 2 compilation warnings → 0

### Removed
- `src/tools/auto.rs`, `src/tools/blast.rs` — empty stubs
- `src/kernel/` — duplicate of core/ (1,270 lines)
- Dead code in `ctr_sugar.rs`

### Infrastructure
- `.claude/` complete architecture: settings.json, commands/, agents/, hooks/, memory/, skills/
- 11 Claude Code skills with `skills.toml` registry
- `CLAUDE.md` project entry point

## [1.7.0] — 2026-06-03

### Added
- BNF Lfp/Gfp 完整重写: induction/coinduction/fold/rec/unfold/corec + map/set/rel/pred (27 tests)
- Ctr_Sugar: case/disc/sel/split/cong/nchotomy/size 定理生成
- Metis 消解证明器 + SAT 求解器 (DPLL/CDCL) + ATP 证明重放 (22 tests)
- Transfer/Lifting: TransferGenerator + RelatorDef + LiftingContext + QuotientType
- Claude Code skills: verify, benchmark, audit-kernel, theory-build, add-method, debug-stack-overflow, phase-release, refactor-module, add-isar-command, search-theorem
- CLAUDE.md 项目入口文件

### Changed
- `src/hol/bnf_lfp.rs`: 从 0 行 stub 重写为 1837 行完整实现
- `src/hol/ctr_sugar.rs`: 从 0 行 stub 重写为 1926 行完整实现
- `src/hol/transfer.rs`: 从 0 行 stub 重写为 1266 行完整实现
- `src/tools/metis.rs`: 新文件, 2305 行
- `src/tools/reconstruct.rs`: 新文件, 452 行
- `src/theory/thy_header.rs`: 新文件, 835 行

### Fixed
- ctr_sugar.rs: 修复 `theorems.exhaust` move-after-use 编译错误

### Known Issues
- test_batch_scan_theories 在 256MB 栈下溢出
- test_verify_all_core_files 在默认栈下溢出
- auto.rs/blast.rs 是空壳桩 (实际逻辑在 method.rs)
- metis 方法 → auto fallback (未真正集成)
- 属性系统 ([simp]/[intro!]/[elim!]) 集成不完整

## [1.5.0] — 2026-05-29

### Added
- thy_header 解析器 (Phase 40)
- HOL 简化器完整: 条件重写 + Solver 插件 (Phase 41)
- Fourier-Motzkin 线性算术求解器 (Phase 42)

## [1.3.0] — 2026-05-28

### Added
- IsarProof.apply() → proof engine 集成
- AUTO_LIMIT 深度限制

## [1.2.0] — 2026-05-27

### Added
- Phase 39: tpairs/shyps 实现
- Phase 38: 验证分类系统 (VerifyClassifier)

## [1.0.0] — 2026-05-26

### Added
- Phase 37: 属性测试基础设施 (26 proptests)
- Phase 36: CI/CD 基础设施 (GitHub Actions)

## [0.7.0] — 2026-05-20

### Added
- Phase 11-20: Isar 引擎完整 + Session/Build + CLI
- 三模式 IsarProof 状态机
- 25 证明方法

## [0.6.0] — 2026-05-15

### Added
- Phase 10.3-10.6: 经典推理器基础 + Isar 完善

## [0.5.0] — 2026-05-10

### Added
- Phase 9-10.2: TypeEnv/CTerm + Nets + Safe Rules

## [0.4.0] — 2026-05-01

### Added
- Phase 7-8: 完整 Method + 性能优化 (92.8%, 24× speedup)

## [0.3.0] — 2026-04-20

### Added
- Phase 5-6: 统一 + 重写 + 基本证明验证 (88%)

## [0.2.0] — 2026-04-10

### Added
- Phase 0-4: 内核基础 + Tactic + 基本 Method

## [0.1.0] — 2026-04-01

### Added
- 初始发布: LCF 内核原型
