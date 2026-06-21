# CLAUDE.md — Isabelle-rs

> **用 Rust 重写 Isabelle，打造更程序员友好的证明助手。**
>
> 功能与 Isabelle/ML 一致。错误信息 → Rust 编译器风格。工具链 → 标准 Rust 生态。
> LCF trusted kernel + higher-order unification + Isar proof language + theory loading pipeline.

## 分支策略

- **`main`** — 稳定发行分支。只通过 PR 从 `dev` 合并。每次 release 在此打 tag。
- **`dev`** — 开发分支。所有日常修改在此进行。功能完成后通过 PR 合并到 `main`。
- **工作流**: `dev` 上开发 → 测试通过 → PR → `main` → 打 tag 发布

## Project State (v2.2.0)

| Metric | Value |
|--------|-------|
| Kernel | 15 ops + tpairs/shyps + **oracle trust footprint (T3)**, unforgeable Thm |
| **Trust Model** | ✅ **T3 done**: `Thm::is_fully_proved()`/`oracles()`, `ThmKernel::admit`, union-propagated. See [docs/TRUST.md](docs/TRUST.md) |
| Proof Engine | Isar state machine (3 modes) + 27 proof methods |
| Classical Reasoner | best/depth/dup_step + three-stage safe rules |
| Arithmetic | Fourier-Motzkin variable elimination (nat/int linear) |
| HOL Simplifier | Conditional rewriting + solver plugins (ArithSolver, AsmSolver) |
| BNF Lfp/Gfp | Complete: induction/coinduction/fold/rec/unfold/corec + map/set/rel/pred |
| Ctr_Sugar | case/disc/sel/split/cong/nchotomy/size theorem generation |
| Meson | Model elimination prover — 1st-class proof method |
| Metis | Given-clause resolution prover — 1st-class, HOL.eq paramodulation ✅ |
| Transfer/Lifting | Transfer rule generation + rel_fun/rel_set + quotient type theorems |
| **hologic** | ✅ 40+ mk_*/dest_*/is_* functions, `dest_hol_equals`, 100→3 bare HOL const calls |
| **simpdata** | ✅ 28 built-in rules, `init_hol_simpset()`, core simpset (8 theories), cached |
| **args** | ✅ `Args::parse_modifiers()` wired into `exec_simp` + `exec_induct` |
| **spec** | ✅ Definition/Axiomatization/Abbreviation/TypeAbbrev/Typedecl parsers |
| **attrs** | ✅ class assumes + attrs_index + lemmas + declare |
| **deadline** | ✅ VERIFY_DEADLINE (7 checkpoints) + PROOF_SEARCH_BUDGET |
| Code | ~55K Rust LOC, 124+ files |
| Toolchain | Rust 1.96.0 stable (edition 2024) |
| Tests | 700+ (642 lib + 76 integration), incl. 4 trust-footprint tests |
| **Verification** | **Core 5/5 100% (125/125)**; **Tier2 真实证明率 85.8% (3277/3821 proved, 544 admitted)** |
| Time | Tier2 178s (3.0 min) — CI ✅ |
| isabelle-source | ✅ Isabelle 2025 full distribution (364MB, 1,473 .thy files) |

## 战略定位 (v2.2.0)

**取舍:放弃追赶 Isabelle 的广度,押注「内核可信 + 片段深度」。**
Isabelle 本体 ~138 万行 (758 .ML + 1843 .thy + 356 .scala),其中 97.6 万行是
30 年积累的理论库(Analysis/Algebra/Probability...),无法也无需复刻。差异化价值在于
做一个干净、内存安全、**诚实可信**、错误信息友好的 Rust HOL 核。

**可信路线:A 先行,B 为北极星** (见 [docs/TRUST.md](docs/TRUST.md))
- **A 务实可信** = T1 不可伪造 + T2 规则可靠 + T3 信任可追溯。系统永不说谎。
- **B 完全可信** = A + T4 独立证明项复检 (de Bruijn)。

| 阶段 | 内容 | 状态 |
|------|------|:--:|
| T3 信任足迹 | `Thm` oracle 追踪 + `admit` 入口 + 真实证明率仪表 | ✅ 已达成 |
| T2 内核加固 | tpairs/shyps 传播 + alpha_eq 收紧 + combination 类型检查 | 🟠 下一步 |
| T1 后门收口 | hol_rules/hol_consts 的假定理制造机降级/标记 | 🟠 待办 |
| 证明率攻坚 | 缩小 544 admitted (Rings 80 + Lattices_Big 63 + Complete_Lattices 25 ...) | 🟠 待办 |
| T4 独立复检 | proofterm.rs check_proof 补完并接通 | 🔴 北极星 |

## Active Strategy: v2.1.5 (历史)

```
Route A ✅ Complete:
1. ✅ Fix 5 failing tests
2. ✅ Fix OOM/stack overflow root causes
3. ✅ Tier2 verification: 36/36 files 100% (2959/2959 lemmas, 513s)
4. ✅ Attribute system (class assumes + attrs_index + lemmas + declare)
5. ✅ Full documentation sync

Phase 3 ✅ Performance:
3.1 ✅ Core simpset injection (8 theories: HOL→Groups→Rings, Rings 4x faster)
3.2 ✅ Memory-bounded search (PROOF_SEARCH_BUDGET + depth branch pruning)
3.3 ✅ Rewrite depth hard limit (MAX_REWRITE_DEPTH=40)

Phase 6-17 ✅ v2.1.5:
6. ✅ Tier2 expansion: 36→57 files (21 new from Library/Data_Structures, +236 lemmas)
7. ✅ Isar engine optimizations (get_premises ref, cached Simplifier, Conv Box→Arc)
8a. ✅ Metis HOL.eq paramodulation (dest_hol_equals)
16. ✅ Metis ∃-skolemization
17. ✅ Tier2 Library expansion: 70→97 files (+27 Library, 3821/3821, 100%, 178s)
```

## Known Issues

| Issue | Severity | Detail |
|-------|:--------:|--------|
| Fields.thy — structured Isar proof replay overhead | 🟡 Medium | 205 lemmas × multi-step proofs; needs IsarProof Arc-sharing (proof.rs) |
| Num.thy — same as Fields | 🟡 Medium | 354 simp calls, structured proofs |
| Hilbert_Choice/Transitive_Closure — auto/blast dense | 🟡 Medium | Memory-budget protected but slow; needs iterativized auto_exec |
| Finite_Set — large file (281 lemmas) | 🟡 Medium | 3h+ processing time; needs proof_state.rs caching |
| Partial_Function — memory explosion | 🟡 Medium | Deep fixpoint constructions |
| LazyLock DB init slow | 🟡 Medium | First HolTheoremDb::get() loads all 1,473 .thy files |
| 4 Library files (Product_Order et al.) — parsing hang | 🟡 Medium | instantiation/datatype/antiquotation parsing stalls |
| hologic constants (3 remaining) | 🟢 Low | Intentional: prop eq, term_builder, comment |


## Iron Laws

1. **`Thm` can only be constructed inside `src/core/thm.rs`** — use `ThmKernel` externally
2. **No `Typ::dummy()` in kernel inference rules** — use `CTerm::term_type()` or `Pure::dest_equals_with_type()`
3. **First step of every proof method must call `apply_safe_rules`** — O(log n) net lookup, matching-first → resolution fallback
4. **Rule lookup uses nets** — `db.intro_net().lookup()` not `db.intros`
5. **Deep recursion must be iterativized** — see `.claude/rules/iterative.md`
6. **After kernel/method changes, run full baseline** — `RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture`
7. **New data fields must update all constructors** — especially `ParsedLemma`, `ProofState`, `HolTheoremDb`
8. **Isar proof state machine: three modes** — Forward (configuration), Chain (linked), Backward (proving)
9. **Theory loading via `TheoryProcessor`** — parse .thy → command dispatch → LocalTheory → finalize
10. **`show` must record `refines`** — for `qed` parent goal refinement
11. **Theorem construction uses `CTerm::certify_annotated`** — auto-annotates types from TypeEnv
12. **`prove_condition` must NOT call `self.rewrite()` or `self.rewrite_deep()`** — this creates unbounded mutual recursion through `rewrite → try_rule → prove_condition`. Isabelle's `simple_prover` only does `ALLGOALS (resolve_tac ctxt (prems_of ctxt))`. Only trivial `True` + external `condition_solver` are safe. See `src/core/simplifier.rs:317-340`.
13. **After any src/ change, sync docs and .claude/** — run `/sync-docs` to update `docs/` (ARCHITECTURE, GAP_ANALYSIS, ROADMAP, DEVELOPMENT) and `.claude/` (CLAUDE.md, skills, settings). Any commit that touches src/ should also touch the relevant doc files.
14. **After every task completion, update ALL project documentation** — 每次完成任何任务/Phase/功能后，必须更新所有文档：`docs/` (ARCHITECTURE, GAP_ANALYSIS, ROADMAP, DEVELOPMENT) 和 `.claude/` (CLAUDE.md, rules/README.md, skills, settings)。文档必须反映代码的最新状态。见 `.claude/hooks/post-session.md`。
15. **After every task completion, audit the changed code** — 每次完成任何任务/Phase/功能后，必须审计变更的代码：(a) 内核变更 → `/audit-kernel`, (b) 证明方法变更 → `/verify` + 回归测试, (c) 任何 src/ 变更 → `cargo check --lib` + `cargo test --lib` (相关模块), (d) 检查是否有新的 `Typ::dummy()`、裸 `Term::const_("HOL.xxx")` 绕过 hologic、重复实现。
16. **At the end of EVERY conversation, update .claude/** — `.claude/rules/README.md` (状态表/已知问题, SOF), `.claude/hooks/post-session.md` (完成检查清单), `CLAUDE.md` (项目状态). This ensures the next session starts with accurate state. Don't wait for the user to ask.
17. **Commit messages in Chinese, NO Co-Authored-By** — 提交信息用中文。禁止添加 `Co-Authored-By:` 或任何形式的 AI 署名。所有 commit 由 MCB-SMART-BOY 提交。See `## Commit Rules` below.
18. **All proof method entry points must check VERIFY_DEADLINE** — `auto_exec`, `exec_simp`, `exec_proof` fallback chains, and any function that triggers deep recursive proof search must check `VERIFY_DEADLINE` at entry. This prevents single slow lemmas (e.g., `by (simp add: field_simps)` without matched named_theorems) from hanging the entire verification. See `src/isar/method.rs` VERIFY_DEADLINE checks.
19. **`dev` 上开发，`main` 为稳定发行** — 日常修改在 `dev` 分支。功能稳定后通过 PR 合并到 `main`。`main` 只接受来自 `dev` 的 PR，不直接在 `main` 上提交。
20. **诚实证明率铁律 — 永不谎称证明** — 对外报告能力时,只引用 `Thm::is_fully_proved()` 派生的**真实证明率**(信任足迹为空),绝不引用"已处理 / verified"计数。证明引擎无法闭合的引理必须经 `ThmKernel::admit(ct, "admitted")` 接受为 oracle 定理,**禁止**用 `ThmKernel::assume` 伪装成已证。`admit` 是内核唯一的"接受而不证明"入口。见 [docs/TRUST.md](docs/TRUST.md)。
21. **新增定理生成路径不得绕过信任足迹** — 任何产出 `Thm` 的代码,若它"接受命题而不真正推导"(如旧的 `generalize_thm`、`hol_rules` 连接词规则),必须经 `admit` 标记 oracle,使 `is_fully_proved()` 如实为 false。内核规则会自动并集传播 `oracles`,无需手动维护。

## Architecture

```
.thy → OuterSyntax::parse_spans() → CommandSpan[]
  → TheoryProcessor::process_span()
    ├─ theory → parse_header() → LocalTheory::begin()
    ├─ lemma  → IsarProof::lemma() (enter proof mode)
    ├─ proof  → open_block() (enter structured proof)
    ├─ have/show → enter sub-goal (Backward mode)
    ├─ fix/assume → local context
    ├─ apply/by → method dispatch → ThmKernel
    ├─ qed     → goal refinement (show matches parent)
    └─ end     → LocalTheory::finalize() → Arc<Theory>
  → SessionBuilder::build_session()
    ├─ TheoryGraph scan + topological sort
    ├─ Batch compile .thy files
    └─ Statistics report
```

## Six-Layer Proof Verification

```
verify_lemma():
  0 → Safe rules fixed-point iteration (match→elim_match→resolution)
  1 → Built-in Var-override (pre-stored DB theorems)
  2 → Anonymous datatype axiom
  3 → Isar structured proof (three-mode state machine)
  4 → exec_proof → 27 methods + chain fallback
  5 → Axiom acceptance (generalize_thm)
```

## Module Map

| Module | Path | Files | LOC |
|--------|------|:-----:|-----|
| LCF Kernel | `src/core/` | 33 | ~11,100 |
| Isar Engine | `src/isar/` | 19 | ~13,400 |
| HOL | `src/hol/` | 22 | ~15,800 |
| Theory | `src/theory/` | 8 | ~3,300 |
| Tools | `src/tools/` | 7 | ~4,800 |
| LSP Server | `src/server/` + `src/lsp/` | 15 | ~2,600 |
| Syntax | `src/syntax/` | 5 | ~1,000 |
| Other | session/wasm/document/fleche/bin | 13 | ~2,000 |

## Domain Rules (`.claude/rules/`)

| Trigger | Rule File |
|---------|----------|
| Modifying `src/core/thm.rs` / `logic.rs` / `drule.rs` | [kernel.md](.claude/rules/kernel.md) |
| Modifying `src/isar/method.rs` | [proof-methods.md](.claude/rules/proof-methods.md) |
| Modifying `src/isar/proof.rs` | [isar.md](.claude/rules/isar.md) |
| Modifying `src/theory/thy_header.rs` | [theory-loading.md](.claude/rules/theory-loading.md) |
| Modifying `src/tools/simp.rs` | [proof-methods.md](.claude/rules/proof-methods.md) |
| Modifying `src/isar/linarith.rs` | [proof-methods.md](.claude/rules/proof-methods.md) |
| Stack overflow | [iterative.md](.claude/rules/iterative.md) |
| Performance optimization | [performance.md](.claude/rules/performance.md) |
| Modifying type system | [type-system.md](.claude/rules/type-system.md) |
| Writing tests/debugging | [testing.md](.claude/rules/testing.md) |

## Engineering Rules (`.claude/rules/`)

| Trigger | Rule File |
|---------|----------|
| Error handling / Result / panic | [error-handling.md](.claude/rules/error-handling.md) |
| Designing pub API / trait / visibility | [api-design.md](.claude/rules/api-design.md) |
| Using Arc/Mutex/OnceLock/thread_local! | [concurrency.md](.claude/rules/concurrency.md) |
| Code style / clippy / rustfmt / unsafe audit | [code-quality.md](.claude/rules/code-quality.md) |
| Toolchain | Rust 1.96.0 stable (edition 2024) |
| New release / semver / changelog | [release.md](.claude/rules/release.md) |
| Refactoring (≥3 files) / code smells | [refactoring.md](.claude/rules/refactoring.md) |
| Using unsafe / adding deps / external input | [security.md](.claude/rules/security.md) |
| Adding documentation / rustdoc / ADR | [documentation.md](.claude/rules/documentation.md) |
| CI/CD / GitHub Actions / automation | [ci-cd.md](.claude/rules/ci-cd.md) |
| Property testing / proptest / invariants | [property-testing.md](.claude/rules/property-testing.md) |
| After each Phase completion | [post-session.md](.claude/hooks/post-session.md) |
| Next phase plan | `/root/.claude/plans/` |

## Skills (`.claude/skills/`)

### Verification & Debugging
- **[verify](.claude/skills/verify.md)** — Verify lemma(s): six-layer architecture, test matrix, failure diagnosis
- **[debug-overflow](.claude/skills/debug-overflow.md)** — Stack overflow: diagnose → choose pattern → convert to iterative
- **[audit-kernel](.claude/skills/audit-kernel.md)** — Kernel safety: scan for Typ::dummy(), check Thm fields, verify tpairs/shyps

### Development
- **[add-method](.claude/skills/add-method.md)** — Add a proof method: 4-step pattern (enum → dispatch → impl → name)
- **[add-isar-command](.claude/skills/add-isar-command.md)** — Add an Isar command: state machine (Forward/Chain/Backward)
- **[port-isabelle](.claude/skills/port-isabelle.md)** — Port from Isabelle/ML to Rust: type mapping, pattern translation
- **[refactor](.claude/skills/refactor.md)** — Safe refactoring: kernel safety, method dispatch, theory pipeline

### Theory & Build
- **[build-theory](.claude/skills/build-theory.md)** — Build .thy files: parse, debug failures, generate reports
- **[search-db](.claude/skills/search-db.md)** — Navigate HolTheoremDb (42K+ theorems) by name, type, net, attribute

### Performance & Release
- **[bench](.claude/skills/bench.md)** — Run test matrix at correct stack sizes, check regressions
- **[release](.claude/skills/release.md)** — Phase SOP: summarize → verify → version → sync 12 docs → finalize

### Maintenance
- **[run-isabelle-rs](.claude/skills/run-isabelle-rs.md)** — Build, run demo, run tests, compile .thy files, verify kernel
- **[sync-docs](.claude/skills/sync-docs.md)** — Sync docs/ and .claude/ after code changes. Run after any src/ change.

## Common Commands

```bash
# Build
cargo build

# All tests (needs 256MB stack for now)
RUST_MIN_STACK=268435456 cargo test --lib

# Kernel tests (fast, 32MB stack OK)
cargo test --lib core::thm

# Core verification (needs 256MB stack)
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture

# Extended verification (36 files, ~8.5 min)
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture

# tmux for long-running tests
tmux new-session -d -s tier2 "RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture 2>&1; exec bash"
tmux attach -t tier2

# Clippy
cargo clippy -- -D warnings

# Format
cargo fmt -- --check
```

## Commit Rules

- **Commit messages MUST be concise and in Chinese (项目使用中文)**
- **NEVER add `Co-Authored-By:` or any AI attribution to commit messages**
- **Git user is `MCB-SMART-BOY`** — all commits are authored by this user

## Error Style — Rust 编译器风格

项目目标：打造更程序员友好的 Isabelle。所有错误信息遵循 `rustc` 风格：

```
E0xxx: short description
  found: ...
  expected: ...
  = help: actionable suggestion
  = note: additional context
```

### 规则
- **每个错误必须有错误码** (E0001-E0405，见 `src/core/error.rs`)
- **每个错误必须有 `= help:` 建议**
- **parse/type/kernel 错误必须包含源代码位置**（行号、列号）
- **禁止裸 `String` 报错** — 用结构化 error enum，避免 `format!("error: ...")`
- **参考**: `rustc --explain E0308` 的格式风格

### 错误码范围
| 范围 | 类别 |
|------|------|
| E0001-E0099 | Kernel (trusted core invariants) |
| E0100-E0199 | Type system |
| E0200-E0299 | Proof search |
| E0300-E0399 | Parse |
| E0400-E0499 | IO/Config/Theory |
