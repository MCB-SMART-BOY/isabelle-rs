# CLAUDE.md — Isabelle-rs

> **用 Rust 重写 Isabelle，打造更程序员友好的证明助手。**
>
> 功能与 Isabelle/ML 一致。错误信息 → Rust 编译器风格。工具链 → 标准 Rust 生态。
> LCF trusted kernel + higher-order unification + Isar proof language + theory loading pipeline.

## Project State (v1.9.0-dev, Route A: Stability First)

| Metric | Value |
|--------|-------|
| Kernel | 15 ops + tpairs/shyps, 100% Isabelle-equivalent, 0 `Typ::dummy()` fallback |
| Proof Engine | Isar state machine (3 modes) + 27 proof methods |
| Classical Reasoner | best/depth/dup_step + three-stage safe rules |
| Arithmetic | Fourier-Motzkin variable elimination (nat/int linear) |
| HOL Simplifier | Conditional rewriting + solver plugins (ArithSolver, AsmSolver) |
| BNF Lfp/Gfp | Complete: induction/coinduction/fold/rec/unfold/corec + map/set/rel/pred |
| Ctr_Sugar | case/disc/sel/split/cong/nchotomy/size theorem generation |
| Meson | Model elimination prover — 1st-class proof method |
| Transfer/Lifting | Transfer rule generation + rel_fun/rel_set + quotient type theorems |
| **hologic** | ✅ 40+ mk_*/dest_*/is_* functions, 100→3 bare HOL const calls (Phase 49 done) |
| **simpdata** | ✅ 28 built-in rules, `init_hol_simpset()`, all simp.rs migrated (Phase 50 done) |
| **args** | ✅ `Args::parse_modifiers()` wired into `exec_simp` + `exec_induct` (Phase 51 done) |
| **spec** | ✅ Definition/Axiomatization/Abbreviation/TypeAbbrev/Typedecl parsers integrated (Phase 52-54 done) |
| Code | ~54K Rust LOC, 124 files |
| Tests | 714 (638 lib + 76 integration) |
| Verification | **Core 5/5 files 100% (125/125)**, Tier2 6/20 files 100% |
| isabelle-source | ✅ Isabelle 2025 full distribution (364MB, 1,473 .thy files) |

## Active Strategy: Route A — Stability First

```
1. ✅ Fix 5 failing tests
2. ✅ Fix OOM/stack overflow root causes
3. 🔄 Expand Tier2 verification (tmux session 'tier2': 6/19 files 100% so far)
4. ✅ Complete attribute system integration (begin_lemma + lemmas + declare + attrs prop)
5. 🔄 Full documentation sync (current)
```

## Known Issues

| Issue | Severity | Detail |
|-------|:--------:|--------|
| Fields.thy prover bottleneck | 🟡 Medium | 根因: `by (simp add: field_simps)` → named_theorems 无法解析 → exec_proof fallback 链触发 auto/blast 深度搜索. 已加 deadline 保护, 但单个 simplifier rewrite 仍需优化 |
| Num.thy prover bottleneck | 🟡 Medium | 354 simp calls, same root cause as Fields |
| Tier2 verification in progress | 🟡 Medium | tmux 'tier2': 6/18 files 100% ✅ (Fun→Rings) |
| ctr_sugar split pop bug | ✅ Fixed | 3处 empty Vec pop().unwrap() → is_empty 检查 |
| LazyLock DB init slow | 🟡 Medium | First HolTheoremDb::get() loads all 1,473 .thy files; should be on-demand |
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
14. **After every task completion, update ALL project documentation** — 每次完成任何任务/Phase/功能后，必须更新所有文档：`docs/` (ARCHITECTURE, GAP_ANALYSIS, ROADMAP, DEVELOPMENT) 和 `.claude/` (CLAUDE.md, skills, settings, phase-sop)。这不是可选的。文档必须反映代码的最新状态。
15. **After every task completion, audit the changed code** — 每次完成任何任务/Phase/功能后，必须审计变更的代码：(a) 内核变更 → `/audit-kernel`, (b) 证明方法变更 → `/verify` + 回归测试, (c) 任何 src/ 变更 → `cargo check --lib` + `cargo test --lib` (相关模块), (d) 检查是否有新的 `Typ::dummy()`、裸 `Term::const_("HOL.xxx")` 绕过 hologic、重复实现。
16. **At the end of EVERY conversation, update .claude/** — `.claude/rules/README.md` (状态表/已知问题), `.claude/rules/phase-sop.md` (完成清单), `CLAUDE.md` (项目状态). This ensures the next session starts with accurate state. Don't wait for the user to ask.
17. **Commit messages in Chinese, NO Co-Authored-By** — 提交信息用中文。禁止添加 `Co-Authored-By:` 或任何形式的 AI 署名。所有 commit 由 MCB-SMART-BOY 提交。See `## Commit Rules` below.
18. **All proof method entry points must check VERIFY_DEADLINE** — `auto_exec`, `exec_simp`, `exec_proof` fallback chains, and any function that triggers deep recursive proof search must check `VERIFY_DEADLINE` at entry. This prevents single slow lemmas (e.g., `by (simp add: field_simps)` without matched named_theorems) from hanging the entire verification. See `src/isar/method.rs` VERIFY_DEADLINE checks.

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
| New release / semver / changelog | [release.md](.claude/rules/release.md) |
| Refactoring (≥3 files) / code smells | [refactoring.md](.claude/rules/refactoring.md) |
| Using unsafe / adding deps / external input | [security.md](.claude/rules/security.md) |
| Adding documentation / rustdoc / ADR | [documentation.md](.claude/rules/documentation.md) |
| CI/CD / GitHub Actions / automation | [ci-cd.md](.claude/rules/ci-cd.md) |
| Property testing / proptest / invariants | [property-testing.md](.claude/rules/property-testing.md) |
| After each Phase completion | [phase-sop.md](.claude/rules/phase-sop.md) |
| After any src/ change | [sync-docs](.claude/skills/sync-docs.md) — auto-sync docs/ and .claude/ |

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
- **[run-isabelle-rs](.claude/skills/run-isabelle-rs/)** — Build, run demo, run tests, compile .thy files, verify kernel
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

# Extended verification
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture

# Batch compile HOL
cargo run --bin isabelle-build -- --dir isabelle-source/src/HOL --stats

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
