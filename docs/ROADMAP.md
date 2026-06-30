# Roadmap

This roadmap follows the current project positioning:

```text
Rust Isabelle/Pure-inspired LCF kernel prototype
with explicit oracle footprints, closed-theorem acceptance,
and minimal proofterm replay.
```

The next phases should not chase broad Isabelle/HOL coverage first. The route is
to harden the proof boundary, extend independent replay, then return to
parser/type certification and admitted-lemma reduction.

## Strategy

Current status:

| Track | Status |
|---|---|
| Strict kernel nucleus (`src/kernel/`) | Base primitive set implemented plus conservative `resolve1_match` prototype; ADR-0001 strangler pattern active. |
| Legacy T2 primitive rule hardening | Strict kernel alpha-equivalence split out; `Typ::dummy()` and certification remain known debts in legacy core. |
| Checked instantiation | Production paths closed over `instantiate_checked`. |
| Admit/oracle tracking | Explicit, classified, and propagated. |
| Closed theorem acceptance | Main path, session reporting, and final trusted tables use `is_strict_closed_proved()`. |
| T4 proofterm replay | Legacy proofterm replay remains minimal; strict `src/kernel` invariant replay covers its implemented derivations. |
| HOL/Isar feature parity | Not current priority. |

Architecture vision: ADR-0002 establishes a layered platform architecture
(strangler kernel → workspace → session → agent → plugin). The phases below
follow the dependency order: kernel first, then workspace, then session/agent
infrastructure.

Priority order:

1. Stabilize strict `src/kernel` nucleus: keep the firewall clean, normalize
   resolution substitutions, and make `resolve1_match` limits explicit.
2. Establish a structured compatibility matrix for legacy adapters
   (Core → Isar proof state → HOL bootstrap → Tier2 smoke).
3. Extend strict-kernel replay/invariant coverage only after rule contracts and
   compatibility boundaries are stable.
4. Reduce admitted lemmas by classified reason.
5. Split into Cargo workspace (`isabelle-kernel` crate first).
6. Design session incremental engine (snapshot/rollback/content-addressed cache).
7. Build `isabelle.toml` project system (Lake-style).
8. Design Agent Proof Protocol (APP).
9. Expand HOL/Isar/tool coverage only where it reduces admitted counts without
   weakening trust boundaries.
10. Harden WASM plugin sandbox boundaries.
11. AFP large-scale benchmark.

## Phase 0: Baseline and Documentation Sync

Status: complete for the first trusted-kernel checkpoint.

Goal:

- Preserve the current T2/trust/T4 work as a reviewable baseline.
- Make README, docs, root `CLAUDE.md`, and `~/.codex` agree on the same project
  positioning.
- Remove misleading "Rust rewrite of Isabelle" and "feature complete" language.
- Make `PROJECT_STATUS.md` the canonical high-level status.

Files:

```text
README.md
CLAUDE.md
docs/PROJECT_STATUS.md
docs/BASELINE.md
docs/TRUST.md
docs/ARCHITECTURE.md
docs/GAP_ANALYSIS.md
docs/ROADMAP.md
docs/DEVELOPMENT.md
~/.codex/references/isabelle-rs.md
~/.codex/rules/isabelle-rs.md
~/.codex/skills/isabelle-rs-*/SKILL.md
```

Done when:

- The baseline commits and trusted gate are recorded.
- All high-level docs describe the project as a research prototype, not a full
  Isabelle rewrite.
- All proof-rate language distinguishes `is_fully_proved()` from
  `is_strict_closed_proved()`.
- The next engineering plan starts with T4 replay, not more HOL/Isar features.

Current baseline commits:

```text
e60580b kernel: harden primitive rules and checked instantiation
7465d48 trust: require closed proved theorems for trusted acceptance
2dee3d0 proofterm: add minimal burden-aware derivation replay
eef6d80 docs: reposition project as trusted Rust LCF kernel prototype
```

The next active code phase should start at Phase 1.

## Phase 1: Strict Kernel Boundary

Target work:

```text
kernel_alpha_eq / compat_alpha_eq separation
CTerm::certify_checked
Thm invariant checker
strict kernel mode
```

Status:

- `kernel_alpha_eq` is now strict for trusted theorem construction.
- `compat_alpha_eq` preserves legacy Free/Const, Var/Free, and dummy-binder
  behavior only for explicitly named compatibility paths.

Next strict-boundary tasks:

- Add a checked certification API that rejects dummy-typed trusted inputs.
- Add theorem invariant checks for primitive-rule outputs.
- Add a strict-kernel mode that requires strict certification and invariant
  checks before counting trusted results.

## Legacy Replay Backlog

The sections below preserve the legacy `src/core` proofterm replay backlog.
They are not the active strict-kernel architecture plan. New trusted kernel
work should first land in `src/kernel`; legacy replay work is useful only when
it supports an adapter or a compatibility audit without weakening the new TCB.

## Phase 2: T4 Replay Batch 1

Target rules:

```text
beta_conversion
forall_intr
forall_elim
```

Why first:

- These rules are small enough to replay independently.
- They stress de Bruijn substitution, free-variable side conditions, and binder
  type checks.
- They extend proof replay beyond implication/equality without involving full
  unification or resolution.

Primary files:

```text
src/core/thm.rs
src/core/proofterm.rs
src/core/logic.rs
src/core/term.rs
src/core/term_subst.rs
tests/kernel_soundness.rs
docs/KERNEL_RULES.md
docs/KERNEL_ATTACK_TESTS.md
docs/TRUST.md
```

Implementation tasks:

- Add proofterm constructors or derivation records for each rule if missing.
- Replay `beta_conversion` by checking the input is `(Abs body) arg` and using
  the same bound substitution semantics as `ThmKernel::beta_conversion`.
- Replay `forall_intr` with the same free-in-hypotheses side condition as the
  kernel.
- Replay `forall_elim` with binder/argument known-type compatibility.
- Ensure replay compares `prop`, `hyps`, `tpairs`, and `oracles`.

Required attack tests:

- Replay `(λx. x) a` as `a`, not raw `Bound(0)`.
- `forall_intr` replay rejects a variable free in hypotheses.
- `forall_elim` replay rejects known binder/argument type mismatch.
- Tampering final theorem fields after each rule makes `check_proof()` fail.
- Applying the rule to an admitted premise fails independent replay by oracle
  footprint.

Done when:

```bash
cargo fmt --check
cargo test core::proofterm::tests::
cargo test core::thm::tests::
cargo test --test kernel_soundness
cargo test --lib core::
cargo check
```

## Phase 3: T4 Replay Batch 2

Target rules:

```text
combination
abstraction
equal_intr
equal_elim
```

Notes:

- `combination` must mirror known function-domain compatibility checks.
- `abstraction` must preserve the free-variable-in-hypotheses side condition.
- Add `equal_intr` / `equal_elim` only if they are implemented or needed by
  current derived rules; otherwise document them as missing Pure rules.

Primary files:

```text
src/core/thm.rs
src/core/proofterm.rs
src/core/logic.rs
src/core/types.rs
tests/kernel_soundness.rs
```

Required attack tests:

- Known argument-domain mismatch in `combination` fails replay.
- `abstraction` cannot abstract a free variable from hypotheses.
- Open premise burdens are preserved.
- Oracle premise makes independent replay fail.
- Unsupported equality rules are reported as unsupported, not as successful.

Done when:

- All supported rules replay successfully for positive cases.
- All known side-condition attacks fail closed.
- `docs/KERNEL_RULES.md` marks replay support per rule.

## Phase 4: T4 Replay Batch 3

Target rules:

```text
instantiate_checked
generalize
```

Why this is risky:

- Instantiation touches schematic variables, type variables, and environment
  application.
- Existing T2 hardening solved production instantiation, but replay must prove
  the recorded instantiation is the same one.

Primary files:

```text
src/core/thm.rs
src/core/proofterm.rs
src/core/envir.rs
src/core/unify.rs
src/core/term_subst.rs
src/core/type_infer.rs
```

Required design decisions:

- Proof records must include enough environment data to replay substitution.
- Replay must call checked substitution semantics, not raw `env.apply_*`
  without type checks.
- If a replay environment contains dummy types, behavior must be documented and
  tested.

Required attack tests:

- `?x::nat := b::bool` fails replay.
- Schematic variable indices cannot be ignored.
- Type-variable instantiation preserves known type constraints.
- Successful instantiation preserves all burdens.

Done when:

- Production theorem instantiation and replay instantiation have the same
  acceptance/rejection semantics for known concrete type mismatches.

## Phase 5: T4 Replay Batch 4

Target rules:

```text
bicompose (⚠️ LEGACY CORE — strict-kernel design in docs/RESOLUTION_DESIGN.md)
bicompose_eresolve (⚠️ LEGACY CORE)
subst_premise (⚠️ LEGACY CORE)
```

Why last:

- These rules involve resolution, premise selection, unification, and
  propagation of multiple theorem burdens.
- The strict-kernel resolution family (`resolve1`/`bicompose` in `src/kernel/`)
  will need its own T4 replay strategy; see `docs/RESOLUTION_DESIGN.md`.
- They are the most likely place for `alpha_eq`, `Typ::dummy()`, and
  `Option<Thm>` diagnostics to hide mistakes.

Primary files:

```text
src/core/thm.rs
src/core/proofterm.rs
src/core/unify.rs
src/core/envir.rs
src/core/tactic.rs
src/core/bires.rs
```

Required attack tests:

- Resolution cannot cross known concrete type mismatches.
- E-resolution cannot discharge the wrong hypothesis.
- `subst_premise` (⚠️ LEGACY CORE) cannot rewrite across Free/Const or Var/Free confusion once
  strict `alpha_eq` is enabled.
- Multi-premise burdens union exactly: `hyps`, `tpairs`, `shyps`, `oracles`.
- Unsupported or failed resolution replay is distinguishable from proof
  tampering.

Done when:

- Replay can validate the main proof-search generated derivations without
  silently trusting unsupported rules.

## Phase 6: Parser / Type / Certification Boundary

Goal:

Reduce kernel tolerance by making front-end terms better certified before they
reach `ThmKernel`.

Primary files:

```text
src/isar/term_parser.rs
src/core/type_infer.rs
src/core/types.rs
src/core/thm.rs
src/hol/hol_loader.rs
src/theory/loader.rs
```

Tasks:

- Make parser/loader distinguish `Const`, `Free`, `Var`, and `Bound` more
  accurately.
- Prefer annotated/certified terms at theorem construction sites.
- Reduce `Typ::dummy()` in propositions accepted by kernel rules.
- Replace semantic correction through `alpha_eq` with correct term
  construction earlier in the pipeline.
- Enable ignored Free/Const and Var/Free attack tests once representation is
  aligned.

Done when:

- `alpha_eq` broad Free/Const suffix matching can be removed or narrowed.
- `alpha_eq` Var/Free compatibility can be removed or narrowed.
- Existing Tier2 proof rate does not rely on unsound kernel matching.

## Phase 7: Admitted Lemma Reduction

Goal:

Shrink admitted counts by cause while preserving honest oracle footprints.

Do not target "100%" by hiding fallback. Every remaining admitted fact must keep
its `admitted:*` reason.

Initial targets:

```text
Rings
Lattices_Big
Complete_Lattices
Parity
Power
Map
Order_Relation
```

Likely work areas:

```text
src/core/simplifier.rs
src/tools/simp.rs
src/isar/attrib.rs
src/isar/method.rs
src/isar/linarith.rs
src/hol/hol_loader.rs
```

Tasks:

- Categorize admitted lemmas by reason:
  `admitted:proof_engine_failed`, `admitted:parser_gap`,
  `admitted:unsupported_method`, `admitted:attribute_transformation`,
  `admitted:datatype_stub`, `admitted:class_stub`, `admitted:metis_fallback`,
  `admitted:simp_fallback`.
- Improve named theorem handling for `field_simps`, `algebra_simps`, intro,
  elim, dest, and simp attributes.
- Add conditional rewrite support only where it can be justified by kernel
  derivations or explicit admitted footprints.
- Improve simp/linarith cooperation for arithmetic-heavy files.

Done when:

- Admitted count decreases with a reason-by-reason report.
- No admitted path is reclassified as proved without a kernel derivation or
  proof replay support.

## Phase 8: Optional Proof Replay Integration

Goal:

Make independent replay available in verification workflows after enough
primitive rules are supported.

Tasks:

- Add a CLI or test flag such as `--check-proof` or an equivalent verifier
  option.
- Make replay failures classify as:
  unsupported rule, oracle/admitted theorem, tampered proof, or burden mismatch.
- Keep replay optional until coverage is broad enough to avoid excessive false
  negatives.
- Never let replay success replace `is_strict_closed_proved()`; strict closed theorem
  acceptance remains required.

Done when:

- Core theorem batches can optionally run proof replay on strict closed proved results.
- Unsupported rules are reported as coverage gaps, not trust failures.

## Phase 9: Compatibility Matrix

Goal:

Establish structured, measurable compatibility tracking rather than anecdotal
claims.

Primary files:

```text
tests/compatibility/
docs/COMPATIBILITY.md
```

Tasks:

- Define compatibility levels:
  ```text
  Level 0: Core syntax compatibility
  Level 1: Pure compatibility
  Level 2: HOL-Main compatibility
  Level 3: Library compatibility
  Level 4: AFP selected benchmark (20 entries)
  Level 5: AFP large-scale compatibility
  Level 6: Major tools compatibility
  ```
- Build CI that reports per-file proved/admitted/oracle counts.
- Track admitted count per version as a regression gate.
- Compare output with reference Isabelle where applicable.

Done when:

- Each version has a published compatibility report.
- Admitted count never increases between versions.

## Phase 10: Cargo Workspace Split

Goal:

Extract `isabelle-kernel` as the first independent crate, enforcing the
dependency direction established by ADR-0002.

Primary deliverable:

```text
crates/isabelle-kernel/  — strict TCB, minimal deps, no tokio/LSP/WASM
```

Tasks:

- Move `src/kernel/` to `crates/isabelle-kernel/src/`.
- Define `isabelle-kernel/Cargo.toml` with minimal dependencies.
- Ensure `isabelle-kernel` compiles and tests independently.
- Establish the dependency rule: no other crate may be depended on by the kernel.
- Legacy `src/core/` stays in the root crate until migration is complete.

Done when:

```bash
cargo test -p isabelle-kernel
cargo test --test kernel_rewrite_soundness
```

## Phase 11: Session Incremental Engine

Goal:

Design and implement a content-addressed incremental checking engine with
snapshot/rollback, serving as shared infrastructure for both LSP and Agent
protocol.

Primary files:

```text
crates/isabelle-session/src/
```

Key API:

```rust
pub trait ProofSession {
    fn snapshot(&self) -> SnapshotId;
    fn apply_command(&mut self, span: CommandSpan) -> Result<StateDiff>;
    fn rollback(&mut self, snapshot: SnapshotId);
    fn goals(&self) -> Vec<GoalView>;
    fn diagnostics(&self) -> Vec<Diagnostic>;
}
```

Cache structure:

```text
target/isabelle/
  cache/
    spans/
    theories/
    thms/
    proofcerts/
  diagnostics.db
  graph.db
```

Done when:

- Snapshot/rollback round-trips preserve theorem state.
- Incremental checking correctly invalidates only changed spans.
- Parallel build produces deterministic results.

## Phase 12: isabelle.toml Project System

Goal:

Lake-style project scaffolding with dependency locking and toolchain pinning.

Primary deliverable:

```bash
isabelle-rs new my_project
isabelle-rs build
isabelle-rs test
isabelle-rs fmt
isabelle-rs lsp
isabelle-rs doc
isabelle-rs add AFP/Graph_Theory
```

Project structure:

```text
my_project/
  isabelle.toml
  isabelle.lock
  toolchain.toml
  src/
    Main.thy
  tests/
  docs/
  target/
```

Configuration features (`isabelle.toml`):

```toml
[build]
parallel = true
incremental = true
deny_admit = true       # CI gate: no admitted theorems
max_oracles = 0          # CI gate: no oracle dependencies
trust_report = true      # generate per-build trust report
proof_certificates = true # generate proof certificates
```

Done when:

- `isabelle-rs new` scaffolds a working project.
- `isabelle-rs build` produces a trust report.
- `deny_admit = true` fails the build when any theorem is admitted.

## Phase 13: Agent Proof Protocol (APP)

Goal:

Design a structured protocol for machine proof search that operates at the
proof-state level, not the text level.

Primary files:

```text
crates/isabelle-agent/src/
```

Core API:

```text
proof/open_project
proof/open_theory
proof/get_state
proof/get_goals
proof/search_facts
proof/apply_command
proof/try_method
proof/rollback
proof/replay
proof/minimize
proof/trust_report
proof/export_certificate
```

`get_goals` returns structured JSON:

```json
{
  "state_id": "s42",
  "mode": "ProofBackward",
  "goals": [
    {
      "id": "g0",
      "target": "xs @ [] = xs",
      "variables": [{"name": "xs", "type": "'a list"}],
      "hypotheses": [],
      "suggestions": [
        {"kind": "induction", "on": "xs"},
        {"kind": "simp", "facts": ["append_Nil"]}
      ]
    }
  ]
}
```

`apply_command` returns a state diff:

```json
{
  "before": "s42",
  "after": "s43",
  "accepted": true,
  "new_goals": [],
  "diagnostics": [],
  "trust_delta": {"oracles_added": [], "admitted_added": []}
}
```

Design principle:

```text
                 ┌──────────────┐
VS Code/Neovim ← │ isabelle-lsp  │
                 └──────┬───────┘
                        │
                 ┌──────▼───────┐
                 │ isabelle-session │
                 └──────▲───────┘
                        │
Agent/Codex/Claude ← ┌──┴──────────┐
                     │ isabelle-agent │
                     └──────────────┘
```

LSP serves humans; APP serves machines. Both share the session layer.

Done when:

- Agent can call `get_goals` and receive structured goal state.
- Agent can `apply_command` and receive a state diff.
- Agent can `rollback` to a previous snapshot.
- `trust_report` accurately reflects oracle/admitted footprint.

## Phase 14: WASM Plugin Sandbox Hardening

Goal:

Enforce capability boundaries on WASM plugins: plugins must not construct
trusted theorems directly, modify kernel state, bypass oracle footprint, or
silently admit.

Primary files:

```text
crates/isabelle-plugin-wasm/src/
```

Plugin capabilities (allowed):

```text
custom tactic
proof search strategy
domain-specific simplifier
theorem search extension
Agent strategy plugin
document generation plugin
```

Plugin restrictions (forbidden):

```text
direct trusted theorem construction
kernel state modification
oracle footprint bypass
silent admit
```

Plugin return boundary: proof script, proof term, method suggestion, fact
ranking, diagnostic — never a raw theorem.

Done when:

- Plugin capability violations are rejected at the WASM boundary.
- Plugin-produced proof scripts must pass kernel checking before theorem acceptance.

## Phase 15: AFP Large-Scale Benchmark

Goal:

Systematic compatibility measurement against AFP entries.

Primary files:

```text
tests/afp/
```

Tasks:

- Select 20 representative AFP entries.
- Build automated compatibility CI.
- Track per-entry proved/admitted/oracle counts.
- Require admitted count to be non-increasing between versions.
- Publish per-version compatibility report.

Done when:

- 20 AFP entries have compatibility status.
- CI gate rejects admitted-count regressions.
- Compatibility report is generated per release.

## Later Work

Only after the above tracks are stable:

- Broaden Isar grammar and structured proof coverage.
- Improve HOL packages where they reduce admitted counts.
- Extend LSP integration with richer IDE features.
- Consider Sledgehammer/SMT/Code Generator only as non-core research tracks.
- WASM plugin marketplace and registry.

## Standing Verification Policy

For docs-only changes:

```bash
cargo fmt --check
cargo check
```

For kernel, proof replay, or theorem acceptance changes:

```bash
cargo fmt --check
cargo test --test kernel_soundness
cargo test --test kernel_rewrite_soundness
cargo test core::proofterm::tests::
cargo test core::thm::tests::
cargo test --lib core::
cargo check
```

For theory-wide claims:

```bash
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture
```

Do not report full `cargo test --lib` success unless the current checkout has
verified the known theory-loader stack overflow is fixed.
