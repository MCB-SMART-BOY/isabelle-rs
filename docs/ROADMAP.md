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
| T2 primitive rule hardening | Main body done, but `alpha_eq` and `Typ::dummy()` remain known debts. |
| Checked instantiation | Production paths closed over `instantiate_checked`. |
| Admit/oracle tracking | Explicit, classified, and propagated. |
| Closed theorem acceptance | Main path, session reporting, and final trusted tables use `is_closed_proved()`. |
| T4 proofterm replay | Minimal replay prototype exists for six rules. |
| HOL/Isar feature parity | Not current priority. |

Priority order:

1. Extend T4 proofterm replay rule coverage.
2. Tighten parser/type/certification boundaries.
3. Reduce admitted lemmas by reason.
4. Expand HOL/Isar/tool coverage only where it reduces admitted counts without
   weakening trust boundaries.
5. Add optional replay gates to CLI/verification paths after replay covers the
   main primitive rules.

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
  `is_closed_proved()`.
- The next engineering plan starts with T4 replay, not more HOL/Isar features.

Current baseline commits:

```text
e60580b kernel: harden primitive rules and checked instantiation
7465d48 trust: require closed proved theorems for trusted acceptance
2dee3d0 proofterm: add minimal burden-aware derivation replay
eef6d80 docs: reposition project as trusted Rust LCF kernel prototype
```

The next active code phase should start at Phase 1.

## Phase 1: T4 Replay Batch 1

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

## Phase 2: T4 Replay Batch 2

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

## Phase 3: T4 Replay Batch 3

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

## Phase 4: T4 Replay Batch 4

Target rules:

```text
bicompose
bicompose_eresolve
subst_premise
```

Why last:

- These rules involve resolution, premise selection, unification, and
  propagation of multiple theorem burdens.
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
- `subst_premise` cannot rewrite across Free/Const or Var/Free confusion once
  strict `alpha_eq` is enabled.
- Multi-premise burdens union exactly: `hyps`, `tpairs`, `shyps`, `oracles`.
- Unsupported or failed resolution replay is distinguishable from proof
  tampering.

Done when:

- Replay can validate the main proof-search generated derivations without
  silently trusting unsupported rules.

## Phase 5: Parser / Type / Certification Boundary

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

## Phase 6: Admitted Lemma Reduction

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

## Phase 7: Optional Proof Replay Integration

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
- Never let replay success replace `is_closed_proved()`; closed theorem
  acceptance remains required.

Done when:

- Core theorem batches can optionally run proof replay on closed proved results.
- Unsupported rules are reported as coverage gaps, not trust failures.

## Later Work

Only after the above tracks are stable:

- Broaden Isar grammar and structured proof coverage.
- Improve HOL packages where they reduce admitted counts.
- Build richer proof-state diagnostics for agents.
- Extend LSP and WASM integration.
- Consider Sledgehammer/SMT/Code Generator only as non-core research tracks.

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
