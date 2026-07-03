# Project Status and Positioning

This document is the canonical high-level status for Isabelle-rs. It should be
read before using older roadmap, architecture, or gap-analysis notes.

## Current Position

Isabelle-rs is not a full Rust rewrite of Isabelle. The accurate current
position is:

```text
A Rust implementation of an Isabelle/Pure-inspired LCF kernel
with explicit oracle footprints, closed-theorem acceptance,
and minimal proofterm replay.
```

Chinese summary:

```text
一个受 Isabelle/Pure 启发的 Rust 化 LCF 证明内核原型，
重点研究 oracle 足迹追踪、闭合定理接收条件、
以及 proofterm replay 复检机制。
```

The project is now beyond a toy parser: it has a meaningful trusted-kernel
prototype and a growing soundness attack-test suite. Its research value is not
feature parity with Isabelle/HOL. Its value is a smaller Rust-native setting for
studying theorem-construction boundaries, admitted/oracle accounting, closed
theorem statistics, and proof-object replay.

## Current Baseline

The first trusted-kernel engineering checkpoint is recorded in
[BASELINE.md](BASELINE.md). It includes four reviewable commits:

```text
e60580b kernel: harden primitive rules and checked instantiation
7465d48 trust: require closed proved theorems for trusted acceptance
2dee3d0 proofterm: add minimal burden-aware derivation replay
eef6d80 docs: reposition project as trusted Rust LCF kernel prototype
```

The baseline gate is:

```bash
bash scripts/check-strict-kernel.sh
```

The baseline originally carried two ignored `alpha_eq` tests:

```text
Free / Const suffix matching
Var / Free index confusion
```

Strict kernel alpha-equivalence now rejects both in trusted paths. The legacy
behavior is isolated as explicit `compat_alpha_eq` parser/loader compatibility.
The next strict-kernel step has started: `CTerm::certify_checked(term, type_env)`
now provides a hard certification API that rejects residual dummy types and
ill-typed applications. Most old parser/HOL/Isar call sites still use
best-effort compatibility certification. `CTerm` now records checked vs compat
status, and strict `ThmKernel::assume` / `reflexive` reject compat CTerms; old
call sites have been made explicit as `assume_compat` / `reflexive_compat`.
`Thm` now also records construction trust as `Strict`, `Compat`, or
`Admitted`, so compatibility theorems cannot enter trusted statistics merely
because they are oracle-free and closed-shaped. `Thm::check_kernel_invariants`
now provides separate `Compat` and `Strict` invariant checks so strict trust is
auditable rather than only a source label. The first Isar proof-state
production boundary has also moved onto the strict path: local assumptions,
top-level proof goals, and checked subgoal scaffolding now use checked
certification plus strict `ThmKernel::assume`, producing Strict open theorem
obligations rather than compatibility theorem scaffolds. This proof-state
boundary now uses an explicit `ProofCertContext` / `TypeEnv` source: constants
and local frees must be declared in the proof context before certification, so
raw terms can no longer self-declare their own names merely by carrying
non-dummy type annotations.

Important limitation: `check_kernel_invariants(Strict)` is an internal theorem
consistency audit, not a closed-lemma predicate and not a complete replay
certificate. Strict open theorems may pass it while failing
`is_strict_closed_proved()`. Strict derivations that use currently unsupported
replay rules are structurally audited but still fail `check_proof()` until their
replay rule is implemented.

The next architectural reset has started in `src/kernel/`. This is a new strict
kernel nucleus, not another compatibility patch over the legacy `src/core`
types. Its current version is independent from old Isar/HOL/tactic paths and
introduces separate `RawTerm -> CTerm/CProp -> KernelThm -> ClosedThm ->
TrustedTheorem` stages, a `ProofObligation` type that is not a theorem, and
separate `TrustedTheory` / `SearchFactDb` storage. It deliberately has no dummy
type constructor and no compatibility certification API. The strict nucleus now
implements the base primitive rule set plus conservative `resolve1_match`,
`subst_premise`, and `bicompose` wrapper rules with invariant replay and attack
tests. `resolve1_match` / `bicompose` use strict matching and deterministic
substitutions and reject Free/schematic Var namespace collisions with
`RequiresLifting`; `bicompose` v1 records `Derivation::Resolve1Match`.
`subst_premise` is propositional-equality only, fixed lhs -> rhs, exact
selected-subgoal matching.
See
[ADR-0001-kernel-core-rewrite.md](ADR-0001-kernel-core-rewrite.md) and
[KERNEL_PRIMITIVES.md](KERNEL_PRIMITIVES.md).

## What Is Solid

The following areas have a coherent implementation and regression coverage:

| Area | Current state |
|---|---|
| LCF-style theorem type | `Thm` fields are private; external construction routes through `ThmKernel`. |
| Kernel primitive rules | All 15 base primitives implemented (assume, reflexive, symmetric, transitive, combination, abstraction, beta_conversion, implies_intr, implies_elim, forall_intr, forall_elim, equal_intr, equal_elim, generalize, instantiate); several rounds of type/burden/oracle boundary hardening done. |
| Checked instantiation | Production paths use `instantiate_checked`; legacy infallible instantiation is not a production API. |
| Strict alpha equality | Trusted kernel equality uses `kernel_alpha_eq`; legacy broad matching is isolated as `compat_alpha_eq`. |
| Checked CTerm certification | `CTerm::certify_checked` exists, CTerms carry checked/compat status, and strict `assume`/`reflexive` reject compat terms. |
| Proof-state strict entry points | `ProofState::assume`, `Goal::init`, and checked subgoal scaffolding construct Strict open theorem obligations from explicit proof-context certification. |
| Strict kernel nucleus | `src/kernel` contains an isolated TCB nucleus with no dummy type, no compat certification, separate proof obligations, trusted/searchable fact separation, primitive rules, strict matching, `resolve1_match`, conservative `subst_premise`, and conservative `bicompose` wrapper. |
| Strict theorem invariants | `check_kernel_invariants(Strict)` rejects compat/admitted provenance, dummy-tainted burdens, `maxidx` drift, oracle-tainted strict theorems, and supported replay burden mismatches. |
| Proof outcome summary classifier | `src/isar/method.rs` classifies existing `verify_lemma` results as strict closed, compat closed oracle-free, open oracle-free, admitted, or failed without changing theorem construction. |
| Targeted strict vertical slice | A Pure implication identity smoke slice proves `A ==> A` through the strict kernel nucleus (`KernelRules::assume` + `implies_intr`) and verifies that the current ProofOutcome summary path counts the checked identity adapter as `StrictClosed` while rejecting the compat version. |
| Core/kernel migration framing | `src/core` is still a legacy proof engine today; the target is to shrink it into compatibility, automation, diagnostics, and migration adapters while `src/kernel` becomes the only TCB. |
| Oracle/admit tracking | `ThmKernel::admit(ct, reason)` marks unproved accepted propositions and propagates oracle footprints. |
| Closed theorem acceptance | A trusted proved lemma requires strict construction, no oracles, no hypotheses, no unresolved `tpairs`, and no dummy types. |
| Isar goal export boundary | `verify_lemma` no longer returns oracle-free open proof-method results as accepted lemmas. Results are exported by legal `implies_intr` discharge of known context assumptions, or admitted with `admitted:goal_export_*` / `admitted:proof_engine_failed`. |
| Simplifier rewrite-rule admission | `RewriteRule::from_thm` rejects open, admitted, unresolved, or conditional rewrite theorems instead of treating them as unconditional simp rules. Unproved HOL built-in rewrite templates are disabled until backed by closed theorem sources. |
| Searchable vs trusted facts | `HolTheoremDb` is a proof-search fact index; final trusted theorem tables use strict closed proved filters. |
| Attribute fallback honesty | Non-derivational theorem transformations are admitted as `admitted:attribute_transformation`. |
| T4 minimal replay | `assume`, `reflexive`, `symmetric`, `transitive`, `implies_intr`, `implies_elim` replay with burden checks. |
| HPC symbolic compute | Design-only parallel track for untrusted candidate generation, fingerprinting, and prefiltering; no Burn/CubeCL dependency and no kernel dependency. |
| Attack tests | `tests/kernel_soundness.rs`, `src/core/thm.rs`, and `src/core/proofterm.rs` encode regression attacks. |

Important distinction:

```text
is_fully_proved() == oracle-free
is_closed_proved() == oracle-free + no hyps + no unresolved tpairs
is_strict_closed_proved() == strict construction + is_closed_proved() + no dummy types
check_kernel_invariants(Strict) == strict construction + theorem invariant audit
```

`assume(A)` is a valid theorem of shape `A |- A`; it is not `|- A` and must not
be counted as a closed proved lemma.
`assume_compat` / `reflexive_compat` may still create closed-shaped facts, but
they are `ThmTrust::Compat` and must not be counted as trusted verified lemmas.
Passing `check_kernel_invariants(Strict)` means the theorem is internally
consistent as a strict theorem; final theorem-table acceptance still requires
`is_strict_closed_proved()`, and replay coverage remains partial.

## What Is Not Complete

The project is not close to full Isabelle/HOL:

| Layer | Honest current assessment |
|---|---|
| Term / type / certification boundary | Strict `CTerm::certify_checked` exists and is status-tracked, but legacy best-effort certification is still widely used through explicit `_compat` paths. |
| Pure kernel | Research-grade prototype with a strict invariant checker for core theorem internals, not full Isabelle `thm.ML` equivalence. |
| Proofterm replay | Minimal derivation replay, not full Isabelle `proofterm.ML` checking. |
| Isar | Partial state machine and method dispatch, far from full Isabelle/Isar semantics. |
| HOL tools | Simplifier/Metis/Meson/linarith/datatype packages are partial or heuristic. |
| HOL library coverage | Small subset; many accepted facts remain admitted or generated stubs. |
| Session/PIDE/LSP | Useful skeletons, not Isabelle session/PIDE infrastructure. |
| AFP / ecosystem | Out of scope for the current research slice. |

Current core verification status remains conservative:

```text
test_verify_all_core_files: 0/125 StrictClosed
ProofOutcome summary:
  StrictClosed: 0
  CompatClosedOracleFree: 1
  Admitted(goal_export_unknown_hyps): 66
  Admitted(goal_export_open_subgoals): 3
  Admitted(parser_gap): 3
  Admitted(datatype_stub): 2
  Admitted(proof_engine_failed): 50
```

The targeted `A ==> A` strict slice is intentionally not counted in this core
batch unless an existing sampled core-file lemma routes through that shape. The
next coverage milestone is therefore narrower and more honest than "make the
smoke test pass": route one existing parsed theorem through strict acceptance
without compat/admit/open fallback.

A scan of the sampled 125 core-file lemmas found no parsed proposition of the
form `A ==> A` / `P ==> P`, so the implication-identity adapter cannot move the
batch count by itself. The current best first existing-theorem candidate is
`HOL::TrueI`, whose source proof is `unfolding True_def by (rule refl)`. That
slice needs a narrow strict definition-unfold/reflexivity adapter, not a broader
`simp` or proof-engine fallback.

The former `OPEN_HAS_HYPS` runtime classification has been closed as a trust
boundary issue: proof-method results with ambient hypotheses are no longer
returned as oracle-free accepted lemmas. If they cannot be legally exported,
they are admitted with a specific `goal_export_*` reason. This improves
reporting honesty, not proof coverage.

Follow-up diagnostics after hardening `RewriteRule::from_thm` showed the
`goal_export_unknown_simp_context` subtype did not decline. Representative
`by simp` samples still reach unknown hyps through the surrounding
`exec_proof` fallback chain, so the next fix is the method fallback boundary,
not conditional rewrite implementation.

The next milestone is not broad HOL/Isar coverage. It is the first existing
core-file vertical strict-kernel acceptance slice:

```text
test_verify_all_core_files: 0/125 StrictClosed -> 1/125 StrictClosed
```

This must happen through strict theorem construction and acceptance, not by
reclassifying admitted, compat, or open oracle-free results.

## Relative Completion Estimates

These are semantic/engineering estimates, not line-count percentages.

| Scope | Current estimate |
|---|---:|
| Full Isabelle/HOL + Isar + PIDE + AFP ecosystem | 15%-25% |
| Isabelle/Pure-inspired Rust kernel research slice | 45%-60% |
| Oracle footprints + closed theorem acceptance specialty | 65%-75% |
| T4 proofterm replay/checker | 10%-20% |
| HOL tools and automation | 10%-20% |
| PIDE/session ecosystem | 5%-15% |

The numbers are intentionally conservative. Do not market the project as
"Rust Isabelle" or "feature-compatible with Isabelle".

## Known T2 Debts

These are trusted-boundary issues that T4 replay does not automatically solve:

| Debt | Why it matters | Correct direction |
|---|---|---|
| `compat_alpha_eq` Free/Const suffix matching | Still available for legacy parser/loader compatibility, but no longer used by trusted kernel equality. | Fix parser/loader/type annotation, then remove/narrow compat usage. |
| `compat_alpha_eq` Var/Free matching | Still available for schematic-variable parser gaps, but no longer used by trusted kernel equality. | Align theorem DB/parser representation of schematic variables. |
| `Typ::dummy()` at kernel boundaries | Lets ill-typed terms remain too long. | Make parser/type inference/CTerm certification produce well-typed certified terms. |
| Best-effort `CTerm::certify` call sites | Legacy paths can still wrap dummy-tainted terms. | Migrate explicit `_compat` theorem-construction call sites to `certify_checked`, real derivations, or `admit`. |
| Compatibility theorem taint | `_compat` constructors still exist for many old call sites. | Keep them searchable only; trusted acceptance uses `is_strict_closed_proved()`. |
| `Option<Thm>` errors | Type mismatch and normal non-match can both become `None`. | Gradually move trusted boundaries toward `Result<Option<Thm>, KernelError>`. |

## T4 Replay Status

Current supported replay rules:

```text
assume
reflexive
symmetric
transitive
implies_intr
implies_elim
```

Current replay behavior:

- `Thm::check_proof()` reconstructs theorem shape and compares `prop`, `hyps`,
  `tpairs`, and `oracles`.
- `Thm::validate_proof()` uses the same burden-aware replay gate.
- `ProofBody::check(expected_prop)` is proposition-only compatibility code and
  is not a trusted theorem validation gate.
- `POracle` / admitted theorem replay fails for independent kernel replay.
- Unsupported rules fail explicitly; they are not silently trusted.

This is a kernel derivation replay prototype, not a full Isabelle proofterm
checker. Isabelle-style proof reconstruction, `PThm` expansion, proof
compression, type abstraction/application, stored theorem graph replay, and full
primitive rule coverage are still open.

## Next Priority Order

Do not spend the next phase on more HOL/Isar surface features, LSP, WASM,
Sledgehammer, SMT, or Code Generator work. The route is:

1. Design and implement `ProofOutcome` as the single verification outcome model.
2. Create one final theorem acceptance path: only `StrictClosed` results enter
   trusted theorem tables.
3. Use the core/kernel overlap inventory and migration matrix to guide every
   proof-boundary change.
4. Migrate one small theorem path to strict-kernel acceptance and move the core
   batch from `0/125` to `1/125` `StrictClosed`.
5. Continue core hardening only as migration support: diagnostics, boundary
   checks, and adapters, not new trusted proof power in `src/core`.
6. Split and reduce admitted/compat paths by cause, especially method fallback
   and proof export reasons.
7. Extend T4 proofterm replay rule coverage after strict kernel semantics are
   stable.
8. Split into Cargo workspace (`isabelle-kernel` crate first).
9. Design session incremental engine (snapshot/rollback/content-addressed cache).
10. Build `isabelle.toml` project system (Lake-style).
11. Design Agent Proof Protocol (APP).
12. Expand HOL/Isar/tool coverage only after the trusted boundary remains stable.
13. Harden WASM plugin sandbox boundaries.
14. AFP large-scale benchmark.

Parallel non-blocking design track: high-performance symbolic compute may
define packed IR, a deterministic CPU baseline, and future optional Burn/CubeCL
backends. It must not add GPU/backend dependencies to the kernel, produce
trusted theorems, or delay the strict-kernel / resolution / admitted-inventory
main line.

The full layered platform architecture is formalized in
[docs/ADR-0002-layered-platform-architecture.md](ADR-0002-layered-platform-architecture.md).
See [docs/ROADMAP.md](ROADMAP.md) for detailed phase plans.

## Recommended Project Description

Use this in papers, README summaries, or external descriptions:

```text
Isabelle-rs is a Rust research prototype of an Isabelle/Pure-inspired
LCF-style proof kernel evolving into a layered proof engineering platform.
It focuses on explicit oracle footprints, closed-theorem acceptance,
proof-object replay, and agent-native proof interaction rather than broad
Isabelle/HOL feature parity.
```

Avoid:

```text
Rust rewrite of Isabelle
Feature-complete Isabelle/HOL in Rust
Full Isabelle-compatible prover
```
