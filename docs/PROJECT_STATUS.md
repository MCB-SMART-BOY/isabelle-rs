# Project Status and Positioning

This document is the canonical high-level status for Isabelle-rs. Agents should
read root [AGENTS.md](../AGENTS.md) first, then this document before older
roadmap, architecture, gap-analysis, or session notes.

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

## Trust Metric Correction

The sampled HOL result reported as `TransitionalStrictClosed: 1/125` is a
legacy `core::Thm + ThmTrust::Strict` migration classification. It does not
enforce a `CProp : prop` theorem conclusion and is not a
`src/kernel::TrustedTheorem`. The current status is:

```text
TransitionalStrictClosed: 1/125
KernelTrustedClosed:      0/125
```

In particular, the current `HOL::TrueI` bridge experiment stores bool-valued
`HOL.True` as its legacy theorem proposition. It exposed the missing
`HOL.Trueprop`, conservative definition, HOL axiom-basis, and immutable theory
context boundaries; it is not a completed Isabelle/Pure trusted theorem loop.
The new `src/kernel` already represents theorem conclusions as `CProp` and
rejects non-`prop` certification. The gap is that no current HOL theorem slice
reaches that new-kernel boundary.

## Historical Baseline And Current Gate

The first trusted-kernel engineering checkpoint is recorded in
[BASELINE.md](BASELINE.md). It includes four reviewable commits:

```text
e60580b kernel: harden primitive rules and checked instantiation
7465d48 trust: require closed proved theorems for trusted acceptance
2dee3d0 proofterm: add minimal burden-aware derivation replay
eef6d80 docs: reposition project as trusted Rust LCF kernel prototype
```

The baseline gate is `scripts/dev-check.sh strict`; the implementation is
[check-strict-kernel.sh](../scripts/check-strict-kernel.sh).

The baseline originally carried two ignored `alpha_eq` tests:

```text
Free / Const suffix matching
Var / Free index confusion
```

Strict kernel alpha-equivalence now rejects both in trusted paths. The legacy
behavior is isolated as explicit `compat_alpha_eq` parser/loader compatibility.
A completed legacy hardening step added `CTerm::certify_checked(term, type_env)`,
which provides a hard certification API that rejects residual dummy types and
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

A separate architectural reset now exists in `src/kernel/`. This is a new strict
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

As of 2026-07-18, the correct maturity statement is: the Pure kernel research
nucleus is meaningful and substantially hardened, but the minimum
Isabelle/Pure trusted loop is not closed. In particular, no sampled HOL theorem
yet combines source-faithful elaboration, `CProp : prop`, immutable theory/logic
identity, conservative definitions, an explicit HOL basis, and new-kernel
acceptance.
The current implementation inventory and the minimal context-bound acceptance
API are audited in
[KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](KERNEL_TRUSTED_ACCEPTANCE_GAPS.md).

## Repository And Agent Policy

Root [AGENTS.md](../AGENTS.md) is the versioned, harness-neutral rule source.
`.claude/`, `~/.codex/`, and harness memory are routing/cache layers and cannot
override source, tests, canonical status/trust docs, or accepted ADRs.

Short explanatory code/configuration blocks are allowed in Markdown. Large
runnable or repeated snippets live in `scripts/` or classified
`scripts/templates/`. Standalone template compilation does not establish
compatibility with the production API or validate a trusted architecture.

Dependency and vendor changes remain separate from trust-boundary work.
Unexplained lock-only refreshes are not accepted merely because
`cargo metadata --locked` succeeds.

## What Is Solid

The following areas have a coherent implementation and regression coverage:

| Area | Current state |
|---|---|
| LCF-style theorem type | `Thm` fields are private; external construction routes through `ThmKernel`. |
| Kernel primitive rules | All 15 base primitives implemented (assume, reflexive, symmetric, transitive, combination, abstraction, beta_conversion, implies_intr, implies_elim, forall_intr, forall_elim, equal_intr, equal_elim, generalize, instantiate); several rounds of type/burden/oracle boundary hardening done. |
| Checked instantiation | Production paths use `instantiate_checked`; legacy infallible instantiation is not a production API. |
| Strict alpha equality | Trusted kernel equality uses `kernel_alpha_eq`; legacy broad matching is isolated as `compat_alpha_eq`. |
| Checked CTerm certification | `CTerm::certify_checked` exists, CTerms carry checked/compat status, and strict `assume`/`reflexive` reject compat terms. |
| Source proposition fail-closed guard | The loader records typed consumption status and a narrow source-shape classification. The registered explicit-proof `TrueI` adapter requires `FullyConsumed + StandaloneHolTrueAlias`; recovered, contextual, incomplete, or unavailable source becomes `admitted:strict_adapter_source_prop_unverified` without parser-gap or legacy fallback. This is transitional metadata, not a name-resolved AST. |
| Proof-state strict entry points | `ProofState::assume`, `Goal::init`, and checked subgoal scaffolding construct Strict open theorem obligations from explicit proof-context certification. |
| Strict kernel nucleus | `src/kernel` contains an isolated TCB nucleus with no dummy type, no compat certification, separate proof obligations, trusted/searchable fact separation, primitive rules, strict matching, `resolve1_match`, conservative `subst_premise`, and conservative `bicompose` wrapper. |
| Strict theorem invariants | `check_kernel_invariants(Strict)` rejects compat/admitted provenance, dummy-tainted burdens, `maxidx` drift, oracle-tainted strict theorems, and supported replay burden mismatches. |
| Proof outcome summary classifier | `src/isar/method.rs` classifies existing `verify_lemma` results as transitional strict closed, compat closed oracle-free, open oracle-free, admitted, or failed without changing theorem construction. |
| Targeted migration slice | A Pure implication identity smoke slice exercises the strict kernel nucleus (`KernelRules::assume` + `implies_intr`), while the current ProofOutcome adapter reports a legacy result as `TransitionalStrictClosed`. The summary label itself is not a new-kernel theorem handle. |
| Core/kernel migration framing | `src/core` is still a legacy proof engine today; the target is to shrink it into compatibility, automation, diagnostics, and migration adapters while `src/kernel` becomes the only TCB. |
| Checked definition sources | `HolTheoremDb` has a separate `checked_definitions` table for non-theorem definition inputs. The first entry is `True_def`, checked against the explicit `TypeEnv`; it is not inserted into searchable facts and is not counted as `TransitionalStrictClosed` or `KernelTrustedClosed`. |
| Oracle/admit tracking | `ThmKernel::admit(ct, reason)` marks unproved accepted propositions and propagates oracle footprints. |
| Closed theorem acceptance | The legacy filter requires strict construction, no oracles, no hypotheses, no unresolved `tpairs`, and no dummy types. Final trust additionally requires a context-bound `src/kernel::TrustedTheorem` over `CProp : prop`; no sampled HOL theorem has reached that gate. |
| Isar goal export boundary | `verify_lemma` no longer returns oracle-free open proof-method results as accepted lemmas. Results are exported by legal `implies_intr` discharge of known context assumptions, or admitted with `admitted:goal_export_*` / `admitted:proof_engine_failed`. |
| Simplifier rewrite-rule admission | `RewriteRule::from_thm` rejects open, admitted, unresolved, or conditional rewrite theorems instead of treating them as unconditional simp rules. Unproved HOL built-in rewrite templates are disabled until backed by closed theorem sources. |
| Searchable vs trusted facts | `HolTheoremDb` is a proof-search and migration index. Its legacy strict filter is not the final trusted-theory gate; final acceptance requires a context-bound `src/kernel::TrustedTheorem` and is recorded as `KernelTrustedClosed`. |
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
consistent as a legacy strict theorem. The transitional legacy table additionally
requires `is_strict_closed_proved()`; final acceptance instead requires a
context-bound new-kernel `TrustedTheorem` and the `KernelTrustedClosed` gate.

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

Current core verification status records one transitional migration slice and
zero new-kernel trusted HOL theorems:

```text
TransitionalStrictClosed: 1/125
KernelTrustedClosed:      0/125
ProofOutcome summary:
  TransitionalStrictClosed: 1
  CompatClosedOracleFree: 1
  Admitted(goal_export_unknown_hyps): 65
  Admitted(goal_export_open_subgoals): 3
  Admitted(parser_gap): 3
  Admitted(datatype_stub): 2
  Admitted(proof_engine_failed): 50
```

The targeted `A ==> A` kernel smoke slice is intentionally not counted in this
core batch unless an existing sampled core-file lemma routes through that
shape. It demonstrates Pure kernel construction but is not an existing sampled
theorem and does not repair HOL source elaboration.

A scan of the sampled 125 core-file lemmas found no parsed proposition of the
form `A ==> A` / `P ==> P`, so the implication-identity adapter could not move
the batch count by itself. The first existing-theorem transitional slice is
`HOL::TrueI`, whose source proof is `unfolding True_def by (rule refl)`. It is
routed through the legacy checked payload and named bridges, not through
`simp`, compat `refl`, or ProofOutcome reclassification.

Targeted `HOL::TrueI` diagnostics and bridge work currently show:

```text
Parsed TrueI prop: True
Parsed TrueI proof: unfolding True_def by (rule refl)
Source proposition status: FullyConsumed
Source proposition shape: StandaloneHolTrueAlias
Current outcome: TransitionalStrictClosed
True_def parsed theorem / DB fact: missing (expected; definition source is not a theorem)
True_def checked definition source: done, non-theorem input only
HOL object-equality/reflexivity bridge: implemented as narrow legacy bridge
try_strict_hol_refl: implemented
theorem-specific transport/fold-back to True: implemented for legacy True_def payload
try_strict_hol_true_i adapter: implemented as a narrow TrueI-only adapter
refl DB fact: compat/open, not TransitionalStrictClosed
Pure.refl DB fact: compat closed-shaped, not TransitionalStrictClosed
TransitionalStrictClosed: 1/125
KernelTrustedClosed:      0/125
```

The compatibility parser still deliberately returns a parsed prefix, and its
recovery can reduce malformed `True =` source to the same legacy `HOL.True`
term while reporting `FullyConsumed`. The loader therefore retains both
`SourcePropositionStatus` and `SourcePropositionShape`. The `TrueI` adapter
requires `FullyConsumed + StandaloneHolTrueAlias`; `True =` is
`FullyConsumed + Other`, while local `fixes` / `includes`, locale-qualified
lemmas, and enclosing contexts are `FullyConsumed + Contextual`. Those cases, incomplete
input, and missing provenance all produce
`admitted:strict_adapter_source_prop_unverified` before the legacy builtin
parser-gap override and never fall through to legacy verification.

This is a transitional fail-closed guard, not checked source elaboration. The
shape enum is a deliberately narrow lexical/context classification; it neither
resolves whether a name is shadowed nor supplies a name-resolved source AST or
an unforgeable certification token.

Therefore the first existing-core-file transitional milestone has been reached
through the narrow `HOL::TrueI` adapter:

```text
1. True_def checked legacy payload: done, non-theorem input only
2. HOL object-equality/reflexivity bridge: implemented as narrow legacy bridge
3. theorem-specific transport/fold-back to True: implemented for the payload
4. try_strict_hol_true_i adapter: implemented
```

The bridge designs are tracked in
[HOL_OBJECT_EQUALITY_BRIDGE.md](HOL_OBJECT_EQUALITY_BRIDGE.md) and
[CHECKED_DEFINITION_TRANSPORT.md](CHECKED_DEFINITION_TRANSPORT.md). They are
explicitly not a general unfolding engine, simplifier, or broad HOL proof
engine.

Do not generalize this `TrueI` path by returning `True` directly, using the
current compat `refl` fact, or turning it into a general unfolding/simp engine.
The `TrueI` path is now routed through the minimal strict adapter dispatcher in
`src/isar/method.rs`. The dispatcher currently registers only this adapter and
returns explicit `NotApplicable` / `Proved` / `Rejected(reason)` outcomes so
future strict slices do not turn `verify_lemma` into a theorem-name switchboard.
Shape-hit rejections are admitted with `admitted:strict_adapter_*` reasons
instead of falling through as ordinary legacy proof-engine failures.
The ranked scan of the remaining 124 sampled theorems is retained as a
diagnostic inventory in
[NEXT_STRICT_SLICE_CANDIDATES.md](NEXT_STRICT_SLICE_CANDIDATES.md); its original
adapter recommendation is superseded by immutable context acceptance.

The `TrueI` dispatcher entry now relies on an explicit parser alias:
source-level `True` / `HOL.True` becomes canonical `Const("HOL.True", bool)`.
The strict normalizer no longer converts a `Free("True")` or dummy-typed True
into a checked proposition. For lemmas with an explicit proof, registered
strict adapters run before the legacy builtin Var/Free parser-gap shortcut;
only `NotApplicable` continues to compatibility verification.

`HOL::trans` remains deferred. The common future checked proposition boundary
and object-logic trust layer are specified in
[CHECKED_HOL_PROPOSITION_NORMALIZATION.md](CHECKED_HOL_PROPOSITION_NORMALIZATION.md)
and
[ADR-0003-hol-logic-trusted-extension.md](ADR-0003-hol-logic-trusted-extension.md).
Both are design gates, not new proof power. The current `1/125` result remains a
legacy `core::Thm` migration classification rather than a new-kernel
`TrustedTheorem`.

The former `OPEN_HAS_HYPS` runtime classification has been closed as a trust
boundary issue: proof-method results with ambient hypotheses are no longer
returned as oracle-free accepted lemmas. If they cannot be legally exported,
they are admitted with a specific `goal_export_*` reason. This improves
reporting honesty, not proof coverage.

Follow-up diagnostics after hardening `RewriteRule::from_thm` showed the
`goal_export_unknown_simp_context` subtype did not decline. Representative
`by simp` samples still reach unknown hypotheses through the surrounding
`exec_proof` fallback chain. That remains admitted-path debt; it does not
preempt immutable context identity or justify conditional rewrite proof power.

The just-completed milestone is not broad HOL/Isar coverage or new-kernel
acceptance. It is the first existing core-file legacy adapter slice:

```text
TransitionalStrictClosed: 0/125 -> 1/125
KernelTrustedClosed:      0/125
```

The adapter still usefully rejects admitted, compat, and open fallback, but its
bool-valued legacy theorem is not evidence of an Isabelle/Pure trusted proof
loop.

## Relative Completion Estimates

These are semantic/engineering estimates, not line-count percentages.

| Scope | Current estimate |
|---|---:|
| Full Isabelle/HOL + Isar + PIDE + AFP ecosystem | 15%-25% |
| Isabelle/Pure-inspired Rust kernel research slice | 45%-60% |
| Minimal end-to-end Isabelle/Pure trusted kernel | 30%-40% |
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
| Transitional source status/shape metadata | `parse_term` may return a prefix or recover malformed syntax, and surface names may be shadowed by local context. The current guard catches known unsafe shapes but is not name resolution. | Keep compatibility behavior isolated, require the narrow fail-closed guard for current adapters, and build a name-resolved source AST for future checked elaboration. |
| `Typ::dummy()` at kernel boundaries | Lets ill-typed terms remain too long. | Make parser/type inference/CTerm certification produce well-typed certified terms. |
| Best-effort `CTerm::certify` call sites | Legacy paths can still wrap dummy-tainted terms. | Migrate explicit `_compat` theorem-construction call sites to `certify_checked`, real derivations, or `admit`. |
| Compatibility theorem taint | `_compat` constructors still exist for many old call sites. | Keep them searchable only; use `is_strict_closed_proved()` solely for transitional filtering and require `KernelTrustedClosed` for final trust. |
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
Sledgehammer, SMT, or Code Generator work. The immediate source slice is
immutable context identity; the route is:

1. Introduce immutable `TheoryId` / `SignatureId` values and propagate exact
   context identity through `ProofContext`, certified terms, and strict
   theorems.
2. Implement one context-bound, mutually exclusive `KernelTrustedClosed`
   acceptance gate while retaining the separate `TransitionalStrictClosed`
   migration report.
3. Preserve a source-aware proposition AST that distinguishes meta/HOL
   connectives, scopes, term identities, types/sorts, spans, and implicit
   judgment positions before legacy lowering.
4. Elaborate checked `judgment`, constant, and polymorphic type-scheme
   declarations, including `HOL.Trueprop`, into the existing `CProp : prop`
   boundary.
5. Install the explicit HOL logical basis as an immutable data-only manifest
   and replay generic axiom-schema instances through Pure kernel rules; add no
   theorem-specific Rust constructors.
6. Implement a generic conservative definition extension before treating
   `True_def` as trusted input; the legacy `true_def_transport` bridge is not a
   certificate.
7. Re-derive `HOL::TrueI` as the first real `KernelTrustedClosed` HOL theorem
   before resuming `HOL::trans` or any `2/125` coverage work.
8. Continue core hardening only as migration support: diagnostics, boundary
   checks, and adapters, not new trusted proof power in `src/core`.
9. Split and reduce admitted/compat paths by cause, especially method fallback
   and proof export reasons.
10. Extend T4 proofterm replay rule coverage after strict kernel semantics are
    stable.
11. Split into Cargo workspace (`isabelle-kernel` crate first).
12. Design session incremental engine (snapshot/rollback/content-addressed cache).
13. Build `isabelle.toml` project system (Lake-style).
14. Design Agent Proof Protocol (APP).
15. Expand HOL/Isar/tool coverage only after the trusted boundary remains stable.
16. Harden WASM plugin sandbox boundaries.
17. AFP large-scale benchmark.

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
