# Gap Analysis: Isabelle-rs vs Isabelle

This document gives an honest comparison between Isabelle-rs and full
Isabelle/HOL. It is intentionally conservative.

Read root [AGENTS.md](../AGENTS.md), then
[PROJECT_STATUS.md](PROJECT_STATUS.md), first.

## Executive Summary

Isabelle-rs is not close to full Isabelle. It is best understood as a
Rust-native research slice:

```text
Isabelle/Pure-inspired LCF kernel
+ oracle/admit footprint tracking
+ closed theorem acceptance
+ minimal proofterm replay
```

Compared with complete Isabelle/HOL + Isar + PIDE + AFP, the project is still
early. Compared with the narrower research goal of a Rust LCF kernel and trust
boundary experiment, it is meaningful and already useful.

## Relative Completion Estimates

These are semantic and engineering estimates, not line-count percentages.

| Layer / scope | Current estimate | Comment |
|---|---:|---|
| Full Isabelle/HOL + Isar + PIDE + AFP ecosystem | 15%-25% | Isabelle's ecosystem, libraries, tools, PIDE, and AFP are far larger. |
| Isabelle/Pure-inspired Rust kernel research slice | 45%-60% | Core theorem type and several primitive rules exist, but not full `thm.ML` equivalence. |
| Term / Typ / CTerm foundation | 40%-50% | Basic structures exist; parser/type/certification boundary remains weak. |
| LCF `Thm` kernel | 50%-60% | Research prototype with recent soundness hardening. |
| Primitive inference rules | 40%-55% | Important subset implemented; coverage and Isabelle equivalence incomplete. |
| Oracle/admit tracking | 65%-75% | Strong project area: explicit footprints and propagation. |
| Closed theorem acceptance | ~70% for legacy filtering; 0 sampled HOL theorems at the target gate | Statistics report `TransitionalStrictClosed`; final `TrustedTheory` still requires context-bound new-kernel theorems. |
| Proofterm replay/checker | 10%-20% | Minimal derivation replay, not full Isabelle proofterm checker. |
| Isar proof engine | 25%-35% | Partial state machine and method dispatch. |
| Simplifier / automation | 10%-20% | Useful prototypes, far from HOL Tools. |
| HOL theory loading | 8%-15% | Partial theory processing; many gaps and admitted facts. |
| Session/build system | 15%-25% | Statistics and DAG skeleton exist; not Isabelle sessions. |
| PIDE / IDE / LSP | 5%-15% | Skeleton only. |
| Isabelle library / AFP ecosystem | 1%-5% | Essentially out of current scope. |

## What Isabelle Has That Isabelle-rs Does Not

Full Isabelle includes:

- Mature Pure kernel, proof terms, theory/context infrastructure, and proof
  reconstruction.
- Full Isabelle/Isar command language, proof contexts, local theories, locales,
  classes, attributes, methods, and proof state tooling.
- HOL packages: simplifier, classical reasoner, Metis, Sledgehammer, SMT,
  Nitpick, Quickcheck, Code Generator, Datatype/BNF, Function, Inductive,
  Transfer/Lifting, Quotient, and more.
- Isabelle/Scala + PIDE document model, incremental checking, session database,
  build graph, IDE integrations, and large-scale parallel checking.
- Decades of HOL libraries and AFP developments.

Isabelle-rs has prototypes or partial versions of some of these, but not the
same semantic coverage or robustness.

## Where Isabelle-rs Is Strong

### Explicit Trust Accounting

The project makes these statuses explicit:

```text
oracle-free theorem
closed proved shape
transitional strict closed theorem
kernel-trusted closed theorem
open theorem with hypotheses
admitted theorem
searchable fact
trusted theorem table entry
```

This distinction is central. In particular:

```text
is_fully_proved() != is_closed_proved() != is_strict_closed_proved()
```

All three predicates above inspect legacy `core::Thm`; even
`is_strict_closed_proved()` is only the `TransitionalStrictClosed` classifier.
Final acceptance requires a context-bound `src/kernel::TrustedTheorem` over
`CProp : prop`, immutable theory/logic provenance, and the selected replay gate.

Recent verification diagnostics made this distinction stricter. Proof-method
results with ambient hypotheses are no longer returned as oracle-free accepted
lemmas: they must be exported by legal `implies_intr` discharge of known
context assumptions, or admitted with `admitted:goal_export_*` /
`admitted:proof_engine_failed`. This removes the misleading `OPEN_HAS_HYPS`
runtime bucket, but it does not improve proof coverage:

```text
TransitionalStrictClosed: 1/125
KernelTrustedClosed:      0/125
CompatClosedOracleFree: 1
Admitted(goal_export_unknown_hyps): 65
Admitted(proof_engine_failed): 50
Admitted(goal_export_open_subgoals): 3
Admitted(parser_gap): 3
Admitted(datatype_stub): 2
```

Immutable theory/signature identity is now implemented. The next trust-critical
sequence is one context/dependency-aware `KernelTrustedClosed` acceptance
operation, a source-aware proposition AST, checked HOL basis elaboration, and
generic conservative definitions. Admitted-reason reduction remains useful but
must not reclassify transitional or compatibility results as trusted proofs.

`RewriteRule::from_thm` now rejects theorem hyps, oracle/admitted footprints,
unresolved `tpairs`, and Pure-premise conditional rewrites. This prevents open
or admitted theorems from entering the simplifier as unconditional rewrite
rules. Unproved HOL built-in rewrite templates are also skipped until backed by
closed theorem sources. A follow-up subtype diagnostic still left
`goal_export_unknown_simp_context` unchanged, which points to `exec_proof`'s
simp-to-auto/blast fallback path rather than rewrite-rule admission as the next
target.

### Strict Kernel vs Legacy Core Firewall

The strict `src/kernel/` nucleus is enforced by automated checks:
- `scripts/check-kernel-firewall.sh` validates no legacy dependencies or forbidden patterns.
- `pub(in crate::kernel)` visibility gating prevents upper-layer modules (`src/core/`, `src/isar/`, `src/tools/`) from bypassing certified-origin constructors.
- `scripts/dev-check.sh strict` runs the maintained full gate: formatting,
  compilation, firewall, current attack/boundary suites, strict inline suites,
  and legacy `core::` compatibility tests. The script output is authoritative
  for test counts.

### Attack-Test-Driven Kernel Work

The regression suite now includes attacks for:

- ill-typed transitivity and instantiation;
- beta-conversion exposing raw `Bound(0)`;
- open theorem misclassification;
- `accept_all` admitted facts being counted as verified;
- attribute transformations using `assume` as a fake proof;
- proofterm tampering;
- oracle premise replay;
- stale checked proof bodies.

This makes the project useful as a kernel-security case study even before it is
feature-complete.

### Rust-Native Integration

The codebase is suitable for experiments that would be harder inside
Isabelle/ML + Scala:

- embedding a small checker as a Rust crate;
- integrating with Rust agent runtimes and CI tools;
- exposing machine-readable theorem status;
- separating proof-search facts from trusted theorem tables;
- forcing all fallback through typed admitted/oracle footprints.

## Major Remaining Gaps

### Theory Identity, Acceptance, And HOL Authorization

Immutable identity and Pure-only acceptance are implemented for the current
strict monomorphic kernel. `CTerm`, `CProp`, `KernelThm`, and
`TrustedTheorem` carry exact `TheoryId` / `SignatureId` stamps; rules reject
mixed contexts before logical matching; and `accept_closed_theorem` owns
recursive recertification/replay, replay-derived theorem dependencies,
duplicate-safe immutable insertion, and token sealing.

The largest immediate gap is now source-aware elaboration into an authorized
object-logic theory. The current root/signature can express synthetic Pure
contexts, but it has no checked polymorphic declaration pipeline,
`LogicBasisId`, installed HOL axiom schemas, or conservative definition
certificates. Those layers must exist before any sampled HOL theorem can use the
implemented acceptance gate.

See
[KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](KERNEL_TRUSTED_ACCEPTANCE_GAPS.md).

### Term / Type / Certification Boundary

Current debts:

```text
Typ::dummy()
Free / Const confusion
Var / Free compatibility
compatibility-only alpha_eq matching
parser / loader / theorem DB representation mismatch
```

These are trusted-boundary issues. T4 replay does not automatically fix them.
The correct direction is to make parser, loader, type inference, and `CTerm`
certification produce well-typed terms with correct heads before they reach the
kernel.

### Kernel Rule Coverage

Existing replay covers only:

```text
assume
reflexive
symmetric
transitive
implies_intr
implies_elim
```

Important missing replay coverage:

```text
beta_conversion
forall_intr
forall_elim
combination
abstraction
equal_intr
equal_elim
instantiate_checked
generalize
bicompose ✅ strict conservative wrapper implemented; full legacy semantics remain compatibility debt
bicompose_eresolve ⚠️ LEGACY CORE
subst_premise ✅ strict conservative version implemented
```

The harder remaining rules are `instantiate_checked`, full `bicompose*`
semantics (⚠️ LEGACY CORE), and `abstraction`, because they interact with
unification, variable discipline, typing, and theorem burdens. Strict
`subst_premise` now has only the conservative propositional-equality version;
strict `bicompose` has only the conservative `resolve1_match` wrapper version;
legacy-core full resolution remains compatibility debt.

### Isar

Current status:

- state machine and method dispatch exist;
- some commands and structured proof patterns work;
- many features are partial or approximated.

Missing or incomplete:

- full grammar and command classification;
- local theory targets;
- context export/import;
- full `fix`/`assume`/`show`/`have` semantics;
- `obtain`, `cases`, locales, classes, and attributes at Isabelle level;
- method combinators and proof context type checking.

### HOL Tools

This is the largest gap. The following are far from Isabelle parity:

```text
simp / auto / blast
metis / meson
sledgehammer / SMT
linarith / presburger
datatype / codatatype / BNF
function / inductive
transfer / lifting / quotient
named theorems and attributes
code generator
nitpick / quickcheck
```

Some prototypes exist; many facts remain admitted or generated stubs.

### Session / PIDE / IDE

Isabelle's PIDE/session infrastructure is a mature distributed document and
build system. Isabelle-rs currently has:

- a session builder skeleton;
- closed theorem count reporting;
- searchable fact databases;
- LSP/WASM skeletons.

This is not comparable to Isabelle/PIDE.

## Recommended External Positioning

Use:

```text
A Rust research prototype of an Isabelle/Pure-inspired LCF kernel
with explicit oracle footprints, closed-theorem acceptance,
and minimal proofterm replay.
```

Avoid:

```text
Rust rewrite of Isabelle
Feature-complete Isabelle/HOL in Rust
Drop-in replacement for Isabelle
```

## Next Work With Highest Research Value

1. Keep immutable `SignatureId` / `TheoryId` and mixed-context rejection stable.
2. Add one context/dependency-aware theorem acceptance operation and mutually
   exclusive `KernelTrustedClosed` outcome.
3. Preserve a source-aware proposition AST before legacy lowering.
4. Elaborate checked `HOL.Trueprop` and polymorphic declarations into
   `CProp : prop`.
5. Install a data-only HOL basis and generic conservative definitions.
6. Re-derive `HOL::TrueI` through the new kernel.
7. Continue replay/attack-test hardening and admitted-reason reduction without
   adding proof power to legacy `src/core`.
8. Keep symbolic compute design-only and untrusted; increase broad HOL/Isar
   coverage only after the trusted loop closes.
