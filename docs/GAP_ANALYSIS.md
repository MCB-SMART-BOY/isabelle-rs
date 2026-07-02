# Gap Analysis: Isabelle-rs vs Isabelle

This document gives an honest comparison between Isabelle-rs and full
Isabelle/HOL. It is intentionally conservative.

Read [PROJECT_STATUS.md](PROJECT_STATUS.md) first.

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
| Closed theorem acceptance | ~70% | Main statistics and final trusted tables use strict closed proved filters. |
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
strict closed proved theorem
open theorem with hypotheses
admitted theorem
searchable fact
trusted theorem table entry
```

This distinction is central. In particular:

```text
is_fully_proved() != is_closed_proved() != is_strict_closed_proved()
```

### Strict Kernel vs Legacy Core Firewall

The strict `src/kernel/` nucleus is enforced by automated checks:
- `scripts/check-kernel-firewall.sh` validates no legacy dependencies or forbidden patterns.
- `pub(in crate::kernel)` visibility gating prevents upper-layer modules (`src/core/`, `src/isar/`, `src/tools/`) from bypassing certified-origin constructors.
- `scripts/check-strict-kernel.sh` runs the full 7-step gate (fmt, check, firewall, 124 attack, 26 soundness, 56 kernel inline, 199 core).

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
bicompose ⚠️ LEGACY CORE
bicompose_eresolve ⚠️ LEGACY CORE
subst_premise ⚠️ LEGACY CORE
```

The harder rules are `instantiate_checked`, `bicompose*` (⚠️ LEGACY CORE), `subst_premise` (⚠️ LEGACY CORE), and
`abstraction`, because they interact with unification, variable discipline,
typing, and theorem burdens.

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

1. Harden kernel equality/certification boundaries.
2. Extend T4 replay to the next primitive rules after strict kernel semantics
   are stable.
3. Reduce `Typ::dummy()` at theorem construction sites.
4. Shrink admitted lemmas by reason while preserving oracle footprints.
5. Only then increase HOL/Isar surface coverage.
