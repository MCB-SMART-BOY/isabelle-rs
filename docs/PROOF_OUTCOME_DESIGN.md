# Proof Outcome Design

## Status

Phase 1 summary classifier implemented in `src/isar/method.rs`.

Current implementation:

- defines `ProofOutcome`, `TheoremSummary`, `OpenReason`, `AdmitReason`, and
  `ProofFailure`;
- classifies existing `verify_lemma` results without changing theorem
  construction;
- keeps `StrictClosed` separate from compat, open, admitted, and failed
  outcomes;
- makes `test_verify_all_core_files` print ProofOutcome summary counts.
- includes a targeted Pure implication identity smoke slice: `A ==> A` can be
  constructed by the strict kernel nucleus, and the current `verify_lemma`
  summary path can count the checked identity adapter as `StrictClosed`.

Not yet implemented:

- final theorem-table acceptance has not been rewritten around `ProofOutcome`;
- no existing HOL/core-file theorem has been migrated to `StrictClosed` yet;
- `StrictClosed` remains `0/125` in the core verification batch because the
  sampled core lemmas do not currently route through the targeted identity
  slice.

## Problem

The project currently has several overlapping theorem-status concepts:

```text
oracle-free
closed-shaped
strict construction
compat construction
admitted(reason)
open theorem
proof-method failure
```

These are not interchangeable. In particular:

```text
oracle-free != strict proved
compat closed != strict closed
open theorem != accepted theorem
```

Recent goal-export work made this boundary more honest: proof-method results
with unknown hypotheses are now admitted with `goal_export_*` reasons instead
of being reported as misleading open oracle-free results. The next step is to
replace scattered predicates and string reasons with one explicit outcome model.

## Goals

- Provide a single classification for every theorem verification attempt.
- Make trusted theorem-table acceptance depend only on strict closed outcomes.
- Keep compat/oracle-free facts searchable without counting them as proved.
- Structure admitted and failure reasons for stable reports.
- Give the core-to-kernel migration a measurable target: `0/125 -> 1/125`
  `StrictClosed` in the core verification batch.

## Non-Goals

- Do not add new proof power to `src/core`.
- Do not make compatibility theorems trusted.
- Do not hide admitted paths behind successful-looking outcomes.
- Do not implement APP, LSP, workspace, HPC, Burn, or CubeCL work here.

## Proposed Outcome Model

The implemented Phase 1 shape is intentionally summary-first. It stores a
`TheoremSummary` rather than moving theorem ownership through every caller:

```rust
pub enum ProofOutcome {
    StrictClosed {
        summary: TheoremSummary,
    },
    CompatClosedOracleFree {
        summary: TheoremSummary,
    },
    OpenOracleFree {
        reason: OpenReason,
        summary: TheoremSummary,
    },
    Admitted {
        reason: AdmitReason,
        summary: TheoremSummary,
    },
    Failed {
        reason: ProofFailure,
        name: String,
    },
}
```

The model intentionally separates theorem storage from theorem summaries. A
report does not need to retain a full legacy theorem to explain why a proof did
not become trusted.

## Outcome Semantics

| Outcome | Meaning | Trusted theorem table? |
|---|---|---|
| `StrictClosed` | Result was constructed by the strict path, has no oracles, no hypotheses, no unresolved `tpairs`, no dummy types, and passed the required acceptance gate. | Yes |
| `CompatClosedOracleFree` | Legacy theorem is closed-shaped and oracle-free, but not strict. | No |
| `OpenOracleFree` | Legacy theorem is oracle-free but still has open hypotheses, subgoals, unresolved `tpairs`, or another open condition. | No |
| `Admitted` | The system accepted an unproved proposition with an explicit reason. | No |
| `Failed` | The proof attempt failed without producing an accepted theorem. | No |

Only `StrictClosed` may enter final trusted theorem tables. All other outcomes
may be useful for proof search, diagnostics, or migration prioritization, but
their taint must not be erased.

## Structured Reasons

Initial `OpenReason` categories:

```text
UnknownHyps
OpenSubgoals
UnresolvedTpairs
PropMismatch
SelfGoalHyp
RulePremiseHyp
MethodFallbackHyp
LocalAssumeLeak
ParserCompatOpen
Other
```

Initial `AdmitReason` categories:

```text
GoalExportUnknownHyps
GoalExportOpenSubgoals
GoalExportPropMismatch
GoalExportUnresolvedTpairs
GoalExportDischargeFailed
GoalInitializationFailed
ParserGap
DatatypeStub
AttributeTransformation
ProofEngineFailed
FinalGeneralizeFallback
UnsupportedMethod
FactLookupFailed
OracleOrAdmittedResult
Other
```

Initial `ProofFailure` categories:

```text
MethodNone
UnsupportedStructuredIsar
ReplayFailed
StrictCertificationFailed
KernelReplayMismatch
Timeout
Panic
Other
```

String reasons such as `admitted:goal_export_unknown_hyps` can remain as a
compatibility layer, but the target report should be derived from structured
reason values.

## Acceptance Policy

Final theorem acceptance must flow through one gate:

```text
proof method / replay / adapter
  -> ProofOutcome
  -> StrictClosed only enters TrustedTheory / trusted theorem tables
```

Rules:

- `CompatClosedOracleFree` may be searchable, but not trusted.
- `OpenOracleFree` must not be counted as proved.
- `Admitted` must keep its explicit reason.
- `Failed` must not create a theorem.
- A dynamic report must not classify `oracle-free` as `proved` without checking
  the full strict closed predicate.

## Reporting Target

Verification reports should become stable outputs over `ProofOutcome`:

```text
StrictClosed: N
CompatClosedOracleFree: N
OpenOracleFree(reason): N
Admitted(reason): N
Failed(reason): N
```

This replaces one-off diagnostic runners and avoids conflating static call-site
counts with runtime theorem outcomes.

## Migration Phases

| Phase | Gate |
|---|---|
| Phase 0: design | This document exists and status docs point to it. |
| Phase 1: summary classifier | Implemented. Existing `verify_lemma` results are summarized without changing theorem construction. |
| Phase 2: report integration | Core verification reports count `ProofOutcome` buckets instead of ad-hoc strings. |
| Phase 3: acceptance integration | Final theorem tables accept only `StrictClosed`. |
| Phase 4a: targeted strict slice | Direct `A ==> A` strict-kernel smoke test and ProofOutcome adapter test classify the checked identity as `StrictClosed`. |
| Phase 4b: first core-file strict slice | At least one existing core verification theorem is classified as `StrictClosed`. |

## First Strict Closed Slice Candidates

| Candidate | Required strict rules | Advantages | Risks |
|---|---|---|---|
| Pure reflexivity `t == t` | `KernelRules::reflexive`, checked term certification, `ClosedThm::trust` | Smallest strict kernel smoke test. | May not correspond to a current core-file lemma. |
| Implication identity `A ==> A` | `KernelRules::assume`, `KernelRules::implies_intr`, checked proposition certification | Exercises hypothesis discharge and closed theorem acceptance. | Targeted smoke slice implemented; still needs routing from an existing core-file lemma. |
| Simple equality theorem | Reflexivity plus equality encoding adapter | Closer to HOL-facing facts. | HOL equality/object equality boundaries may add noise. |
| `HOL::TrueI` | Checked `True_def`, strict HOL object-equality/reflexivity bridge, narrow adapter | Best current existing core-file candidate. | `True_def` source exists as non-theorem input; strict HOL object-equality/reflexivity bridge is implemented; checked-definition transport/fold-back to `True` is still pending. |

Completed smoke slice:

```text
strict Pure implication identity
```

It is the smallest path that tests parser/certifier/export/acceptance rather
than only kernel unit tests. It does not change the core-file batch because the
sampled 125 lemmas contain no `A ==> A` / `P ==> P` candidate. The next
existing-theorem milestone is `HOL::TrueI`, but only after the HOL
object-equality/reflexivity bridge is implemented and checked-definition
transport back to `True` is available, without using compat `refl` or treating
Pure equality as HOL object equality.
