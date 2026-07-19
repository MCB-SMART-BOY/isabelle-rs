# Proof Outcome Design

## Status

Phase 1 summary classifier implemented in `src/isar/method.rs`.

The implemented `ProofOutcome::TransitionalStrictClosed` variant classifies
legacy `core::Thm + ThmTrust::Strict`. The distinct target metric
`KernelTrustedClosed`, backed by `src/kernel::TrustedTheorem` and `CProp : prop`,
is currently `0/125` and is not yet represented by this enum.

Current implementation:

- defines `ProofOutcome`, `TheoremSummary`, `OpenReason`, `AdmitReason`, and
  `ProofFailure`;
- classifies existing `verify_lemma` results without changing theorem
  construction;
- keeps `TransitionalStrictClosed` separate from compat, open, admitted, and failed
  outcomes;
- makes `core_batch_snapshot_reports_one_transitional_and_zero_kernel_trusted`
  print and assert the exact sampled `ProofOutcome` summary;
- includes a targeted Pure implication identity smoke slice: `A ==> A` can be
  constructed by the strict kernel nucleus, and the current `verify_lemma`
  summary path can count the checked identity adapter as
  `TransitionalStrictClosed`.
- routes the existing core-file theorem `HOL::TrueI` through the narrow
  transitional adapter, raising the sampled core batch to
  `TransitionalStrictClosed: 1/125` while `KernelTrustedClosed` remains `0/125`;

Not yet implemented:

- final theorem-table acceptance has not been rewritten around `ProofOutcome`;
- only one existing HOL/core-file theorem has been classified as
  `TransitionalStrictClosed` so far (`HOL::TrueI`);
- broad HOL/Isar proof methods still mostly return admitted or compat/open
  outcomes.

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
compat closed != transitional strict closed
open theorem != accepted theorem
```

Recent goal-export work made this boundary more honest: proof-method results
with unknown hypotheses are now admitted with `goal_export_*` reasons instead
of being reported as misleading open oracle-free results. The summary/reporting
model is implemented. The remaining outcome change is intentionally blocked on
immutable context identity and a real kernel acceptance value.

## Goals

- Provide a single classification for every theorem verification attempt.
- Keep the `TransitionalStrictClosed` bucket diagnostic-only for final trust.
- Make final theorem-table acceptance depend on a context-bound
  `KernelTrustedClosed` value carrying `src/kernel::TrustedTheorem`.
- Keep compat/oracle-free facts searchable without counting them as proved.
- Structure admitted and failure reasons for stable reports.
- Keep both migration metrics visible: transitional legacy coverage is `1/125`,
  while new-kernel coverage remains `KernelTrustedClosed: 0/125`.

## Non-Goals

- Do not add new proof power to `src/core`.
- Do not make compatibility theorems trusted.
- Do not hide admitted paths behind successful-looking outcomes.
- Do not implement APP, LSP, workspace, HPC, Burn, or CubeCL work here.

## Proposed Outcome Model

The implemented Phase 1 shape is intentionally summary-first. It stores a
`TheoremSummary` rather than moving theorem ownership through every caller.
The authoritative Rust definition is
[`ProofOutcome`](../src/isar/method.rs), not a copied documentation template.

The model intentionally separates theorem storage from theorem summaries. A
report does not need to retain a full legacy theorem to explain why a proof did
not become trusted.

## Outcome Semantics

| Outcome | Meaning | Trusted theorem table? |
|---|---|---|
| `TransitionalStrictClosed` | Legacy `core::Thm + ThmTrust::Strict` result with no oracles, hypotheses, unresolved `tpairs`, or dummy types. | No |
| `CompatClosedOracleFree` | Legacy theorem is closed-shaped and oracle-free, but not strict. | No |
| `OpenOracleFree` | Legacy theorem is oracle-free but still has open hypotheses, subgoals, unresolved `tpairs`, or another open condition. | No |
| `Admitted` | The system accepted an unproved proposition with an explicit reason. | No |
| `Failed` | The proof attempt failed without producing an accepted theorem. | No |

None of the current summary variants is sufficient for final trusted-theory
acceptance. Only the future `KernelTrustedClosed` gate may enter final trusted
theorem tables. It must retain a `src/kernel::TrustedTheorem`, certify a
`CProp : prop`, bind an immutable theory/logic context, and satisfy the required
replay policy. Current outcomes remain useful for search, diagnostics, and
migration prioritization, but their provenance must not be erased.

## Structured Reasons

Implemented `OpenReason` categories:

```text
UnknownHyps
UnresolvedTpairs
Other
```

Implemented `AdmitReason` categories:

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
UnsupportedMethod
ProofEngineFailed
AxiomAcceptedWithoutOracle
OracleOrAdmittedResult
Other
```

Implemented `ProofFailure` categories:

```text
MethodNone
```

String reasons such as `admitted:goal_export_unknown_hyps` can remain as a
compatibility layer, but the target report should be derived from structured
reason values.

Registered adapter source-provenance failure uses the exact oracle reason
`admitted:strict_adapter_source_prop_unverified`. It remains an `Admitted`
outcome and must not be classified as `ParserGap`: the registered adapter was
applicable, but its source proposition failed the typed status/shape gate. The
exact oracle string remains on the admitted theorem; the current aggregate
classifier maps it to `AdmitReason::Other` because there is no dedicated
structured variant. This hardening therefore does not change the sampled
outcome counts or existing ProofOutcome categories.

## Acceptance Policy

Final theorem acceptance must flow through the new-kernel gate, not through the
legacy summary label:

checked elaboration / kernel derivation
  -> accept_closed_theorem(exact immutable owner)
  -> immutable child TrustedTheory
     + sealed src/kernel::TrustedTheorem
     + replay-derived dependencies
  -> ProofOutcome::KernelTrustedClosed

legacy verification
  -> ProofOutcome::TransitionalStrictClosed
  -> TransitionalStrictClosed report only

`LogicBasisId` is the sole object-logic identity vocabulary. `None` means
Pure-only ancestry; every HOL or other object-logic theorem must carry the exact
basis ID installed in its accepted theory.

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
KernelTrustedClosed: M
TransitionalStrictClosed: N
CompatClosedOracleFree: N
OpenOracleFree(reason): N
Admitted(reason): N
Failed(reason): N
```

`KernelTrustedClosed` now owns the accepted token and is mutually exclusive
with every legacy outcome. `ProofOutcomeStats::total()` includes it. The
production HOL verifier supplies no token yet, so the sampled value remains
zero.

This replaces one-off diagnostic runners and avoids conflating static call-site
counts with runtime theorem outcomes.

## Trusted Implementation Order

The trusted implementation order is mandatory:

```text
immutable SignatureId / TheoryId
  -> unique context-bound acceptance
  -> source-aware proposition AST
  -> checked judgment / constant / type-scheme elaboration
  -> data-only HOL logic-basis manifest
  -> generic conservative definition extension
  -> HOL::TrueI as HOL.Trueprop HOL.True
  -> HOL::trans only as a later reuse consumer
```

The reporting-phase table below records classifier rollout only. It does not
reorder these trust gates or authorize skipping one.

## Migration Phases

| Phase | Gate |
|---|---|
| Phase 0: design | Implemented; status docs point to this model. |
| Phase 1: summary classifier | Implemented. Existing `verify_lemma` results are summarized without changing theorem construction. |
| Phase 2: report integration | Implemented. Core reports and the 125-theorem snapshot use the explicit buckets. |
| Phase 3: context-bound acceptance | Implemented: exact-owner replay, dependency reconstruction, duplicate-safe immutable insertion, sealed token, and exclusive `KernelTrustedClosed`; synthetic Pure tests stay outside the HOL benchmark. |
| Phase 4a: targeted transitional slice | Implemented. Direct `A ==> A` smoke and adapter tests exercise the migration classifier. |
| Phase 4b: first core-file transitional slice | Implemented by legacy `HOL::TrueI`; no second transitional adapter is planned. |

## Transitional Slice History — No Further Adapter

| Candidate | Required strict rules | Advantages | Risks |
|---|---|---|---|
| Pure reflexivity `t == t` | `KernelRules::reflexive`, checked term certification, exact-owner acceptance | Small accepted-nucleus smoke test. | Synthetic Pure result only; it does not establish an authorized HOL basis. |
| Implication identity `A ==> A` | `KernelRules::assume`, `KernelRules::implies_intr`, checked proposition certification, acceptance | Exercises legal discharge, wrong-context attacks, immutable insertion, dependencies, and exclusive classification. | Deliberately excluded from sampled HOL results. |
| Simple equality theorem | Reflexivity plus an equality encoding | Potential later HOL-facing reuse. | Not a next slice; requires the common elaboration and HOL-basis boundary. |
| `HOL::TrueI` | Checked legacy `True_def` payload, legacy HOL object-equality/reflexivity bridge, theorem-specific transport, narrow adapter | First existing core-file `TransitionalStrictClosed` theorem. | Historical migration experiment only; re-derive through the new kernel instead of adding another adapter. |

Completed slices:

```text
strict Pure implication identity
HOL::TrueI existing core-file transitional theorem
```

The Pure implication identity is the smallest existing synthetic path for
testing legal discharge. Its next use is a context-identity/acceptance unit,
not another parser or theorem adapter. It does not change the sampled batch,
which contains no `A ==> A` / `P ==> P` candidate.

`HOL::TrueI` is the first existing-theorem transitional milestone. It routes
through checked legacy `True_def`, strict legacy HOL object reflexivity, and
checked-definition transport without using compat `refl` or conflating Pure and
HOL equality. None of those bridges supplies final context-bound acceptance.

The `HOL::TrueI` slice now goes through the minimal strict adapter dispatcher:

```text
try_strict_adapter(ParsedLemma, HolTheoremDb)
  -> NotApplicable
  -> Proved(legacy TransitionalStrictClosed theorem)
  -> Rejected(reason)
```

For the registered `HOL::TrueI` adapter with an explicit proof, dispatch first
requires `SourcePropositionStatus::FullyConsumed` together with
`SourcePropositionShape::StandaloneHolTrueAlias`. Every other pair returns
`Rejected(SourcePropositionUnverified { status, shape })`; `verify_lemma` records
`admitted:strict_adapter_source_prop_unverified` instead of parser-gap or
legacy fallback. Missing or empty proof scripts remain `NotApplicable` and
retain their compatibility behavior.

This includes `FullyConsumed + Other` after parser recovery of malformed
`True =`, `FullyConsumed + Contextual` for local `fixes`, `includes`, `notes`,
`if`, `when`, locale-qualified, or enclosing-context sources, and
`Unavailable + Unavailable` without source provenance. The shape is a
transitional fail-closed guard, not a name-resolved source AST and not a new
`ProofOutcome` trust category.

The dispatcher remains `HOL::TrueI`-only. No second transitional adapter is
planned; the next synthetic proof exercise belongs to immutable context
identity and the context-bound acceptance API, not another legacy dispatcher
branch.

The current Phase 1 `TransitionalStrictClosed` summary does not carry a
new-kernel theorem handle, theory context, or `LogicBasisId` provenance. The
target model described in
[ADR-0003-hol-logic-trusted-extension.md](ADR-0003-hol-logic-trusted-extension.md)
must add those to the eventual `TrustedTheorem` acceptance path; a summary
classification alone cannot install or authorize a HOL logic extension.
