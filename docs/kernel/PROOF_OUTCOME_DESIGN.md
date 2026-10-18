# Proof Outcome Design

## Status

The summary classifier, token-owning kernel outcome, and statistics integration
are implemented in `src/isar/method.rs`.

`ProofOutcome::TransitionalStrictClosed` classifies legacy
`core::Thm + ThmTrust::Strict`. The mutually exclusive
`ProofOutcome::KernelTrustedClosed` owns a real
`src/kernel::TrustedTheorem`. The 2026-10-07 bundled five-file sample reported
`KernelTrustedClosed: 1/125`, `TransitionalStrictClosed: 0/125`: only an
audited source projection of `HOL::TrueI` reached exact-owner replay. It did
not execute unrelated HOL/ML commands or compile the complete theory. P2/P3/P4
implementation has resumed and Rust THM consumers have separate narrow
closure evidence; neither is a rerun of sampled acceptance or complete native
compatibility. See the [latest delivery record](../status/PROJECT_STATUS.md#rust-thm-type-and-variable-transformations-2026-10-19).

Current implementation:

- defines `ProofOutcome`, `TheoremSummary`, `OpenReason`, `AdmitReason`, and
  `ProofFailure` in `src/isar/method.rs`;
- keeps kernel token outcomes separate from legacy compat, open, admitted,
  transitional, and failed outcomes;
- the sampled snapshot test
  `core_batch_snapshot_reports_one_kernel_trusted_and_zero_transitional`
  asserts the exclusive result;
- the source-bound `try_strict_adapter` accepts only the audited sampled
  `HOL::TrueI` projection, not the legacy bool-valued theorem;
- two independent standalone HOL/Pure fixtures receive accepted tokens but
  do not contribute to the sampled batch.

The historical 2026-10-03 checkpoint counted the legacy `HOL::TrueI`
transitional bridge as `TransitionalStrictClosed: 1/125` and
`KernelTrustedClosed: 0/125`. That theorem-specific bridge is removed; broad
HOL/Isar proof methods and final theorem-table migration remain open.

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

Legacy proof export now checks an actual Strict/checked result against the
complete proposition and permitted hypotheses, discharging only real scoped
assumptions/fixes. A fresh goal, a tactic obligation, or a theorem proving just
the conclusion does not complete the proof. This hardening does not promote
legacy Strict results to new-kernel acceptance; the summary/reporting model
remains distinct from the sealed token.

## Goals

- Provide a single classification for every theorem verification attempt.
- Keep the `TransitionalStrictClosed` bucket diagnostic-only for final trust.
- Make final theorem-table acceptance depend on a context-bound
  `KernelTrustedClosed` value carrying `src/kernel::TrustedTheorem`.
- Keep compat/oracle-free facts searchable without counting them as proved.
- Structure admitted and failure reasons for stable reports.
- Keep both sampled migration metrics visible: transitional legacy coverage is
  `0/125`, while new-kernel coverage is `KernelTrustedClosed: 1/125`.

## Non-Goals

- Do not add new proof power to `src/core`.
- Do not make compatibility theorems trusted.
- Do not hide admitted paths behind successful-looking outcomes.
- Do not mistake the A-package Cargo workspace/xtask for a proof-session
  runtime split, APP, LSP, HPC, Burn, or CubeCL implementation.

## Outcome Model

The Phase 1 summary classifier and token-owning outcome are implemented; this
heading retains their original design context, not a new proposed enum.
`TheoremSummary` does not move legacy theorem ownership through every caller.
The authoritative Rust definition is
[`ProofOutcome`](../../src/isar/method.rs), not a copied documentation template.
The model intentionally separates theorem storage from theorem summaries. A
report does not need to retain a full legacy theorem to explain why a proof did
not become trusted.

## Outcome Semantics

| Outcome | Meaning | Trusted theorem table? |
|---|---|---|
| `KernelTrustedClosed` | New-kernel accepted token after exact-owner replay, with `CProp : prop`. | Yes |
| `TransitionalStrictClosed` | Legacy `core::Thm + ThmTrust::Strict` result with no oracles, hypotheses, unresolved `tpairs`, or dummy types. | No |
| `CompatClosedOracleFree` | Legacy theorem is closed-shaped and oracle-free, but not strict. | No |
| `OpenOracleFree` | Legacy theorem is oracle-free but still has open hypotheses, subgoals, unresolved `tpairs`, or another open condition. | No |
| `Admitted` | The system accepted an unproved proposition with an explicit reason. | No |
| `Failed` | The proof attempt failed without producing an accepted theorem. | No |

Only `KernelTrustedClosed` may enter final trusted-theory tables: that
implemented gate retains a `src/kernel::TrustedTheorem`, certifies a
`CProp : prop`, binds an immutable theory/logic context, and requires
exact-owner replay. An audited sampled `HOL::TrueI` projection and two
independent standalone source fixtures supply tokens. Other sampled outcomes
remain useful for search, diagnostics, and migration prioritization.

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
structured variant. This fail-closed classification cannot turn an adapter
rejection into proof.

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

`KernelTrustedClosed` owns the accepted token and is mutually exclusive with
every legacy outcome. `ProofOutcomeStats::total()` includes it. The last
recorded bundled verifier supplied exactly one token via the audited
`HOL::TrueI` projection, `KernelTrustedClosed: 1/125` and
`TransitionalStrictClosed: 0/125`. Subsequent external Rust THM consumer
closures did not rerun or enter that sampled verifier.

This replaces one-off diagnostic runners and avoids conflating static call-site
counts with runtime theorem outcomes.

## Trusted Implementation Order

The dependency order remains mandatory. The bracketed stages are implemented
only for the indicated narrow source paths, not general HOL/Isar:

```text
immutable SignatureId / TheoryId (including type constructors/arity) [implemented]
  -> unique context-bound acceptance [implemented]
  -> data-only source proposition AST [implemented]
  -> bounded parser and checked declaration/type-scheme elaboration [narrow paths]
  -> data-only HOL refl logic-basis manifest with checked axiom schemas [implemented]
  -> generic replayable conservative definition extension [implemented]
  -> standalone HOL::TrueI via HOL.Trueprop HOL.True [implemented]
  -> audited sampled HOL::TrueI source projection [implemented, 1/125]
  -> other sampled HOL theorems [open]
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
| Phase 3: context-bound acceptance | Implemented: exact-owner replay, dependency reconstruction, duplicate-safe immutable insertion, sealed token, and exclusive `KernelTrustedClosed`; two fixtures are outside the sample, audited `HOL::TrueI` projection is inside it. |
| Phase 3a: source syntax data model | Implemented: unresolved names/syntax, grouping, binders, source types, and diagnostic spans without trusted-context or theorem conversion. Narrow parsing/elaboration handles two fixtures and the audited sampled projection, not broad Isabelle commands. |
| Phase 4a: targeted transitional slice | Historical: direct `A ==> A` smoke and legacy classifier tests exercised migration. |
| Phase 4b: first core-file transitional slice | Historical 2026-10-03 legacy `HOL::TrueI`; its theorem-specific bridge was replaced, not extended. |

## Transitional Slice History — No Further Adapter

| Candidate | Required strict rules | Advantages | Risks |
|---|---|---|---|
| Pure reflexivity `t == t` | `KernelRules::reflexive`, checked term certification, exact-owner acceptance | Small accepted-nucleus smoke test. | Synthetic Pure result only; it does not establish an authorized HOL basis. |
| Implication identity `A ==> A` | `KernelRules::assume`, `KernelRules::implies_intr`, checked proposition certification, acceptance | Exercises legal discharge, wrong-context attacks, immutable insertion, dependencies, and exclusive classification. | Deliberately excluded from sampled HOL results. |
| Simple equality theorem | Reflexivity plus an equality encoding | Potential later HOL-facing reuse. | Not a next slice; requires the common elaboration and HOL-basis boundary. |
| `HOL::TrueI` | Checked legacy `True_def` payload, legacy HOL object-equality/reflexivity bridge, theorem-specific transport, narrow adapter | First existing core-file `TransitionalStrictClosed` theorem in 2026-10-03 checkpoint. | Historical migration experiment only; replaced by audited source projection and accepted kernel token. |

Historical completed transitional slices (not current acceptance paths):

```text
strict Pure implication identity
HOL::TrueI existing core-file transitional theorem
```

The Pure implication identity is the smallest existing synthetic path for
testing legal discharge. Its next use is a context-identity/acceptance unit,
not another parser or theorem adapter. It does not change the sampled batch,
which contains no `A ==> A` / `P ==> P` candidate.

At the 2026-10-03 checkpoint, `HOL::TrueI` routed through checked legacy
`True_def`, legacy HOL object reflexivity, and definition transport without
compat `refl` or Pure/HOL equality conflation. None supplied final acceptance.
That route is removed. The current source-bound dispatcher returns:

```text
try_strict_adapter(ParsedLemma, HolTheoremDb)
  -> NotApplicable
  -> Proved((TrustedTheory, TrustedTheorem))
  -> Rejected(StrictAdapterReject)
```

For the registered `HOL::TrueI` adapter with an explicit proof, dispatch first
requires `SourcePropositionStatus::FullyConsumed` together with
`SourcePropositionShape::StandaloneHolTrueAlias`. Every other pair returns
`Rejected(SourcePropositionUnverified { status, shape })`; `verify_lemma` records
`admitted:strict_adapter_source_prop_unverified` instead of parser-gap or
legacy fallback. Missing or empty proof scripts remain `NotApplicable` and
retain their compatibility behavior.

This includes `FullyConsumed + Contextual` for local `fixes`, `includes`,
`notes`, `if`, `when`, locale-qualified, or enclosing-context sources, and
`Unavailable + Unavailable` without source provenance. Malformed or mistyped
source propositions such as `True =`, `True :: nat`, and `True :: prop` instead
fail parsing/certification before a lemma candidate exists; they do not enter
the adapter as recovered input. The shape is a transitional fail-closed guard,
not a name-resolved source AST and not a new `ProofOutcome` trust category.

The dispatcher remains `HOL::TrueI`-only. No second theorem-specific legacy
adapter is planned: the current accepted result uses an audited projection of
the bundled HOL source. The legacy Phase 1 transitional summary carries no
new-kernel theorem handle, theory context, or `LogicBasisId` provenance.
The accepted sampled `TrueI` and independent fixtures do carry these through
`TrustedTheorem`. The object-logic boundary in
[ADR-0003-hol-logic-trusted-extension.md](../adr/ADR-0003-hol-logic-trusted-extension.md)
remains mandatory for other sampled lemmas: summary classification cannot
install or authorize a HOL logic extension.
