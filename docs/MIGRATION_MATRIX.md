# Core-to-Kernel Migration Matrix

## Status

Initial migration matrix for the strangler phase. This document turns the
overlap inventory into actionable migration slices.

## Migration Principles

- `src/kernel` is the target TCB.
- `src/core` currently remains a legacy proof engine; the target is to shrink
  it into compatibility, automation, diagnostics, and migration adapters.
- Core changes are allowed only when they harden boundaries, improve
  diagnostics, or enable migration.
- The current `ProofOutcome::TransitionalStrictClosed` is transitional legacy accounting;
  final acceptance must converge on a distinct `KernelTrustedClosed` result
  carrying a context-bound `src/kernel::TrustedTheorem` with `CProp : prop`.
- Workspace, APP, LSP, HPC, Burn, and CubeCL work stay deferred until the
  theorem acceptance path is under control.

## Matrix

| Area | Current state | Risk | Target architecture | Next migration step | Blocking tests |
|---|---|---|---|---|---|
| Isar method export | `src/isar/method.rs` exports core `Thm` results and admits failed exports with `goal_export_*` reasons. | Unknown hyps and method fallbacks still dominate runtime failures. | Method execution returns a structured `ProofOutcome`; kernel-trusted success carries a context-bound new-kernel theorem. | Keep the implemented legacy outcome classifier stable until immutable identity and unique acceptance exist. | `verify_no_open_oracle_free_results_in_core_batch`; reports distinguish `TransitionalStrictClosed`, compat, open, admitted, and failed. |
| Simplifier | `src/core/simplifier.rs` now rejects open/admitted/conditional rewrite theorems. | `by simp` can still route through surrounding method fallback and return unknown hyps. | Simplifier becomes automation/candidate generator; theorem effects are replayed or admitted explicitly. | Trace `Method::Simp` and fallback branches that create `goal_export_unknown_simp_context`. | `simp_does_not_import_rule_hyps_into_result`; dynamic subtype report for simp-context unknown hyps. |
| Theorem database acceptance | HOL/global/theory tables filter with `is_strict_closed_proved()` while reports label that legacy status `TransitionalStrictClosed`. | Transitional facts can be misread as new-kernel proof progress. | Final trusted tables accept only `KernelTrustedClosed` values carrying a `src/kernel::TrustedTheorem` bound to immutable theory/logic context; searchable and transitional databases preserve taint. | Implement the context-bound kernel-trusted gate before moving any fact into final `TrustedTheory`. | Reports show `TransitionalStrictClosed: 1/125` and `KernelTrustedClosed: 0/125` until a real new-kernel HOL theorem exists. |
| Proofterm replay | `src/core/proofterm.rs` supports a small replay subset; `src/kernel` invariant replay covers every current strict derivation variant. | Replay success can be confused with closed theorem acceptance; new-kernel replay is still context-free. | Replay is an independent check in the exact immutable theory context, never a replacement for closed acceptance. | Parameterize existing new-kernel replay by immutable context before adding object-logic derivations. | Existing replay/tampering tests plus wrong-context acceptance attacks. |
| Parser / certifier | Strict `CProp` certification exists, but legacy compatibility parsing remains widespread and loses source distinctions. | Dummy types, omitted context, and meta/object connective loss block trusted theorem construction. | A source-aware proposition AST elaborates checked judgments, constants, schemes, and `HOL.Trueprop` positions into context-bound `CProp`s. | First complete immutable identity and unique acceptance; then build the source AST and checked elaborator, not another theorem adapter. | Current parser/adapter attacks remain fail-closed; future tests preserve spans, binders, connective roles, and explicit types. |
| HOL loader | `HolTheoremDb` remains a searchable fact index with admitted, compat, and transitional strict facts. | Searchable or transitional facts can be mistaken for new-kernel trusted facts. | HOL loader keeps searchable/transitional facts separate from context-bound kernel-trusted facts. | Preserve the `TrueI`-only transitional guard while identity, acceptance, and source-aware elaboration are implemented. | `KernelTrustedClosed` can increase only from a context-bound new-kernel theorem, never a legacy outcome label. |
| Resolution family | Strict kernel has `resolve1_match`, conservative `subst_premise`, and conservative `bicompose` wrapper. | Full `bicompose`, e-resolution, lifting, and freshening are not implemented. | Kernel-backed `proof_search` owns trusted resolution transitions; core resolution becomes legacy/adapters. | Do not expand resolution until the first `KernelTrustedClosed` slice exists, except design-only work. | Existing bicompose/subst attack tests; future `bicompose_eresolve` design tests. |
| Tools / simp front-end | `src/tools/simp.rs` consumes legacy rewrite rules and facts. | Tool success may be confused with a trusted theorem derivation. | Tools produce candidates, scripts, or proof terms; strict replay accepts or rejects. | Keep tool outputs classified as search/automation until replayed. | Tool tests must assert no open/admitted rule is treated as unconditional proved rewrite. |

## Completed Transitional Strict-Closed Experiment

The completed migration checkpoint, not the next trusted milestone, is:

```text
TransitionalStrictClosed: 1/125
KernelTrustedClosed:      0/125
```

A targeted smoke slice now proves Pure implication identity `A ==> A` through
the strict kernel nucleus and verifies that the current summary classifier
counts the checked legacy identity adapter as `TransitionalStrictClosed`. The first existing
core-file slice is now `HOL::TrueI`, which changes the sampled legacy core-file
batch to `TransitionalStrictClosed: 1/125`. Its bool-valued theorem proposition
is not eligible for `KernelTrustedClosed`.

A diagnostic scan of the current 125 sampled core-file lemmas found zero parsed
propositions of the form `A ==> A` / `P ==> P`, so the synthetic identity slice
could not move the batch. `HOL::TrueI` is the first real sampled theorem routed
through the legacy transitional adapter, not new-kernel acceptance.

Candidate slices:

| Candidate | Why it is useful | Required pieces | First-slice suitability |
|---|---|---|---|
| Pure reflexivity `t == t` | Smallest strict kernel theorem construction path. | Checked term certification, `KernelRules::reflexive`, closed acceptance. | Good kernel/acceptance smoke test, but may not map directly to a current core lemma. |
| Pure implication identity `A ==> A` | Exercises assumption introduction and legal discharge. | Checked `CProp`, `KernelRules::assume`, `KernelRules::implies_intr`, context-bound acceptance. | Existing synthetic smoke; reuse next for correct/wrong-context acceptance tests, not as a sampled HOL result. |
| Simple equality reflexivity exposed through HOL | Potential later user-visible reuse. | Source-aware elaboration, HOL basis, immutable context, generic replay. | Not a second transitional slice and not current work. |
| `HOL::TrueI` | First sampled HOL lemma with a small proof: `unfolding True_def by (rule refl)`. | Legacy checked `True_def` payload, HOL object-equality/reflexivity bridge, theorem-specific transport, narrow `TrueI` adapter. | Implemented only as the first `TransitionalStrictClosed` experiment; it must be re-derived through `Trueprop`, a conservative definition, and an explicit HOL basis before becoming kernel-trusted. |

### `HOL::TrueI` Transitional Slice Contract

Target source theorem:

```isabelle
lemma TrueI: True
  unfolding True_def by (rule refl)
```

Current targeted diagnostic:

| Item | Observed state |
|---|---|
| Source theory | `theories/HOL/HOL.thy` |
| Parsed theorem | `TrueI`, prop `True`, proof `unfolding True_def by (rule refl)` |
| Current `verify_lemma` result | legacy theorem whose conclusion is `HOL.True : bool` |
| Current `ProofOutcome` | `TransitionalStrictClosed` |
| `True_def` in parsed lemmas / DB facts | missing, as expected; the checked source is separate from theorem facts |
| `True_def` checked definition source | done; non-theorem input only and not counted as proof progress |
| HOL object-equality/reflexivity bridge | implemented as narrow primitive bridge |
| `try_strict_hol_refl` | implemented |
| checked-definition transport/fold-back to `True` | implemented for checked `True_def` |
| `try_strict_hol_true_i` | implemented as a narrow TrueI-only adapter |
| `refl` DB fact | compat/open `((HOL.eq ?t.0) ?t.0)`, not strict closed |
| `Pure.refl` DB fact | compat closed-shaped `((Pure.eq ?t.0) ?t.0)`, not strict closed |

The implemented transitional slice accepts only when these legacy inputs pass
its narrow checks:

- theorem name is exactly `TrueI`;
- parsed proposition is exactly the declared HOL constant `True`;
- the source proof is exactly the supported shape
  `unfolding True_def by (rule refl)`;
- `True_def` is available as a checked definition, not merely as a declaration
  side effect;
- unfolding `True_def` produces the expected reflexive object equality
  `((λx::bool. x) = (λx. x))`;
- the reflexive equality is constructed by a strict path, not by the compat
  `refl` fact currently stored in `HolTheoremDb`;
- the final legacy result has no hypotheses, no unresolved `tpairs`, no
  oracle/admit footprint, no dummy types, and satisfies
  `is_strict_closed_proved()`.

These conditions do not make the result kernel-trusted: its conclusion remains
`HOL.True : bool`, it has no immutable theory/logic identity, and it is not a
`src/kernel::TrustedTheorem` over `CProp : prop`.

The adapter must reject into the explicit admitted path, without entering the
legacy proof fallback, if:

- `True_def` is missing from the checked definition environment;
- `True_def` or the unfolded RHS contains dummy/compat-only certification;
- the unfolded RHS is not a reflexive equality of the same term;
- the available `refl` fact is compat/admitted/open;
- any ambient hypothesis, unresolved `tpair`, oracle/admit footprint, or dummy
  type would remain.

Current conclusion: the narrow `HOL::TrueI` adapter is implemented and is the
first existing core-file transitional slice. It checks theorem name,
proposition, proof shape, the legacy `True_def` payload, RHS bridge result, and
final legacy closed result. It is now registered through the minimal strict
adapter dispatcher in
`src/isar/method.rs`, which returns `NotApplicable`, `Proved`, or
`Rejected(reason)`. Do not generalize it into direct `return TransitionalStrictClosed(True)`,
simp, definition rewriting, or another direct theorem-name branch in
`verify_lemma`.

The ranked scan of the remaining 124 sampled theorems is recorded in
[NEXT_STRICT_SLICE_CANDIDATES.md](NEXT_STRICT_SLICE_CANDIDATES.md). It recommends
`HOL::trans` only as the first consumer of a reusable checked HOL equality
substitution slice, not as another theorem-specific primitive or direct branch.

That consumer is blocked on the theorem-independent contract in
[CHECKED_HOL_PROPOSITION_NORMALIZATION.md](CHECKED_HOL_PROPOSITION_NORMALIZATION.md)
and the Proposed object-logic boundary in
[ADR-0003-hol-logic-trusted-extension.md](ADR-0003-hol-logic-trusted-extension.md).
The diagnostic confirms that `HOL::trans` needs shared polymorphic type
constraints, checked `HOL.Trueprop` judgment extraction, and exact preservation
of its `Pure.imp` / `HOL.eq` skeleton before any proof rule is considered.

### HOL Object-Equality / Reflexivity Bridge Contract

This bridge is implemented. See
[HOL_OBJECT_EQUALITY_BRIDGE.md](HOL_OBJECT_EQUALITY_BRIDGE.md) for the detailed
contract. It does not reuse compat `refl` or Pure reflexivity as if they
directly proved HOL object equality.

The intended narrow bridge is:

```text
try_strict_hol_refl(t)
  input:
    checked HOL term t : α
  required declarations:
    HOL.eq : α => α => bool
  output:
    legacy transitional theorem for HOL.eq t t : bool, with no hyps, tpairs,
    oracle/admit footprint, or dummy types
```

The bridge is documented as a HOL object-logic primitive/bridge. It is not a
rewrite, simp, unfolding, or general object-logic prover.

It must reject:

- undeclared or dummy-typed `HOL.eq`;
- unchecked, compat, or dummy-tainted input terms;
- non-reflexive `HOL.eq lhs rhs` shapes;
- any attempt to derive HOL object equality by treating `Pure.eq` as
  interchangeable with `HOL.eq`;
- any compat/admitted/open `refl` fact.

Completed transitional sequence (retained as migration history, not the target
kernel-trust sequence):

```text
1. strict Pure implication identity as a direct parser/certifier/export smoke test (done)
2. make `True_def` available as a checked definition source (done; non-theorem input only)
3. implement the strict HOL object-equality/reflexivity bridge needed by `TrueI` (done)
4. implement checked-definition transport/fold-back for checked `True_def` (done)
5. implement strict `HOL::TrueI` only as a narrow adapter over those checked pieces (done)
```

## Next Engineering Gates

1. Keep the completed `ProofOutcome`, dispatcher, and `HOL::TrueI` work as a
   transitional migration diagnostic.
2. Introduce immutable `SignatureId` / `TheoryId` values and propagate exact
   context identity through certification and theorem construction.
3. Implement the unique, mutually exclusive `KernelTrustedClosed` acceptance
   gate from context-bound new-kernel values only.
4. Preserve source proposition structure before legacy lowering.
5. Elaborate checked judgments, constants, and polymorphic schemes, including
   `HOL.Trueprop`, into `CProp : prop`.
6. Encode the explicit HOL basis as immutable data and replay generic schema
   instances through the Pure kernel.
7. Add a generic conservative definition extension; do not generalize the
   current `True_def` payload or `true_def_transport`.
8. Re-derive `HOL::TrueI` as a context-bound `src/kernel::TrustedTheorem` before
   implementing another theorem adapter.
9. Increase `KernelTrustedClosed` only from that accepted new-kernel handle,
   never by reclassifying `TransitionalStrictClosed`.
10. Resume admitted-reason reduction without widening legacy trusted power.
