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
- Final theorem acceptance must converge on `ProofOutcome::StrictClosed`.
- Workspace, APP, LSP, HPC, Burn, and CubeCL work stay deferred until the
  theorem acceptance path is under control.

## Matrix

| Area | Current state | Risk | Target architecture | Next migration step | Blocking tests |
|---|---|---|---|---|---|
| Isar method export | `src/isar/method.rs` exports core `Thm` results and admits failed exports with `goal_export_*` reasons. | Unknown hyps and method fallbacks still dominate runtime failures. | Method execution returns a structured `ProofOutcome`; strict-success paths replay through kernel. | Introduce an outcome classifier around `verify_lemma` before changing proof search. | `verify_no_open_oracle_free_results_in_core_batch`; future report must distinguish `StrictClosed`, compat, open, admitted, failed. |
| Simplifier | `src/core/simplifier.rs` now rejects open/admitted/conditional rewrite theorems. | `by simp` can still route through surrounding method fallback and return unknown hyps. | Simplifier becomes automation/candidate generator; theorem effects are replayed or admitted explicitly. | Trace `Method::Simp` and fallback branches that create `goal_export_unknown_simp_context`. | `simp_does_not_import_rule_hyps_into_result`; dynamic subtype report for simp-context unknown hyps. |
| Theorem database acceptance | HOL/global/theory tables filter with `is_strict_closed_proved()` but reports still depend on legacy `Thm` status. | Compat closed oracle-free facts can be misread as proof progress. | Trusted tables accept only `ProofOutcome::StrictClosed`; searchable databases preserve taint. | Add report-level `ProofOutcome` summaries before moving table internals. | Core verification report shows zero open oracle-free accepted results. |
| Proofterm replay | `src/core/proofterm.rs` supports a small replay subset; `src/kernel` invariant replay covers implemented strict derivations. | Replay success can be confused with closed theorem acceptance, and coverage is limited. | Replay is an independent check for strict derivations, never a replacement for closed acceptance. | Extend only rules needed by the first strict vertical slice. | Existing proofterm replay tests plus first-slice replay check. |
| Parser / certifier | Strict checked certification exists, but legacy compatibility certification remains widespread. | Dummy types and schematic/free mismatches block strict theorem construction. | Parsed theorem propositions for selected slices become checked `CProp`s. | Build the first strict-slice parser/certifier adapter for one small proposition form. | Strict certifier rejects dummy-tainted terms; parser-gap count does not regress. |
| HOL loader | `HolTheoremDb` remains a searchable fact index with admitted and compat facts. | Searchable facts can be mistaken for trusted facts by new code. | HOL loader emits classified outcomes and separates searchable facts from trusted facts. | Route the first selected HOL/Pure lemma through a strict acceptance adapter. | `strict_closed_count` increases only from `StrictClosed`, never admitted/compat. |
| Resolution family | Strict kernel has `resolve1_match`, conservative `subst_premise`, and conservative `bicompose` wrapper. | Full `bicompose`, e-resolution, lifting, and freshening are not implemented. | Kernel-backed `proof_search` owns trusted resolution transitions; core resolution becomes legacy/adapters. | Do not expand resolution until first strict acceptance slice exists, except design-only work. | Existing bicompose/subst attack tests; future `bicompose_eresolve` design tests. |
| Tools / simp front-end | `src/tools/simp.rs` consumes legacy rewrite rules and facts. | Tool success may be confused with a trusted theorem derivation. | Tools produce candidates, scripts, or proof terms; strict replay accepts or rejects. | Keep tool outputs classified as search/automation until replayed. | Tool tests must assert no open/admitted rule is treated as unconditional proved rewrite. |

## First Strict Closed Theorem Slice

The immediate milestone is not broad coverage. It is:

```text
test_verify_all_core_files: 1/125 StrictClosed
```

A targeted smoke slice now proves Pure implication identity `A ==> A` through
the strict kernel nucleus and verifies that the current summary classifier
counts the checked identity adapter as `StrictClosed`. The first existing
core-file slice is now `HOL::TrueI`, which changes the sampled core-file batch
to `StrictClosed: 1/125`.

A diagnostic scan of the current 125 sampled core-file lemmas found zero parsed
propositions of the form `A ==> A` / `P ==> P`, so the synthetic identity slice
could not move the batch. `HOL::TrueI` is the first real sampled theorem routed
through strict acceptance.

Candidate slices:

| Candidate | Why it is useful | Required pieces | First-slice suitability |
|---|---|---|---|
| Pure reflexivity `t == t` | Smallest strict kernel theorem construction path. | Checked term certification, `KernelRules::reflexive`, closed acceptance. | Good kernel/acceptance smoke test, but may not map directly to a current core lemma. |
| Pure implication identity `A ==> A` | Exercises assumption introduction and legal discharge. | Checked `CProp`, `KernelRules::assume`, `KernelRules::implies_intr`, `ClosedThm` acceptance. | Targeted smoke slice implemented; next step is an existing core-file lemma. |
| Simple equality reflexivity exposed through HOL | Brings the path closer to user-visible HOL facts. | HOL equality adapter, type certification, strict reflexivity. | Good second slice after Pure path works. |
| `HOL::TrueI` | First sampled HOL lemma with a small proof: `unfolding True_def by (rule refl)`. | Checked `True_def` definition source, strict HOL object-equality/reflexivity bridge, checked `True_def` transport, narrow `TrueI` adapter. | Implemented as the first existing core-file `StrictClosed`; not a general simp/unfolding path. |

### `HOL::TrueI` Strict Slice Contract

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
| Current `verify_lemma` result | strict closed theorem for `HOL.True` |
| Current `ProofOutcome` | `StrictClosed` |
| `True_def` in parsed lemmas / DB facts | missing, as expected; the checked source is separate from theorem facts |
| `True_def` checked definition source | done; non-theorem input only and not counted as proof progress |
| HOL object-equality/reflexivity bridge | implemented as narrow primitive bridge |
| `try_strict_hol_refl` | implemented |
| checked-definition transport/fold-back to `True` | implemented for checked `True_def` |
| `try_strict_hol_true_i` | implemented as a narrow TrueI-only adapter |
| `refl` DB fact | compat/open `((HOL.eq ?t.0) ?t.0)`, not strict closed |
| `Pure.refl` DB fact | compat closed-shaped `((Pure.eq ?t.0) ?t.0)`, not strict closed |

The strict slice may be implemented only when these inputs can be checked
without compatibility trust:

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
- the final result has no hypotheses, no unresolved `tpairs`, no oracle/admit
  footprint, no dummy types, and satisfies `is_strict_closed_proved()`.

The adapter must reject and fall back to the existing admitted path if:

- `True_def` is missing from the checked definition environment;
- `True_def` or the unfolded RHS contains dummy/compat-only certification;
- the unfolded RHS is not a reflexive equality of the same term;
- the available `refl` fact is compat/admitted/open;
- any ambient hypothesis, unresolved `tpair`, oracle/admit footprint, or dummy
  type would remain.

Current conclusion: the narrow `HOL::TrueI` adapter is implemented and is the
first existing core-file strict slice. It checks theorem name, proposition,
proof shape, checked `True_def`, strict RHS proof, and final strict closed
result. Do not generalize it into direct `return StrictClosed(True)`, simp, or
definition rewriting.

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
    strict theorem for HOL.eq t t, with no hyps, tpairs, oracle/admit footprint,
    or dummy types
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

Recommended order:

```text
1. strict Pure implication identity as a direct parser/certifier/export smoke test (done)
2. make `True_def` available as a checked definition source (done; non-theorem input only)
3. implement the strict HOL object-equality/reflexivity bridge needed by `TrueI` (done)
4. implement checked-definition transport/fold-back for checked `True_def` (done)
5. implement strict `HOL::TrueI` only as a narrow adapter over those checked pieces (done)
6. simple equality reflexivity exposed through HOL after the equality adapter is clearer
```

## Next Engineering Gates

1. Implement `ProofOutcome` as a report/classification layer without changing
   proof behavior.
2. Use it in core verification reports.
3. Add a strict adapter for the chosen implication-identity slice.
4. Add a checked-definition source for `True_def`. (done; not counted as theorem progress)
5. Implement a strict object-equality/reflexivity bridge sufficient for
   `HOL::TrueI` after the term/type diagnostic confirms the checked `HOL.eq`
   shape. (done)
6. Implement checked-definition transport/fold-back for checked `True_def`. (done)
7. Route one existing core-file theorem through a strict `HOL::TrueI` adapter. (done)
8. Increase the strict closed count only through `StrictClosed`.
9. Resume admitted-reason reduction based on the new outcome report.
