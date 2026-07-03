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
test_verify_all_core_files: 0/125 StrictClosed -> 1/125 StrictClosed
```

A targeted smoke slice now proves Pure implication identity `A ==> A` through
the strict kernel nucleus and verifies that the current summary classifier
counts the checked identity adapter as `StrictClosed`. This does not yet change
the core-file batch because none of the current sampled lemmas route through
that shape.

Candidate slices:

| Candidate | Why it is useful | Required pieces | First-slice suitability |
|---|---|---|---|
| Pure reflexivity `t == t` | Smallest strict kernel theorem construction path. | Checked term certification, `KernelRules::reflexive`, closed acceptance. | Good kernel/acceptance smoke test, but may not map directly to a current core lemma. |
| Pure implication identity `A ==> A` | Exercises assumption introduction and legal discharge. | Checked `CProp`, `KernelRules::assume`, `KernelRules::implies_intr`, `ClosedThm` acceptance. | Targeted smoke slice implemented; next step is an existing core-file lemma. |
| Simple equality reflexivity exposed through HOL | Brings the path closer to user-visible HOL facts. | HOL equality adapter, type certification, strict reflexivity. | Good second slice after Pure path works. |
| `HOL::TrueI` | User-visible base fact. | HOL `True` encoding, method/export routing, possibly simplifier/proofterm support. | Too entangled for the first slice. |

Recommended order:

```text
1. strict Pure implication identity as a direct parser/certifier/export smoke test (done)
2. smallest parsed core-file theorem that can reuse that strict path
3. HOL equality/True-facing slices after object-logic adapters are clearer
```

## Next Engineering Gates

1. Implement `ProofOutcome` as a report/classification layer without changing
   proof behavior.
2. Use it in core verification reports.
3. Add a strict adapter for the chosen implication-identity slice.
4. Route one existing core-file theorem through that adapter.
5. Increase the strict closed count only through `StrictClosed`.
6. Resume admitted-reason reduction based on the new outcome report.
