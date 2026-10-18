# Next Strict Slice Candidates

## Status

Historical candidate scan and deferred design report, not a current backlog
for a second trusted HOL constructor. It predates the fail-closed parser,
proof-result and automation changes; per-theorem outcomes and reasons below
are *scan-time findings*, not current checkout results. The 2026-10-03
post-hardening core library and binary samplers report:

```text
KernelTrustedClosed: 0/125
TransitionalStrictClosed: 1/125
CompatClosedOracleFree: 0
Admitted(parser_gap): 2
Admitted(datatype_stub): 2
Admitted(proof_engine_failed): 120
```

See [PROJECT_STATUS.md](../status/PROJECT_STATUS.md) for the dated sampled
metric and current delivery blockers. The 2026-10-03 transitional `HOL::TrueI`
bridge recorded above is removed. On 2026-10-07 an audited projection of the
bundled `HOL::TrueI` source instead reached `KernelTrustedClosed: 1/125` and
`TransitionalStrictClosed: 0/125`, not complete HOL/ML execution. Two independent
source-backed CLI fixtures, HOL `TrueI` and Pure identity, remain outside the
125 sampled theorems. The subsequently resumed P2/P3/P4 implementation has
not rerun this scan or established additional sampled trusted HOL constructors.

## Scan Contract

This historical scan used the 125-lemma core selection (first 25 parsed
explicit-proof lemmas each from HOL, Orderings, Set, Nat and List), excluding
the then-migrated `HOL::TrueI` while ranking alternatives. It compared source
propositions/proofs with legacy parsed terms, outcomes and missing strict
derivations at the time. Since parser/goal-export contracts have changed, its
individual failure-reason fields must not be used as present-day telemetry.
Historical shape findings for the then-ranked candidates:

- No remaining theorem uses `by assumption`, `.`, or `by .`.
- No remaining parsed implication chain has a conclusion identical to one of
  its premises, so the existing strict implication-identity path does not apply.
- No remaining parsed proposition in this historical scan was top-level
  reflexive `HOL.eq t t`; the former `try_strict_hol_refl` alone could not
  produce a second transitional result.
- Every ranked candidate in this scan contained dummy-typed or incompletely reconstructed
  HOL terms and fails direct checked certification as parsed.
- No remaining theorem can be migrated using only the existing strict
  implication and HOL reflexivity paths.

## Ranked Summary

| Rank | Theorem | Outcome at historical scan | Required reusable logical basis | Recommendation |
|---:|---|---|---|---|
| 1 | `HOL::trans` | `Admitted(proof_engine_failed)` | checked HOL object-equality substitution plus implication discharge | Best eventual consumer after the foundational kernel-trust gates; not a current coverage target |
| 2 | `HOL::sym` | `Admitted(parser_gap)` | installed HOL `subst` and `refl` axiom schemas plus Pure rules | Possible follow-up only after the same foundational gates |
| 3 | `HOL::back_subst` | `Admitted(goal_export_open_subgoals)` | the same substitution rule over an arbitrary checked predicate | Best proof that the bridge is not equality-chain-specific |
| 4 | `HOL::iffD2` | `Admitted(proof_engine_failed)` | the same substitution rule specialized to checked booleans | Useful bool-equality follow-up |
| 5 | `HOL::forw_subst` | `Admitted(goal_export_open_subgoals)` | symmetry/direction handling over the same substitution rule | Useful family coverage, but not the first slice |

## 1. `HOL::trans`

| Field | Finding |
|---|---|
| Theory/file | `HOL`, `theories/HOL/HOL.thy` |
| Source proposition | `\<lbrakk>r = s; s = t\<rbrakk> \<Longrightarrow> r = t` |
| Parsed proposition | `(r = s) ==> (s = t) ==> (r = t)` |
| Proof script | `by (erule subst)` |
| Historical `ProofOutcome` | `Admitted(proof_engine_failed)` |
| Historical failure reason | `admitted:proof_engine_failed` |
| Dummy in parsed proposition | Yes |
| Direct `certify_checked` | No; the parsed `HOL.eq` applications and free-variable types are not yet reconstructed consistently |
| Strict rules needed | checked assumptions, `implies_intr`, and a checked instance of the installed HOL `subst` axiom schema |
| Existing adapter reuse | Reuses only the dispatcher and typed `NotApplicable/Proved/Rejected` boundary; the current legacy theorem constructors are not reusable for kernel trust |
| Target trust dependency | Immutable HOL basis manifest plus HOL-agnostic `LogicAxiom` schema instantiation and replay; no theorem-specific Rust bridge |
| Broad engine needed | No simp, unfolding, full resolution, lifting/freshening, or broad unification |
| Recommendation | Highest eventual consumer. The source is a single rule application, but implementation remains blocked on source-aware elaboration and the common theory/logic gates |

`LogicAxiom` in this historical target is design vocabulary, not a current
public API: the strict kernel currently uses `Derivation::AxiomInstance` for
installed schema replay. The `subst` basis and this consumer remain deferred.

## 2. `HOL::sym`

| Field | Finding |
|---|---|
| Theory/file | `HOL`, `theories/HOL/HOL.thy` |
| Source proposition | `s = t \<Longrightarrow> t = s` |
| Parsed proposition | `(s = t) ==> (t = s)` |
| Proof script | `by (erule subst) (rule refl)` |
| Historical `ProofOutcome` | `Admitted(parser_gap)` |
| Historical failure reason | `admitted:parser_gap` |
| Dummy in parsed proposition | Yes |
| Direct `certify_checked` | No; the equality operand type remains unresolved |
| Strict rules needed | installed HOL `subst` and `refl` axiom instances, checked assumption, and `implies_intr` |
| Existing adapter reuse | Uses the same equality-family normalization and dispatcher entry as `trans` |
| Target trust dependency | The same immutable HOL manifest and generic schema replay; no `sym`-specific primitive and no reuse of legacy `try_strict_hol_refl` for final trust |
| Broad engine needed | No general proof engine or resolution |
| Recommendation | Second eventual consumer. Its term shape is small; dispatcher priority is fixed, but source/type elaboration and kernel-trust gates remain open |

## 3. `HOL::back_subst`

| Field | Finding |
|---|---|
| Theory/file | `HOL`, `theories/HOL/HOL.thy` |
| Source proposition | `P a \<Longrightarrow> a = b \<Longrightarrow> P b` |
| Parsed proposition | `P a ==> (a = b) ==> P b` |
| Historical `ProofOutcome` | `Admitted(goal_export_open_subgoals)` |
| Historical failure reason | `admitted:goal_export_open_subgoals` |
| Dummy in parsed proposition | Yes |
| Direct `certify_checked` | No; `P : 'a => bool` and the shared type of `a`/`b` are not reconstructed as checked inputs |
| Strict rules needed | a checked installed `subst` axiom instance and two implication discharges |
| Existing adapter reuse | Reuses the equality-family elaboration and generic logic-axiom path while testing an arbitrary checked predicate |
| Target trust dependency | The same immutable HOL manifest and generic schema replay |
| Broad engine needed | No simp or resolution; checked higher-order application normalization is more involved than for `trans` |
| Recommendation | Third. It is a strong reuse test, but its certification boundary is larger than the equality-only `trans` slice |

## 4. `HOL::iffD2`

| Field | Finding |
|---|---|
| Theory/file | `HOL`, `theories/HOL/HOL.thy` |
| Source proposition | `\<lbrakk>P = Q; Q\<rbrakk> \<Longrightarrow> P` |
| Parsed proposition | `(P = Q) ==> Q ==> P` |
| Proof script | `by (erule ssubst)` |
| Historical `ProofOutcome` | `Admitted(proof_engine_failed)` |
| Historical failure reason | `admitted:proof_engine_failed` |
| Dummy in parsed proposition | Yes |
| Direct `certify_checked` | No; boolean operands and the theorem proposition boundary are not checked as parsed |
| Strict rules needed | the same substitution rule at object type `bool`, with the required equality direction made explicit |
| Existing adapter reuse | Reuses the equality-family checked normalization and typed dispatcher result |
| Target trust dependency | The same immutable HOL manifest and generic schema replay |
| Broad engine needed | No general automation |
| Recommendation | Fourth. It demonstrates bool equality reuse but is not the smallest first instance of the bridge |

## 5. `HOL::forw_subst`

| Field | Finding |
|---|---|
| Theory/file | `HOL`, `theories/HOL/HOL.thy` |
| Source proposition | `a = b \<Longrightarrow> P b \<Longrightarrow> P a` |
| Parsed proposition | `(a = b) ==> P b ==> P a` |
| Proof script | `by (rule ssubst)` |
| Historical `ProofOutcome` | `Admitted(goal_export_open_subgoals)` |
| Historical failure reason | `admitted:goal_export_open_subgoals` |
| Dummy in parsed proposition | Yes |
| Direct `certify_checked` | No; the predicate and equality operand types remain unresolved |
| Strict rules needed | the same installed substitution schema plus explicit direction/symmetry derivation |
| Existing adapter reuse | Reuses the same equality-family adapter infrastructure as ranks 1-4 |
| Target trust dependency | The same immutable HOL manifest and generic schema replay |
| Broad engine needed | No general resolution; direction handling makes it a later family member |
| Recommendation | Fifth. Useful evidence of reuse, but less direct than `trans` or `back_subst` |

## Rejected Near-Term Candidates

| Candidate | Why it is not a near-term strict slice |
|---|---|
| `HOL::meta_eq_to_obj_eq` | Source is `(A \<equiv> B) ==> A = B`, but the parsed proposition loses the meta-equality premise and becomes `A ==> A = B`; parser repair and a separate Pure-to-HOL equality design are prerequisites |
| `Set::CollectI` | It is the only sampled `CompatClosedOracleFree` result, but the parsed proposition degrades to `P a ==> a` and the source proof uses `simp`; compatibility status is not strict progress |
| Nat candidates | The first 25 depend on datatype rules, induction, malformed parser output, or compat/admitted facts |
| List candidates | The first 25 depend on datatype stubs, induction, simp, or malformed parser output |

## Eventual Consumer Contract

The scan ranks `HOL::trans` as the eventual first consumer after the
foundational gates, not as the next implementation task:

```text
source-aware HOL equality implication chain
  -> checked elaboration with explicit Trueprop and theory context
  -> checked local assumptions
  -> installed HOL subst axiom schema through generic LogicAxiom replay
  -> Pure implication discharge
  -> existing strict adapter dispatcher
  -> context-bound src/kernel::TrustedTheorem
  -> KernelTrustedClosed
```

The next implementation must not be:

```text
if theorem_name == "trans" { return a fabricated theorem }
```

The logic-basis path must be theorem-independent and have positive, negative,
burden/provenance, replay, context-identity, and malformed-type attack tests. `HOL::sym`,
`HOL::back_subst`, `HOL::iffD2`, and `HOL::forw_subst` should be able to reuse
the same normalization and rule boundary.

The historical proposal to move directly from the ranked `trans` family to
new HOL substitution logic is superseded as an *immediate* task. Immutable
signature/theory identity, strict type/arity and axiom-schema checks, exact
owner replay, a minimal installed HOL `refl` basis, conservative `True_def`,
and narrow standalone source fixtures now support the audited sampled
`HOL::TrueI` projection. It does not reconstruct the full sampled HOL theory
or authorize `HOL::trans`; only after extending the source-backed path should
the `trans` family be reconsidered, without theorem-specific trusted
constructors.

The broader parser-to-checked requirements remain documented in
[CHECKED_HOL_PROPOSITION_NORMALIZATION.md](CHECKED_HOL_PROPOSITION_NORMALIZATION.md);
the deferred object-logic design lives in
[ADR-0003-hol-logic-trusted-extension.md](../adr/ADR-0003-hol-logic-trusted-extension.md).
Neither document implements `HOL::trans` or general substitution.
