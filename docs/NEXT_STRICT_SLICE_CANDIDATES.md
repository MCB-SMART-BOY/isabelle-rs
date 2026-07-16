# Next Strict Slice Candidates

## Status

Diagnostic and design report only. This scan does not implement a second strict
theorem adapter or add a kernel primitive.

Current sampled baseline:

```text
StrictClosed: 1/125
CompatClosedOracleFree: 1
Admitted(goal_export_unknown_hyps): 65
Admitted(goal_export_open_subgoals): 3
Admitted(parser_gap): 3
Admitted(datatype_stub): 2
Admitted(proof_engine_failed): 50
```

`HOL::TrueI` remains the only sampled `StrictClosed` theorem.

## Scan Contract

The scan reproduces `test_verify_all_core_files_reports_at_least_one_strict_closed`:

```text
HOL, Orderings, Set, Nat, List
first 25 parsed lemmas with proof_script.is_some() from each file
125 attempted theorems total
124 remaining after excluding HOL::TrueI
```

For each remaining theorem, the scan compared the source proposition and proof
with the parsed term, dynamic `ProofOutcome`, oracle/admit reason, residual
dummy types, direct `certify_checked` viability, and the strict rules needed to
reconstruct it.

Stable negative findings:

- No remaining theorem uses `by assumption`, `.`, or `by .`.
- No remaining parsed implication chain has a conclusion identical to one of
  its premises, so the existing strict implication-identity path does not apply.
- No remaining parsed proposition is top-level reflexive `HOL.eq t t`, so
  `try_strict_hol_refl` alone cannot produce `2/125`.
- Every ranked candidate still contains dummy-typed or incompletely reconstructed
  HOL terms and fails direct checked certification as parsed.
- No remaining theorem can be migrated using only the existing strict
  implication and HOL reflexivity paths.

## Ranked Summary

| Rank | Theorem | Current outcome | Required reusable strict rule | Recommendation |
|---:|---|---|---|---|
| 1 | `HOL::trans` | `Admitted(proof_engine_failed)` | checked HOL object-equality substitution plus implication discharge | Recommended next `1/125 -> 2/125` target |
| 2 | `HOL::sym` | `Admitted(parser_gap)` | the same substitution rule plus existing HOL reflexivity | Strong follow-up after the parser-gap preemption is removed |
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
| Current `ProofOutcome` | `Admitted(proof_engine_failed)` |
| Current failure reason | `admitted:proof_engine_failed` |
| Dummy in parsed proposition | Yes |
| Direct `certify_checked` | No; the parsed `HOL.eq` applications and free-variable types are not yet reconstructed consistently |
| Strict rules needed | checked assumptions, `implies_intr`, and a general checked HOL object-equality substitution rule |
| Existing adapter reuse | Reuses the dispatcher, typed `NotApplicable/Proved/Rejected` boundary, checked normalization pattern, and strict implication discharge |
| New TCB bridge | Yes: one general, replayable HOL substitution bridge; not a `trans`-specific primitive |
| Broad engine needed | No simp, unfolding, full resolution, lifting/freshening, or broad unification |
| Recommendation | Highest. The source is a single rule application, the parsed logical skeleton is intact, and the bridge also serves ranks 2-5 |

## 2. `HOL::sym`

| Field | Finding |
|---|---|
| Theory/file | `HOL`, `theories/HOL/HOL.thy` |
| Source proposition | `s = t \<Longrightarrow> t = s` |
| Parsed proposition | `(s = t) ==> (t = s)` |
| Proof script | `by (erule subst) (rule refl)` |
| Current `ProofOutcome` | `Admitted(parser_gap)` |
| Current failure reason | `admitted:parser_gap` |
| Dummy in parsed proposition | Yes |
| Direct `certify_checked` | No; the equality operand type remains unresolved |
| Strict rules needed | the general HOL substitution bridge, existing `try_strict_hol_refl`, checked assumption, and `implies_intr` |
| Existing adapter reuse | Uses the same equality-family normalization and dispatcher entry as `trans` |
| New TCB bridge | The same general HOL substitution bridge; no `sym`-specific primitive |
| Broad engine needed | No general proof engine or resolution |
| Recommendation | Second. Its term shape is small, but `verify_lemma` currently admits it at the earlier builtin Var/Free parser-gap path, which must be addressed without hiding that gap |

## 3. `HOL::back_subst`

| Field | Finding |
|---|---|
| Theory/file | `HOL`, `theories/HOL/HOL.thy` |
| Source proposition | `P a \<Longrightarrow> a = b \<Longrightarrow> P b` |
| Parsed proposition | `P a ==> (a = b) ==> P b` |
| Proof script | `by (rule subst)` |
| Current `ProofOutcome` | `Admitted(goal_export_open_subgoals)` |
| Current failure reason | `admitted:goal_export_open_subgoals` |
| Dummy in parsed proposition | Yes |
| Direct `certify_checked` | No; `P : 'a => bool` and the shared type of `a`/`b` are not reconstructed as checked inputs |
| Strict rules needed | general checked HOL substitution and two implication discharges |
| Existing adapter reuse | Reuses the equality-family bridge while testing it over an arbitrary checked predicate |
| New TCB bridge | The same general HOL substitution bridge |
| Broad engine needed | No simp or resolution; checked higher-order application normalization is more involved than for `trans` |
| Recommendation | Third. It is a strong reuse test, but its certification boundary is larger than the equality-only `trans` slice |

## 4. `HOL::iffD2`

| Field | Finding |
|---|---|
| Theory/file | `HOL`, `theories/HOL/HOL.thy` |
| Source proposition | `\<lbrakk>P = Q; Q\<rbrakk> \<Longrightarrow> P` |
| Parsed proposition | `(P = Q) ==> Q ==> P` |
| Proof script | `by (erule ssubst)` |
| Current `ProofOutcome` | `Admitted(proof_engine_failed)` |
| Current failure reason | `admitted:proof_engine_failed` |
| Dummy in parsed proposition | Yes |
| Direct `certify_checked` | No; boolean operands and the theorem proposition boundary are not checked as parsed |
| Strict rules needed | the same substitution rule at object type `bool`, with the required equality direction made explicit |
| Existing adapter reuse | Reuses the equality-family checked normalization and typed dispatcher result |
| New TCB bridge | The same general HOL substitution bridge |
| Broad engine needed | No general automation |
| Recommendation | Fourth. It demonstrates bool equality reuse but is not the smallest first instance of the bridge |

## 5. `HOL::forw_subst`

| Field | Finding |
|---|---|
| Theory/file | `HOL`, `theories/HOL/HOL.thy` |
| Source proposition | `a = b \<Longrightarrow> P b \<Longrightarrow> P a` |
| Parsed proposition | `(a = b) ==> P b ==> P a` |
| Proof script | `by (rule ssubst)` |
| Current `ProofOutcome` | `Admitted(goal_export_open_subgoals)` |
| Current failure reason | `admitted:goal_export_open_subgoals` |
| Dummy in parsed proposition | Yes |
| Direct `certify_checked` | No; the predicate and equality operand types remain unresolved |
| Strict rules needed | the same HOL substitution bridge plus explicit direction/symmetry handling |
| Existing adapter reuse | Reuses the same equality-family adapter infrastructure as ranks 1-4 |
| New TCB bridge | The same general HOL substitution bridge |
| Broad engine needed | No general resolution; direction handling makes it a later family member |
| Recommendation | Fifth. Useful evidence of reuse, but less direct than `trans` or `back_subst` |

## Rejected Near-Term Candidates

| Candidate | Why it is not a near-term strict slice |
|---|---|
| `HOL::meta_eq_to_obj_eq` | Source is `(A \<equiv> B) ==> A = B`, but the parsed proposition loses the meta-equality premise and becomes `A ==> A = B`; parser repair and a separate Pure-to-HOL equality design are prerequisites |
| `Set::CollectI` | It is the only sampled `CompatClosedOracleFree` result, but the parsed proposition degrades to `P a ==> a` and the source proof uses `simp`; compatibility status is not strict progress |
| Nat candidates | The first 25 depend on datatype rules, induction, malformed parser output, or compat/admitted facts |
| List candidates | The first 25 depend on datatype stubs, induction, simp, or malformed parser output |

## Recommended Next Slice Contract

Recommend `HOL::trans`, but only as the first consumer of a reusable equality
substitution slice:

```text
parsed HOL equality implication chain
  -> reusable checked HOL proposition/equality normalization
  -> checked local assumptions
  -> general replayable HOL object-equality substitution bridge
  -> strict implication discharge
  -> existing strict adapter dispatcher
  -> StrictClosed
```

The next implementation must not be:

```text
if theorem_name == "trans" { return a fabricated theorem }
```

The bridge contract must be theorem-independent and have positive, negative,
burden-propagation, replay, and malformed-type attack tests. `HOL::sym`,
`HOL::back_subst`, `HOL::iffD2`, and `HOL::forw_subst` should be able to reuse
the same normalization and rule boundary.

This recommendation does require a new TCB bridge. If the next round also
forbids any new TCB bridge, none of the remaining 124 sampled theorems is an
eligible `2/125` target; the correct next task would be checked HOL proposition
normalization and bridge design rather than theorem implementation.
