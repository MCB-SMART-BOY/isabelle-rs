# Next Strict Slice Candidates

## Status

Diagnostic and design report only. This scan does not implement a second strict
theorem adapter or add a kernel primitive.

Current sampled baseline:

```text
TransitionalStrictClosed: 1/125
KernelTrustedClosed: 0/125
CompatClosedOracleFree: 1
Admitted(goal_export_unknown_hyps): 65
Admitted(goal_export_open_subgoals): 3
Admitted(parser_gap): 3
Admitted(datatype_stub): 2
Admitted(proof_engine_failed): 50
```

`HOL::TrueI` remains the only sampled `TransitionalStrictClosed` theorem. Its
bool-valued legacy conclusion is not eligible for `KernelTrustedClosed`.

## Scan Contract

The scan reproduces `core_batch_snapshot_reports_one_transitional_and_zero_kernel_trusted`:

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

| Rank | Theorem | Current outcome | Required reusable logical basis | Recommendation |
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
| Current `ProofOutcome` | `Admitted(proof_engine_failed)` |
| Current failure reason | `admitted:proof_engine_failed` |
| Dummy in parsed proposition | Yes |
| Direct `certify_checked` | No; the parsed `HOL.eq` applications and free-variable types are not yet reconstructed consistently |
| Strict rules needed | checked assumptions, `implies_intr`, and a checked instance of the installed HOL `subst` axiom schema |
| Existing adapter reuse | Reuses only the dispatcher and typed `NotApplicable/Proved/Rejected` boundary; the current legacy theorem constructors are not reusable for kernel trust |
| Target trust dependency | Immutable HOL basis manifest plus HOL-agnostic `LogicAxiom` schema instantiation and replay; no theorem-specific Rust bridge |
| Broad engine needed | No simp, unfolding, full resolution, lifting/freshening, or broad unification |
| Recommendation | Highest eventual consumer. The source is a single rule application, but implementation remains blocked on source-aware elaboration and the common theory/logic gates |

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
| Proof script | `by (rule subst)` |
| Current `ProofOutcome` | `Admitted(goal_export_open_subgoals)` |
| Current failure reason | `admitted:goal_export_open_subgoals` |
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
| Current `ProofOutcome` | `Admitted(proof_engine_failed)` |
| Current failure reason | `admitted:proof_engine_failed` |
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
| Current `ProofOutcome` | `Admitted(goal_export_open_subgoals)` |
| Current failure reason | `admitted:goal_export_open_subgoals` |
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

The historical recommendation assumed a new object-logic bridge. The trust
correction supersedes that path: none of the remaining 124 sampled theorems is
eligible for a `KernelTrustedClosed` increase.

Immutable theory/signature identity, unique acceptance, and the unresolved
source-AST data model are now implemented. The next source work is parser
integration plus checked declaration/type-scheme elaboration, followed by an
explicit replayable HOL basis and conservative definitions. It is not
another theorem adapter or legacy TCB bridge.

The required parser-to-checked boundary is now specified in
[CHECKED_HOL_PROPOSITION_NORMALIZATION.md](CHECKED_HOL_PROPOSITION_NORMALIZATION.md),
and the proposed replacement for adding more trusted power to legacy core is
[ADR-0003-hol-logic-trusted-extension.md](ADR-0003-hol-logic-trusted-extension.md).
Neither document implements `HOL::trans` or substitution.
