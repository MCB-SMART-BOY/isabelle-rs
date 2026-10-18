# Resolution / Bicompose Family — Design and Status

This document records the current conservative resolution family in
`crates/kernel` (re-exported at `src/kernel`): `resolve1_match` and propositional
`subst_premise`. The historical `KernelRules::bicompose` wrapper is not exported
by the current crate; its residual `src/kernel/rules.rs` file is outside the
module tree. `resolve1_match` records `Derivation::Resolve1Match` and has no
full unifier. Separately, the resumed
P1 native-closure work provides `KernelRules::bicompose_candidate`, a bounded
Pure composition checker that replays both complete source proofs, accepts a
finite untrusted candidate and records `Derivation::Bicompose`; it can carry
residual flex pairs, which prevent closed acceptance. This is not a complete
Isabelle/ML `bicompose`/`biresolution` search or Seq facade. The conservative
resolution contracts and historical design template below are not that newer API;
see [P1 composition lowering](../kernel/KERNEL_PRIMITIVES.md#p1-composition-lowering)
and [THM inventory](../status/NATIVE_THM_INTERFACE_INVENTORY.md).

This is not authorization to broaden resolution: alongside two standalone
source-backed HOL/Pure fixtures, the pre-cutover bundled 125-lemma sample
accepted only the audited `HOL::TrueI` projection (`KernelTrustedClosed: 1/125`,
`TransitionalStrictClosed: 0/125`). The subsequently resumed P2/P3/P4
native closure implementation has not rerun that sampler or established
complete HOL/ML execution. See
[PROJECT_STATUS.md](../status/PROJECT_STATUS.md).

## Relationship to `KERNEL_PRIMITIVES.md`

[KERNEL_PRIMITIVES.md](../kernel/KERNEL_PRIMITIVES.md) documents the base
Pure rules. This conservative resolution subset additionally handles premise
selection, one-way matching and hypothesis substitution; it does not grant
Isabelle-style complete bicomposition or general ATP replay.

## Core Conceptual Difference from Previous Draft

A previous draft described `bicompose` backwards:

```text
❌ WRONG: select premise Aᵢ of rule and unify with goal G
```

The correct direction for **backward resolution** is:

```text
✅ CORRECT: select subgoal Gᵢ of goal state and unify with rule conclusion C
```

This document uses the corrected contract throughout.

---

## 1. Goal State Representation

In a proof engine, a goal is not a bare proposition. It is an **implication chain**:

```text
goal_state: Δ |- G₁ ==> G₂ ==> ... ==> Gₘ ==> R
```

where:
- `G₁, G₂, ..., Gₘ` are the **subgoals** (premises of the implication chain).
- `R` is the **conclusion**.
- `Δ` are the **hypotheses**.

When a goal has zero subgoals (`m = 0`), it is `Δ |- R` — a terminal goal.

### Implication-Chain Utilities

The strict kernel provides these utilities on `Term`. Their authoritative
implementations live in [`crates/kernel/src/term.rs`](../../crates/kernel/src/term.rs). A
standalone API sketch for experimentation is maintained in
[resolution_api.rs](../../scripts/templates/resolution_api.rs).

These utilities are unit-tested and do not require unification.

---

## 2. Corrected `bicompose` Contract (Backward Resolution)

```text
rule:
  Γ |- A₁ ==> A₂ ==> ... ==> Aₙ ==> C

goal_state:
  Δ |- G₁ ==> G₂ ==> ... ==> Gᵢ ==> ... ==> Gₘ ==> R

match:
  unify(C, Gᵢ) = σ   where σ is the most-general unifier

result:
  Γσ ∪ Δσ |-
    G₁σ ==> ... ==> Gᵢ₋₁σ ==>
    A₁σ ==> A₂σ ==> ... ==> Aₙσ ==>
    Gᵢ₊₁σ ==> ... ==> Gₘσ ==> Rσ
```

Key points:
- The **rule conclusion `C`** is unified with the **selected subgoal `Gᵢ`**.
- The rule's premises `A₁...Aₙ` **replace** the selected subgoal in the goal state.
- The remaining subgoals (`G₁...Gᵢ₋₁` and `Gᵢ₊₁...Gₘ`) are preserved.
- Hypotheses are unioned and the substitution `σ` is applied throughout.

### Special cases

**Empty rule premises** (`n = 0`): The rule is `Γ |- C`. Resolution with subgoal
`Gᵢ` simply removes `Gᵢ` from the goal chain:

```text
result: Γσ ∪ Δσ |-
  G₁σ ==> ... ==> Gᵢ₋₁σ ==> Gᵢ₊₁σ ==> ... ==> Gₘσ ==> Rσ
```

**Empty goal subgoals** (`m = 0`): There is no selected subgoal.
`resolve1` / `bicompose` with any `selected_subgoal_index` must return
`SubgoalIndexOutOfRange`. This is consistent with `select_subgoal(R, 0) = None`:
when there are no subgoals, there is nothing to select and nothing to resolve
against.

Conclusion-resolution (matching a rule conclusion `C` against the goal-state
conclusion `R` directly, without subgoal indexing) is a separate future operation
(e.g., `resolve_conclusion` or `terminal_resolve`). It must NOT be mixed into
the subgoal-index model. This keeps the contract simple: the index always refers
to a subgoal in the implication chain, never the conclusion.

---

## 2A. Current `resolve1_match` and Historical `bicompose` Wrapper

The current conservative interface is `KernelRules::resolve1_match`.
The earlier thin `KernelRules::bicompose` alias is not part of the isolated
crate API. Its historical name must not be inferred from residual source files.
The restrictions below do not describe `KernelRules::bicompose_candidate`,
whose separate [P1 contract](../kernel/KERNEL_PRIMITIVES.md#p1-composition-lowering)
covers finite candidate checking, source replay and residual obligations.
`resolve1_match` does not copy legacy `ThmKernel::bicompose` and does not
introduce full unification, lifting/freshening, e-resolution or premise solving.

### Relationship To `resolve1_match`

`resolve1_match` implements conservative backward resolution:

```text
rule conclusion C  --strict one-way match-->  selected goal subgoal Gᵢ
rule premises replace Gᵢ
substitution applies to rule premises, remaining goal, and hypotheses
invariant replay recomputes the match and result proposition
```

The historical `bicompose` alias delegated to this operation; current callers
use `resolve1_match` directly.

It must not duplicate subgoal-splicing logic. `Term::replace_subgoal_with_premises`
remains the single ordering primitive for replacing a selected subgoal.

### Major / Minor Roles

The current API keeps roles explicit. Its exact signature is owned by
[`KernelRules::resolve1_match`](../../crates/kernel/src/rules.rs).
The standalone template is design-only, not a callable `bicompose` API.

Do not infer roles from theorem shape. The `rule` theorem supplies inserted
premises; the `goal_state` theorem supplies the selected subgoal and retained
goal chain.

### Selected Subgoal Semantics

`selected_subgoal_index` indexes the goal theorem's implication-chain premises,
not the rule theorem's premises and not the goal conclusion:

```text
goal_state: Δ |- G₁ ==> ... ==> Gᵢ ==> ... ==> Gₘ ==> R
selected_subgoal_index = i
```

Out-of-range selection fails before theorem construction:

```text
SubgoalIndexOutOfRange { index, nprems: m }
```

### Supported Subset

Only `resolve1_match` is restricted to the following conservative subset,
not the separate P1 candidate API:

```text
strict one-way matching only
rule-side Vars may be instantiated
goal-side Vars are treated as concrete targets
overlapping rule/goal schematic Var (name, index) pairs are rejected
no full unification
no e-resolution / premise solving
no lifting / freshening
no flex-flex pairs
no conclusion-resolution
```

This conservative operation is not Isabelle's full `bicompose`.
The current backward-resolution entry point is `resolve1_match`.

### Variable Namespace Policy

The first version must not silently merge rule and goal namespaces.

Current `resolve1_match` rejects same-named Free collisions and
overlapping rule/goal schematic variable `(name, index)` pairs with
`RequiresLifting`.

The first implementation chooses rejection rather than proving that goal-side
Vars-as-concrete is sufficient. This may reject valid cases, but it keeps the
trusted rule from depending on unstated freshening semantics.

### Unsupported Cases

`resolve1_match` must reject or leave unsupported:

```text
goal has no selectable subgoal
rule/goal Free collision requiring lifting
rule/goal Var namespace collision
match failure between rule conclusion and selected subgoal
full unification requirement
flex-flex pairs / tpairs
elimination premise solving
conclusion-resolution
legacy compatibility alpha-equivalence
```

### Derivation Replay Strategy

`resolve1_match` records `Derivation::Resolve1Match`, as its historical
`bicompose` alias did. It does not record the separate `Derivation::Bicompose`
used by the current P1 candidate checker. `Resolve1Match` replay must:

1. recursively check `rule` and `goal_state`;
2. reselect the goal subgoal by `selected_subgoal_index`;
3. rederive the same strict match substitution;
4. reject if recorded `subst` differs from replay-derived `subst`;
5. rebuild the result via `replace_subgoal_with_premises`;
6. compare replayed theorem fields with stored theorem fields.

### Current Conservative Resolution Attack Tests

Examples in [`crates/kernel/src/rules.rs`](../../crates/kernel/src/rules.rs):

- `resolve1_basic_no_vars`
- `resolve1_basic_with_match`
- `resolve1_selected_index_is_goal_subgoal_not_rule_premise`
- `resolve1_rejects_goal_var_namespace_collision_without_lifting`
- `resolve1_preserves_rigid_hypotheses_after_matching`
- `resolve1_multiple_bindings_preserve_subgoal_order`
- `resolve1_tampered_result_rejected`

These are current test locations, not results from a new run. Old
`bicompose_*` wrapper tests outside the module tree are not current coverage.

---

## 3. Corrected `bicompose_eresolve` Contract (Elimination Resolution)

```text
rule (elimination rule):
  Γ |- A₁ ==> A₂ ==> ... ==> Aₙ ==> C

goal_state:
  Δ |- G₁ ==> ... ==> Gᵢ ==> ... ==> Gₘ ==> R

Step 1 — match major premise:
  unify(C, Gᵢ) = σ

Step 2 — solve minor premises with additional facts:
  For each minor premise Aⱼ, attempt to prove it using the
  provided premises list. Unsolved premises become new subgoals.

result:
  Δσ ∪ Γσ |-
    G₁σ ==> ... ==> Gᵢ₋₁σ ==>
    (unsolved minor premises)σ ==>
    Gᵢ₊₁σ ==> ... ==> Gₘσ ==> Rσ
```

Note: the proposed full `bicompose_eresolve` is a higher-level operation
with premise solving and ML search semantics; `resolve1_match` does not
implement it. The separate `bicompose_candidate` now checks a supplied finite
elimination choice, but has no ML unifier or lazy `Seq` facade and does not
establish full elimination-resolution compatibility.

---

## 4. Conservative `subst_premise` Contract (Premise Rewriting)

`subst_premise` is implemented as a conservative strict-resolution rule. This
section describes the **first strict-kernel version only**. It is deliberately
smaller than Isabelle's full premise-rewriting machinery.

```text
input:
  eq_thm:      Γ |- A == B       where A, B : prop
  goal_state:  Δ |- G₁ ==> ... ==> A ==> ... ==> Gₘ ==> R
  i:           selected subgoal index, where Gᵢ is exactly A

output:
  Γ ∪ Δ |-
    G₁ ==> ... ==> B ==> ... ==> Gₘ ==> R
```

`subst_premise` rewrites a single premise of the goal state using an equality
theorem. It exercises premise indexing, propositional equality elimination, and
hypothesis propagation without introducing unification, lifting, or freshening.

### First-Version Restrictions

The first version must enforce:

```text
prop equality only
lhs -> rhs only
no symmetric rewrite
no object equality rewrite
no full unification
no matching beyond exact strict alpha-equivalence
no lifting / freshening
no flex-flex pairs
```

Consequences:

- The equality theorem must have proposition `A == B` where both sides have
  type `prop`.
- The selected subgoal must be strict alpha-equivalent to `A`.
- If the selected subgoal equals `B` but not `A`, the rule rejects. Callers can
  apply `symmetric` explicitly in a later version, but the first version does
  not do this automatically.
- Object equality such as `x == y` where `x, y : nat` is rejected with
  `NotProposition` or an equivalent typed error.
- The remaining goal subgoals and conclusion are preserved exactly.
- Hypotheses are unioned modulo strict alpha-equivalence:

```text
hyps(result) = Γ ∪ Δ
```

No substitution is applied in the first version because there is no
unification/matching step.

### First-Version Error Behavior

Expected failures:

```text
SubgoalIndexOutOfRange
NotEquality
NotProposition
AntecedentMismatch / PremiseMismatch
Invariant violation on replay/tampering
```

If the goal state has no subgoals, any index is out of range. If `i` points
outside the implication-chain premise list, the rule must fail before theorem
construction.

### Relationship To `equal_elim`

`equal_elim` already validates propositional equality:

```text
Γ |- A == B
Δ |- A
----------
Γ ∪ Δ |- B
```

`subst_premise` is the goal-state version of this operation. It rewrites the
selected subgoal in an implication chain rather than consuming a standalone
minor theorem. The strict implementation decomposes the goal into premises and
rebuilds it with `Term::replace_subgoal_with_premises`; it records its own
derivation and supports invariant replay.

### Out Of Scope For First Version

Future versions may add:

```text
symmetric rewrite mode
object equality rewriting
matching or unification against the selected subgoal
lifting / freshening
multi-premise rewrite tactics
integration with simplifier rewrite indexing
```

Those extensions must be designed and tested separately. They must not be
smuggled into the first version.

### Implemented Attack Tests

The first strict implementation covers these tests in
`crates/kernel/src/rules.rs` and `tests/kernel_rewrite_soundness.rs`.

| Test | What it checks |
|---|---|
| `subst_premise_basic` | `A == B` rewrites selected premise `A` to `B` in a goal chain. |
| `subst_premise_rejects_object_equality` | `x == y` for non-`prop` object type is rejected. |
| `subst_premise_rejects_out_of_range` | Selecting a missing subgoal fails before theorem construction. |
| `subst_premise_rejects_mismatch` | Selected subgoal not strict-alpha-equal to lhs `A` is rejected. |
| `subst_premise_rejects_symmetric_direction` | Selected subgoal equal to rhs `B`, not lhs `A`, is rejected. |
| `subst_premise_selected_index_is_goal_subgoal` | Selected index refers to the goal implication-chain subgoal, not part of the equality theorem. |
| `subst_premise_preserves_other_subgoals` | Premises before and after the selected subgoal remain unchanged. |
| `subst_premise_preserves_hypotheses` | Equality and goal hypotheses are unioned and preserved. |
| `subst_premise_invariant_check_passes` | Valid output replays through strict invariant checking. |
| `subst_premise_tampered_result_rejected` | Replay rejects forged proposition, wrong replacement, or dropped hypotheses. |

Additional negative coverage:

- selected subgoal equals rhs `B`, not lhs `A`, and is rejected unless caller
  explicitly supplies a symmetric equality theorem;
- object-equality rewrite is rejected even when the object terms are identical
  except for names;
- empty goal state rejects every selected index.

---

## 5. Strict Matcher/Unifier Requirements

### Hard constraint

```text
isabelle-kernel MUST NOT depend on legacy src/core
```

`src/kernel` is a re-export facade; `crates/kernel` owns this implementation.

### What the strict kernel needs

The strict matcher in `crates/kernel/src/unify.rs` produces raw bindings;
`crates/kernel/src/rules.rs` wraps replacements known to originate in a
certified proposition as `InstEntry`. Both helpers are `pub(crate)` within
the dedicated `isabelle-kernel` crate, not a public bare-`Term` to `InstEntry`
conversion. The reusable design sketch is
[resolution_api.rs](../../scripts/templates/resolution_api.rs).

### Implementation status

| Component | Status |
|---|---|
| `unify::match_terms` (raw matcher, kernel-crate-private) | Implemented (`crates/kernel/src/unify.rs`) |
| `MatchBinding` (raw binding, kernel-crate-private) | Implemented |
| `CTerm::from_certified_subterm` (kernel-crate-private) | Implemented |
| `KernelRules::match_terms_certified` (kernel-crate-private) | Implemented |
| Public `Term → CTerm` API | Intentionally absent |
| Legacy `src/core` and upper layers cannot call private match helpers | Enforced by separate crate |
| Full unification (`unify_terms`) | Deferred, not implemented |

The matcher is a **one-way structural matcher**, not full unification.
The file is named `crates/kernel/src/unify.rs`; higher-order/full
unification remains deferred.

### Conservative first version

For the initial `bicompose` (or a minimal `resolve1`), we can start with
**strict matching only** — the rule conclusion must match the goal subgoal
without instantiating goal-side Vars. This is sufficient for many resolution
steps in practice and avoids the complexity of full unification.

### Certified Replacement Construction

The strict matcher must produce `InstEntry` values whose `replacement` fields
are `CTerm`. This raises a design question: how does `match_terms`, given only
`&Term` references, construct fully certified `CTerm` replacements?

#### The problem

`InstEntry::replacement` requires a checked `CTerm`.

But `match_terms(pattern: &Term, target: &Term)` receives bare `Term` references,
not `CTerm` values. A naive implementation might:

1. **Bypass certification entirely** — construct `CTerm` via an unchecked
   internal path, undermining the certification boundary.
2. **Create a public unchecked `CTerm` constructor** — exposing a hole that
   any external code could exploit to build uncertified `CTerm` values.

Neither is acceptable for the strict kernel.

#### Design: certified-by-origin

The strict matcher only operates on subterms that **originate from already
certified propositions**. Specifically:

- The `target` argument is a subterm of a `KernelThm`'s certified proposition
  (obtained via `Term::select_subgoal` on the goal state's `CProp`).
- The `pattern` argument is a subterm of a rule's certified proposition.

Because both inputs trace back to certified `CProp` values, their subterms
inherit certification by origin. The matcher computes replacements from
these subterms and wraps them through a `pub(crate)` constructor scoped to
the dedicated `isabelle-kernel` crate. The implementation lives in
[`crates/kernel/src/cterm.rs`](../../crates/kernel/src/cterm.rs).
External code must use `ProofContext::certify_term`.

Key properties:

| Property | Guarantee |
|---|---|
| Visibility | `pub(crate)` inside the dedicated strict kernel crate |
| Certified-by-origin | Caller guarantees the term originated from a certified `CProp`/`KernelThm` |
| No dummy types | The certified term already passed `ProofContext` checks |
| Firewall integrity | `src/core/`, `src/isar/`, `src/tools/` and external crates cannot call this helper |

#### Alternative (rejected): pass `ProofContext` to the matcher

An alternative is to pass `ProofContext` directly to `match_terms` before the
pattern and target arguments. It remains an architectural option, not a copied
API template.

This is rejected for the first version because:
- It couples the matcher to the certification context.
- The `target` subterms already originate from certified propositions,
  so re-certification is redundant.
- It adds parameter noise to what should be a pure structural operation.

If later evidence shows that re-certification is valuable (e.g., for
cross-theory matching), the crate-private constructor can be replaced
by explicit context-passing without changing the matcher's API.

#### Impact on `InstEntry`

The `InstEntry::new` constructor already requires `CTerm` replacements.
The matcher produces `InstEntry` values through `InstEntry::new`, which
enforces the certification boundary. No new public API is needed.

---

## 6. Lifting / Freshening Policy

When a rule is applied, its free variables may collide with those in the goal.
The future `lift_rule` operation must increment bound indices and freshen free
variables before combining the rule with a goal. Its non-executable API sketch
is maintained in
[`scripts/templates/resolution_api.rs`](../../scripts/templates/resolution_api.rs).

**First version**: Do NOT implement lifting/freshening. However, the kernel
MUST NOT silently proceed when a collision would cause incorrect results.

Instead, `resolve1_match` and conservative `bicompose` must **detect** when the
rule and goal variable spaces collide in a way that requires lifting, and return
`KernelError::RequiresLifting` rather than proceeding. The authoritative error
definition is in [`crates/kernel/src/lib.rs`](../../crates/kernel/src/lib.rs).

#### What constitutes a collision?

A collision can occur when both the rule and the goal state contain variables
that may be incorrectly identified without lifting/freshening. Specifically:

1. **Same-named Free variables**: The rule has `Free("x", ...)` and the goal
   has `Free("x", ...)`. Without lifting, these would be incorrectly identified.
2. **Same-index Var variables**: The rule has `Var("?x", i, ...)` and the goal
   has `Var("?x", i, ...)`. Without freshening the rule's index space (e.g.,
   by incrementing indices above `goal.maxidx`), these could be incorrectly
   unified if a future rule starts instantiating both sides.

#### Conservative detection heuristic (first version)

Current `resolve1_match` / `bicompose` scan the rule and goal for overlapping
Free names and schematic Var `(name, index)` pairs. The reviewed implementation
is [`KernelRules::detect_collision`](../../crates/kernel/src/rules.rs); the corresponding
design template remains in
[`scripts/templates/resolution_api.rs`](../../scripts/templates/resolution_api.rs).

This is deliberately conservative: it may reject valid cases, but it will
never silently produce a wrong theorem. As lifting is implemented, the
rejection set shrinks.

For conservative `bicompose`, Var namespace policy is fixed for v1: reject
overlapping rule/goal schematic variable `(name, index)` pairs.

#### Test requirement

```text
resolve1_rejects_variable_collision_without_lifting
resolve1_rejects_goal_var_namespace_collision_without_lifting
bicompose_rejects_free_collision_without_lifting
bicompose_rejects_var_namespace_collision_without_lifting
```

These tests construct rule/goal pairs with overlapping Free names or schematic
Var keys and assert that the rule returns `Err(RequiresLifting)` rather than
silently producing an incorrect theorem.

This is a conservative boundary — lifting can be added later without changing
the bicompose contract.

---

## 7. Hypothesis Propagation

The resolution family propagates hypotheses as follows:

```text
hyps(result) = (hyps(rule) ∪ hyps(goal))σ
```

Where `σ` is the unifier/matcher. This requires:
1. Union the hypothesis sets (existing `union_hyps` with alpha-equivalence).
2. Apply the substitution to each hypothesis in the result.

The strict kernel already has `union_hyps` and `Term::instantiate_vars`.
`resolve1_match` now applies substitution to theorem hypotheses before union
and uses `Term::replace_subgoal_with_premises` as the single subgoal-splicing
primitive for result propositions. Future resolution-family rules should reuse
that helper instead of hand-rolling premise insertion order.
Invariant replay also covers the empty-rule-premise case: if a rule solves the
selected subgoal, replay recomputes the deletion and rejects forged results that
keep the solved premise in the goal chain.
Inline tests additionally lock the conservative prototype semantics: match
failure constructs no theorem, `selected_subgoal_index` indexes the goal's
premise chain, and the derived substitution is applied to inserted rule
premises, remaining goal subgoals, and theorem hypotheses.

---

## 8. Instantiate Integration

The `bicompose` family must integrate with the existing `instantiate` primitive:
- The matching/unification step produces `InstEntry` values.
- The substitution is applied via the same `Term::instantiate_vars`.
- The `CTerm` certification boundary is already enforced by `InstEntry`.

---

## 9. Open Design Questions

### Q1: Major/Minor Theorem Roles

Should the kernel be explicit about which theorem is the rule and which is the
goal, or should `bicompose` accept two `KernelThm` values and infer roles?

**Recommendation**: Two named parameters (`rule` and `goal_state`) with
explicit types. Not positional.

### Q2: Premise Selection

Options:
- Index-based: `selected_subgoal: usize` (0-indexed).
- Pattern-based: match the first premise that unifies.

**Recommendation**: Index-based for the first version, since `select_subgoal`
already provides 0-indexed access.

### Q3: Subgoal vs Premise Terminology

Should we say "premise" or "subgoal" when referring to elements of the goal
state's implication chain? This document uses "subgoal" for goal-state premises
to avoid confusion with rule premises.

### Q4: `tpairs` / Flex-Flex

The narrow `resolve1_match` operation does not create flex pairs.
The separate `bicompose_candidate` path now retains checked residual pairs in
the private theorem payload and replays them; unresolved pairs block closure.
That partial checker is not a full ML unifier or `tpairs_of` interface.

### Q5: Invariant Replay

Each resolution rule must have:
- A `Derivation` variant recording the inputs.
- An invariant replay path.
- Attack tests for tampered outputs.

### Q6: Error Types

Current reusable errors are `KernelError::SubgoalIndexOutOfRange` and
`KernelError::RequiresLifting`; their authoritative definitions are in
[`crates/kernel/src/lib.rs`](../../crates/kernel/src/lib.rs). Rules with no premises are valid and
therefore do not require a separate error variant.

Current strict matching failures are propagated from `match_terms_certified`
as existing `KernelError` values (`TypeMismatch`, `BoundInSubstitution`, or
`Invariant` with a mismatch diagnostic). A later full `bicompose` may introduce
a narrower `ResolutionMatchFailure` error, but that should be a separate API
cleanup, not a blocker for the conservative design.

### Q7: `subst_premise` vs `bicompose` Ordering

The current `resolve1_match` and `subst_premise` operations do not replace
full Isabelle-style bicomposition. The separate P1 `bicompose_candidate` path
adds a finite checked composition IR, not an ML unifier, search sequence, or
compatibility acceptance.

The first `subst_premise` version exercises premise indexing, propositional
equality elimination, hypothesis union, and invariant replay without requiring
unification.

---

## 10. Implementation Dependencies

| Dependency | Status | Impact |
|---|---|---|
| `dest_imp_chain` / `mk_imp_chain` / `nprems` / `select_subgoal` / `replace_subgoal_with_premises` | ✅ Implemented | Foundation for all resolution rules; `resolve1_match` uses the shared replacement helper |
| `instantiate` with Var→CTerm | ✅ Done | Substitution under certified boundary |
| `generalize` (Free→Var) | ✅ Done | For schematic rules |
| `union_hyps` + substitution | Implemented for `resolve1_match` | Applies substitution to rule and goal hyps before union |
| Strict matcher (`match_terms` + `match_terms_certified`) | ✅ Implemented | Dedicated-kernel-crate-private only; no public Term→CTerm API |
| `resolve1_match` | ✅ Prototype implemented | Conservative one-way backward resolution; shared subgoal-splicing helper; invariant replay covered; rejects Free and schematic Var namespace collisions |
| conservative `subst_premise` | ✅ Implemented | Prop equality only, lhs→rhs only, exact selected-subgoal match, no unification; invariant replay and attack tests covered |
| historical conservative `bicompose` | Not exported by the current crate | Earlier alias of `resolve1_match`; residual source is not an active API or replay path |
| Full ML unification/search | Not implemented | `bicompose_candidate` checks supplied finite candidates; no general ML unifier or Seq facade |
| Lifting / freshening | Implemented in the separate P1 composition path | Not provided by `resolve1_match` |
| `tpairs` / flex-flex | Residual flex pairs implemented in the separate P1 composition path | Checked obligations block closure; no complete ML projection or full unification |

---

## 11. Resolution-Family Implementation Order

1. ✅ **Implication-chain utilities** — `dest_imp_chain`, `mk_imp_chain`, `nprems`,
   `select_subgoal`, `replace_subgoal_with_premises`.
2. **Strict matcher** — raw `match_terms(pattern, target)` returns
   `Result<Vec<MatchBinding>, KernelError>`; crate-private
   `KernelRules::match_terms_certified(pattern, target, context)` certifies
   those bindings by origin under a `ContextStamp` and returns
   `Result<Vec<InstEntry>, KernelError>` (see Section 5).
   Conservative: pattern Vars only, exact type match, consistent duplicates.
   Bindings are returned in deterministic `(name, index, type)` order so
   derivation replay is not HashMap-order dependent.
3. ✅ **`resolve1_match`** — minimal backward resolution using strict matching only.
   No lifting, no flex-flex, no elimination premise solving.
4. ✅ **Conservative `subst_premise`** — prop equality only, lhs→rhs only,
   exact selected-subgoal match, no unification, no symmetric rewrite.
5. ✅ **Conservative `bicompose` design** — explicit major/minor roles, selected
   goal subgoal semantics, no full unification, no lifting/freshening, reviewed
   variable namespace policy.
6. **Historical conservative `bicompose` implementation** — the earlier thin
   alias is no longer exported; current callers use `resolve1_match`.
7. **Full `bicompose_eresolve` / ML elimination search** — deferred. The
   separate P1 `bicompose_candidate` checks finite elimination proposals but
   does not provide the proposed search/Seq interface.

Neither this wrapper sequence nor the newer candidate checker can be broadened
into ATP/HOL acceptance merely because a narrow sampled projection receives a
token. Other sampled HOL proofs, proof-runtime crate splitting (not the Cargo
workspace/xtask), APP, `isabelle.toml`, and AFP benchmarks remain separate
deferred work.

---

## 12. Attack Test Plans

Each resolution rule needs:

- Valid resolution: rule conclusion matches selected subgoal.
- Empty rule premises: subgoal is simply removed.
- Single subgoal: rule premises become the only new subgoals.
- Empty goal subgoals (m=0) → `SubgoalIndexOutOfRange` for any index.
- Subgoal index out of range → `SubgoalIndexOutOfRange`.
- Match failure between rule conclusion and subgoal → `ResolutionMatchFailure`.
- Hypothesis propagation: rule and goal hypotheses are unioned.
- Substitution applied to hypotheses as well as propositions.
- Tampered result: wrong subgoal count, wrong substitution → invariant failure.
- Round-trip: `bicompose` then `implies_intr` list → recovers original rule.
- Multiple independent resolutions produce consistent results.

Implemented `subst_premise` attack tests:

- `subst_premise_basic`
- `subst_premise_rejects_object_equality`
- `subst_premise_rejects_out_of_range`
- `subst_premise_rejects_mismatch`
- `subst_premise_rejects_symmetric_direction`
- `subst_premise_selected_index_is_goal_subgoal`
- `subst_premise_preserves_other_subgoals`
- `subst_premise_preserves_hypotheses`
- `subst_premise_invariant_check_passes`
- `subst_premise_tampered_result_rejected`

Current conservative resolution coverage is listed in
[Section 2A](#current-conservative-resolution-attack-tests). Historical
`bicompose_*` wrapper test names are not evidence for the current module tree.

---
