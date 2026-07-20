# Resolution / Bicompose Family — Design and Status

This is the **design and implementation-status document** for the strict-kernel
(`src/kernel/`) resolution family: `resolve1_match`, conservative
`subst_premise`, conservative `bicompose`, and future `bicompose_eresolve`.

**STATUS**: Conservative prototype. `KernelRules::resolve1_match`,
`KernelRules::subst_premise`, and `KernelRules::bicompose` are implemented with
invariant replay and attack tests. `bicompose` v1 is a thin wrapper around
`resolve1_match` and records the existing `Derivation::Resolve1Match`.
`resolve1_match`/`bicompose` use strict one-way matching and deterministic
substitutions; `subst_premise` is prop-equality only and fixed lhs -> rhs. Full
Isabelle-style `bicompose`, `bicompose_eresolve`, lifting, freshening,
flex-flex pairs, and higher-order unification remain design-phase.

This document does not set the repository's current priority.
`bicompose_eresolve`, lifting, freshening, and full unification remain deferred
until immutable theory/signature identity, context-bound acceptance, and the
first new-kernel `HOL::TrueI` loop are complete.

## Relationship to `KERNEL_PRIMITIVES.md`

`docs/KERNEL_PRIMITIVES.md` documents the 15 implemented base primitive rules with
their contracts. The resolution family is tracked here because it is more complex:
it requires premise selection, unification/matching, goal-state decomposition,
and hypothesis propagation under substitution.

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
implementations live in [`src/kernel/term.rs`](../src/kernel/term.rs). A
standalone API sketch for experimentation is maintained in
[resolution_api.rs](../scripts/templates/resolution_api.rs).

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

## 2A. Conservative `bicompose` First Version (Implemented Wrapper)

The first strict `bicompose` is implemented as a named, conservative
backward-resolution wrapper that reuses the already-tested `resolve1_match`
semantics. It does not copy legacy `ThmKernel::bicompose`, and it does not
introduce full unification, lifting/freshening, e-resolution, or premise
solving.

### Relationship To `resolve1_match`

`resolve1_match` is the current verified core:

```text
rule conclusion C  --strict one-way match-->  selected goal subgoal Gᵢ
rule premises replace Gᵢ
substitution applies to rule premises, remaining goal, and hypotheses
invariant replay recomputes the match and result proposition
```

Conservative `bicompose` v1 is a thin public/named wrapper around
`resolve1_match`.

It must not duplicate subgoal-splicing logic. `Term::replace_subgoal_with_premises`
remains the single ordering primitive for replacing a selected subgoal.

### Major / Minor Roles

The first API keeps roles explicit. The exact signature is owned by
[`KernelRules::bicompose`](../src/kernel/rules.rs); the standalone template uses
the same `rule`, `goal_state`, and `selected_subgoal_index` roles.

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

The first version should support only the subset already validated by
`resolve1_match`:

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

This means conservative `bicompose` v1 is not Isabelle's full `bicompose`.
It is a stable strict-kernel name for the current backward-resolution core.

### Variable Namespace Policy

The first version must not silently merge rule and goal namespaces.

Current `resolve1_match` / `bicompose` reject same-named Free collisions and
overlapping rule/goal schematic variable `(name, index)` pairs with
`RequiresLifting`.

The first implementation chooses rejection rather than proving that goal-side
Vars-as-concrete is sufficient. This may reject valid cases, but it keeps the
trusted rule from depending on unstated freshening semantics.

### Unsupported Cases

The first strict `bicompose` must reject or defer:

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

Conservative `bicompose` v1 does **not** add a `Derivation::Bicompose` node
carrying the two theorems, selected index, and substitution.

It intentionally records `Derivation::Resolve1Match` until the rule grows beyond
the existing core. Replay therefore remains the existing `Resolve1Match` replay:

1. recursively check `rule` and `goal_state`;
2. reselect the goal subgoal by `selected_subgoal_index`;
3. rederive the same strict match substitution;
4. reject if recorded `subst` differs from replay-derived `subst`;
5. rebuild the result via `replace_subgoal_with_premises`;
6. compare replayed theorem fields with stored theorem fields.

### Implemented Conservative `bicompose` Attack Tests

Implemented wrapper-level tests:

- `bicompose_basic_no_vars`
- `bicompose_basic_with_rule_var_match`
- `bicompose_rejects_match_failure`
- `bicompose_rejects_out_of_range`
- `bicompose_selected_index_is_goal_subgoal`
- `bicompose_replaces_selected_subgoal`
- `bicompose_applies_substitution_to_rule_premises`
- `bicompose_rejects_goal_remaining_subgoal_substitution_without_lifting`
- `bicompose_applies_substitution_to_hypotheses`
- `bicompose_rejects_free_collision_without_lifting`
- `bicompose_rejects_var_namespace_collision_without_lifting`
- `bicompose_allows_same_var_name_different_index_without_lifting`
- `bicompose_allows_non_overlapping_goal_side_var`
- `bicompose_invariant_check_passes`

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

Note: `bicompose_eresolve` is a higher-level operation that wraps `bicompose`
with premise solving. It remains deferred; stability of the wrapper alone is
not authorization to implement it before the trusted acceptance chain.

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
`src/kernel/rules.rs` and `tests/kernel_rewrite_soundness.rs`.

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
src/kernel/ MUST NOT depend on crate::core::unify
```

The legacy core has unification (`src/core/unify.rs`, `src/core/pattern.rs`),
but the strict kernel firewall forbids `use crate::core::...`.

### What the strict kernel needs

A strict matcher/unifier module (`src/kernel/unify.rs`) provides the raw matcher,
while `src/kernel/rules.rs` owns the certified-origin wrapper. Both remain
`pub(in crate::kernel)`; there is intentionally no public bare-`Term` to
`InstEntry` conversion. The reusable design skeleton is
[resolution_api.rs](../scripts/templates/resolution_api.rs).

### Implementation status

| Component | Status |
|---|---|
| `unify::match_terms` (raw matcher, `pub(in crate::kernel)`) | ✅ Implemented (`src/kernel/unify.rs`) |
| `MatchBinding` (raw binding, `pub(in crate::kernel)`) | ✅ Implemented |
| `CTerm::from_certified_subterm` (`pub(in crate::kernel)`) | ✅ Implemented |
| `KernelRules::match_terms_certified` (`pub(in crate::kernel)`) | ✅ Implemented |
| Public `Term → CTerm` API | ❌ Intentionally absent |
| Visibility: `src/core/` and upper-layer modules blocked | ✅ Enforced by `pub(in crate::kernel)` |
| Full unification (`unify_terms`) | ❌ Not started (deferred) |

The matcher is a **one-way structural matcher**, not full unification.
The file is named `src/kernel/unify.rs` because full unification will be
added there later, but the current implementation is matching-only.

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
these subterms and wraps them using a `pub(in crate::kernel)` constructor that
is NOT exposed outside `src/kernel/`. The authoritative contract and
implementation are in [`src/kernel/cterm.rs`](../src/kernel/cterm.rs). Its
constructor remains `pub(in crate::kernel)` and requires certified-subterm
origin; external code must use `ProofContext::certify_term`.

Key properties:

| Property | Guarantee |
|---|---|
| Visibility | `pub(in crate::kernel)` — only `src/kernel/` modules can call this |
| Certified-by-origin | Caller guarantees the term originated from a certified `CProp`/`KernelThm` |
| No dummy types | The certified term already passed `ProofContext` checks |
| Firewall integrity | `src/core/`, `src/isar/`, `src/tools/` and external crates blocked |

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
cross-theory matching), the `pub(in crate::kernel)` constructor can be
replaced by explicit context-passing without changing the matcher's API.

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
[`scripts/templates/resolution_api.rs`](../scripts/templates/resolution_api.rs).

**First version**: Do NOT implement lifting/freshening. However, the kernel
MUST NOT silently proceed when a collision would cause incorrect results.

Instead, `resolve1_match` and conservative `bicompose` must **detect** when the
rule and goal variable spaces collide in a way that requires lifting, and return
`KernelError::RequiresLifting` rather than proceeding. The authoritative error
definition is in [`src/kernel/mod.rs`](../src/kernel/mod.rs).

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
is [`ThmKernel::detect_collision`](../src/kernel/rules.rs); the corresponding
public-shape design template remains in
[`scripts/templates/resolution_api.rs`](../scripts/templates/resolution_api.rs).

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

The strict kernel currently has no `tpairs`. When full unification is added,
unresolved flex-flex pairs must become `tpairs` on the result theorem. This is
a deferred concern.

### Q5: Invariant Replay

Each resolution rule must have:
- A `Derivation` variant recording the inputs.
- An invariant replay path.
- Attack tests for tampered outputs.

### Q6: Error Types

Current reusable errors are `KernelError::SubgoalIndexOutOfRange` and
`KernelError::RequiresLifting`; their authoritative definitions are in
[`src/kernel/mod.rs`](../src/kernel/mod.rs). Rules with no premises are valid and
therefore do not require a separate error variant.

Current strict matching failures are propagated from `match_terms_certified`
as existing `KernelError` values (`TypeMismatch`, `BoundInSubstitution`, or
`Invariant` with a mismatch diagnostic). A later full `bicompose` may introduce
a narrower `ResolutionMatchFailure` error, but that should be a separate API
cleanup, not a blocker for the conservative design.

### Q7: `subst_premise` vs `bicompose` Ordering

**Recommendation**: conservative `bicompose` v1 now exists only as the reviewed
wrapper subset. Stabilize that wrapper and its variable namespace rejection
before designing full bicomposition or `bicompose_eresolve`. The minimal
`resolve1_match` prototype, conservative `subst_premise`, and conservative
`bicompose` wrapper do not replace full Isabelle-style bicomposition.

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
| `union_hyps` + substitution | ✅ Implemented for `resolve1_match` / `bicompose` | Applies substitution to rule and goal hyps before union |
| Strict matcher (`match_terms` + `match_terms_certified`) | ✅ Implemented | Internal (`pub(in crate::kernel)`) only; no public Term→CTerm API |
| `resolve1_match` | ✅ Prototype implemented | Conservative one-way backward resolution; shared subgoal-splicing helper; invariant replay covered; rejects Free and schematic Var namespace collisions |
| conservative `subst_premise` | ✅ Implemented | Prop equality only, lhs→rhs only, exact selected-subgoal match, no unification; invariant replay and attack tests covered |
| conservative `bicompose` | ✅ Implemented wrapper | Thin wrapper over `resolve1_match`; records `Derivation::Resolve1Match`; no separate replay path or `Derivation::Bicompose` in v1 |
| Full unification | Not started | Deferred |
| Lifting / freshening | Not started | Deferred (caller responsibility for v1) |
| `tpairs` / flex-flex | Not in strict kernel | Deferred |

---

## 11. Resolution-Family Implementation Order

1. ✅ **Implication-chain utilities** — `dest_imp_chain`, `mk_imp_chain`, `nprems`,
   `select_subgoal`, `replace_subgoal_with_premises`.
2. ✅ **Strict matcher** — `match_terms(pattern, target) -> Vec<InstEntry>`.
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
6. ✅ **Conservative `bicompose` implementation** — thin wrapper over
   `resolve1_match`; rejects Free and schematic Var namespace collisions.
7. **`bicompose_eresolve`** — deferred elimination resolution with premise
   solving.

Do not start item 7, workspace splitting, APP, `isabelle.toml`, or AFP
benchmarks before the repository's context-bound trusted theorem loop closes.

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

Implemented conservative `bicompose` wrapper attack tests:

- `bicompose_basic_no_vars`
- `bicompose_basic_with_rule_var_match`
- `bicompose_rejects_match_failure`
- `bicompose_rejects_out_of_range`
- `bicompose_selected_index_is_goal_subgoal`
- `bicompose_replaces_selected_subgoal`
- `bicompose_applies_substitution_to_rule_premises`
- `bicompose_rejects_goal_remaining_subgoal_substitution_without_lifting`
- `bicompose_applies_substitution_to_hypotheses`
- `bicompose_rejects_free_collision_without_lifting`
- `bicompose_rejects_var_namespace_collision_without_lifting`
- `bicompose_allows_same_var_name_different_index_without_lifting`
- `bicompose_allows_non_overlapping_goal_side_var`
- `bicompose_invariant_check_passes`

---
