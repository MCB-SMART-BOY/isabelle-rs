# Resolution / Bicompose Family — Design and Status

This is the **design and implementation-status document** for the strict-kernel
(`src/kernel/`) resolution family: `resolve1_match`, conservative
`subst_premise`, future `bicompose`, and future `bicompose_eresolve`.

**STATUS**: Conservative prototype. `KernelRules::resolve1_match` and
`KernelRules::subst_premise` are implemented with invariant replay and attack
tests. `resolve1_match` uses strict one-way matching and deterministic
substitutions. `subst_premise` is prop-equality only and fixed lhs -> rhs. Full
`bicompose`, `bicompose_eresolve`, lifting, freshening, flex-flex pairs, and
higher-order unification remain design-phase.

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

The strict kernel provides these utilities on `Term`:

```rust
/// Decompose a proposition into its implication-chain premises and conclusion.
///
/// `A ==> B ==> C` returns `([A, B], C)`.
/// `C` (no implication) returns `([], C)`.
fn dest_imp_chain(term: &Term) -> (Vec<Term>, Term);

/// Build an implication chain from premises and a conclusion.
///
/// `mk_imp_chain([A, B], C)` returns `A ==> B ==> C`.
/// `mk_imp_chain([], C)` returns `C`.
fn mk_imp_chain(prems: &[Term], conclusion: &Term) -> Term;

/// Count the premises of a goal state.
///
/// `nprems(A ==> B ==> C)` returns `2`.
/// `nprems(C)` returns `0`.
fn nprems(prop: &Term) -> usize;

/// Select the i-th subgoal (0-indexed) from a goal state.
///
/// `select_subgoal(A ==> B ==> C, 0)` returns `Some(A)`.
/// `select_subgoal(A ==> B ==> C, 1)` returns `Some(B)`.
/// `select_subgoal(A ==> B ==> C, 2)` returns `None` (it's the conclusion).
fn select_subgoal(prop: &Term, i: usize) -> Option<Term>;

/// Replace the i-th subgoal with a list of new premises.
///
/// `replace_subgoal_with_premises(A ==> C, 0, [P, Q])` returns `P ==> Q ==> C`.
/// `replace_subgoal_with_premises(A ==> C, 0, [])` returns `C` (subgoal solved).
fn replace_subgoal_with_premises(
    prop: &Term,
    i: usize,
    new_prems: &[Term],
) -> Result<Term, KernelError>;
```

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

## 2A. Conservative `bicompose` First Version (Design Only)

This section is design-only. Do **not** implement strict `bicompose` until this
contract and its attack-test matrix have been reviewed.

The first strict `bicompose` should be a named, conservative backward-resolution
rule that reuses the already-tested `resolve1_match` semantics. It should not
copy legacy `ThmKernel::bicompose`, and it should not introduce full
unification, lifting/freshening, e-resolution, or premise solving.

### Relationship To `resolve1_match`

`resolve1_match` is the current verified core:

```text
rule conclusion C  --strict one-way match-->  selected goal subgoal Gᵢ
rule premises replace Gᵢ
substitution applies to rule premises, remaining goal, and hypotheses
invariant replay recomputes the match and result proposition
```

Conservative `bicompose` v1 should either:

- be a thin public/named wrapper around `resolve1_match`; or
- share the same internal helper used by `resolve1_match`.

It must not duplicate subgoal-splicing logic. `Term::replace_subgoal_with_premises`
remains the single ordering primitive for replacing a selected subgoal.

### Major / Minor Roles

The first API should keep roles explicit:

```rust
KernelRules::bicompose(
    rule: &KernelThm,       // major theorem: A1 ==> ... ==> An ==> C
    goal_state: &KernelThm, // minor theorem: G1 ==> ... ==> Gi ==> ... ==> R
    selected_subgoal_index: usize,
) -> Result<KernelThm, KernelError>
```

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

Current `resolve1_match` rejects same-named Free collisions with
`RequiresLifting`. Before conservative `bicompose` is implemented, the design
must choose one of these two gates for schematic Vars:

- Reject overlapping rule/goal schematic variable `(name, index)` pairs with
  `RequiresLifting`.
- Prove and document that the one-way matcher treats goal-side Vars as concrete
  strongly enough that no namespace merge occurs.

The safer first implementation choice is rejection. It may reject valid cases,
but it keeps the trusted rule from depending on unstated freshening semantics.

### Unsupported Cases

The first strict `bicompose` must reject or defer:

```text
goal has no selectable subgoal
rule/goal Free collision requiring lifting
rule/goal Var namespace collision unless explicitly proven safe
match failure between rule conclusion and selected subgoal
full unification requirement
flex-flex pairs / tpairs
elimination premise solving
conclusion-resolution
legacy compatibility alpha-equivalence
```

### Derivation Replay Strategy

If implemented as a distinct rule, add:

```rust
Derivation::Bicompose {
    rule: Box<KernelThm>,
    goal_state: Box<KernelThm>,
    selected_subgoal_index: usize,
    subst: Vec<InstEntry>,
}
```

Replay must:

1. recursively check `rule` and `goal_state`;
2. reselect the goal subgoal by `selected_subgoal_index`;
3. rederive the same strict match substitution;
4. reject if recorded `subst` differs from replay-derived `subst`;
5. rebuild the result via `replace_subgoal_with_premises`;
6. compare replayed theorem fields with stored theorem fields.

If implemented as a wrapper around `resolve1_match` without a new derivation
variant, document that it intentionally records `Derivation::Resolve1Match`
until the rule grows beyond the existing core.

### Planned Conservative `bicompose` Attack Tests

Add these tests before or with implementation:

- `bicompose_basic_no_vars`
- `bicompose_basic_with_rule_var_match`
- `bicompose_rejects_match_failure`
- `bicompose_rejects_out_of_range`
- `bicompose_rejects_empty_goal_subgoals`
- `bicompose_selected_index_is_goal_subgoal`
- `bicompose_replaces_selected_subgoal`
- `bicompose_preserves_other_subgoals`
- `bicompose_applies_substitution_to_rule_premises`
- `bicompose_applies_substitution_to_goal_remaining_subgoals`
- `bicompose_applies_substitution_to_hypotheses`
- `bicompose_rejects_free_collision_without_lifting`
- `bicompose_rejects_or_documents_var_namespace_collision`
- `bicompose_invariant_check_passes`
- `bicompose_tampered_result_rejected`

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
with premise solving. It should be implemented after `bicompose` is stable.

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

A strict matcher/unifier module (`src/kernel/unify.rs`) providing:

```rust
// ── Internal (pub(in crate::kernel)) API ──

/// Raw structural matcher (in `src/kernel/unify.rs`).
/// Returns `MatchBinding` with bare `Term` replacements — NOT CTerm.
/// Only `src/kernel/` modules may call this.
pub(in crate::kernel) fn match_terms(pattern: &Term, target: &Term)
    -> Result<Vec<MatchBinding>, KernelError>;

/// Certified-origin wrapper (in `KernelRules`, pub(in crate::kernel)).
/// Wraps raw MatchBinding into InstEntry via CTerm::from_certified_subterm.
/// Caller guarantees pattern and target are subterms of certified CProp/KernelThm.
/// Legacy `src/core/` and upper-layer modules CANNOT call this.
pub(in crate::kernel) fn match_terms_certified(pattern: &Term, target: &Term)
    -> Result<Vec<InstEntry>, KernelError>;

// ── There is intentionally NO public API that accepts bare &Term ──
// ── and returns InstEntry. External code must use ProofContext.    ──
```

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

```rust
// InstEntry requires:
replacement: CTerm   // ← must be certified (type-checked, no dummy types)
```

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
is NOT exposed outside `src/kernel/`:

```rust
// In src/kernel/cterm.rs — pub(in crate::kernel), NOT pub:
impl CTerm {
    /// Wrap a term that is known to originate from a certified CProp.
    ///
    /// # Contract (caller MUST guarantee)
    ///
    /// 1. The term is a subterm of a previously certified `CProp`.
    /// 2. The term contains no `Ty::Dummy`.
    /// 3. The term contains no unbound de Bruijn indices.
    /// 4. The term's constants are declared in the active `Signature`.
    ///
    /// This constructor is `pub(in crate::kernel)` — only `src/kernel/`
    /// modules can call it. External code and upper-layer modules MUST
    /// use `ProofContext::certify_term` instead.
    pub(in crate::kernel) fn from_certified_subterm(term: Term) -> Self {
        CTerm { term }
    }
}
```

Key properties:

| Property | Guarantee |
|---|---|
| Visibility | `pub(in crate::kernel)` — only `src/kernel/` modules can call this |
| Certified-by-origin | Caller guarantees the term originated from a certified `CProp`/`KernelThm` |
| No dummy types | The certified term already passed `ProofContext` checks |
| Firewall integrity | `src/core/`, `src/isar/`, `src/tools/` and external crates blocked |

#### Alternative (rejected): pass `ProofContext` to the matcher

An alternative is to pass `ProofContext` directly to `match_terms`:

```rust
fn match_terms(
    ctx: &ProofContext,
    pattern: &Term,
    target: &Term,
) -> Result<Vec<InstEntry>, KernelError>;
```

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
Lifting handles this:

```rust
/// Lift a rule theorem to avoid variable capture with the goal.
///
/// Increments Bound indices and freshens free variables so that the rule
/// can be safely combined with a goal.
fn lift_rule(rule: &KernelThm, goal: &KernelThm) -> KernelThm;
```

**First version**: Do NOT implement lifting/freshening. However, the kernel
MUST NOT silently proceed when a collision would cause incorrect results.

Instead, `resolve1_match` (and later `bicompose`) must **detect** when the rule
and goal variable spaces collide in a way that requires lifting, and return an
explicit error rather than proceeding:

```rust
#[error("variable collision between rule and goal requires lifting: \
         rule has {rule_var:?}, goal has {goal_var:?}")]
RequiresLifting { rule_var: Name, goal_var: Name },
```

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

Current `resolve1_match` scans the rule and goal for overlapping Free names:

```rust
fn detect_collision(rule: &KernelThm, goal: &KernelThm) -> Result<(), KernelError> {
    let rule_frees: HashSet<Name> = rule.prop().free_names();
    let goal_frees: HashSet<Name> = goal.prop().free_names();
    if !rule_frees.is_disjoint(&goal_frees) {
        return Err(KernelError::RequiresLifting { ... });
    }
    Ok(())
}
```

This is deliberately conservative: it may reject valid cases, but it will
never silently produce a wrong theorem. As lifting is implemented, the
rejection set shrinks.

For conservative `bicompose`, Var namespace policy is an explicit
pre-implementation gate. Either reject overlapping rule/goal schematic variable
`(name, index)` pairs, or document why the one-way matcher treats goal-side Vars
as concrete strongly enough that no namespace merge occurs.

#### Test requirement

```text
resolve1_rejects_variable_collision_without_lifting
```

This test constructs a rule and goal with overlapping free variable names
and asserts that `resolve1_match` returns `Err(RequiresLifting)` rather
than silently producing an incorrect theorem.

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

Current reusable errors:

```rust
enum KernelError {
    // ... existing ...
    /// The selected subgoal index is out of range for the goal state.
    SubgoalIndexOutOfRange { index: usize, nprems: usize },
    /// Variable collision between rule and goal requires lifting/freshening.
    /// First-version resolve1_match does not implement lifting; it returns this
    /// error instead of silently proceeding with incorrect substitution.
    RequiresLifting { rule_var: Name, goal_var: Name },
    /// The rule conclusion is not an implication chain (has no premises to replace with).
    // (This is actually not an error — rules with 0 premises are fine.)
}
```

Current strict matching failures are propagated from `match_terms_certified`
as existing `KernelError` values (`TypeMismatch`, `BoundInSubstitution`, or
`Invariant` with a mismatch diagnostic). A later full `bicompose` may introduce
a narrower `ResolutionMatchFailure` error, but that should be a separate API
cleanup, not a blocker for the conservative design.

### Q7: `subst_premise` vs `bicompose` Ordering

**Recommendation**: design conservative `bicompose` first, review the variable
namespace policy, then implement only the reviewed subset. Full
`bicompose_eresolve` comes after conservative `bicompose` is stable. The minimal
`resolve1_match` prototype and conservative `subst_premise` now exist, but they
do not replace full bicomposition.

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
| `union_hyps` + substitution | ✅ Implemented for `resolve1_match` | Applies substitution to rule and goal hyps before union |
| Strict matcher (`match_terms` + `match_terms_certified`) | ✅ Implemented | Internal (`pub(in crate::kernel)`) only; no public Term→CTerm API |
| `resolve1_match` | ✅ Prototype implemented | Conservative one-way backward resolution; shared subgoal-splicing helper; invariant replay covered |
| conservative `subst_premise` | ✅ Implemented | Prop equality only, lhs→rhs only, exact selected-subgoal match, no unification; invariant replay and attack tests covered |
| conservative `bicompose` | Design only | Should reuse/wrap `resolve1_match`; variable namespace policy must be reviewed before implementation |
| Full unification | Not started | Deferred |
| Lifting / freshening | Not started | Deferred (caller responsibility for v1) |
| `tpairs` / flex-flex | Not in strict kernel | Deferred |

---

## 11. Recommended Implementation Order

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
5. **Conservative `bicompose` design** — explicit major/minor roles, selected
   goal subgoal semantics, no full unification, no lifting/freshening, reviewed
   variable namespace policy.
6. **Conservative `bicompose` implementation** — only after design review; must
   reuse/wrap the same core semantics as `resolve1_match`.
7. **`bicompose_eresolve`** — elimination resolution with premise solving.

Do NOT start workspace splitting, APP, `isabelle.toml`, or AFP benchmarks
before the resolution-family prototype has a stable compatibility matrix and
clear limits.

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

Planned conservative `bicompose` attack tests:

- `bicompose_basic_no_vars`
- `bicompose_basic_with_rule_var_match`
- `bicompose_rejects_match_failure`
- `bicompose_rejects_out_of_range`
- `bicompose_rejects_empty_goal_subgoals`
- `bicompose_selected_index_is_goal_subgoal`
- `bicompose_replaces_selected_subgoal`
- `bicompose_preserves_other_subgoals`
- `bicompose_applies_substitution_to_rule_premises`
- `bicompose_applies_substitution_to_goal_remaining_subgoals`
- `bicompose_applies_substitution_to_hypotheses`
- `bicompose_rejects_free_collision_without_lifting`
- `bicompose_rejects_or_documents_var_namespace_collision`
- `bicompose_invariant_check_passes`
- `bicompose_tampered_result_rejected`

---
