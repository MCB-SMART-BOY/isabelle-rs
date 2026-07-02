# Strict Kernel Primitive Contracts

This document describes the first `src/kernel/` nucleus rules. It is a contract
for the new TCB, not a description of the legacy `src/core` implementation.

## Global Invariants

- There is no dummy type in the strict kernel type language.
- Constants must be declared in `Signature`.
- Local frees must be declared in `ProofContext`.
- `CTerm` and `CProp` are produced only by strict certification.
- Theorem fields are private.
- Theorem values are produced only by `KernelRules`.
- `ProofObligation` is not a theorem.
- `ClosedThm` is a wrapper for theorems with no hypotheses.
- `TrustedTheorem` is a checked `ClosedThm`.
- `TrustedTheory` accepts only `TrustedTheorem`.
- `SearchFactDb` facts are not trusted theorem-table entries.

## `assume`

```text
input:  A : CProp
output: OpenThm, A |- A
```

Side conditions:

- `A` must be a certified proposition.

Result:

- hypothesis set is `{A}`;
- proposition is `A`;
- the theorem is open and cannot become a `ClosedThm`.

## `reflexive`

```text
input:  t : CTerm
output: ClosedThm, |- t == t
```

Side conditions:

- `t` must be certified.
- the object type of both sides is exactly `type_of(t)`.

Result:

- no hypotheses;
- eligible for `TrustedTheorem` after invariant replay.

## `symmetric`

```text
input:  Γ |- t == u
output: Γ |- u == t
```

Side conditions:

- premise proposition must be equality.

Propagation:

- hypotheses are preserved.

## `transitive`

```text
input:  Γ |- t == u
        Δ |- u == v
output: Γ ∪ Δ |- t == v
```

Side conditions:

- both premises must be equality propositions;
- equality object types must be identical;
- middle terms must be strict alpha-equivalent;
- Free/Const and Var/Free compatibility are rejected.

Propagation:

- hypotheses are unioned modulo strict alpha-equivalence.

## `implies_intr`

```text
input:  Γ ∪ {A} |- B
output: Γ |- A ==> B
```

Side conditions:

- `A` must occur in the theorem hypotheses modulo strict alpha-equivalence.

Propagation:

- exactly one matching hypothesis is discharged.

## `implies_elim`

```text
input:  Γ |- A ==> B
        Δ |- A
output: Γ ∪ Δ |- B
```

Side conditions:

- major premise proposition must be implication;
- minor conclusion must be strict alpha-equivalent to the antecedent.

Propagation:

- hypotheses are unioned modulo strict alpha-equivalence.

## `beta_conversion`

```text
input:  redex : CTerm, shape ((λx:τ. body) arg)
output: ClosedThm, |- ((λx:τ. body) arg) == body[arg/x]
```

Side conditions:

- `redex` term must be an `App` whose `func` is an `Abs`.
- `arg` type must match the binder parameter type `τ`.
- Bound substitution is strict de Bruijn `instantiate_bound0(body, arg)`.

Result:

- no hypotheses;
- eligible for `TrustedTheorem` after invariant replay.

Attack tests cover:

- identity reduction: `(λx:nat. x) a ≡ a`;
- non-application CTerm rejected;
- non-lambda `App` (Const function) rejected;
- inner bound variables preserved under substitution;
- invariant check passes on valid output;
- closed theorem trust path works;
- function application substitution `(λx:nat. f x) a ≡ f a`;
- nested lambda capture avoidance: `(λx:nat. (λy:nat. x)) a ≡ (λy:nat. a)`;
- argument with bound variable lifted correctly: `(λf. f a) (λx. x) ≡ (λx. x) a`;
- triple-nested lambda substitution;
- invariant replay catches tampered proposition;
- invariant replay catches tampered hypotheses.

## `forall_intr`

```text
input:  variable : CTerm, free variable x : τ
        theorem  : Γ |- P
output: Γ |- ⋀x:τ. P[x → Bound(0)]
```

Side conditions:

- `variable` must be a `Free` term (Var not yet supported);
- `x` must not occur free in any hypothesis in Γ.
- The free variable is abstracted from the conclusion using de Bruijn
  abstraction: every `Free(x, τ)` becomes `Bound(depth, τ)` where `depth`
  counts enclosing Abs/Forall binders. Existing `Bound` indices are unchanged.

Propagation:

- hypotheses are preserved.

Attack tests cover:

- generalises free variable in conclusion: `|- (x == a) ⇒ (x == a)` → `|- ⋀x. ((x == a) ⇒ (x == a))`;
- rejects variable with same name free in hypotheses;
- rejects non-Free variable (Const, App, Abs);
- produces closed theorem from closed input;
- invariant check passes on valid output;
- hypotheses are preserved through generalisation.

## `forall_elim`

```text
input:  Γ |- ⋀x:τ. P(x)
        t : CTerm with type τ
output: Γ |- P(t)
```

Side conditions:

- Theorem proposition must be a `Forall` (⋀x:τ. body).
- Argument type must exactly match the binder parameter type τ.
- Substitution uses strict de Bruijn `instantiate_bound0(body, arg)` — the
  inverse of the `abstract_over` used in `forall_intr`.

Propagation:

- Hypotheses are preserved.

Attack tests cover:

- instantiates bound variable correctly: `⋀x:nat. (x==a)⇒(x==a)` with `a` → `(a==a)⇒(a==a)`;
- rejects non-Forall input with `NotForall`;
- rejects binder/argument type mismatch with `ForallBinderMismatch`;
- preserves hypotheses through elimination;
- invariant check passes on valid output;
- nested Forall: eliminates only the outermost binder, preserves inner structure;
- `forall_intr`/`forall_elim` round-trip: `forall_elim(forall_intr(thm), x) ≡ thm`;
- invariant replay catches tampered proposition (unreduced forall body).

Substitution-depth stress tests cover:

- `forall_elim` does not replace `Bound(1)` when eliminating the outer binder;
- multiple `Bound(0)` occurrences all replaced;
- consecutive nested forall elimination (outer then inner);
- `forall_elim` with `Abs` argument substitutes correctly;
- `beta_conversion` then `forall_elim` without de Bruijn interference.

## `combination`

```text
input:  Γ |- f == g       (f, g : τ → σ)
        Δ |- x == y       (x, y : τ)
output: Γ ∪ Δ |- f x == g y
```

Side conditions:

- Both premises must be equality propositions.
- `f` and `g` must be function types; the equality object type `τ → σ` is
  destructured via `dest_arrow` to extract domain `τ` and codomain `σ`.
- The argument equality object type must match the function domain exactly.
- The result application terms `f x` and `g y` share the codomain `σ`.

Propagation:

- Hypotheses are unioned modulo strict alpha-equivalence.

Attack tests cover:

- basic function-congruence application: `f == g`, `a == b` → `f a == g b`;
- rejects non-equality function premise with `NotEquality`;
- rejects non-equality argument premise with `NotEquality`;
- rejects non-function `f`/`g` with `NotFunctionType`;
- rejects domain/argument type mismatch with `TypeMismatch`;
- preserves open hypotheses through union;
- invariant check passes on valid output;
- invariant replay catches tampered proposition (swapped argument order);
- composition with `reflexive` produces closed theorem.

## `abstraction`

```text
input:  Γ |- t == u              (t, u : β)
        variable name x, type α
output: Γ |- (λx:α. t[x→Bound(0)]) == (λx:α. u[x→Bound(0)])   (λx..., λx... : α → β)
```

Side conditions:

- Premise proposition must be equality.
- `x` must not be free in any hypothesis in Γ.

Propagation:

- Hypotheses are preserved.
- `t` and `u` are abstracted via `Term::abstract_over`:
  every `Free(x, α)` in the body is replaced with `Bound(0, α)`,
  while `Free(v, _)` for `v ≠ x` are left unchanged.

Attack tests cover:

- basic lambda introduction: `a==b ⊢ (λx. a)==(λx. b)`;
- rejects abstraction when `x` is free in hypotheses;
- preserves hypotheses through abstraction;
- rejects non-equality premise with `NotEquality`;
- invariant check passes on valid output;
- produces closed theorem from closed input;
- nested abstraction preserves binder structure;
- composes with `forall_elim` + `combination` + `abstraction`;
- invariant replay catches tampered proposition (wrong binder name);
- `Free(x)` replaced by `Bound(0)` in body (critical binding-correctness);
- only target variable abstracted — other `Free`s preserved;
- `Free(x)` replaced within application terms.

## `equal_intr`

```text
input:  Γ |- A ==> B
        Δ |- B ==> A
output: Γ ∪ Δ |- A == B
```

Side conditions:

- Both premises must be implication propositions.
- The antecedent of the first must be strict alpha-equivalent to the
  consequent of the second (`A == A`), and vice versa (`B == B`).

Propagation:

- Hypotheses are unioned modulo strict alpha-equivalence.

Attack tests cover:

- mutual implications `A==>B, B==>A` yield `A==B`;
- rejects non-implication left premise with `NotImplication`;
- rejects non-implication right premise with `NotImplication`;
- rejects mismatched pairs with `AntecedentMismatch`;
- preserves distinct open hypotheses through union;
- round-trip with `equal_elim`: `equal_elim(equal_intr(…), A) → B`;
- invariant replay catches tampered proposition.

## `equal_elim`

```text
input:  Γ |- A == B
        Δ |- A
output: Γ ∪ Δ |- B
```

Side conditions:

- Major premise must be an equality proposition.
- The equality must be **propositional**: `A == B` where `A, B : prop`.
  Object equality (`x == y` where `x, y : nat`) is rejected with
  `NotProposition`.
- Minor premise must be strict alpha-equivalent to the left-hand side `A`.

Propagation:

- Hypotheses are unioned modulo strict alpha-equivalence.

Attack tests cover:

- `A==B, A ⊢ B` elimination;
- rejects non-equality major premise with `NotEquality`;
- rejects object equality with `NotProposition`;
- rejects minor-premise mismatch with `AntecedentMismatch`;
- round-trip: `equal_elim(equal_intr(A==>B, B==>A), A) → B`;
- preserves open minor hypothesis through union;
- invariant replay catches tampered proposition.

## First Attack-Test Set

The independent test file `tests/kernel_rewrite_soundness.rs` covers:

- undeclared constants rejected;
- undeclared frees rejected;
- dummy type construction rejected;
- ill-typed application rejected;
- Free/Const middle-term mismatch rejected;
- Var/Free middle-term mismatch rejected;
- `assume(A)` creates an open theorem;
- `reflexive(t)` creates a closed trusted theorem;
- implication introduction discharges hypotheses;
- implication elimination requires exact antecedent;
- transitivity requires typed middle equality;
- beta conversion reduces identity applications;
- beta conversion rejects non-lambda applications;
- beta conversion preserves inner bound variables;
- beta conversion produces closed trusted theorems;
- beta conversion substitution is correct;
- beta conversion nested lambda capture avoidance;
- beta conversion argument bound lift;
- beta conversion triple nested substitution;
- `forall_intr` generalises a free variable in the conclusion;
- `forall_intr` rejects a variable free in hypotheses;
- `forall_intr` rejects non-Free terms;
- `forall_intr` produces closed theorems from closed input;
- `forall_elim` instantiates bound variable with matching argument;
- `forall_elim` rejects non-Forall input;
- `forall_elim` rejects binder/argument type mismatch;
- `forall_elim` preserves hypotheses;
- `forall_elim` handles nested Forall (outer-only elimination);
- `forall_intr`/`forall_elim` round-trips;
- `combination` basic function-congruence;
- `combination` rejects non-equality premises;
- `combination` rejects non-function `f`/`g`;
- `combination` rejects domain/argument type mismatch;
- `combination` preserves open hypotheses;
- `combination` invariant passes and catches tampering;
- `combination` composes with `reflexive` for closed theorems;
- `abstraction` introduces lambda binders on both sides of equality;
- `abstraction` rejects `x` free in hypotheses;
- `abstraction` preserves hypotheses;
- `abstraction` rejects non-equality premise;
- `abstraction` invariant passes and catches tampering;
- `abstraction` produces closed theorem from closed input;
- `abstraction` nested supports two binders;
- `abstraction` composes with `forall_elim` + `combination`;
- `abstraction` replaces `Free(x)` with `Bound(0)` (binding semantics);
- `abstraction` only abstracts target variable — other Frees preserved;
- `abstraction` replaces `Free(x)` within application terms;
- `equal_intr` mutual implications yield equality;
- `equal_intr` rejects non-implication premises;
- `equal_intr` rejects mismatched implication pairs;
- `equal_intr` preserves hypotheses;
- `equal_intr`/`equal_elim` round-trip;
- `equal_elim` A==B, A → B;
- `equal_elim` rejects non-equality major premise;
- `equal_elim` rejects minor mismatch;
- `equal_elim` preserves open minor hypotheses;
- `equal_elim` rejects object (non-prop) equality;
- `ProofObligation` is not a theorem;
- `SearchFact` cannot become `TrustedTheorem`;
- `generalize` basic free→var transformation;
- `generalize` preserves hypotheses;
- `generalize` multiple frees → distinct incrementing Var indices;
- `generalize` ignores non-free/const/bound terms;
- `generalize` only targeted frees replaced;
- `generalize` closed/open theorem status preserved;
- `generalize` invariant check passes;
- `generalize` empty frees no-op;
- `generalize` ignores unmatched frees;
- `generalize` avoids existing Var index collision;
- `generalize` uses global max Var index (not per-name);
- `generalize` type-sensitive matching;
- `generalize` round-trip records derivation for future instantiate;
- `instantiate` basic Var→Term replacement;
- `instantiate` rejects type mismatch;
- `instantiate` respects Var index (Var(x,0) ≠ Var(x,1));
- `instantiate` type-sensitive name+index matching;
- `instantiate` rejects duplicate (name,idx) entries;
- `instantiate` rejects Bound in replacement;
- `instantiate` partial substitution keeps unmatched Vars;
- `instantiate` preserves hypotheses;
- `instantiate` invariant check passes;
- `instantiate` closed theorem stays closed;
- `instantiate` does not affect Const/Free nodes;
- `instantiate` empty subst is identity;
- `instantiate` multiple Vars with different replacements;
- `instantiate` all occurrences of same Var replaced;
- `instantiate` round-trip with generalize.

## `generalize` (Free → Schematic Var)

```text
input:  Γ |- P
        frees: [(name₁, τ₁), ..., (nameₙ, τₙ)]
output: Γσ |- Pσ
        where each Free(nameᵢ, τᵢ) in Γ or P is replaced by
        Var(nameᵢ, start + i, τᵢ), with:
            start = 1 + max existing Var index in Γ and P
            (or start = 0 if no Var present)
```

Design decisions:

- **Direction**: `Free → Var` (schematic variable generalisation), **not** `Free → Forall`.
  `forall_intr` already handles universal quantifier introduction.
  `generalize` turns concrete fixed variables into schematic variables, making the
  theorem applicable to any term of the same type when later instantiated.
- **Fresh index start**: Generated Var indices must **avoid collision** with any
  `Var` already present in the theorem. The start index is
  `max_existing_var_index(thm) + 1`. If no Var exists, start = 0.
- **Unmatched frees**: Ignored as a no-op. If the input list names a free
  variable not present in the theorem, it is silently skipped. This is not an
  error — it is the caller's responsibility to provide a meaningful list.
- **Scope**: Replaces in both hypotheses and proposition.
- **No capture concern**: Free→Var does not introduce Bound indices; the
  transformation is purely a tag change on the variable node.

### Implementation plan

1. Add `Term::max_var_index(&self) -> Option<usize>` in `term.rs` — scans for
   the highest Var index in the term tree.
2. Compute `start = thm.max_var_index().map(|m| m + 1).unwrap_or(0)`.
3. Add `Term::generalize_to_vars(&self, frees: &[(Name, Ty)], start: usize) -> Term`
   in `term.rs`. When `Free(name, ty)` matches entry `i`, replaces with
   `Var(name, start + i, ty)`.
4. `KernelRules::generalize(thm, frees)` applies to hyps and prop, preserves
   derivation via `Derivation::Generalize`.

### Contract

Side conditions:
- Unmatched frees are silently ignored (no-op).
- No dummy type in frees or theorem.
- Only `Free → Var` transformation (not `Var → Var` or `Const → Var`).

Propagation:
- Hypotheses are transformed in-place (same count).
- The theorem remains open/closed as before.
- No new error variants needed (generalize cannot fail).

## `instantiate` (Schematic Var → Certified Term)

```text
input:  Γ |- P
        subst: [InstEntry{name₁, idx₁, τ₁, replacement₁}, ...]
output: Γσ |- Pσ
        where each Var(nameᵢ, idxᵢ, τᵢ) in Γ or P is replaced by replacementᵢ
```

### Trust boundary

Every replacement must be a certified `CTerm`, passed via `InstEntry`:
`InstEntry { name, index, var_ty, replacement: CTerm }`. This enforces the
kernel certification boundary:

```text
RawTerm → Signature/ProofContext certification → CTerm → InstEntry → KernelRules::instantiate
```

Bare `Term` values cannot be passed as replacements.

### Design decisions

- **Direction**: `Var → Certified Term` (schematic variable instantiation).
  Inverse of `generalize`: generalise then instantiate with the original term
  should round-trip.
- **Exact match**: Var matching is on **all three** of `(name, index, type)`.
  `Var("x", 0, nat)` ≠ `Var("x", 1, nat)` ≠ `Var("x", 0, bool)`.
- **Duplicate detection is keyed by `(name, index)` only** — two entries with
  the same `(name, idx)` but different `var_ty` are still rejected as
  `DuplicateSubstitution`. The type field does not participate in duplicate
  detection because the same schematic variable cannot have two different types.
- **Partial substitution**: Unmatched Vars remain unchanged. Valid if the
  theorem contains Vars not listed in the substitution.
- **Type check (defense-in-depth)**: `replacement.ty() == var_ty` for every
  entry. While `InstEntry` construction should preserve this invariant, the
  kernel performs a runtime check.
- **Simultaneous substitution**: The replacement is a single-pass traversal
  over the original theorem. Var nodes inside replacement terms are NOT
  substituted even if they match another entry. Substitution order does not
  matter — the result is deterministic and independent of entry ordering.
- **No capture (initial)**: Replacements must be **closed** — no `Bound`
  indices. The certification boundary prevents Bound from entering via
  `ProofContext::certify_term`. An internal defense-in-depth check
  (`BoundInSubstitution`) remains in `KernelRules::instantiate`.
- **Scope**: Replaces in both hypotheses and proposition.

### Implementation plan

1. `InstEntry { name, index, var_ty, replacement: CTerm }` — typed substitution
   entry enforcing the certification boundary at the Rust type level.
2. `Term::instantiate_vars(&self, subst: &[InstEntry]) -> Term` — iterative
   continuation-frame traversal replacing `Var(name, idx, ty)` with
   `entry.replacement.term().clone()` when all three fields match.
3. `KernelRules::instantiate(thm, subst)` validates duplicates (keyed by
   name+index), type-checks each replacement, rejects Bound, then applies to
   hyps and prop, constructing `Derivation::Instantiate`.

### Contract

Side conditions:
- Every replacement is a certified `CTerm` (enforced by `InstEntry` type).
- `replacement.ty() == var_ty` for every entry (type match) → `TypeMismatch`.
- No duplicate `(name, idx)` entries → `DuplicateSubstitution`.
- No `Bound` in any replacement → `BoundInSubstitution`.
- No dummy type in replacements (enforced by CTerm certification).
- Partial substitution is valid: unmatched `Var`s remain unchanged.

Propagation:
- Hypotheses are transformed in-place.
- The theorem remains open/closed as before.

### Round-trip guarantee

```text
generalize(thm, [(name, ty)]), then instantiate(result, [(name, start, ty, original_cterm)])
  ≡ thm  (modulo hyps reshuffling due to α-equivalence)
```

Note: the instantiate step must use the same `start` index that generalize
produced. The round-trip test must capture this dynamically.

And:

```text
instantiate(thm, subst), then generalize(result, ...)
  is NOT guaranteed to round-trip, because instantiate may replace Vars
  with terms that contain Frees different from the original schematic
  representation.
```

## Attack Tests (generalize) — ✅ Implemented

| Test | What it checks |
|------|----------------|
| `generalize_basic` | Free(nat) → Var(start, nat) in closed reflexive theorem |
| `generalize_preserves_hypotheses` | Hypotheses are transformed alongside prop |
| `generalize_multiple_frees` | Frees get distinct incrementing Var indices |
| `generalize_non_free_unchanged` | Const and Bound nodes unchanged |
| `generalize_only_target_free` | Only named frees replaced; different-name frees preserved |
| `generalize_closed_remains_closed` | Closed theorem stays closed |
| `generalize_open_remains_open` | Open theorem stays open |
| `generalize_invariant_check_passes` | check_kernel_thm succeeds |
| `generalize_empty_frees_noop` | Empty free list = identity |
| `generalize_ignores_unmatched_free` | Free in list but not in theorem → no-op |
| `generalize_avoids_existing_var_index` | Theorem has Var(x,0); generalize Free(y) → Var(y,1) |
| `generalize_type_sensitive_same_name` | Free(x,nat) generalized, Free(x,bool) not |
| `generalize_roundtrip_with_instantiate` | generalize then instantiate = original |
| `generalize_tampered_prop_fails_invariant` | Wrong Var index |

## Attack Tests (instantiate) — ✅ Implemented (18 total)

| Test | What it checks |
|------|----------------|
| `instantiate_basic` | Var(name,idx,τ) → Certified Term, matching type |
| `instantiate_rejects_type_mismatch` | Var(nat) := prop_term → TypeMismatch |
| `instantiate_respects_index` | Var(x,0) and Var(x,1) not confused |
| `instantiate_rejects_duplicate_substitution` | Same (name,idx) twice → DuplicateSubstitution |
| `instantiate_rejects_duplicate_same_name_index_different_type` | Duplicate keyed by (name,idx) regardless of type |
| `instantiate_rejects_bound_in_replacement` | CTerm certification prevents Bound; defense-in-depth check tested inline |
| `instantiate_is_simultaneous_not_sequential` | Single-pass traversal; order-independent result |
| `instantiate_type_sensitive_same_name_index` | Var(x,0,nat) not matched by prop term |
| `instantiate_multiple_vars` | Multiple different Vars with different replacements |
| `instantiate_partial_substitution_keeps_unmatched_var` | Var not in subst remains as-is |
| `instantiate_same_var_all_occurrences` | All occurrences of same Var replaced |
| `instantiate_preserves_hypotheses` | Hyps Vars also instantiated |
| `instantiate_invariant_check_passes` | check_kernel_thm succeeds |
| `instantiate_closed_remains_closed` | Closed theorem stays closed |
| `instantiate_does_not_affect_const_or_free` | Only Vars replaced |
| `instantiate_empty_subst_noop` | Empty subst = identity |
| `instantiate_roundtrip_with_generalize` | generalize→instantiate = original |
| `instantiate_invariant_catches_tampered_result` | Tampered result caught by invariant (inline test) |

---

# Resolution / Bicompose Family

**Design tracked in [docs/RESOLUTION_DESIGN.md](RESOLUTION_DESIGN.md).**

The resolution family (`bicompose`, `bicompose_eresolve`, `subst_premise`) is
more complex than the base primitive rules and requires careful design before
implementation. See that document for:

- Corrected `bicompose` contract (rule conclusion matches goal subgoal, not
  rule premise matches goal).
- Goal state as implication chain.
- Strict matcher/unifier requirements and the firewall rule
  (`src/kernel/` MUST NOT depend on `crate::core::unify`).
- Current implementation order/status: implication-chain utilities → strict
  matcher → `resolve1_match` prototype → conservative `subst_premise` are
  implemented; full `bicompose` and `bicompose_eresolve` remain future work.
- Open design questions (9 items).
- Attack test plans.

**Current status**: Conservative prototype. Implication-chain utilities
(`dest_imp_chain`, `mk_imp_chain`, `nprems`, `select_subgoal`,
`replace_subgoal_with_premises`), strict matching
(`match_terms` / `match_terms_certified`), and `KernelRules::resolve1_match`
are implemented with invariant replay and attack tests. `resolve1_match` now
uses `replace_subgoal_with_premises` directly, so subgoal replacement order is
shared with the implication-chain foundation instead of duplicated locally.
Conservative `KernelRules::subst_premise` is also implemented: propositional
equality only, lhs→rhs only, no symmetric rewrite, no object equality rewrite,
no full unification, no lifting/freshening, and no flex-flex. Full
`bicompose`, `bicompose_eresolve`, lifting/freshening, flex-flex pairs, and
higher-order unification are not implemented.
