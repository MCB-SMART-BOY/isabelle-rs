# HOL Object Equality / Reflexivity Bridge

## Status

Design-only. No implementation is present yet.

Current implementation status:

```text
try_strict_hol_refl: not implemented
try_strict_hol_trueI: not implemented
core batch StrictClosed: 0/125
```

This document specifies the next prerequisite for the first existing core-file
`StrictClosed` slice:

```text
HOL::TrueI:
  True
  unfolding True_def by (rule refl)
```

`True_def` is already available as a checked definition source in
`HolTheoremDb::checked_definitions`, but it is not a theorem and does not count
as proof progress. `HOL::TrueI` remains unsafe to accept until a strict bridge
can prove the unfolded reflexive HOL object equality.

## Problem

The project currently has two different equalities:

```text
Pure equality:        t == u      (Pure.eq, kernel meta-equality)
HOL object equality:  t = u       (HOL.eq, boolean-valued object-logic equality)
```

These must not be conflated.

`KernelRules::reflexive(t)` proves:

```text
|- t == t
```

It does not prove:

```text
|- HOL.eq t t
```

The current searchable `refl` facts in the HOL database are compatibility facts,
not strict closed theorem sources. They must not be reused to produce
`ProofOutcome::StrictClosed`.

## Non-Goals

- Do not implement general unfolding.
- Do not implement `simp`.
- Do not implement a broad HOL proof engine.
- Do not treat `Pure.eq` and `HOL.eq` as interchangeable.
- Do not use compat, open, admitted, or searchable-only `refl` facts.
- Do not implement `try_strict_hol_trueI` before this bridge exists.

## Term Shape

The bridge only concerns terms with this object-logic shape:

```text
HOL.eq t t
```

where:

```text
HOL.eq : α => α => bool
t      : α
```

The result proposition is the boolean term `HOL.eq t t` lifted through the
current HOL proposition representation used by the verified slice. It must not
be represented as Pure meta-equality unless the proposition explicitly requires
meta-equality.

## Trust Decision

Short term, the bridge should be treated as a narrow HOL object-logic primitive
bridge:

```text
try_strict_hol_refl(t)
  input:
    checked HOL term t : α
  output:
    strict closed theorem for HOL.eq t t
```

This is a TCB extension point. It is not derived from Pure reflexivity alone.
Until a fuller HOL axiom package and replay path exists, the bridge must be:

- explicitly named;
- documented in `TRUST.md`;
- represented in derivation/proof metadata, not hidden as a compat theorem;
- covered by attack tests;
- limited to reflexive object equality only.

## Acceptance Conditions

`try_strict_hol_refl(t)` may succeed only if all conditions hold:

- `HOL.eq` is declared in the checked type environment.
- `HOL.eq` has type compatible with `α => α => bool`.
- `t` is checked, not compatibility-certified.
- `t` has no dummy type annotation.
- The constructed proposition is exactly reflexive: left and right sides are
  strict alpha-equivalent copies of the same checked term.
- The result has no hypotheses.
- The result has no unresolved `tpairs`.
- The result has no oracle/admit footprint.
- The result is marked strict and classifies as `ProofOutcome::StrictClosed`.

## Rejection Conditions

The bridge must reject:

- missing `HOL.eq`;
- dummy-typed `HOL.eq`;
- dummy-typed or compatibility-certified input term;
- non-reflexive `HOL.eq lhs rhs`;
- any attempt to use `Pure.eq lhs rhs` as the object equality proof;
- any compat/open/admitted `refl` fact;
- any output with hypotheses, `tpairs`, oracle/admit footprints, or dummy types.

## `HOL::TrueI` Dependency

After the bridge exists, `HOL::TrueI` may be attempted only by the narrow path:

```text
1. recognize theorem name `HOL::TrueI`;
2. require parsed proposition `True`;
3. require proof shape `unfolding True_def by (rule refl)`;
4. look up checked non-theorem source `True_def`;
5. unfold to the expected reflexive HOL object equality;
6. call `try_strict_hol_refl` on the checked RHS term;
7. transport back to `True` only through a documented checked-definition step;
8. accept only if the final theorem is `StrictClosed`.
```

The last transport step is a separate proof obligation and is not solved by this
bridge alone. If the project lacks a legal definitional-equality rule from
checked definitions back to the defined constant, `HOL::TrueI` must remain
admitted even after `try_strict_hol_refl` exists.

## First Tests

The first implementation must add tests equivalent to:

```text
hol_refl_bridge_accepts_checked_term
hol_refl_bridge_rejects_dummy_type
hol_refl_bridge_rejects_missing_hol_eq
hol_refl_bridge_rejects_compat_term
hol_refl_bridge_rejects_pure_eq_substitution
hol_refl_bridge_produces_strict_closed_hol_eq
```

Later `HOL::TrueI` tests must separately check:

```text
strict_hol_trueI_rejects_missing_true_def
strict_hol_trueI_rejects_compat_refl
strict_hol_trueI_rejects_non_reflexive_unfolded_rhs
proof_outcome_counts_hol_trueI_as_strict_closed
```

## Implementation Boundary

The bridge should live outside `src/kernel` until the object-logic trust story is
settled. The strict kernel proves Pure propositions; this bridge connects the
HOL object logic to the strict acceptance path and must therefore remain a
small, named adapter with explicit documentation.

Do not expand this bridge into general equality reasoning. The only immediate
milestone is:

```text
test_verify_all_core_files: StrictClosed 0/125 -> 1/125
```

and the only intended first consumer is the `HOL::TrueI` slice.
