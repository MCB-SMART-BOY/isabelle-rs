# HOL Object Equality / Reflexivity Bridge

## Status

Narrow legacy bridge implemented. `HOL::TrueI` is the first existing core-file
`TransitionalStrictClosed` slice, not a new-kernel trusted theorem.

Current implementation status:

```text
HOL.eq term/type diagnostic: done
try_strict_hol_refl: implemented
checked-definition transport/fold-back to True: implemented for checked True_def
try_strict_hol_true_i: implemented as a narrow TrueI-only adapter
core batch TransitionalStrictClosed: 1/125
KernelTrustedClosed: 0/125
```

This bridge produces a bool-valued legacy `core::Thm`, has no immutable theory
or logic-extension identity, and cannot enter `KernelTrustedClosed`. It must not
be generalized with additional HOL primitives in `src/core`; the target
replacement boundary is proposed in
[ADR-0003-hol-logic-trusted-extension.md](ADR-0003-hol-logic-trusted-extension.md).

The current tests in `src/hol/hol_loader.rs` establish:

- `HOL.eq` is declared in the checked `TypeEnv` as `'a => 'a => bool`.
- A checked application `HOL.eq HOL.True HOL.True` has result type `bool`.
- The checked `True_def` RHS is reflexive `HOL.eq` over `bool => bool`.
- `Pure.eq` remains distinguishable from `HOL.eq` and must not be accepted as
  an object-equality bridge input.
- `try_strict_hol_refl` accepts only checked input terms and checked `HOL.eq`
  declarations, and rejects missing/dummy `HOL.eq` and compatibility inputs.

This document records the transitional experiment used by the first existing
core-file `TransitionalStrictClosed` slice:

```text
HOL::TrueI:
  True
  unfolding True_def by (rule refl)
```

`True_def` is already available as a checked definition source in
`HolTheoremDb::checked_definitions`, but it is not a theorem and does not count
as proof progress. `try_strict_hol_refl` can prove the unfolded reflexive HOL
object equality, and `true_def_transport` can fold that exact checked RHS back
to `HOL.True`. `HOL::TrueI` remains unsafe to accept until a narrow adapter
checks the theorem name, parsed proposition, proof shape, checked definition,
RHS proof, and final `TransitionalStrictClosed` result. Those checks do not supply
`HOL.Trueprop`, a theory context, or new-kernel theorem provenance.

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
not transitional strict-closed theorem sources. They must not be reused to
produce `ProofOutcome::TransitionalStrictClosed`.

## Non-Goals

- Do not implement general unfolding.
- Do not implement `simp`.
- Do not implement a broad HOL proof engine.
- Do not treat `Pure.eq` and `HOL.eq` as interchangeable.
- Do not use compat, open, admitted, or searchable-only `refl` facts.
- Do not modify `try_strict_hol_true_i` to bypass checked `True_def`
  transport, proof-shape checks, or final strict-closed validation.

## Term Shape

The implemented bridge only concerns terms with this object-logic shape:

```text
HOL.eq t t
```

where:

```text
HOL.eq : α => α => bool
t      : α
```

The current result is the boolean term `HOL.eq t t : bool`; it is not lifted
through `HOL.Trueprop` and therefore is not a valid `CProp` for final kernel
acceptance. It must not be represented as Pure meta-equality either. A future
HOL elaborator must construct `HOL.Trueprop (HOL.eq t t) : prop` from the source
judgment position before kernel certification.

## Trust Decision

The bridge is treated only as a named legacy migration derivation:

```text
try_strict_hol_refl(t)
  input:
    checked HOL term t : α
  output:
    legacy TransitionalStrictClosed theorem for HOL.eq t t : bool
```

This expands the transitional `src/core` trusted surface but is not part of the
target Pure kernel or HOL logic extension. It is not derived from Pure
reflexivity alone and is ineligible for `KernelTrustedClosed`. While it remains,
the bridge must be:

- explicitly named;
- documented in `TRUST.md`;
- represented in derivation/proof metadata, not hidden as a compat theorem;
- covered by attack tests;
- limited to reflexive object equality only.

## Acceptance Conditions

`try_strict_hol_refl(t)` succeeds only if all conditions hold:

- `HOL.eq` is declared in the checked type environment.
- `HOL.eq` has type compatible with `α => α => bool`.
- `t` is checked, not compatibility-certified.
- `t` has no dummy type annotation.
- The constructed proposition is exactly reflexive: left and right sides are
  strict alpha-equivalent copies of the same checked term.
- The result has no hypotheses.
- The result has no unresolved `tpairs`.
- The result has no oracle/admit footprint.
- The result is marked strict and classifies as
  `ProofOutcome::TransitionalStrictClosed`.

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

`HOL::TrueI` is implemented only by the narrow path:

```text
1. recognize theorem name `HOL::TrueI`;
2. require parsed proposition `True`;
3. require proof shape `unfolding True_def by (rule refl)`;
4. look up checked non-theorem source `True_def`;
5. unfold to the expected reflexive HOL object equality;
6. call `try_strict_hol_refl` on the checked RHS term;
7. transport back to `True` through the documented checked `True_def` step;
8. classify the final legacy theorem as `TransitionalStrictClosed` only.
```

The transport step is documented separately in
[CHECKED_DEFINITION_TRANSPORT.md](CHECKED_DEFINITION_TRANSPORT.md). It is
deliberately restricted to checked `True_def`, not arbitrary definitions.

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

`HOL::TrueI` tests separately check:

```text
strict_hol_true_i_accepts_checked_true_def_refl_path
strict_hol_true_i_rejects_missing_true_def
strict_hol_true_i_rejects_wrong_theorem_name
strict_hol_true_i_rejects_wrong_prop
strict_hol_true_i_rejects_wrong_proof_shape
strict_hol_true_i_rejects_rhs_mismatch
strict_hol_true_i_rejects_compat_refl_path
proof_outcome_counts_hol_true_i_as_transitional_strict_closed
```

The checked-definition transport attack tests live next to the HOL loader and
proofterm replay tests and include `true_def_transport_*` coverage.

## Implementation Boundary

The bridge remains quarantined outside `src/kernel` and must not be copied into
the future HOL object-logic layer. The target path installs explicit HOL axiom
schemas and conservative definitions in an immutable context, then derives a
`CProp` using generic kernel operations.

Do not expand this bridge into general equality reasoning. The completed
milestone is:

```text
TransitionalStrictClosed: 0/125 -> 1/125
KernelTrustedClosed:      0/125
```

and the only current consumer is the `HOL::TrueI` slice.
