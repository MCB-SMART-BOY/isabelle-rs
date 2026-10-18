# HOL Object Equality / Reflexivity Bridge

## Status

Historical record of the removed legacy `try_strict_hol_refl` /
`try_strict_hol_true_i` bridges. On 2026-10-03 the sampled core-file
`HOL::TrueI` produced a bool-valued `core::Thm` with
`TransitionalStrictClosed: 1/125` and `KernelTrustedClosed: 0/125`; this
legacy theorem had no immutable owner or installed HOL logic-basis dependency.

On 2026-10-07 the audited bundled-source `HOL::TrueI` projection instead
produces the sole sampled exact-owner token (`KernelTrustedClosed: 1/125`,
`TransitionalStrictClosed: 0/125`). The independent source-backed
`TrustedTrueI.thy` fixture also produces a token outside the sample. Neither
path executes unrelated HOL/ML commands or implements general HOL equality
reasoning; see [PROJECT_STATUS.md](../status/PROJECT_STATUS.md) and
[ADR-0003-hol-logic-trusted-extension.md](../adr/ADR-0003-hol-logic-trusted-extension.md).

The historical tests of the removed bridge checked:

- `HOL.eq` declared in the checked `TypeEnv` as `'a => 'a => bool`;
- checked application `HOL.eq HOL.True HOL.True` with result type `bool`;
- a checked, reflexive `True_def` RHS;
- `Pure.eq` distinct from `HOL.eq`.

The legacy `True_def` payload and `true_def_transport` fold-back supplied
only a bool-valued `HOL.True`. The current audited source projection uses
the strict kernel's basis, conservative definition, Pure transport and owner
replay instead. The sections below document the superseded experiment:

```text
HOL::TrueI:
  True
  unfolding True_def by (rule refl)
```

Historically `True_def` was available as non-theorem legacy input. The
legacy bridge proved its reflexive object-equality RHS and
`true_def_transport` folded it back to bool-valued `HOL.True`. The former
`try_strict_hol_true_i` checked the narrow name/proposition/proof shape,
but supplied neither `HOL.Trueprop` nor an immutable theorem owner.

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

Searchable `refl` facts in the legacy HOL database are not strict
accepted theorem evidence; they cannot produce `KernelTrustedClosed`.

## Non-Goals

- Do not implement general unfolding.
- Do not implement `simp`.
- Do not implement a broad HOL proof engine.
- Do not treat `Pure.eq` and `HOL.eq` as interchangeable.
- Do not use compat, open, admitted, or searchable-only `refl` facts.
- Do not revive `try_strict_hol_true_i` to bypass audited source/definition
  provenance, proof-shape checks, or exact-owner kernel acceptance.

## Term Shape

The former bridge concerned only terms with this object-logic shape:

```text
HOL.eq t t
```

where:

```text
HOL.eq : α => α => bool
t      : α
```

Its result was the boolean term `HOL.eq t t : bool`, not lifted through
`HOL.Trueprop` and therefore not a valid `CProp` for final kernel acceptance.
It must not be represented as Pure meta-equality either. The audited sampled
projection now checks `HOL.Trueprop (HOL.True) : prop` through the strict
kernel; general HOL equality elaboration remains open.

## Trust Decision

The removed bridge was treated only as a named legacy migration derivation:

```text
try_strict_hol_refl(t)
  input:
    checked HOL term t : α
  output:
    legacy TransitionalStrictClosed theorem for HOL.eq t t : bool
```

This expanded the transitional `src/core` trusted surface but was not part of
the target Pure kernel or HOL logic extension. It was not derived from Pure
reflexivity alone and was ineligible for `KernelTrustedClosed`. The historical
requirements while it existed were explicit naming, trust documentation,
derivation metadata, attack coverage, and reflexive-only scope.

## Acceptance Conditions

The removed `try_strict_hol_refl(t)` required all these conditions:

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

The removed bridge had to reject:

- missing `HOL.eq`;
- dummy-typed `HOL.eq`;
- dummy-typed or compatibility-certified input term;
- non-reflexive `HOL.eq lhs rhs`;
- any attempt to use `Pure.eq lhs rhs` as the object equality proof;
- any compat/open/admitted `refl` fact;
- any output with hypotheses, `tpairs`, oracle/admit footprints, or dummy types.

## `HOL::TrueI` Dependency

The former transitional `HOL::TrueI` path was:

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

The historical transport step is documented separately in
[CHECKED_DEFINITION_TRANSPORT.md](CHECKED_DEFINITION_TRANSPORT.md). It was
restricted to checked `True_def`, not arbitrary definitions.

## Legacy Regression Coverage

These names document historical tests of the removed legacy bridge; they
are not current executable test names:

```text
hol_refl_bridge_accepts_checked_term
hol_refl_bridge_rejects_dummy_type
hol_refl_bridge_rejects_missing_hol_eq
hol_refl_bridge_rejects_compat_term
hol_refl_bridge_rejects_pure_eq_substitution
hol_refl_bridge_produces_strict_closed_hol_eq
```

The historical `HOL::TrueI` tests separately checked:

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

The historical checked-definition transport tests included
`true_def_transport_*`; current attack coverage for the sampled projection
is in [`tests/sampled_true_i.rs`](../../tests/sampled_true_i.rs).

## Implementation Boundary

The removed bridge must not be restored in the strict kernel. The sampled
`HOL::TrueI` projection now audits only the necessary bundled source
declarations and proof, installs a minimal logic basis and conservative
definition in an immutable owner, and derives a checked `CProp` via Pure
transport. The current milestone is `TransitionalStrictClosed: 0/125`,
`KernelTrustedClosed: 1/125`; broader source-theory compilation and general
object-equality reasoning remain open.
