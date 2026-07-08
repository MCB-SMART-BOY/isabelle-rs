# Checked Definition Transport

## Status

Narrow `True_def` transport is implemented as the next prerequisite for the
first existing core-file `StrictClosed` theorem.

Current chain:

```text
True_def checked definition source: done, non-theorem input only
HOL object-equality/reflexivity bridge: done
checked-definition transport/fold-back for True_def: done in this phase
try_strict_hol_trueI: not implemented
core batch StrictClosed: still 0/125 until TrueI is routed
```

## Purpose

`True_def` is stored in `HolTheoremDb::checked_definitions` as checked
definition input:

```text
lhs: HOL.True
rhs: HOL.eq (λx::bool. x) (λx::bool. x)
```

This source is not a theorem, not a searchable fact, and not proof progress by
itself. It only gives a checked definitional relation that a named, auditable
transport step may use.

The narrow transport step is:

```text
rhs_thm:
  |- HOL.eq (λx::bool. x) (λx::bool. x)

True_def source:
  HOL.True := HOL.eq (λx::bool. x) (λx::bool. x)

result:
  |- HOL.True
```

## Trust Boundary

This transport is a TCB extension point. It is not:

- general unfolding;
- general definition rewriting;
- `simp`;
- a broad HOL proof engine;
- a way to turn checked definitions into theorem facts;
- a shortcut for `HOL::TrueI`.

The first version is deliberately restricted to `True_def`. Arbitrary checked
definitions must remain unsupported until the project has a general,
documented definitional equality story.

## Acceptance Conditions

`try_strict_true_def_transport(true_def, rhs_thm)` succeeds only if all
conditions hold:

- `true_def.name == "True_def"`;
- `true_def.const_name == "HOL.True"`;
- `true_def.const_type == bool`;
- `true_def.lhs` is checked, dummy-free, and exactly `HOL.True`;
- `true_def.rhs` is checked, dummy-free, and exactly
  `HOL.eq (λx::bool. x) (λx::bool. x)`;
- `rhs_thm` is strict closed proved;
- `rhs_thm.prop == true_def.rhs`;
- the result has no hypotheses, unresolved `tpairs`, oracle/admit footprint,
  or dummy types;
- the result is marked `ThmTrust::Strict` and classifies as
  `ProofOutcome::StrictClosed`.

## Rejection Conditions

The transport must reject:

- missing `True_def`;
- any checked definition source whose name is not `True_def`;
- any checked definition source whose defined constant is not `HOL.True`;
- dummy-tainted or compatibility-certified lhs/rhs CTerms;
- a RHS theorem whose proposition does not match the checked `True_def` RHS;
- compatibility, open, admitted, or oracle-backed RHS theorems;
- any attempt to use `Pure.eq` as the RHS proof;
- any attempt to treat the checked definition source as a theorem/fact.

## Replay Contract

The theorem records a named derivation rule:

```text
true_def_transport(rhs_thm)
```

Proof replay checks:

- exactly one premise exists;
- the premise replays to the checked `True_def` RHS shape;
- the result proposition is `HOL.True`;
- premise burdens are preserved.

The replay rule is intentionally shape-specific. It does not inspect or accept
arbitrary definition names.

## Relationship To HOL::TrueI

This transport still does not implement `HOL::TrueI`.

`HOL::TrueI` may be routed to strict acceptance only after the verifier checks
all of the following:

```text
theorem name: HOL::TrueI / TrueI
parsed proposition: HOL.True
proof shape: unfolding True_def by (rule refl)
checked True_def source exists
try_strict_hol_refl proves the checked RHS
true_def_transport folds RHS back to HOL.True
final theorem is StrictClosed
```

Until that narrow adapter is implemented, the core batch may remain at
`StrictClosed: 0/125`.

## Attack Tests

Required tests:

```text
true_def_transport_accepts_checked_true_def_rhs
true_def_transport_rejects_missing_true_def
true_def_transport_rejects_non_true_def
true_def_transport_rejects_rhs_mismatch
true_def_transport_rejects_compat_rhs_theorem
true_def_transport_rejects_admitted_rhs_theorem
true_def_transport_rejects_open_rhs_theorem
true_def_transport_rejects_dummy_tainted_definition
true_def_transport_produces_strict_closed_true
true_def_transport_replay_succeeds
true_def_transport_replay_rejects_wrong_rhs
```
