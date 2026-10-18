# Checked Definition Transport

## Status

Historical design/implementation record for the legacy `True_def` transport
used in the 2026-10-03 sampled transitional `HOL::TrueI` experiment. The
theorem-specific bridge is no longer present in the current verification path.
The strict kernel separately implements `TrustedTheory::define_const`: a
parent-context checked, fresh, closed, monomorphic definition certificate
whose entry and replay share semantic validation (including every RHS type
annotation), followed by an accepted definition theorem.

```text
2026-10-03: legacy True_def + HOL object refl + shape-specific fold-back
  -> sampled TransitionalStrictClosed: 1/125; KernelTrustedClosed: 0/125
2026-10-07: audited bundled HOL::TrueI source projection + strict definition
  -> sampled TransitionalStrictClosed: 0/125; KernelTrustedClosed: 1/125
```

The current projection checks only the declarations and proof needed for
`HOL::TrueI`, not arbitrary sampled HOL definitions or the complete theory.
Do not revive theorem-specific legacy transport as general definition
rewriting. The deferred general boundary is discussed in
[ADR-0003-hol-logic-trusted-extension.md](../adr/ADR-0003-hol-logic-trusted-extension.md).

## Purpose

`True_def` was stored in `HolTheoremDb::checked_definitions` as checked
legacy definition input:

```text
lhs: HOL.True
rhs: HOL.eq (λx::bool. x) (λx::bool. x)
```

This source was not itself a theorem, searchable fact, or proof progress.
The legacy payload was not a strict-kernel conservative definition certificate:
it established neither a fresh constant, exact parent identity, complete RHS
monomorphism, nor replayable definition dependency. The former transport was:

```text
rhs_thm:
  |- HOL.eq (λx::bool. x) (λx::bool. x)

True_def source:
  HOL.True := HOL.eq (λx::bool. x) (λx::bool. x)

result:
  |- HOL.True
```

## Trust Boundary

This transport expanded the transitional legacy trusted surface. It was not
part of the target TCB and was not:

- general unfolding;
- general definition rewriting;
- `simp`;
- a broad HOL proof engine;
- a way to turn checked definitions into theorem facts;
- a shortcut for `HOL::TrueI`.

The historical version was restricted to `True_def`; its conditions below
are not a live API. Current source-backed acceptance uses generic strict
definition replay, not the theorem-specific fold-back.

## Acceptance Conditions

The removed `try_strict_true_def_transport(true_def, rhs_thm)` required all
of the following:

- `true_def.name == "True_def"`;
- `true_def.const_name == "HOL.True"`;
- `true_def.const_type == bool`;
- `true_def.lhs` is checked, dummy-free, and exactly `HOL.True`;
- `true_def.rhs` is checked, dummy-free, and exactly
  `HOL.eq (λx::bool. x) (λx::bool. x)`;
- `rhs_thm` satisfies the legacy transitional strict-closed predicate;
- `rhs_thm.prop == true_def.rhs`;
- the result has no hypotheses, unresolved `tpairs`, oracle/admit footprint,
  or dummy types;
- the result is marked `ThmTrust::Strict` and classifies as
  `ProofOutcome::TransitionalStrictClosed`.

## Rejection Conditions

The removed transport had to reject:

- missing `True_def`;
- any checked definition source whose name is not `True_def`;
- any checked definition source whose defined constant is not `HOL.True`;
- dummy-tainted or compatibility-certified lhs/rhs CTerms;
- a RHS theorem whose proposition does not match the checked `True_def` RHS;
- compatibility, open, admitted, or oracle-backed RHS theorems;
- any attempt to use `Pure.eq` as the RHS proof;
- any attempt to treat the checked definition source as a theorem/fact.

## Replay Contract

The legacy theorem recorded a named derivation rule:

```text
true_def_transport(rhs_thm)
```

Historical proof replay checked:

- exactly one premise exists;
- the premise replays to the checked `True_def` RHS shape;
- the result proposition is `HOL.True`;
- premise burdens are preserved.

That replay rule was shape-specific and did not inspect or accept arbitrary
definition names.

## Relationship To HOL::TrueI

Historically the legacy `HOL::TrueI` adapter consumed this transport with the
following checked shape; it is not the current acceptance route:

```text
theorem name: HOL::TrueI / TrueI
parsed proposition: HOL.True
proof shape: unfolding True_def by (rule refl)
checked True_def source exists
try_strict_hol_refl proves the checked RHS
true_def_transport folds RHS back to HOL.True
final legacy theorem is TransitionalStrictClosed
```

The 2026-10-07 sampled core batch instead reports
`TransitionalStrictClosed: 0/125` and `KernelTrustedClosed: 1/125`: only its
source-backed `HOL::TrueI` projection obtains a replayed exact-owner token.
The independent source-backed HOL/Pure fixtures remain outside this batch.

## Attack Tests

The `true_def_transport_*` names below refer to historical bridge coverage,
not tests or an API in the current checkout:

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

Current sampled projection attack coverage is in
[`tests/sampled_true_i.rs`](../../tests/sampled_true_i.rs).
