# ADR-0001: Strict Kernel Nucleus and Legacy Quarantine

## Status

Accepted.

## Context

The first trusted-engineering pass made legacy theorem accounting more honest:
compatibility theorems, open theorems, and admitted facts no longer count as
strict closed proved lemmas. It also introduced strict alpha-equivalence,
checked CTerms, theorem trust taint, and strict invariant checks.

That remains a patch over the legacy architecture. The old `src/core`,
`src/isar`, `src/hol`, and tactic layers still contain many compatibility paths
whose values can be searchable or useful during migration, but they should not
define the next TCB.

## Decision

Create a new `src/kernel/` strict kernel nucleus and treat the existing system
as legacy/quarantine until it is migrated through explicit adapters.

This is not a full-project rewrite. It is a strangler-style kernel reset:

```text
new strict kernel first
legacy system isolated
adapters migrate old terms/proofs into the new boundary
compat never enters the new TCB
```

## TCB Boundary

`src/kernel/` is the new TCB experiment. It must not contain:

- compatibility alpha-equivalence;
- `Typ::dummy` or equivalent unknown type values;
- best-effort certification;
- fallback `assume`;
- raw-term auto-declare of constants or frees;
- goal-as-theorem proof obligations;
- public theorem constructors;
- crate-wide unchecked certification or theorem constructors (`pub(crate)`);
- implicit conversion from search facts to trusted theorems.

The legacy `src/core` remains available for existing code while migration is
planned. It is not the target shape for new trusted work.

## Type/Data Flow

The strict flow is:

```text
RawTerm
  -> name/type certification by Signature + ProofContext
  -> CTerm / CProp
  -> primitive KernelRules
  -> KernelThm
  -> ClosedThm
  -> TrustedTheorem
  -> TrustedTheory
```

The non-TCB flow is:

```text
SearchFact / legacy compat fact / admitted fact
  -> proof search and diagnostics only
  -> no implicit TrustedTheorem conversion
```

## Logical Compatibility

Breaking old Isabelle-rs APIs is allowed when it shrinks the TCB. Breaking
Isabelle/Pure logical semantics is not allowed.

Every primitive rule must have:

- a contract;
- explicit side conditions;
- burden propagation behavior;
- invariant/replay tests;
- attack tests for rejected malformed inputs.

## Consequences

- `CTerm` in the new kernel means certified term only. Compatibility terms must
  use separate legacy/search types.
- Internal escape hatches such as certified-subterm wrappers and theorem
  constructors are visible only inside `crate::kernel` (`pub(in crate::kernel)`)
  or narrower. Legacy `src/core`, Isar, HOL, tools, and session modules must
  enter through strict certification or explicit adapters.
- `ProofObligation` is separate from theorem values.
- `TrustedTheory` accepts only `TrustedTheorem`.
- `SearchFactDb` may hold untrusted facts but cannot promote them to
  trusted theorems.
- Old Isar/HOL/tactic migration should happen through adapters after the
  strict nucleus is stable.
