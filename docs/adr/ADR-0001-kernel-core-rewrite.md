# ADR-0001: Strict Kernel Nucleus and Legacy Quarantine

## Status

Accepted. The kernel-nucleus decision is implemented in `crates/kernel/`;
`src/kernel/mod.rs` is the root crate's re-export, not a second TCB.

## Context

The first trusted-engineering pass made legacy theorem accounting more honest:
compatibility theorems, open theorems, and admitted facts no longer count as
transitional strict-closed lemmas. It also introduced strict alpha-equivalence,
checked CTerms, theorem trust taint, and strict invariant checks.

That remains a patch over the legacy architecture. The old `src/core`,
`src/isar`, `src/hol`, and tactic layers still contain many compatibility paths
whose values can be searchable or useful during migration, but they should not
define the next TCB.

## Decision

Create a strict kernel nucleus (originally planned at `src/kernel/`, now
implemented in `crates/kernel/`) and treat the existing system as
legacy/quarantine until it is migrated through explicit adapters.

This is not a full-project rewrite. It is a strangler-style kernel reset:

```text
new strict kernel first
legacy system isolated
adapters migrate old terms/proofs into the new boundary
compat never enters the new TCB
```

## TCB Boundary

`crates/kernel/` is the strict TCB experiment; `src/kernel/mod.rs` re-exports it. It must not contain:

- compatibility alpha-equivalence;
- `Typ::dummy` or equivalent unknown type values;
- best-effort certification;
- fallback `assume`;
- raw-term auto-declare of constants or frees;
- goal-as-theorem proof obligations;
- public theorem constructors;
- unchecked certification or theorem constructors exposed to the root product,
  legacy/frontends or external callers;
- implicit conversion from search facts to trusted theorems.

Unchecked construction may use `pub(crate)` or narrower visibility only inside
the isolated `isabelle-kernel` crate. Its public frontend API must not expose
those constructors; sharing a workspace does not share crate-private access.

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
  -> accept_closed_theorem(exact immutable owner, fact name)
  -> (child TrustedTheory, sealed TrustedTheorem)
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
- Direct theorem constructors and unchecked certification are confined to the
  strict kernel crate. Public helper operations such as `theorem_builder` can
  return candidate `KernelThm` values, but cannot mint accepted tokens;
  `accept_closed_theorem` still verifies exact-owner replay. Legacy `src/core`,
  Isar, HOL, tools, and session code cannot promote compatibility results.
- `ProofObligation` is separate from theorem values.
- `TrustedTheory` acceptance now uses `accept_closed_theorem` with the exact
  immutable owner and replay; the older context-free `add` limitation recorded
  when this decision was written has been superseded by that implementation.
  See [KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](../kernel/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md).
- `SearchFactDb` may hold untrusted facts but cannot promote them to
  trusted theorems.
- Old Isar/HOL/tactic migration should happen through adapters after the
  strict nucleus is stable.
