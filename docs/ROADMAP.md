# Roadmap

This is the current dependency-ordered roadmap. Root
[AGENTS.md](../AGENTS.md), [PROJECT_STATUS.md](PROJECT_STATUS.md), and
[TRUST.md](TRUST.md) define the authoritative position; historical phase plans
and transfer notes do not override them.

## Current State

```text
TransitionalStrictClosed: 1/125
KernelTrustedClosed:      0/125
```

The strict `src/kernel` nucleus has checked `CProp : prop`, private theorem
construction, the base Pure rule set, conservative resolution prototypes, and
derivation replay. It does not yet have immutable theory/signature identity or
a context-bound final acceptance operation.

The existing `HOL::TrueI` path is a bool-valued legacy migration experiment.
It is not the first new-kernel HOL theorem.

## Trusted Main Line

```text
immutable SignatureId / TheoryId
  -> unique context-bound acceptance
  -> source-aware proposition AST
  -> checked judgment / constant / type-scheme elaboration
  -> data-only HOL logic-basis manifest
  -> generic conservative definition extension
  -> HOL::TrueI as HOL.Trueprop HOL.True
  -> HOL::trans only as a later reuse consumer
```

The order is mandatory. A later phase may be designed in parallel, but it may
not enter trusted production paths before its prerequisites.

Phases 1 and 2 form the first bounded implementation sequence, but they land as
separate reviewable changes. The immediate next change is Phase 1 only:
immutable context identity, propagation, and mixed-context rejection, with no
new acceptance API or `ProofOutcome` change. Phase 2 starts only after those
context invariants pass review. Do not start Phase 3 in parallel.

## Phase 1: Immutable Context Identity — Slice Foundation

### Goal

Make it impossible to combine certified terms or theorems from unrelated
signatures by accident.

### Minimum implementation

1. Add private, opaque `SignatureId` and `TheoryId` types.
2. Replace silent declaration overwrite with checked monotonic extension.
3. Define canonical, domain-separated identity input for validated
   declarations and parent identity.
4. Bind `ProofContext`, `CTerm`, `CProp`, `KernelThm`, `ClosedThm`, and
   `TrustedTheorem` to the relevant context identity.
5. Reject mixed-context inputs in every strict rule before theorem
   construction.
6. Preserve parent contexts unchanged when creating an extension.

Do not add a hashing dependency merely to make the type look content-addressed.
First specify and test canonical declaration encoding, domain separation, and
collision/error behavior. Any dependency and `Cargo.lock` change needs a
separate rationale.

### Required attacks

- equal canonical signatures produce equal IDs;
- declaration order has the documented deterministic meaning;
- a conflicting constant declaration is rejected, not overwritten;
- extending a signature does not mutate the parent;
- a `CProp` certified under signature A cannot be used with signature B;
- two contexts with the same surface names but different declarations do not
  interoperate;
- callers cannot construct or spoof identity values.

### Exit condition

Focused identity tests and the existing strict gate pass. No proof outcome or
sampled HOL count changes.

## Phase 2: Unique Context-Bound Acceptance — Slice Completion

Implement one operation conceptually equivalent to:

```rust
pub fn accept_closed_theorem(
    theory: &TrustedTheory,
    theorem: ClosedThm,
) -> Result<TrustedTheorem, KernelError>;
```

The exact ownership shape may change during implementation, but the operation
must:

- check exact theory/signature identity;
- require `CProp : prop` and no open hypotheses or unresolved obligations;
- replay in the supplied immutable context;
- recompute and validate all axiom, definition, and theorem dependencies;
- reject compat, admitted, search-fact, and legacy inputs;
- leave trusted-table storage to a typed operation that rejects context mismatch
  and duplicate/conflicting names without silent overwrite.

After this exists:

- `ClosedThm::trust` becomes internal or is removed;
- `KernelTrustedClosed` becomes a mutually exclusive `ProofOutcome` variant
  that owns the returned `TrustedTheorem`;
- the temporary reporting overlay is removed;
- synthetic Pure `A ==> A` tests correct and wrong-context acceptance without
  changing the 125-theorem HOL benchmark.

Detailed audit:
[KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](KERNEL_TRUSTED_ACCEPTANCE_GAPS.md).

## Phase 3: Source-Aware Proposition AST

Preserve source semantics before legacy term lowering:

```text
Pure implication versus HOL implication
Pure equality versus HOL.eq
Const / Free / Var / Bound identity
binder scope
explicit types and sorts
source spans
notation and name-resolution provenance
HOL.Trueprop insertion positions
```

The current `SourcePropositionStatus` and `SourcePropositionShape` values remain
transitional rejection metadata only.

Do not repair a damaged legacy `CTerm` by guessing what the source meant.

## Phase 4: Checked Declarations And Proposition Elaboration

Use one provenance-bearing pipeline for `typedecl`, `judgment`, `consts`,
`axiomatization`, and `definition`.

The first required judgment is:

```text
HOL.Trueprop : bool => prop
```

The elaborator must resolve checked polymorphic schemes and sorts, preserve the
source skeleton, insert `Trueprop` only at recorded judgment positions, and
return a checked `CProp` without constructing a theorem.

Do not add a `HOL.Trueprop` string special case to legacy
`HolTheoremDb::build_type_env`.

## Phase 5: Data-Only HOL Logic Basis

Install the Isabelle/HOL logical basis as immutable data:

```text
HOL.Trueprop judgment
HOL.eq declaration
refl axiom schema
subst axiom schema
ext axiom schema when required
```

Generic kernel code validates declaration schemes, installs the basis,
instantiates axioms, records dependencies, and replays derivations. The
manifest contains no callbacks, theorem factories, executable validators, or
theorem-name special cases.

Do not add `ThmKernel::hol_*` or `KernelRules::hol_*` proof shortcuts.

## Phase 6: Generic Conservative Definition Extension

Implement a theorem-independent operation that:

- requires a fresh constant;
- validates the declaration and legal definition left-hand side;
- checks a closed, well-typed RHS with no direct or indirect self-reference;
- checks type variables, sorts, and parent-theory dependencies;
- returns a child theory and replayable Pure meta-equality definition theorem.

The legacy `CheckedDefinitionSource` and `true_def_transport` mechanisms remain
transitional evidence only.

## Phase 7: First Real HOL Theorem

Re-derive:

```text
|- HOL.Trueprop HOL.True
```

Required chain:

```text
source-aware TrueI
  -> checked Trueprop elaboration
  -> immutable HOL theory
  -> installed refl schema instance
  -> conservative True_def theorem
  -> ordinary Pure equality/congruence transport
  -> context-bound TrustedTheorem
  -> unique acceptance
  -> KernelTrustedClosed: 1/125
```

Only this milestone authorizes changing the sampled kernel-trusted count.

## Phase 8: Reuse Consumer

`HOL::trans` may be implemented only after Phase 7. It must reuse the same
source AST, elaborator, immutable HOL context, installed `subst` schema,
dependency replay, and acceptance operation. It must not introduce a
`try_strict_hol_trans` theorem-name bridge.

## Parallel Maintenance

Allowed when it does not delay or weaken the main line:

- strict-kernel attack-test and replay hardening;
- classified admitted/compat diagnostics;
- documentation and agent-rule synchronization;
- design-only deterministic CPU symbolic-compute work.

Compute remains an untrusted candidate producer. Burn/CubeCL/GPU work, if ever
added, stays outside the kernel and cannot produce theorem values.

## Deferred Platform Work

Defer until the trusted HOL loop closes:

- Cargo workspace split;
- session snapshot/rollback engine;
- `isabelle.toml` project system;
- Agent Proof Protocol;
- broad LSP/PIDE/WASM/plugin work;
- broad HOL/Isar/tool coverage;
- AFP-scale claims.

## Standing Verification Policy

- Documentation/agent changes: `scripts/dev-check.sh docs`.
- Kernel or trust-boundary changes: `scripts/dev-check.sh strict`.
- Sampled HOL metric changes: `scripts/dev-check.sh core`.
- Broader theory claims: run the exact relevant `tier2`, `tier3`, or `broad`
  mode.

Report observed results only. Do not infer project API correctness from a
standalone template compile, mathematical trust from an oracle-free count, or
dependency intent from a successful locked metadata command.
