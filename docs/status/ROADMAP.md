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
construction, the base Pure rule set, conservative resolution prototypes,
immutable content-addressed signature/theory and accepted-fact ancestry,
owner-parameterized recursive recertification/replay, theorem-reference
dependency reconstruction, and one non-forgeable accepted token.

The existing `HOL::TrueI` path is a bool-valued legacy migration experiment.
It is not the first new-kernel HOL theorem.

## Trusted Main Line

```text
immutable SignatureId / TheoryId [implemented]
  -> unique context-bound acceptance [implemented]
  -> data-only source proposition AST [implemented]
  -> checked source parsing + judgment / constant / type-scheme elaboration [next]
  -> data-only HOL logic-basis manifest
  -> generic conservative definition extension
  -> HOL::TrueI as HOL.Trueprop HOL.True
  -> HOL::trans only as a later reuse consumer
```

The order is mandatory. A later phase may be designed in parallel, but it may
not enter trusted production paths before its prerequisites.

Phases 1 and 2 landed with synthetic Pure tests outside the HOL benchmark.
Phase 3 now supplies only an untrusted syntax data model; it deliberately has
no parser integration, semantic resolution, trusted context, or kernel
conversion. Phase 4 is the first unfinished dependency.

## Phase 1: Immutable Context Identity — Implemented

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

Implemented with the repository's existing `sha2` dependency; `Cargo.lock` did
not change.

## Phase 2: Unique Context-Bound Acceptance — Implemented

The implemented operation is:

```rust
pub fn accept_closed_theorem(
    theory: &TrustedTheory,
    name: impl Into<Name>,
    theorem: ClosedThm,
) -> Result<(TrustedTheory, TrustedTheorem), KernelError>;
```

It:

- checks exact theory/signature identity and immutable owner-chain integrity;
- recursively recertifies every checked theorem and derivation payload under
  the supplied owner;
- requires a proposition-valued, replay-equal, closed result;
- reconstructs and authorizes ancestor-theorem dependencies;
- rejects currently unsupported axiom/definition dependency categories;
- rejects duplicate theorem names without mutation or overwrite;
- atomically returns the immutable fact child and sealed token;
- accepts no compat, admitted, search-fact, or legacy input.

`ClosedThm::trust` is removed, `SearchFact` carries no extractable proof,
and `KernelTrustedClosed` is a mutually exclusive token-owning
`ProofOutcome`. `ProofOutcomeStats::total()` includes that bucket.

Synthetic Pure `A ==> A` tests exercise correct/wrong context, dependency,
duplicate, tampering, malformed-term, owner/store, canonical-ID, and classifier
attacks without changing the 125-theorem HOL benchmark.

Detailed audit:
[KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](KERNEL_TRUSTED_ACCEPTANCE_GAPS.md).

## Phase 3: Source-Aware Proposition AST — Data Model Implemented

`src/isar/source_ast.rs` now preserves source structure before any trusted
elaboration:

```text
SourceProposition { SourceId, SourceSpan, SourceExpr }
SourceExpr::{Name, Application, Binder, SyntaxApplication, TypeAscription, Group}
SourceType::{Name, Application, Arrow}
```

`SourceName` stores exact spelling without preclassifying dotted text as a
qualified constant. `SourceSyntax` stores raw binder/operator spelling and its
span instead of hard-coding Pure/HOL binder meaning. `SourceSpan` is a
half-open byte range `[start, end)` and `SourceId` is a caller-supplied label;
both are forgeable diagnostic metadata, not trusted provenance.

The model has no `ContextStamp`, `SignatureId`, `TheoryId`, `CProp`,
`ClosedThm`, or `TrustedTheorem`, and compile-fail tests forbid direct
conversion into kernel or legacy theorem authority.

This phase does **not** yet parse Isabelle source into the model, resolve
`Const` / `Free` / `Var` / `Bound`, classify Pure versus HOL syntax, check
types/sorts, or record authorized judgment insertion. Those are Phase 4
responsibilities. Transitional `SourcePropositionStatus` and
`SourcePropositionShape` remain separate rejection metadata.

Do not repair a damaged legacy `CTerm` by guessing what the source meant.

## Phase 4: Checked Declarations And Proposition Elaboration — Next

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

## Phase 9+: ISIP Platform

ISIP (Isabelle Structured Interaction and Proof) is a family of standards
for editor-agnostic, model-agnostic proof interaction. See
[docs/isip/ISIP.md](isip/ISIP.md). **Design-only until TCB closes.**

ISIP implementation stages:

| Stage | Name | Prerequisite | Key Deliverables |
|-------|------|-------------|-----------------|
| 0 | Design | None (now) | ISIP-000, ISIP-100 draft, ISIP-300 draft |
| 1 | Observable | TCB closed | `getSnapshot`, `getGoals`, `getContext`, diagnostics |
| 2 | Transactional | Stage 1 | `LogicalAction`, `StateTransition`, `StateDiff` |
| 3 | Branching + Agent | Stage 2 | `fork`, `moveHead`, `tryBatch`, budget, MCP Profile |
| 4 | Evidence-Aware | Stage 3 | Replay, certificate check, artifact persist, theory extend |
| 5 | Multi-Logic | Stage 4 | Second logic backend, TranslationEvidence, A2A Profile |

## Deferred Platform Work

Defer until the trusted HOL loop closes:

- Cargo workspace split;
- ISIP Stage 1+ runtime implementation;
- session snapshot/rollback engine;
- `isabelle.toml` project system;
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
