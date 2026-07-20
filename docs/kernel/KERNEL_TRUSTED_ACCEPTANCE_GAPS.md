# Kernel-Trusted Acceptance Gaps

## Status

Immutable context identity and one Pure-only trusted acceptance boundary are
implemented. This work adds theorem acceptance and ancestor theorem references,
but no HOL adapter, object-logic axiom, definition rule, source elaborator, or
sampled HOL proof power.

Read root [AGENTS.md](../AGENTS.md), then
[PROJECT_STATUS.md](PROJECT_STATUS.md) and [TRUST.md](TRUST.md), before using
this audit as an implementation plan.

Current sampled status remains:

```text
TransitionalStrictClosed: 1/125
KernelTrustedClosed:      0/125
```

`KernelTrustedClosed` is now a mutually exclusive `ProofOutcome` that owns a
non-forgeable accepted token. The production HOL verifier has no adapter that
can produce that token, so the sampled count remains zero.


## Checkpoint (2026-07-21)

Branch `wip/kernel-trusted-slice` merged at `03d28a6` closed two previously
open gaps:

| Gap | Status | Resolution |
| --- | ------ | ---------- |
| Axiom-schema instance trust (derivation trusts stored prop) | **Closed** | `AxiomInstance` replay reconstructs from basis schema; see `AxiomDependencyId` |
| Dual-entry axiom dependency (AxiomBasis + Axiom) | **Closed** | Single atomic `AxiomDependencyId::compute(basis_id, schema_id)` |
| Polymorphic constant instance matching (always-true) | **Closed** | `is_monomorphic_instance_of` with `BTreeMap<TypeVarId,Ty>` + concrete check |

Remaining open gaps:
- `ConservativeDefinition` not certificate-backed (multi-source payload)
- `PolyType.params` not authoritative
- `Ty::base("'a")` not rejected
- No production source->kernel bridge
- `KernelTrustedClosed` still 0/125

## Scope

This audit covers the strict path:

```text
RawTerm
  -> immutable Signature + TheorySnapshot + ProofContext
  -> CTerm / CProp
  -> KernelRules
  -> KernelThm
  -> ClosedThm
  -> accept_closed_theorem(owner, name, candidate)
  -> (child TrustedTheory, TrustedTheorem)
  -> ProofOutcome::KernelTrustedClosed
```

It distinguishes the implemented Pure acceptance gate from the still-missing
source elaboration, authorized HOL basis, axiom, and definition layers.

## Current Certification Boundary

### What `ProofContext::certify_prop` checks

`src/kernel/context.rs::ProofContext::certify_prop` recursively certifies a
`RawTerm` and then calls the private `CProp::new` constructor. The current checks
are:

- a `Const` name must exist in the context's `Signature`, with exactly the
  declared monomorphic `Ty`;
- a `Free` name must exist in the `ProofContext`, with exactly the declared
  `Ty`;
- a `Bound` index must be in scope;
- an application head must have an arrow type and its argument type must match
  exactly;
- a `Forall` body must have type `prop`;
- both operands of a Pure equality must have the same type;
- both operands of a Pure implication must have type `prop`;
- the final certified term must have type `prop`.

`src/kernel/typ.rs::Ty` has no dummy constructor, and the reserved concrete type
name `dummy` is rejected. `CProp` fields and constructors are private to
`crate::kernel`.

The attack tests in `tests/kernel_rewrite_soundness.rs` therefore establish the
following type-level boundary:

```text
b : bool                         -> rejected as CProp
HOL.True : bool                  -> rejected as CProp
HOL.eq a b : bool                -> rejected as CProp
HOL.Trueprop HOL.True : prop     -> accepted after local declaration
```

This is a real `CProp : prop` defense. The immutable-identity foundation now
also establishes:

- a deterministic, domain-separated `SignatureId` over the canonical checked
  constant declaration map;
- an ancestry-sensitive `TheoryId` over the parent ID, extension kind and
  payload, and resulting `SignatureId`;
- immutable signature/theory extension with duplicate declaration rejection;
- a `ContextStamp { TheoryId, SignatureId }` on `CTerm`, `CProp`, `KernelThm`,
  and `TrustedTheorem`;
- exact-stamp propagation through every current rule and derivation replay,
  with mixed contexts rejected before logical matching.

### What certification does not check

The current representation still has no:

- `LogicBasisId`, installed object-logic axiom, or definition certificate;
- type-constructor declaration table or arity check in the strict `Signature`;
- type-variable/sort representation distinct from ordinary concrete type
  names;
- polymorphic constant schemes or checked scheme instantiation;
- declaration provenance for `judgment`, `axiomatization`, or `definition`.

The accepted-theorem layer now records replay-derived theorem dependencies.
`DependencyKind::Axiom` and `DependencyKind::Definition` are reserved and
canonicalized, but acceptance rejects them until matching installed
certificates exist.

`RawTerm::Var` is accepted with its carried `Ty`; it is not resolved against a
schematic-variable and sort context. `Ty::base("'a")` is structurally just a
concrete name, not a checked polymorphic variable.

`Signature::extend_const` returns a fresh immutable signature and rejects both
identical and conflicting duplicates. `Signature::from_untrusted_snapshot`
recomputes the canonical digest and rejects a claimed-ID mismatch. This fixes
identity drift for the declarations the strict signature currently represents;
it does not make an ad hoc locally declared `HOL.Trueprop` an authorized HOL
judgment.

The `declared_trueprop_wraps_hol_true_as_cprop` regression still manually
installs `HOL.Trueprop : bool => prop`. It proves the type and context gates,
not production HOL declaration loading or logic-basis provenance.

## Current Theorem Acceptance

### Unique gate and token

`KernelThm` stores one exact `ContextStamp`, hypotheses, a `CProp` conclusion,
and a replayable `Derivation`. `KernelThm::try_close` checks only that the
hypothesis list is empty; it does not create a trusted value.

`TrustedTheorem` is now a private `Arc`-backed seal containing:

```text
TheoremId
fact name
ClosedThm
replay-derived DependencySet
proved-in TheoryId
accepted-in TheoryId
```

No public constructor, deserializer, raw-part assembler, or
`ClosedThm::trust` operation can create it. The only production constructor is
`accept_closed_theorem`.

### Immutable owner and fact ancestry

`TrustedTheory` is an immutable `Arc` chain. Every node stores the exact
`TheorySnapshot`, its parent owner, and at most one local accepted fact.
`begin_child`, checked declaration extension, and accepted-fact insertion
return new child values; parents and siblings remain unchanged.

Before acceptance, the owner chain is recomputed and checked against every
snapshot extension. A stored theorem must match the committed
`StoreTheorem { name, theorem_id }` extension, the parent proof context, its
dependencies, and its `accepted_in` child ID. Lookup searches ancestry, and
duplicate names are rejected rather than replaced.

### Acceptance checks and ordering

`accept_closed_theorem(&TrustedTheory, name, ClosedThm)` performs:

1. exact candidate `TheoryId` / `SignatureId` comparison;
2. immutable owner-chain consistency validation;
3. duplicate-name rejection;
4. owner-parameterized recursive replay and recertification;
5. exact replayed context, hypotheses, and conclusion comparison;
6. closedness validation on the replayed result;
7. dependency resolution against owner ancestry;
8. canonical theorem-ID computation and atomic child/token construction.

The function returns `(child_theory, accepted_token)`. This tuple is necessary:
the fact name and theorem ID are part of the immutable child `TheoryId`.

### Logical identity versus token authority

`TheoremId` and `DependencySet` are canonical logical identity data.
`DependencySet` intentionally stores a referenced theorem's `TheoremId`, not
its `accepted_in` child. This does not collapse authorization:

- `KernelRules::theorem_ref` requires the exact sealed token's `id`, fact
  `name`, and `accepted_in` value in the supplied owner ancestry;
- accepting replay repeats that exact-token check before inserting the logical
  dependency ID;
- equal theorem content accepted under different names may share a
  `TheoremId`, but the tokens are not interchangeable across sibling branches;
- a dependent theorem ID includes its own exact `ContextStamp`, so proofs built
  in distinct sibling branches remain distinct.

The digest-only `TrustedTheory::resolves` check is post-replay consistency, not
proof authority. A future persistence format must serialize and revalidate
accepted-token provenance; it must never reconstruct authority from a
`DependencySet` alone.

The strict theorem representation has no legacy `tpairs`, `shyps`, oracle, or
admit field. Those burdens are unrepresentable inside the current nucleus, but
there is still no production legacy-to-kernel conversion that proves they were
empty. Any future adapter must reject non-empty burdens rather than discard
them.

## Replay Inventory

`check_kernel_thm` remains a structural diagnostic only. Trusted acceptance
uses `replay_closed_theorem_in(owner, candidate)`, constructs a fresh
`ProofContext` from the supplied immutable owner, and recursively validates:

- every theorem conclusion and hypothesis;
- every `CProp` and `CTerm` derivation payload;
- every substitution replacement;
- cached application, abstraction, equality, and bound-variable types;
- every nested theorem before applying its logical rule.

This rejects same-stamp payloads created under a larger local-free map,
malformed cached checked terms, stale contexts, and mixed siblings. Replay has
an explicit arm for every current `Derivation` variant:

```text
TheoremRef
Assume
Reflexive
Symmetric
Transitive
BetaConversion
ForallIntr
ForallElim
ImpliesIntr
ImpliesElim
Combination
Abstraction
EqualIntr
EqualElim
SubstPremise
Generalize
Instantiate
Resolve1Match
```

The conservative `bicompose` wrapper records `Resolve1Match`. Unsupported
variants fail closed.

`TheoremRef` accepts only a non-forgeable token installed in the current
trusted ancestry, recertifies its proposition into the descendant context, and
adds its `TheoremId` to the replay-derived dependency set. Search facts carry
no proof object and cannot manufacture this derivation.

Replay still cannot validate object-logic axioms, conservative definitions, or
an authorized Isabelle/HOL bootstrap root. Those derivations and certificates
do not exist yet.

## Bypass Audit

### Boundaries that are closed

- `CProp`, `CTerm`, `KernelThm`, `OpenThm`, and `ClosedThm` constructors remain
  scoped to `crate::kernel`.
- `TrustedTheorem` has one private seal operation, called only after accepting
  replay; its private `Arc` state has no deserializer or public parts API.
- `TrustedTheory` has no public mutation or unchecked theorem insertion.
- `SearchFact::Kernel` retains only a proposition; proof extraction and
  conversion to `TrustedTheorem` are absent.
- `ProofObligation`, parser values, legacy `core::Thm`, compatibility results,
  admissions, and oracles have no conversion into the accepted token.
- The accepted classifier takes a real `TrustedTheorem`; it does not accept a
  Boolean, enum tag, theorem name, or caller-provided digest.

### Remaining authorization boundary

An upper layer may construct a content-addressed synthetic Pure root, declare
monomorphic constants, derive Pure tautologies, and submit them to acceptance.
The returned token is valid only for that exact content-addressed theory. It
does not claim that the root is the authorized Isabelle/Pure or HOL bootstrap,
and it cannot prove an arbitrary declared proposition without an axiom or
assumption.

Public source-shape metadata remains only a transitional rejection gate. It
establishes neither name resolution nor trusted provenance and cannot authorize
`KernelTrustedClosed`.

## Remaining Minimal Components

The Pure acceptance boundary is complete for current derivations. A real HOL
`KernelTrustedClosed` result still needs:

1. checked type constructors, arities, sorts, judgments, and polymorphic
   constant schemes in the immutable signature;
2. an authorized data-only logic-basis manifest and `LogicBasisId`;
3. generic replayable axiom-schema instances with exact axiom dependencies;
4. generic conservative definition certificates and dependencies;
5. parser integration plus a declaration-aware elaborator that consumes the
   implemented data-only source AST;
6. an explicit burden-complete adapter, if any legacy theorem is ever migrated.

None may be replaced by theorem names, source-shape metadata, executable HOL
validators, or caller-provided identity strings.

## Implemented Acceptance API

The kernel produces both the immutable child theory and the trusted value; the
reporting layer only classifies the token:

```rust
pub fn accept_closed_theorem(
    theory: &TrustedTheory,
    name: impl Into<Name>,
    theorem: ClosedThm,
) -> Result<(TrustedTheory, TrustedTheorem), KernelError>;
```

The theorem identity is a versioned, domain-separated SHA-256 digest over:

```text
exact ContextStamp
proposition role
burden tags
alpha-canonical checked proposition
sorted replay-derived dependencies
```

Binder display names and proof derivation structure are omitted. Constructor
tags, constant/free/variable namespaces, variable indices, all checked types,
and dependency kinds are included. A fixed-width big-endian encoder is used;
`Debug` output and platform-native integer layout are not hash inputs.

Accepted ancestor facts are reused only through:

```rust
KernelRules::theorem_ref(&TrustedTheory, &TrustedTheorem)
    -> Result<ClosedThm, KernelError>
```

The rule requires the token in the supplied owner ancestry. Accepting replay
revalidates that ancestry, recertifies the proposition in the descendant
signature, and reconstructs the theorem dependency.

Reporting now uses one exclusive outcome:

```rust
pub enum ProofOutcome {
    KernelTrustedClosed { theorem: TrustedTheorem },
    TransitionalStrictClosed { summary: TheoremSummary },
    CompatClosedOracleFree { summary: TheoremSummary },
    OpenOracleFree { reason: OpenReason, summary: TheoremSummary },
    Admitted { reason: AdmitReason, summary: TheoremSummary },
    Failed { reason: ProofFailure, name: String },
}
```

`verify_lemma` returns `LemmaVerification`, which carries an explicit optional
accepted token and optional `(legacy theorem, exit)` evidence. No thread-local
or global value participates in classification. `classify_proof_outcome` gives
an accepted token precedence over any legacy result, and
`ProofOutcomeStats::record` increments exactly one bucket.
`ProofOutcomeStats::total()` includes the kernel bucket. The production HOL
path currently supplies no token, preserving the `0/125` benchmark.

The acceptance attack suite covers wrong theory/signature, stale parents,
sibling tokens, duplicate names, tampered derivations/conclusions, same-stamp
undeclared frees, malformed checked-term caches, owner/store mismatches,
search-fact erasure, alpha-canonical IDs, dependency ordering/kinds, an
independent golden theorem-ID vector, and the distinction between equal logical
theorem IDs and non-interchangeable sibling acceptance tokens.

### Post-commit verification audit

The immutable-context baseline `38c5f14` (then `origin/dev`) and all five
candidate commits independently pass `cargo +stable check --locked` and
`scripts/check-strict-kernel.sh` when built with isolated Cargo targets.
`cargo +stable check --locked --all-targets` fails at that baseline and every
candidate with the same four pre-existing benchmark errors: two private
`Result<Thm>` argument mismatches in `benches/kernel_benchmarks.rs`. The
issues are now fixed (commit `878d8ae`); `--all-targets` passes.

## Required Implementation Order

### 1. Immutable `SignatureId` / `TheoryId` — implemented

- private, deterministic, domain-separated IDs commit to the current validated
  monomorphic signature and immutable theory ancestry;
- checked extension rejects declaration conflicts and preserves parents and
  siblings;
- exact identity propagates through certification, theorem construction, and
  replay;
- mixed contexts fail before logical matching.

### 2. Mutually exclusive kernel acceptance — implemented

- one context-bound acceptance API owns replay, dependency reconstruction,
  duplicate-safe immutable insertion, and token sealing;
- the existing Pure `A ==> A` test exercises acceptance without entering the
  HOL benchmark;
- `KernelTrustedClosed` is a real exclusive outcome, still `0/125`.

### 3. Source-aware proposition AST — data model implemented

- `src/isar/source_ast.rs` provides `SourceProposition`, `SourceExpr`,
  `SourceType`, and `SourceSyntax` as unresolved source-level data;
- `SourceName` retains exact spelling without a parser-time qualified-name,
  `Const`, `Free`, `Var`, or `Bound` classification;
- binder/operator syntax remains a raw `SourceSyntax` spelling plus span, not a
  fixed Pure/HOL semantic enum;
- `SourceSpan` is a half-open byte range `[start, end)`, while `SourceId` is a
  caller-supplied label; both are forgeable diagnostics and confer no trust;
- no `ContextStamp`, `SignatureId`, `TheoryId`, `CProp`, `ClosedThm`, or
  `TrustedTheorem` appears in the module or its public API;
- compile-fail doc-tests enforce the absence of conversions into `Term`,
  `CProp`, `ClosedThm`, `TrustedTheorem`, and `DependencySet`;
- parser integration, full-consumption binding, name/syntax resolution,
  type/sort checking, and judgment insertion are deferred to Change C2.

### 4. Checked judgment / constant / type-scheme elaboration

Use one provenance-bearing pipeline for `typedecl`, `judgment`,
`consts`/`axiomatization`, and `definition`. The first required judgment is
`HOL.Trueprop : bool => prop`; do not add a legacy string special case.

### 5. Data-only HOL logic-basis manifest

Install canonical schemas for Isabelle/HOL `refl`, `subst`, and later `ext`.
The manifest contains data only. Generic kernel code validates installation,
schema instances, context identity, and replay; no executable HOL validator or
theorem-name primitive is allowed.

### 6. Generic conservative definition extension

Implement immutable, theorem-independent `extend_definition`, checking
freshness, legal shape, closed checked RHS, self-reference, type/sort
discipline, parent dependencies, and type agreement. It returns a child theory
and replayable Pure definition theorem. Legacy `true_def_transport` is not a
certificate.

### 7. Re-derive `HOL::TrueI`

Only after the preceding gates:

```text
source-aware proposition
  -> checked CProp: HOL.Trueprop HOL.True
  -> installed refl schema
  -> conservative True_def theorem
  -> ordinary Pure transport
  -> accept_closed_theorem
  -> KernelTrustedClosed
```

`HOL::trans` remains a later reuse consumer. No `hol_subst`, second adapter,
general simplifier, or HOL-specific kernel primitive is authorized.

## Audit Conclusion

The strict nucleus now has a non-forgeable, immutable, dependency-aware
acceptance boundary for its current Pure derivations. It recursively
recertifies replay payloads, binds accepted facts to exact theory ancestry,
stores them conflict-safely, and exposes a token-backed mutually exclusive
`KernelTrustedClosed` outcome.

This does **not** make the sampled HOL theorem trusted. The remaining chain is:

```text
source proposition
  -> checked declaration-aware CProp
  -> authorized immutable HOL basis
  -> axiom and conservative-definition dependencies
  -> accepted TrustedTheorem
```

Until that chain exists, `TransitionalStrictClosed: 1/125` and
`KernelTrustedClosed: 0/125` remain the honest sampled result.
