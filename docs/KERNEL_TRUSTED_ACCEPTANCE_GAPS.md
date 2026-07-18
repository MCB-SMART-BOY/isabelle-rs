# Kernel-Trusted Acceptance Gaps

## Status

Audit and implementation gate only. This document adds no theorem constructor,
HOL adapter, object-logic axiom, definition rule, or proof power.

Read root [AGENTS.md](../AGENTS.md), then
[PROJECT_STATUS.md](PROJECT_STATUS.md) and [TRUST.md](TRUST.md), before using
this audit as an implementation plan.

Current sampled status remains:

```text
TransitionalStrictClosed: 1/125
KernelTrustedClosed:      0/125
```

`TransitionalStrictClosed` is a mutually exclusive legacy-verifier outcome.
Until a context-bound kernel acceptance outcome exists,
`ProofOutcomeStats::kernel_trusted_closed` is only a separately reported overlay
and is excluded from `ProofOutcomeStats::total()`.

## Scope

This audit covers the current strict path:

```text
RawTerm
  -> Signature + ProofContext
  -> CTerm / CProp
  -> KernelRules
  -> KernelThm
  -> ClosedThm
  -> ClosedThm::trust
  -> TrustedTheorem
  -> TrustedTheory::add
```

It answers four questions:

1. what `ProofContext::certify_prop` currently establishes;
2. what `TrustedTheorem`, `ClosedThm::trust`, and `TrustedTheory::add` currently
   check;
3. which derivations replay and which theory dependencies are represented;
4. whether parser, legacy `core::Thm`, or search facts can bypass the strict
   constructors.

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

This is a real `CProp : prop` defense. It is not yet evidence that
`HOL.Trueprop` came from Isabelle/HOL's checked theory.

### What certification does not check

The current representation has no:

- `SignatureId`, `TheoryId`, or `LogicBasisId`;
- type-constructor declaration table or arity check in the strict `Signature`;
- type-variable/sort representation distinct from ordinary concrete type
  names;
- polymorphic constant schemes or checked scheme instantiation;
- declaration provenance for `judgment`, `axiomatization`, or `definition`;
- context identity stored in `CTerm` or `CProp`.

`RawTerm::Var` is accepted with its carried `Ty`; it is not resolved against a
schematic-variable and sort context. `Ty::base("'a")` is structurally just a
concrete name, not a checked polymorphic variable.

`Signature::declare_const` and `ProofContext::declare_free` mutate maps and
silently replace an existing entry. `Signature` is cloneable and has no frozen
state or digest. Consequently, two certified values do not record whether they
came from the same signature, and later rules cannot reject mixed-context
inputs by identity.

The current `declared_trueprop_wraps_hol_true_as_cprop` regression manually
installs `HOL.Trueprop : bool => prop` into a local `Signature`. This proves the
type gate, not production HOL declaration loading or immutable HOL provenance.

## Current Theorem Acceptance

### `TrustedTheorem`

`src/kernel/thm.rs::KernelThm` stores only:

```text
hyps: Vec<CProp>
prop: CProp
derivation: Derivation
```

`KernelThm::try_close` checks only that `hyps` is empty.
`ClosedThm::trust` calls `invariant::check_kernel_thm` and then wraps the value in
`TrustedTheorem`. The current `TrustedTheorem` is a tuple wrapper around
`ClosedThm`; it stores no theory, signature, logic-basis, axiom, definition, or
theorem-dependency identity.

The current name therefore means "closed and successfully replayed by the
context-free strict nucleus", not yet "accepted in an immutable Isabelle/Pure
or HOL theory context".

The strict theorem representation has no legacy `tpairs`, `shyps`, or oracle
field. This makes those burdens unrepresentable inside the current nucleus, but
there is also no production legacy-to-kernel conversion that proves they were
empty before migration. Any future conversion must reject non-empty burdens;
it must not discard them.

### `TrustedTheory::add`

`src/kernel/theory.rs::TrustedTheory` is a mutable
`HashMap<Name, TrustedTheorem>`. `TrustedTheory::add`:

- performs no replay;
- performs no theory/signature identity check;
- performs no dependency or ancestry check;
- performs no proposition recertification;
- returns no error;
- silently replaces an existing theorem with the same name.

Thus `TrustedTheory::add` is type-gated but is not the final trusted acceptance
API.

### No unique closed-theorem gate

The current flow has two independent public operations:

```text
ClosedThm::trust() -> TrustedTheorem
TrustedTheory::add(name, TrustedTheorem)
```

Neither receives a theory context. There is no single operation that can
establish all requirements for `KernelTrustedClosed`.

## Replay Inventory

`src/kernel/invariant.rs::check_kernel_thm` currently:

1. checks that every hypothesis and the conclusion has type `prop`;
2. recursively replays the stored derivation;
3. compares the replayed hypotheses and proposition with the theorem fields.

`replay_derivation` has an explicit arm for every current `Derivation` variant:

```text
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

The conservative `bicompose` wrapper records `Resolve1Match`, so it reuses that
arm. Unsupported strict derivation variants do not currently exist in the enum.

The replay is nevertheless context-free. It cannot check:

- the signature under which a `CTerm` or `CProp` was certified;
- theory ancestry;
- theorem references, because there is no theorem-reference derivation;
- object-logic axioms, because there is no `LogicAxiom` derivation;
- conservative definitions, because there is no definition certificate or
  derivation;
- basis or definition dependency propagation;
- replay under the same immutable context that produced the theorem.

All current replay roots are Pure rule data already embedded in the derivation.
This is enough for the existing synthetic Pure rule tests, but not for a HOL
root or `HOL::TrueI`.

## Bypass Audit

### Boundaries that are already closed

- `CProp` and `CTerm` constructors are scoped to `crate::kernel`; parser, HOL,
  Isar, and legacy core cannot directly wrap a `Term`.
- `KernelThm`, `OpenThm`, and `ClosedThm` constructors are scoped to
  `crate::kernel`; upper layers must use `KernelRules`.
- `ProofObligation` has no conversion into a theorem.
- `TryFrom<SearchFact> for TrustedTheorem` always returns
  `KernelError::SearchFactNotTrusted`, including for `SearchFact::Kernel`.
- Production code outside `src/kernel` currently has no conversion from legacy
  `core::Thm` or parser values into `TrustedTheorem` or `TrustedTheory`.

### Remaining acceptance gap

An upper layer may legitimately create its own mutable `Signature`, declare a
name such as `HOL.Trueprop` with a chosen type, certify a proposition, derive a
closed Pure theorem, call `ClosedThm::trust`, and store it in `TrustedTheory`.
That path does not forge kernel rule replay, but it does demonstrate why the
current value cannot be reported as context-bound HOL trust: the declaration
and theory identities are not part of the theorem.

The public, forgeable `SourcePropositionStatus`, `SourcePropositionShape`,
`DefLocation`, and `ParsedLemma` fields are only transitional fail-closed
metadata. They establish neither name resolution nor trusted provenance and
must never authorize `KernelTrustedClosed`.

## Missing Minimal Components

A real `KernelTrustedClosed` result needs all of the following:

1. **Immutable signature identity.** Checked type constructors, arities, sorts,
   judgments, constant schemes, and definitions produce a content-addressed
   `SignatureId`. Conflicting insertion fails; parent values never mutate.
2. **Immutable theory identity.** A `TheoryId` commits to its parent,
   `SignatureId`, installed logic-basis manifests, axiom declarations, and
   conservative definition certificates.
3. **Context propagation.** `ProofContext`, `CTerm`, `CProp`, `KernelThm`, and
   `TrustedTheorem` carry or unforgeably reference the relevant identity. Pure
   rules reject incompatible contexts instead of combining them.
4. **Dependency provenance.** Derivations record the exact object-logic axiom,
   definition, and theorem dependencies they use; replay recomputes the set and
   verifies every dependency belongs to the accepted theory ancestry.
5. **Context-parameterized replay.** Replay receives the immutable theory and
   resolves schemas/certificates from it. A derivation valid in one signature
   must fail in an incompatible context.
6. **One acceptance API.** Only a successful context-bound replay can produce
   the token counted as `KernelTrustedClosed`.
7. **Conflict-safe storage.** The trusted table rejects duplicate/conflicting
   theorem names and never overwrites silently.
8. **Migration burden gate.** Any future legacy adapter proves that hypotheses,
   unresolved constraints, `tpairs`, `shyps`, and oracle/admit footprints are
   absent; no field is dropped during conversion.

## Recommended Minimal Acceptance API

The kernel should produce the trusted value; the reporting layer should only
classify it:

```rust
pub fn accept_closed_theorem(
    theory: &TrustedTheory,
    theorem: ClosedThm,
) -> Result<TrustedTheorem, KernelError>;
```

`ProofOutcome::KernelTrustedClosed` then owns that returned
`TrustedTheorem`. It is not a second constructor or a Boolean status flag.
Passing `TrustedTheorem` *into* acceptance would preserve the current naming
problem: a value would be called trusted before the unique context gate checked
it.

Before this API is added, the theorem path must carry context identity
conceptually as follows:

```rust
pub struct KernelThm {
    theory_id: TheoryId,
    signature_id: SignatureId,
    dependencies: DependencySet,
    // private hypotheses, proposition, and derivation
}

pub struct TrustedTheorem {
    theory_id: TheoryId,
    signature_id: SignatureId,
    logic_basis_id: Option<LogicBasisId>,
    dependencies: DependencySet,
    theorem: ClosedThm,
}
```

`logic_basis_id` is `None` only for Pure-only ancestry. Every HOL or other
object-logic theorem must carry the exact `LogicBasisId` installed in its
theory. IDs have private constructors and come from canonical,
domain-separated hashes of validated data, not caller-provided strings.

`accept_closed_theorem` rejects unless:

- the theorem's `TheoryId` and `SignatureId` exactly match the supplied theory;
- the conclusion is a `CProp : prop` certified under that signature;
- the theorem has no undischarged hypotheses or unresolved obligations;
- every recorded axiom, definition, and theorem dependency belongs to that
  theory or its ancestry;
- context-parameterized replay succeeds for every derivation node and exactly
  reproduces proposition, burdens, context identity, and dependencies;
- no compatibility, admission, search-fact, or legacy theorem value entered the
  construction path.

`ClosedThm::trust` must become internal or be removed; it cannot remain an
alternative context-free producer of the final trusted type. Trusted theorem
storage must separately reject context mismatch and duplicate/conflicting names
without manufacturing another acceptance path.

After this gate exists, reporting uses one mutually exclusive outcome per
attempt:

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

Only `KernelTrustedClosed` increments the kernel count. A theorem cannot also
increment `TransitionalStrictClosed`. Until then, the kernel counter remains an
overlay excluded from the legacy attempted total.

### First bounded implementation sequence

Land this sequence as two separately reviewed changes.

**Change A — immutable identity (immediate next action):**

1. Add private, deterministic, domain-separated `SignatureId` and `TheoryId`
   values for the current validated strict signature and its immutable Pure
   root theory. Conflicting declaration extension returns an error; no map
   overwrite may preserve an old identity.
2. Propagate both IDs through `ProofContext`, `CTerm`/`CProp`, `KernelThm`, and
   every multi-premise rule. Reject mismatched IDs before comparing terms or
   combining hypotheses.
3. Add deterministic-ID, wrong-signature certification, mixed-context rule,
   conflicting-declaration, and parent-immutability attacks.
4. Do not add the acceptance API, change `ProofOutcome`, or alter any sampled
   metric in this change.

**Change B — unique acceptance (only after Change A passes review):**

1. Replace public context-free `ClosedThm::trust` with
   `accept_closed_theorem(&TrustedTheory, ClosedThm)`.
2. Parameterize replay by the immutable context and make theorem-table
   insertion return typed duplicate/context-conflict errors instead of silently
   replacing entries.
3. Exercise correct-context acceptance with the existing Pure `A ==> A`
   derivation and reject wrong theory, wrong signature, and duplicate names.
4. Make `KernelTrustedClosed` a mutually exclusive outcome that owns the
   accepted theorem.
5. Do not connect the synthetic Pure unit to the 125-theorem HOL benchmark. The
   sampled result remains `KernelTrustedClosed: 0/125`.

Neither change adds a source parser, HOL manifest, polymorphic scheme,
definition, or theorem adapter. Those follow only after context identity and
acceptance are unforgeable.

## Required Implementation Order

### 1. Immutable `SignatureId` / `TheoryId`

- derive private, deterministic, domain-separated IDs from canonical validated
  data for the current strict monomorphic signature and immutable Pure root;
- replace mutable overwriting declaration insertion with checked monotonic
  extension and a fresh child ID;
- propagate identity through certification and strict theorem construction;
- reject mixed-context rule inputs and conflicting declarations;
- version the canonical encoding so later checked sorts and polymorphic schemes
  extend the model without identity ambiguity;
- add deterministic-ID, wrong-context, and parent-immutability attack tests.

### 2. Mutually exclusive kernel acceptance

- implement the single context-bound acceptance API;
- parameterize replay by the immutable theory;
- make trusted-table insertion conflict-safe;
- use the Pure `A ==> A` unit only to exercise acceptance;
- replace the temporary metric overlay with a real exclusive
  `ProofOutcome::KernelTrustedClosed` variant.

### 3. Source-aware proposition AST

Preserve before legacy `CTerm` lowering:

```text
meta implication versus HOL implication
Pure equality versus HOL.eq
source spans and binder scopes
Const / Free / Var / Bound identity
explicit types and sorts
notation and name-resolution provenance
implicit HOL.Trueprop positions
```

The existing source status/shape metadata remains only a transitional rejection
gate.

### 4. Checked judgment / constant / type-scheme elaboration

Use one provenance-bearing declaration pipeline for `typedecl`, `judgment`,
`consts`/`axiomatization`, and `definition`. Do not add a `HOL.Trueprop` string
special case to legacy `HolTheoremDb::build_type_env`.

The first required judgment is the Isabelle/HOL declaration:

```text
HOL.Trueprop : bool => prop
```

The elaborator resolves checked schemes, solves shared type/sort constraints,
inserts `HOL.Trueprop` only at parser-recorded proposition positions, preserves
the source skeleton, and returns `CProp` without constructing a theorem.

### 5. Data-only HOL logic-basis manifest

The repository and upstream Isabelle/HOL source both declare:

```text
HOL.thy:90       judgment Trueprop :: bool => prop
HOL.thy:92-94    HOL.eq :: ['a, 'a] => bool
HOL.thy:219-222  refl, subst, ext by axiomatization
```

At minimum, the first milestones need faithful schemas for `refl` and `subst`.
The manifest contains only canonical checked schema data and stable identifiers:
no function pointers, closures, callbacks, theorem factories, or executable HOL
validator. Generic kernel code validates schema installation, instantiation,
context identity, and replay through a generic `LogicAxiom` derivation.

`refl`, `subst`, and `ext` must retain their Isabelle/HOL logical status. They
must not become `ThmKernel::hol_refl`, `hol_subst`, theorem-name primitives, or
silently derived replacements.

### 6. Generic conservative definition extension

Implement theorem-independent `extend_definition` over immutable parent theory
data. It checks freshness, legal left-hand side shape, checked and closed RHS,
absence of direct or indirect self-reference, type-variable/sort discipline,
parent-theory dependencies, and exact declared/RHS type agreement. It returns a
child theory and a replayable Pure definition theorem:

```text
|- c == rhs
```

The current legacy `true_def_transport` and `CheckedDefinitionSource` are not
valid final certificates.

### 7. Re-derive `HOL::TrueI`

Only after the preceding gates:

```text
source-aware TrueI proposition
  -> checked elaboration
  -> CProp: HOL.Trueprop HOL.True
  -> installed HOL refl schema instance
  -> conservative True_def theorem
  -> ordinary Pure equality/congruence transport
  -> context-bound TrustedTheorem
  -> accept_closed_theorem
  -> KernelTrustedClosed
```

### 8. `HOL::trans` only as a later reuse consumer

Only after the `HOL::TrueI` chain reaches `KernelTrustedClosed: 1/125` may
`HOL::trans` reuse the same source AST, elaborator, immutable HOL theory,
installed `subst` axiom schema, dependency replay, and acceptance operation.
`hol_subst`, a second theorem adapter, general simplification, and new
kernel/core HOL primitives remain prohibited.

## Audit Conclusion

The current strict nucleus already prevents direct bool-as-proposition and
public theorem-constructor attacks, and it fully replays every derivation variant
it currently records. The blocking gap is semantic context, not another local
`CProp` wrapper:

```text
source proposition
  -> checked declaration-aware CProp
  -> immutable theory/signature/logic basis
  -> context-parameterized replay
  -> unique trusted acceptance
```

Until that chain exists, `ClosedThm::trust` and `TrustedTheory::add` are useful
strict-kernel experiments but are insufficient evidence for sampled
`KernelTrustedClosed` progress.
