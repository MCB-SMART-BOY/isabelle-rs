# ADR-0003: HOL Logic Trusted Extension Boundary

## Status

Proposed. This ADR defines a target boundary only. It does not authorize or
implement a HOL substitution primitive, theorem adapter, module move, or
workspace split.

## Context

ADR-0001 made `src/kernel` the new strict Pure/LCF nucleus and quarantined the
legacy `src/core` theorem engine. ADR-0002 identified a separate object-logic
layer above the kernel.

The first migrated theorem, `HOL::TrueI`, currently crosses transitional
legacy bridges for HOL object reflexivity and checked `True_def` transport. It
demonstrates the strangler path, but it must not establish a precedent of
adding each new HOL rule to `src/core::ThmKernel`.

Its `TransitionalStrictClosed: 1/125` result is represented by legacy
`core::Thm` with `ThmTrust::Strict`; it is not a
`src/kernel::TrustedTheorem` accepted into a new-kernel `TrustedTheory`. The
metric is useful migration evidence, not evidence that the target boundary is
complete.

The current sampled metrics are:

```text
TransitionalStrictClosed: 1/125
KernelTrustedClosed:      0/125
```

`KernelTrustedClosed` requires a new-kernel theorem whose conclusion is a
checked `CProp : prop`, not a bool-valued HOL term stored directly as a theorem
proposition.

The eventual equality family (`trans`, `sym`, `back_subst`, `iffD2`, and
`forw_subst`) needs the common checked elaboration and object-equality calculus.
It is not the next implementation slice. A theorem-specific `hol_subst` escape
hatch in legacy core would grow a second kernel and obscure which logical basis
is trusted.

## Decision

Adopt this target dependency and trust structure:

```text
src/kernel
  Pure/LCF theorem representation and primitive framework rules
  owns theorem internals and final theorem construction

src/logic/hol
  checked HOL signature and immutable, data-only object-logic basis manifest
  no theorem constructors, executable validators, or legacy-core dependency

src/isar
  parsing, checked elaboration, proof-language dispatch, and adapters only
  cannot fabricate theorems or define theorem-name trusted rules

src/core
  legacy compatibility, search, diagnostics, and migration quarantine
  receives no new trusted proof power
```

`src/logic/hol` is a target path; this ADR does not create or move modules in
the current monolithic crate.

## Construction Authority

The Pure kernel remains the only layer that owns theorem fields and can create
the final theorem representation. The HOL extension does not receive a raw
theorem constructor or executable validation callback. Object-logic roots must
enter through one HOL-agnostic kernel mechanism which:

- identifies the registered object logic and checked theory context;
- instantiates a named axiom schema from an immutable data manifest;
- certifies the instantiated proposition as a `CProp`;
- records a generic `LogicAxiom` derivation with manifest and axiom identity;
- lets replay reconstruct the schema instance rather than trust a proposition
  carried inside the derivation;
- preserves all theorem burdens and trust provenance.

The generic schema-instantiation and theorem-construction code is part of the
kernel code TCB. The installed HOL manifest is the explicit logical basis for a
HOL session, but it adds no executable code TCB. Audits and reports must
distinguish kernel code trust from declared object-logic assumptions.

The object-logic basis manifest must be immutable, data-oriented, and identified
by a `LogicBasisId` derived from a stable manifest hash. It must not be a
runtime callback or executable theorem factory. Generic kernel code may validate
an installed logic-basis manifest and its schema instances, but it must not
hard-code names such as `HOL.eq`, `HOL.Trueprop`, `trans`, or `subst`.

## Checked HOL Context

A HOL theory with an installed logic basis must be created from checked theory
declarations, not from searchable or admitted theorems. At minimum, equality
work requires:

```text
bool                         checked type declaration
HOL.Trueprop : bool => prop checked judgment declaration
HOL.eq : 'a => 'a => bool   checked polymorphic constant declaration
```

The context must have stable `SignatureId` and `TheoryId` values included in
derivation replay. A theorem produced under one HOL signature cannot be replayed
under an incompatible signature.

The sole object-logic identity is `LogicBasisId`. In final theorem provenance,
`None` means Pure-only ancestry; every HOL or other object-logic theorem must
carry the exact basis ID installed in its `TheoryId`, together with the basis
entries actually used. Being strict closed means there are no undischarged
local hypotheses, admissions, or oracle footprints; it does not mean the theorem
is independent of an explicit object-logic axiom basis.

Definitions, object-logic axioms, and derived theorems are distinct inputs:

- checked definitions are not theorem facts;
- axioms must be explicit derivation roots with an auditable theory source;
- derived rules must replay from strict premises;
- search facts, compatibility theorems, and admitted theorems cannot be
  promoted into the checked theory or its installed logic basis.

## HOL Equality Calculus Gate

Isabelle/HOL already fixes the logical status of equality rules. In
`theories/HOL/HOL.thy:219-222`, `refl`, `subst`, and `ext` are declared by
`axiomatization`. This migration must preserve that logical semantics:

```text
refl:  t = (t::'a)
subst: s = t ==> P s ==> P t
ext:   (!!x::'a. (f x::'b) = g x) ==> (%x. f x) = (%x. g x)
```

The open design question is their checked manifest/schema encoding, not whether
they may instead become Rust primitives or silently different derived rules.
Before installing these roots, a rule-basis contract must document:

- exact `CProp` schemas, implicit `HOL.Trueprop` positions, types, sorts, and
  direction;
- generic type and term instantiation checks;
- the relationship between bool-valued `HOL.eq` and prop-valued judgments;
- manifest, theory-context, and axiom identities;
- a generic `LogicAxiom` derivation encoding and replay algorithm;
- basis provenance in derived theorems;
- attack tests for malformed schemas, instantiations, identifiers, contexts,
  and forged replay results.

`trans`, `sym`, `ssubst`, and other equality theorems must then be derived by
applying these explicit HOL axiom schemas through Pure inference rules. This ADR
does not permit `hol_subst`, `hol_refl`, or any theorem-name equivalent as a
trusted Rust constructor in `src/logic/hol`, `src/kernel`, or `src/core`.

`HOL.eq` remains bool-valued object equality. It must never be reinterpreted as
Pure equality or mapped to a Pure equality term merely because the surface
syntax uses the same `=` glyph.

Checked definitions require a separate conservative-definition mechanism.
`True_def` must not be hidden inside an arbitrary logic-axiom manifest, and the
current theorem-specific transport bridge must not be generalized as a
substitute for that mechanism.

## Conservative Definition Gate

A generic definition extension must be logic-neutral and produce a checked
Pure equality theorem, not a theorem-specific transport operation. Installing
`c := rhs` must at least verify:

- `c` is fresh in the parent signature and no existing declaration is
  overwritten;
- `rhs` does not reference `c` directly or through an unresolved alias;
- `rhs` is closed with respect to term variables in the defining theory
  context;
- every type and sort variable in `rhs` is permitted by the declared type of
  `c`, with no extra unconstrained variables;
- the declared type and inferred RHS type agree under checked polymorphic
  instantiation and sort constraints;
- all constants and types used by `rhs` belong to the immutable parent theory;
- the result creates a fresh child `TheoryId` / `SignatureId` with an explicit
  definition dependency, rather than mutating the parent context;
- the emitted definition theorem has checked proposition
  `Pure.eq c rhs : prop` and a replayable generic definition certificate.

Using the definition theorem under `HOL.Trueprop` must proceed through ordinary
checked Pure equality/congruence rules. It must not directly convert a theorem
of `rhs` into a theorem of `c`. The existing `true_def_transport` bridge is
therefore ineligible as the template for future definitions.

## Kernel-Neutral Implementation Gates

The target boundary requires several logic-neutral capabilities. The strict
nucleus already has a private `CProp` constructor,
`ProofContext::certify_prop`, and `KernelThm { prop: CProp }`; the current
HOL/Isar migration path does not use them. Some remaining gates are absent and
others are not connected end to end. Before an extension root can produce a
new-kernel trusted theorem, designs and attack tests are required for:

- type variables, polymorphic schemes, sorts, and type-constructor arities;
- routing HOL elaboration through the existing type-level `CProp` boundary,
  with explicit tests that reject `HOL.True : bool` and `HOL.eq t u : bool`
  unless they occur under checked `HOL.Trueprop` in a proposition position;
- checked signature insertion that rejects conflicts and freezes before replay;
- source-aware proposition normalization and exact Pure/HOL syntax separation;
- derivation roots for an installed logic basis rather than arbitrary theorem
  propositions carried inside proofs;
- replay parameterized by an immutable theory and its installed `LogicBasisId`;
- propagation and recomputation of logic-basis provenance;
- an explicit policy for legacy `tpairs`, `shyps`, and oracle footprints: the
  new kernel must either represent and replay them or prove them impossible and
  empty at the migration boundary, never discard them during conversion;
- theorem provenance containing `SignatureId`, `TheoryId`, and `LogicBasisId`,
  plus used axiom identifiers and used definition identifiers;
- trusted-theory insertion that rejects conflicting theorem identities.

None of these gates may be bypassed with a fake concrete type named `'a`, a
monomorphic equality special case, or a legacy fact promoted to strict input.

The current legacy `hol_object_refl` and `true_def_transport` derivations are
transitional experiments. A theorem whose stored proposition is
`HOL.eq t t : bool` or `HOL.True : bool` is ineligible for
`KernelTrustedClosed`, regardless of its legacy `ThmTrust` flag.

## Premise and Burden Rules

Future HOL rules may accept strict open theorems as intermediate premises. This
is required for a proof such as `HOL::trans`, where equality assumptions are
introduced and later discharged with Pure implication introduction. Open is
not the same as untrusted.

Every installed logic-axiom instance and Pure derivation using it must:

- require strict checked premises in the same logic context;
- reject compatibility and admitted premises;
- allow declared open hypotheses only through ordinary Pure inference;
- preserve or union hypotheses, `tpairs`, `shyps`, and oracle footprints exactly;
- never erase an admission or upgrade trust;
- produce `KernelTrustedClosed` only after all hypotheses and burdens are
  legally discharged and replay succeeds in the same immutable context.

## Isar Adapter Boundary

An Isar strict adapter may:

- recognize a registered source proof shape;
- require typed `FullyConsumed` status plus the adapter's explicitly registered
  fail-closed source shape before any adapter-specific normalization or proof
  step;
- invoke theorem-independent checked proposition normalization;
- select checked local assumptions;
- instantiate an installed HOL axiom schema and compose it with Pure rules;
- discharge Pure implications;
- map typed failures to `NotApplicable`, `Proved`, or `Rejected`.

It may not:

- construct a theorem from a theorem name;
- accept a legacy parsed prefix, parser-recovery `Other` shape, local
  `fixes`/`includes`, locale/enclosing `Contextual` shape, or unavailable source
  proposition provenance;
- repair Free/Const or Var/Free mismatches using compatibility equality;
- invent types, constants, definitions, or object-logic axioms;
- fall back to legacy verification after a registered adapter rejects;
- add a trusted method to `src/core`.

For the current transitional `TrueI` entry, the only registered pair is
`SourcePropositionStatus::FullyConsumed` plus
`SourcePropositionShape::StandaloneHolTrueAlias`. `Other`, `Contextual`, and
`Unavailable` shapes fail closed with the same explicit source-unverified
rejection. This shape enum is temporary parser/loader metadata, not source name
resolution and not the checked proposition AST required by this ADR.

## Replay Boundary

Independent replay must cover the generic logic basis and Pure composition:

```text
LogicAxiom derivation
  -> verify checked HOL context identity
  -> load the exact immutable manifest schema
  -> recheck type/term instantiation and certify its CProp
Pure derivation nodes
  -> replay ordinary Pure kernel operations
  -> recompute proposition and all burdens
  -> compare exact checked result
```

Structural invariant checking alone is insufficient. Unsupported derivation
nodes must fail explicitly rather than be treated as replayed.

For new-kernel trusted-theory acceptance, this ADR proposes a proof-carrying
gate: every non-primitive result must replay to supported Pure primitive nodes
and installed generic `LogicAxiom` schema instances. Legacy structural-only or
unsupported derivations may remain diagnostic migration values, but cannot
become `KernelTrustedClosed`.

## Migration Sequence

Retain the hardened parser/dispatcher status-and-shape guard as transitional
fail-closed infrastructure. It is not a name-resolved AST and is not a trusted
acceptance input. Future implementation proceeds in this order:

1. [Implemented] Introduce immutable `SignatureId` / `TheoryId` values and
   propagate exact context stamps through strict certification, theorem
   construction, current rules, and replay. This does not authorize a HOL basis
   or accept a theorem.
2. Implement the unique context-bound, mutually exclusive
   `KernelTrustedClosed` acceptance gate. Exercise it first with the existing
   synthetic Pure `A ==> A` unit; do not count that unit in the 125-theorem HOL
   benchmark.
3. Preserve source proposition structure in a source-aware AST that retains
   meta/HOL connective roles, scopes, identities, spans, types/sorts, and
   implicit judgment positions.
4. Implement theorem-independent checked declaration and proposition
   elaboration as specified in
   [CHECKED_HOL_PROPOSITION_NORMALIZATION.md](CHECKED_HOL_PROPOSITION_NORMALIZATION.md),
   including checked `judgment`/constant/type-scheme resolution and explicit
   `HOL.Trueprop` insertion into the existing `CProp` boundary.
5. Encode and audit Isabelle/HOL's declared logical axiom schemas in the
   data-only HOL logic-basis manifest and implement their HOL-agnostic
   instantiation/replay boundary without expanding legacy `src/core`.
6. Implement a generic conservative definition extension, with immutable child
   theory identity and replayable certificates, before trusting `True_def`.
7. Re-derive `HOL::TrueI` as `HOL.Trueprop HOL.True`, represented by a
   context-bound new-kernel `TrustedTheorem` using a conservative `True_def`
   theorem and the installed HOL basis. This is the first eligible sampled
   `KernelTrustedClosed` HOL milestone.
8. Only after `TrueI` closes the end-to-end boundary, derive `HOL::trans` from
   installed HOL axiom instances and Pure rules as the first reuse consumer.
9. Demonstrate reuse with later equality-family theorems before adding another
   logical root.

## Rejected Alternatives

### Add `ThmKernel::hol_subst` to legacy core

Rejected because it expands the quarantined TCB and creates a competing HOL
kernel inside `src/core`.

### Add a `trans` theorem-name primitive

Rejected because it proves no framework reuse and turns adapters into theorem
fabricators.

### Put HOL semantics in the Pure kernel

Rejected because the Pure kernel must remain reusable and independent of one
object logic.

### Treat a legacy parsed or builtin theorem as the substitution axiom

Rejected because searchable, compatibility, or admitted facts are not checked
logical roots.

### Split crates before the boundary is implemented

Rejected for the current phase because it would freeze an untested dependency
boundary. The module and rule contracts must stabilize first.

## Consequences

- The Pure kernel TCB stays logic-neutral.
- A HOL session has an explicit additional trusted surface that can be audited
  separately.
- The current `HOL::TrueI` bridges remain transitional debt; they are not a
  template for expanding `src/core`.
- `HOL::trans` remains blocked until checked proposition elaboration, an
  authorized immutable HOL context, conservative definitions, the replayable
  HOL basis, and a real new-kernel `HOL::TrueI` loop all exist.
- Transitional coverage may remain `1/125` and kernel-trusted coverage `0/125`
  while these boundaries are built. That is preferable to increasing either
  count through unverifiable trusted shortcuts.
