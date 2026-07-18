# Checked HOL Proposition Normalization

## Status

Design and diagnostic only. No production normalizer, theorem adapter, HOL
substitution rule, or trusted primitive is implemented by this document.

The targeted diagnostic case is the proposition of `HOL::trans`:

```isabelle
lemma trans: "\<lbrakk>r = s; s = t\<rbrakk> \<Longrightarrow> r = t"
  by (erule subst)
```

This document defines a theorem-independent parser-to-checked-term boundary. It
does not authorize a `try_strict_hol_trans` adapter or increase either
`TransitionalStrictClosed: 1/125` or `KernelTrustedClosed: 0/125`. The first HOL
trust milestone remains re-deriving `HOL::TrueI` through the new kernel; `trans`
is an eventual reuse consumer after the wider theory/logic gates close.

## Boundary

Normalization accepts untrusted parsed syntax plus checked signature and proof
context inputs. Its only output is a checked proposition and normalization
provenance:

```text
untrusted parsed proposition
  + checked HOL signature
  + checked free/type-variable context
  -> typed normalization
  -> checked, dummy-free proposition
```

Normalization is elaboration, not proof. It must not:

- construct a theorem;
- invoke a theorem adapter;
- admit a proposition;
- use a compatibility theorem as evidence;
- use Free/Const or Var/Free compatibility matching;
- silently change connective nesting, premise order, or operand identity.

The current legacy `CTerm` is not a sufficient long-term input by itself.
`ParsedLemma` retains the compatibility theorem but not a source proposition
AST with name-resolution and type-annotation provenance. A general future
boundary therefore needs source-aware parsed roles, or an equivalent exact
structural-role witness, until checked elaboration succeeds or returns a typed
error.

### Current status/shape gate

The transitional parser boundary now records both whether the legacy parser
consumed all input presented to it and a deliberately narrow source shape:

```text
parse_term(input)
  -> compatibility API; may return a parsed prefix

parse_term_with_status(input)
  -> (term, FullyConsumed | Incomplete)

source loader
  -> SourcePropositionStatus::{FullyConsumed, Incomplete, Unavailable}
  -> SourcePropositionShape::{StandaloneHolTrueAlias, Other, Contextual, Unavailable}
```

`ParsedLemma` retains both typed values with its source-location provenance;
absence of source provenance makes both `Unavailable`. For the registered
`TrueI` adapter with an explicit proof, only
`FullyConsumed + StandaloneHolTrueAlias` may reach proposition normalization
or the adapter proof body. Every other combination becomes
`Rejected(SourcePropositionUnverified { status, shape })` and is recorded as
`admitted:strict_adapter_source_prop_unverified`; they do not become
`admitted:parser_gap` and do not enter legacy proof fallback.

The current accepted shape is limited to a standalone source `True` or
`HOL.True`, optionally annotated `:: bool`. Parser recovery of malformed
`True =` can still report `FullyConsumed`, but its shape is `Other`. A lemma
with local `fixes` or `includes`, a locale qualifier, or an enclosing source
context is `Contextual`, even if its parsed legacy term is the same canonical
`HOL.True`.

This is a transitional fail-closed guard, necessary but not sufficient for
future trusted elaboration. `FullyConsumed` says only that the compatibility
parser reached EOF after its converted input, and the shape enum is only a
lexical/context classification for the current adapter. Neither proves that
source conversion preserved every syntax role, resolves whether `True` is
shadowed, or supplies a checked `CProp`. Both values are public metadata carried
by the current `ParsedLemma` / `DefLocation` representation, not a
name-resolved AST or unforgeable certification token. The source-aware AST and
provenance contract below remains required.

The current `TransitionalStrictClosed: 1/125` value is a migration metric over legacy
`core::Thm` plus `ThmTrust::Strict`. A successful legacy
`CTerm::certify_checked` normalization would improve that migration boundary,
but it would not yet be a new-kernel `CProp` or `TrustedTheorem`.

## Targeted `HOL::trans` Diagnostic

Source declarations:

- `theories/HOL/HOL.thy:90` declares
  `judgment Trueprop :: "bool => prop"`.
- `theories/HOL/HOL.thy:92-94` declares polymorphic `HOL.eq` with shape
  `['a, 'a] => bool`.
- `theories/HOL/HOL.thy:274-275` declares and proves `trans`.

The current parser produces this raw skeleton, with no `HOL.Trueprop`
applications:

```text
Pure.imp
  (HOL.eq r s)
  (Pure.imp
    (HOL.eq s t)
    (HOL.eq r t))
```

The exact debug form is:

```text
((Pure.imp ((HOL.eq r) s))
  ((Pure.imp ((HOL.eq s) t)) ((HOL.eq r) t)))
```

Current type state:

| Node class | Count | Current annotation |
|---|---:|---|
| `Pure.imp` heads | 2 | fully typed `prop => prop => prop` |
| `HOL.eq` heads | 3 | `dummy => dummy => bool` |
| Free occurrences | 6 | `r`, `s`, and `t` each occur twice as `Free(_, dummy)` |

There are 9 dummy-bearing nodes and 12 dummy type leaves. The top-level legacy
CTerm reports type `prop`, compatibility certification, and residual dummy
types.

Failure sequence:

1. `Term::type_annotate` reports no change. It only replaces an annotation
   which is wholly `Typ::dummy()`; it does not instantiate dummy leaves inside
   the equality function type, and `r`/`s`/`t` have no declarations.
2. Direct `CTerm::certify_checked` first rejects the parsed `HOL.eq` head with a
   type mismatch between the checked polymorphic declaration and
   `dummy => dummy => bool`.
3. Manually assigning a single shared polymorphic operand type and the checked
   equality signature is still insufficient: `Pure.imp` expects `prop`, while
   each equality produces `bool`.
4. Inserting `HOL.Trueprop` around all three equality formulas then fails with
   `UndeclaredConstant("HOL.Trueprop")`. `HolTheoremDb::build_type_env` does not
   currently extract `judgment` declarations.
5. In the diagnostic only, registering checked
   `HOL.Trueprop : bool => prop`, using one shared polymorphic type for
   `r`/`s`/`t`, and wrapping all three equality formulas produces a checked
   proposition of type `prop` with no dummy annotations.

The diagnostic runner was temporary and was removed. No diagnostic runner is
kept in ordinary tests.

A separate sampled diagnostic shows why the legacy term is insufficient for a
general normalizer:
`HOL::meta_eq_to_obj_eq` starts with a Pure equality premise `(A == B)` in the
source but its current parsed term degrades to `A ==> A = B`. A later
normalizer cannot safely reconstruct whether the lost connective was
`Pure.eq`, `HOL.eq`, or something else from that legacy term.

## Normalization Contract

### Checked declarations

- `HOL.eq` must resolve as an exact constant through the checked HOL signature.
- Its declared scheme must instantiate to `alpha => alpha => bool` for each
  equality occurrence.
- `HOL.Trueprop` must come from the checked `judgment` declaration with exact
  type `bool => prop`; the normalizer must not synthesize an undeclared trusted
  constant.
- In the transitional legacy projection, `Pure.imp` is an exact checked
  meta-implication constant with type `prop => prop => prop`. The target
  `src/kernel` representation uses its native `RawTerm::Imp` / `Term::Imp`
  constructors instead. The semantic `MetaImp` node and its `prop` operands
  must be preserved without requiring one shared internal encoding.
- A parsed Free called `HOL.eq`, `eq`, `Trueprop`, or `Pure.imp` is not a constant
  alias and must be rejected.

### Type constraints

- Repeated occurrences of the same parsed free have one exact identity and one
  type assignment. Same spelling alone is not enough if parser scopes differ.
- For `HOL::trans`, constraints from `r = s`, `s = t`, and `r = t` must solve
  `type(r) = type(s) = type(t) = alpha`, with the required checked sort on
  `alpha`.
- Explicit source type annotations, once preserved by the parser, constrain the
  same graph and cannot be discarded or overwritten.
- Conflicting types are typed errors. A type that is neither constrained by a
  checked declaration/context nor generalizable under an explicit checked
  sort policy is also an error. No residual `Typ::dummy()` may reach the result.
- Fresh polymorphic variables must be allocated deterministically in a checked
  proof context, not auto-declared by scanning raw Free nodes.

### Proposition embedding

- A surface HOL formula in a meta-proposition position is embedded using the
  checked `HOL.Trueprop` declaration.
- For `HOL::trans`, exactly the two premises and final equality conclusion are
  embedded. The two existing `Pure.imp` nodes and their order are preserved.
- Embedding must be driven by parsed proposition roles/provenance. It must not
  reinterpret an arbitrary bool-typed legacy term as a proposition after the
  fact.

### Skeleton preservation

Normalization may only:

- qualify a parser-recorded constant alias to its checked canonical name;
- instantiate checked type schemes and fill recorded type holes;
- insert the parser-recorded implicit `HOL.Trueprop` judgment boundary.

After erasing these permitted annotations and `HOL.Trueprop` wrappers, a
structural projection of the result must equal the parsed projection. For
`HOL::trans`, that projection is exactly:

```text
MetaImp(HolEq(r, s), MetaImp(HolEq(s, t), HolEq(r, t)))
```

The comparison is exact over node kind, constant identity, free identity,
application structure, and premise order. It is not alpha matching and does
not use legacy compatibility equivalence.

### Result invariants

A successful future API result must satisfy all of the following:

- checked certification;
- top-level type `prop`;
- no dummy type at any depth;
- every constant present in the checked signature;
- every free and type variable present in the checked context;
- a recorded skeleton-preservation check;
- no theorem value, oracle, admission, hypothesis, or proof outcome produced.

The targeted legacy diagnostic established checked type `prop` and absence of
dummy annotations. It did not establish the stronger future requirement that
every Free and type variable be registered in an explicit checked context;
current legacy `core::CTerm::certify_checked` does not enforce that for every
fully annotated Free.

## Proposed Typed API

The names are design placeholders, not current production APIs. Their
design-only standalone Rust skeleton is maintained in
[checked_hol_proposition_normalization.rs](../scripts/templates/checked_hol_proposition_normalization.rs);
compilation does not validate it against production types or trust semantics.

The operation is deliberately not named `normalize_trans_prop`.

The same template contains the proposed typed failure enum. Control flow must
depend only on its variants and fields.

Control flow depends only on variants and fields. `KernelError` and display
messages are diagnostic payloads; no caller may classify an error by matching
message text.

## Required Parser and Signature Work

Before this normalizer can be implemented safely, the parser/signature boundary
must provide:

1. mandatory full-consumption provenance and a proposition AST that
   distinguishes meta connectives from HOL formulas;
2. exact source symbol identity and scope for Const, Free, and Var nodes;
3. preserved explicit type annotations instead of discarding `::` syntax;
4. checked extraction of `judgment` declarations, beginning with
   `HOL.Trueprop : bool => prop`;
5. deterministic polymorphic constraint solving anchored in checked constant
   schemes;
6. a skeleton projection and source-to-normalized provenance record.

The proposed API must not accept a theorem name, proof script, search fact, or
`HolTheoremDb` fact as type or name-resolution evidence. The legacy parsed
theorem may be cross-checked for migration diagnostics, but cannot repair the
source representation.

The current strict `src/kernel` also needs an explicit design for polymorphic
type schemes and logic-extension context before the eventual result can flow
as a new-kernel proposition. A legacy `core::CTerm::certify_checked` success is
useful migration evidence, but it is not by itself the final
`src/kernel::TrustedTheorem` boundary.

## Future Tests

Implementation must be preceded or accompanied by tests that:

- accept a checked equality implication chain with one shared polymorphic type;
- accept and preserve a consistent explicit source type annotation;
- reject a Free pretending to be `HOL.eq`, `HOL.Trueprop`, or `Pure.imp`;
- reject Var/Free and Free/Const same-name substitutions;
- reject inconsistent types across the equality chain;
- reject a wrong or missing `HOL.Trueprop` declaration;
- reject a wrong `HOL.eq` declaration;
- reject residual dummy types;
- reject reordered, dropped, or duplicated premises;
- reject a changed equality operand;
- reject an unconsumed source suffix even when the parsed prefix has the
  expected theorem shape;
- reject unavailable source proposition provenance at a registered adapter;
- reject a fully consumed parser-recovery shape such as malformed `True =`;
- reject local `fixes` / `includes`, locale-qualified, and enclosing-context
  `True` sources until checked name resolution exists;
- prove that changing error display text does not change typed classification;
- return no theorem and add no proof power.

## Non-Goals

This design does not implement:

- `try_strict_hol_trans`;
- HOL substitution, symmetry, or transitivity;
- general simp or unfolding;
- resolution, lifting, freshening, or broad unification;
- a theorem-name normalization table;
- a new `src/core` or `src/kernel` primitive;
- a workspace or module migration.

The future trusted object-logic boundary is proposed separately in
[ADR-0003-hol-logic-trusted-extension.md](ADR-0003-hol-logic-trusted-extension.md).
