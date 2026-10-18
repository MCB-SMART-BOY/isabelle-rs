# Checked HOL Proposition Normalization

## Status

The data-only `source_ast` and a separate, narrow, fully consuming
`source_parser` → declaration-aware `elaborator` → strict `CProp` path are
implemented for the two standalone fixtures and the audited sampled
`HOL::TrueI` projection. The general sampled-HOL normalizer described below
(including polymorphic equality, source-role provenance, and `HOL::trans`)
remains a design, not a production adapter. Neither the narrow source
pipeline nor the sampled `TrueI` adapter implements general HOL/ATP
elaboration or an additional trusted primitive.

The targeted diagnostic case is the proposition of `HOL::trans`:

```isabelle
lemma trans: "\<lbrakk>r = s; s = t\<rbrakk> \<Longrightarrow> r = t"
  by (erule subst)
```

This document specifies the wider theorem-independent parser-to-checked-term
boundary needed for other sampled HOL theorems. It does not authorize a
`try_strict_hol_trans` adapter or count additional sampled theorem tokens.
In the 2026-10-07 bundled-source sample, the audited `HOL::TrueI` projection
alone reached `KernelTrustedClosed: 1/125` with
`TransitionalStrictClosed: 0/125`. Standalone source-backed `TrueI` and Pure
identity receive separate tokens outside that 125-lemma sample. The later
P2/P3/P4 native closure implementation was resumed under the reviewed P1
contracts, but has not rerun this sample or established broader HOL acceptance;
see [PROJECT_STATUS.md](../status/PROJECT_STATUS.md) for current verification scope.

`src/isar/source_ast.rs` deliberately stores raw names/syntax and diagnostic
spans only. The narrow elaborator resolves supported names and certifies
`CProp`; the AST itself carries no trusted context or authority.

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

Two distinct consumers must not be conflated:

```text
legacy parse_term(input) -> Some(term) only on FullyConsumed input
legacy parse_term_with_status(input) -> (term, FullyConsumed | Incomplete)
legacy HOL search loader -> SourcePropositionStatus and SourcePropositionShape
strict source_parser + elaborator -> checked CProp for supported source syntax
```

The legacy `ParsedLemma` retains the source status and shape metadata with
diagnostic locations; absent source provenance yields `Unavailable`. The
sampled `TrueI` adapter with an explicit proof requires
`FullyConsumed + StandaloneHolTrueAlias`; other combinations are rejected as
`SourcePropositionUnverified` and cannot become proof via a fallback. The
shape accepts standalone `True` / `HOL.True`, optionally `:: bool`, but not
contextual variants. Malformed input such as `True =` now fails the public
`parse_term` instead of returning a success-shaped prefix; the diagnostic
`parse_term_with_status` can still report `Incomplete`.

These shape/status fields are a transitional, forgeable classification, not a
checked source proposition. The strict compiler parses and elaborates
supported syntax against `ProofContext`; the sampled `TrueI` projection
audits the required bundled source declarations and proof before owner replay.
Neither path executes unrelated HOL/ML commands or implements the general
HOL equality implication-chain normalization below. The historical
2026-10-03 `TransitionalStrictClosed: 1/125` was a legacy `core::Thm` metric,
never a strict-kernel `TrustedTheorem`.

## Targeted `HOL::trans` Diagnostic

Source declarations:

- `theories/HOL/HOL.thy:90` declares
  `judgment Trueprop :: "bool => prop"`.
- `theories/HOL/HOL.thy:92-94` declares polymorphic `HOL.eq` with shape
  `['a, 'a] => bool`.
- `theories/HOL/HOL.thy:274-275` declares and proves `trans`.

The historical legacy parsed-term diagnostic produced this raw skeleton,
without `HOL.Trueprop` applications:

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

Legacy diagnostic type state (not a strict source fixture):

| Node class | Count | Current annotation |
|---|---:|---|
| `Pure.imp` heads | 2 | fully typed `prop => prop => prop` |
| `HOL.eq` heads | 3 | `dummy => dummy => bool` |
| Free occurrences | 6 | `r`, `s`, and `t` each occur twice as `Free(_, dummy)` |

There are 9 dummy-bearing nodes and 12 dummy type leaves. The top-level legacy
CTerm reports type `prop`, compatibility certification, and residual dummy
types.

Historical diagnostic failure sequence:

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

The historical `HOL::trans` diagnostic established checked legacy type `prop`
and absence of dummy annotations only after manual declaration/embedding. It
did not establish registered source Free/type-variable identity or a general
sampled-HOL elaborator. The strict `ProofContext` does validate declared types,
constants and local frees; its separate narrow elaborator does not infer the
polymorphic equality chain described here.

## Proposed Typed API

The names are design placeholders, not current production APIs. Their
design-only standalone Rust skeleton is maintained in
[checked_hol_proposition_normalization.rs](../../scripts/templates/checked_hol_proposition_normalization.rs);
compilation does not validate it against production types or trust semantics.

The operation is deliberately not named `normalize_trans_prop`.

The same template contains the proposed typed failure enum. Control flow must
depend only on its variants and fields; `KernelError` and display messages are
diagnostic payloads, not strings for branching.

## Required Parser and Signature Work

Before a general sampled-HOL normalizer can be implemented safely, its
source/parser/signature boundary must:

1. connect fully consuming source parsing to the sampled theorem's exact
   proposition and proof, without treating forgeable `SourceId`/spans as trust;
2. resolve raw source syntax under the applicable theory's syntax tables so
   meta connectives and HOL formulas remain distinguishable;
3. resolve exact source symbol identity and scope for Const, Free, Var, and
   Bound nodes, with full type-annotation preservation;
4. load checked `judgment` declarations, including
   `HOL.Trueprop : bool => prop`, from that source theory;
5. solve polymorphic constraints deterministically from checked constant
   schemes and emit verifiable source-to-normalized roles.

The existing strict signature already has polymorphic constant schemes,
explicit constructor declarations/arity and declaration-aware certification;
the standalone HOL fixture installs a minimal `refl` basis and a conservative
`True_def`. Those do not supply the general source-theory reconstruction or
`HOL::trans` proof. The proposed API must not accept a theorem name, proof
script, search fact or `HolTheoremDb` fact as resolution evidence. A legacy
parsed theorem may be compared for diagnostics, but cannot repair lost syntax.

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
- a proof-runtime module/crate migration (the A-package Cargo workspace/xtask
  does not implement this design).

The future trusted object-logic boundary is proposed separately in
[ADR-0003-hol-logic-trusted-extension.md](../adr/ADR-0003-hol-logic-trusted-extension.md).
