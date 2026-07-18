# Trust Model

Core promise:

```text
The system must not lie about what was proved.
```

If Isabelle-rs cannot prove a proposition, it may accept it only through an
explicit oracle/admit footprint. Open theorems, admitted theorems, searchable
facts, and closed proved lemmas must remain distinguishable.

Agents should read root [AGENTS.md](../AGENTS.md) first. This document should
then be read together with
[PROJECT_STATUS.md](PROJECT_STATUS.md),
[KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](KERNEL_TRUSTED_ACCEPTANCE_GAPS.md),
[KERNEL_RULES.md](KERNEL_RULES.md), [KERNEL_PRIMITIVES.md](KERNEL_PRIMITIVES.md),
[RESOLUTION_DESIGN.md](RESOLUTION_DESIGN.md), and
[KERNEL_ATTACK_TESTS.md](KERNEL_ATTACK_TESTS.md).

## Current Position

Isabelle-rs is a Rust research prototype of an Isabelle/Pure-inspired LCF
kernel. The current trusted-engineering focus is:

1. non-forgeable theorem construction;
2. sound primitive inference boundaries;
3. explicit oracle/admit propagation;
4. closed theorem acceptance;
5. proofterm replay.

It is not a full Isabelle proofterm checker or a feature-complete Isabelle/HOL
implementation.

## T1-T4 Criteria

| Criterion | Meaning | Current status |
|---|---|---|
| T1 non-forgeable theorem type | `Thm` cannot be built outside the trusted constructor boundary. | Mostly established by private fields and `ThmKernel` routes. |
| T2 reliable kernel rules | Primitive rules enforce side conditions and propagate theorem burdens. | Strict kernel alpha-equivalence split out; checked CTerm certification has started; full `Typ::dummy()` migration remains pending. |
| T3 trust footprint tracking | Unproved acceptance is explicit and propagates through later inference. | Strong project area; `admitted:*`/oracle footprints are explicit. |
| T4 independent replay | A small checker replays proof objects and compares theorem burdens. | Minimal replay prototype for six rules. |

Full de Bruijn-style trust requires all four. The current main line is no
longer another legacy replay batch: it is immutable theory/signature identity,
context-bound theorem acceptance, and then source-aware HOL elaboration.

## Strict Kernel Nucleus

`src/kernel/` is the candidate target TCB nucleus. It is not a replacement for all old
`src/core`/Isar/HOL code yet; it is an isolated target architecture used to make
bad states unrepresentable before adapters migrate legacy paths into it.

The new flow is:

```text
RawTerm
  -> Signature / ProofContext certification
  -> CTerm / CProp
  -> KernelRules
  -> KernelThm
  -> ClosedThm
  -> TrustedTheorem
  -> TrustedTheory
```

The non-TCB flow is:

```text
SearchFact / legacy compat fact / admitted fact
  -> search and diagnostics only
  -> no implicit TrustedTheorem conversion
```

Current strict nucleus constraints:

- no `Typ::dummy` equivalent;
- undeclared constants and local frees are rejected;
- `ProofObligation` is not a theorem;
- theorem fields are private;
- internal certification/theorem-construction helpers are scoped to
  `pub(in crate::kernel)` or narrower, not crate-wide `pub(crate)`;
- primitive rules are the only constructors;
- `TrustedTheory` accepts only `TrustedTheorem`;
- target final object-logic acceptance will additionally bind the theorem to
  immutable theory/signature/logic-extension identity; this binding is not yet
  implemented;
- `SearchFactDb` cannot promote facts to trusted theorems.

Current strict nucleus implementation includes the base primitive rule set,
a conservative `resolve1_match` prototype, conservative `subst_premise`, and a
conservative `bicompose` wrapper. `resolve1_match` / `bicompose` use one-way
strict matching, deterministic substitution ordering, hypothesis
substitution/union, invariant replay, and `RequiresLifting` rejection for Free
or schematic Var namespace collisions. `bicompose` v1 records the existing
`Derivation::Resolve1Match`; it does not add `Derivation::Bicompose`.
`subst_premise` rewrites one selected goal premise using propositional equality
only, fixed lhs -> rhs direction, exact strict alpha-equivalence, and invariant
replay. These conservative rules do not perform symmetric rewriting,
object-equality rewriting, full unification, lifting, freshening, or flex-flex
handling. Full Isabelle-style `bicompose`, higher-order unification, and
elimination resolution remain out of scope.

## Theorem Status Semantics

Important distinction:

```text
is_fully_proved() == oracle-free
is_closed_proved() == oracle-free + no hypotheses + no unresolved tpairs
is_strict_closed_proved() == strict construction + is_closed_proved() + no dummy types
check_kernel_invariants(Strict) == strict construction + structural invariants + supported replay burden check
```

These predicates are deliberately not interchangeable:

```text
check_kernel_invariants(Strict)
  => the theorem is internally consistent as a strict theorem
  != the theorem is a closed lemma

is_strict_closed_proved()
  => the legacy theorem is eligible for TransitionalStrictClosed statistics
  != the theorem is eligible for new-kernel TrustedTheory acceptance
  != proof replay has necessarily covered every primitive rule used

check_proof() / validate_proof()
  => independent derivation replay for the currently supported rule subset
  != a complete Isabelle proofterm checker
```

For example, strict `assume(A)` may pass strict invariants and replay as a valid
open theorem `A |- A`, but it must not satisfy `is_strict_closed_proved()`.
Conversely, a strict theorem whose derivation contains a currently unsupported
rule may pass structural strict invariants but still fail `check_proof()` until
that replay rule is implemented.

Use these terms:

| Status | Meaning | Counts as trusted proved lemma? |
|---|---|---|
| Transitional strict closed theorem | legacy `core::Thm + ThmTrust::Strict`, closed-shaped, oracle-free, no dummy types | No; migration/reporting only |
| Kernel-trusted closed theorem | context-bound `src/kernel::TrustedTheorem` whose conclusion is `CProp : prop` and whose selected replay gate succeeds | Yes |
| Compat closed-shaped theorem | no oracle/hyps/`tpairs`, but constructed through legacy compatibility paths | No |
| Oracle-free open theorem | `A1, ..., An |- P`, no oracle footprint | No |
| Admitted theorem | accepted proposition with `admitted:*` oracle footprint | No |
| Searchable fact | fact available to proof search; may be open/admitted/generated/compat/transitional | No |

`ThmKernel::assume(A)` constructs:

```text
A |- A
```

It does not construct:

```text
|- A
```

Therefore `assume(A)` may be `is_fully_proved()` but must not be
`is_closed_proved()`.

## Admit / Oracle Footprints

`ThmKernel::admit(cterm, reason)` is the explicit entry point for accepted
unproved propositions.

Recommended reason names:

```text
admitted:proof_engine_failed
admitted:parser_gap
admitted:unsupported_method
admitted:attribute_transformation
admitted:datatype_stub
admitted:class_stub
admitted:metis_fallback
admitted:simp_fallback
admitted:sledgehammer_stub
admitted:strict_adapter_source_prop_unverified
admitted:strict_adapter_prop_mismatch
admitted:strict_adapter_proof_shape_mismatch
admitted:strict_adapter_missing_checked_definition
admitted:strict_adapter_certification_failed
admitted:strict_adapter_replay_failed
admitted:strict_adapter_kernel_invariant
```

Rules:

- Proof fallback must use `admit`, not `assume`.
- Strict adapter shape hits that fail strict checks must use a specific
  `admitted:strict_adapter_*` reason instead of falling through silently.
- The registered explicit-proof `TrueI` adapter must require both
  `SourcePropositionStatus::FullyConsumed` and
  `SourcePropositionShape::StandaloneHolTrueAlias`. Any other status or shape
  is rejected as
  `admitted:strict_adapter_source_prop_unverified`, not reclassified as
  `admitted:parser_gap` and not sent to legacy proof fallback.
- Unsupported features and stubs must use `admit`, not fake theorem
  constructors.
- Attribute transformations that do not have a real kernel derivation must use
  `admitted:attribute_transformation`.
- Oracle footprints must union through multi-premise rules and be preserved
  through single-premise rules.

## Closed Theorem Reporting And Acceptance

The current legacy batch increments its transitional verified count only if
`thm.is_strict_closed_proved()`; the exact implementation is in
[`src/isar/method.rs`](../src/isar/method.rs).

`is_closed_proved()` remains a useful closed-shape predicate:

```text
thm.oracles().is_empty()
&& thm.hyps().is_empty()
&& thm.tpairs().is_empty()
```

It is not sufficient even for the transitional count because a compatibility
theorem can have that shape. The legacy strict filter additionally requires:

```text
thm.trust_status() == ThmTrust::Strict
&& !thm.contains_dummy_type()
```

For audit gates, use
`thm.check_kernel_invariants(KernelCheckMode::Strict)` from the legacy theorem
API rather than copying a detached Rust snippet.

`is_strict_closed_proved()` is the cheap legacy table/statistics predicate.
`check_kernel_invariants(Strict)` is stronger: it rejects compat/admitted
provenance, residual dummy types, malformed proposition CTerms, `maxidx` drift,
oracle-tainted strict theorems, and burden mismatches for the currently
replay-supported derivation subset.

It is not a closed-lemma predicate. Open strict theorems are legal theorem
values. Final new-kernel acceptance is a separate decision: the value must be a
context-bound `TrustedTheorem` over `CProp : prop` and pass the selected replay
policy before it becomes `KernelTrustedClosed`.

Current architecture:

```text
HolTheoremDb / theorem_index
  = proof-search fact indexes
  = may contain open/admitted facts

HolTheoremDb.checked_definitions
  = checked definition sources
  = not theorem facts
  = not proof progress

legacy Theory theorem table
  = transitional/export compatibility table
  = currently filters with is_strict_closed_proved()

new-kernel TrustedTheory
  = current theorem table, type-gated to TrustedTheorem
  = does not yet enforce immutable context identity or name conflicts

target final trusted table
  = accepts only context-bound TrustedTheorem values
  = reported as KernelTrustedClosed
```

`SessionBuilder` and verification statistics must report
`TransitionalStrictClosed` separately from `KernelTrustedClosed`, rather than
conflating either with raw indexed entries or compatibility closed shapes.
Until that context-bound outcome exists, `kernel_trusted_closed` is a reporting
overlay and is deliberately excluded from `ProofOutcomeStats::total()`; the
legacy outcome buckets alone partition attempted theorems.

## T2 Kernel Status

Implemented hardening includes:

- known concrete type mismatch checks in several kernel paths;
- `instantiate_checked` production path;
- legacy infallible instantiation removed from production use;
- strict kernel alpha-equivalence separated from compatibility matching;
- `CTerm::certify_checked(term, type_env)` rejects undeclared constants,
  ill-typed applications, unbound de Bruijn indices, and residual
  `Typ::dummy()`;
- `CTerm` records whether it came from checked or compatibility certification;
- strict `ThmKernel::assume` and `ThmKernel::reflexive` reject compatibility
  CTerms, while old behavior is explicitly named `assume_compat` /
  `reflexive_compat`;
- `ProofState::assume`, `Goal::init`, and checked proof-state goal/subgoal
  constructors now create Strict open theorem obligations through checked
  certification instead of defaulting to compatibility theorem construction;
- proof-state checked certification now goes through an explicit
  `ProofCertContext` / `TypeEnv` source. Constants and local frees must already
  be declared in that context; raw terms are no longer allowed to self-declare
  their own Const/Free types into a temporary trusted environment;
- `Thm` records `ThmTrust::{Strict, Compat, Admitted}` so compatibility
  theorems cannot be counted as trusted even if they are oracle-free and closed;
- legacy tables, `SessionBuilder`, and `HolTheoremDb::closed_proved_count`
  currently use `is_strict_closed_proved()` for transitional filtering; this is
  not the future `TrustedTheory` authorization gate;
- `HolTheoremDb::checked_definitions` keeps checked definition sources, starting
  with `True_def`, separate from searchable facts and trusted theorem tables;
- `ThmKernel::hol_object_refl` / `try_strict_hol_refl` is a narrow transitional
  bridge for the bool-valued legacy term `HOL.eq t t`; it records a separate
  derivation but is not a `CProp` theorem and is ineligible for
  `KernelTrustedClosed`;
- `ThmKernel::true_def_transport` / `try_strict_true_def_transport` is a narrow
  theorem-specific legacy transport for `True_def`; its checked payload is not
  a conservative definition certificate, and the bridge must not become the
  template for general definitions or new HOL proof power;
- `try_strict_hol_true_i` is the first existing core-file transitional adapter. It
  accepts only `TrueI` / `HOL::TrueI` with proof
  `unfolding True_def by (rule refl)`, checked `True_def`, strict HOL object
  reflexivity for the checked RHS, and checked `True_def` transport to
  `HOL.True`. It must not become a direct `return True`, compat `refl`, or
  general unfolding path;
- `try_strict_adapter` is the minimal dispatcher for transitional theorem
  adapters. It currently registers only `HOL::TrueI` and reports
  `NotApplicable`, `Proved`, or `Rejected(reason)` instead of scattering direct
  special cases through `verify_lemma`. The compatibility `parse_term` API may
  still return a parsed prefix, but the loader records typed status and shape
  provenance:
  `SourcePropositionStatus::{FullyConsumed, Incomplete, Unavailable}` and
  `SourcePropositionShape::{StandaloneHolTrueAlias, Other, Contextual,
  Unavailable}`. The registered explicit-proof `TrueI` adapter proceeds only
  for `FullyConsumed + StandaloneHolTrueAlias`; every other combination rejects
  with
  `admitted:strict_adapter_source_prop_unverified` before the legacy parser-gap
  override. Thus parser-recovered `True =` is `FullyConsumed + Other`, while a
  lemma with local `fixes` / `includes`, a locale qualifier, or an enclosing
  context is `FullyConsumed + Contextual`; neither may use the adapter. Exact standalone
  source aliases `True` / `HOL.True` are resolved to canonical
  `Const("HOL.True", bool)`; the strict entry rejects Free, dummy-typed, and
  outer-`CTerm`-type-mismatched True inputs. Missing and empty proof scripts
  remain `NotApplicable` and retain compatibility parser-gap behavior;
- `Thm::check_kernel_invariants(KernelCheckMode::{Compat, Strict})` separates
  legacy structural checks from strict trusted-kernel invariant checks;
- `tpairs`, `shyps`, and `oracles` propagation audits;
- `beta_conversion` uses real bound substitution;
- `abstraction` and `forall_intr` check free-variable side conditions;
- attribute transformation fallback is admitted, not assumed;
- accepted-but-unproved `accept_all` paths are admitted and not closed proved.

Known debts:

| Debt | Why it matters | Direction |
|---|---|---|
| Compatibility Free/Const suffix matching | `compat_alpha_eq` still exists for parser/loader legacy paths. | Keep it out of trusted rules; fix parser/loader/type annotations and remove the compat need. |
| Compatibility Var/Free matching | `compat_alpha_eq` still exists for schematic-variable parser gaps. | Keep it out of trusted rules; align theorem DB and parser variable representation. |
| Transitional source-shape guard | `parse_term` may return a prefix or recover `True =` as `True`; local context may shadow the surface name. The current status/shape metadata is a fail-closed lexical guard, not a name-resolved AST or certification token. | Require `FullyConsumed + StandaloneHolTrueAlias` for the narrow adapter, reject every other combination, and replace the guard with source-aware checked elaboration. |
| `Typ::dummy()` tolerance | Lets ill-typed terms survive too far. | Migrate trusted paths to `CTerm::certify_checked` and checked kernel entry points. |
| Best-effort `CTerm::certify` | Still widely used by parser/HOL/Isar compatibility paths. | Keep it compatibility-only; explicit `_compat` theorem constructors are migration debt, not TCB. |
| `Option<Thm>` proof-search APIs | Can hide `KernelError` diagnostics. | Move trusted paths toward `Result<Option<Thm>, KernelError>`. |

The next checked HOL proposition boundary is specified in
[CHECKED_HOL_PROPOSITION_NORMALIZATION.md](CHECKED_HOL_PROPOSITION_NORMALIZATION.md).
The proposed target separation between the Pure kernel, a trusted HOL
object-logic extension, Isar adapters, and legacy core is recorded in
[ADR-0003-hol-logic-trusted-extension.md](ADR-0003-hol-logic-trusted-extension.md).
The current `TransitionalStrictClosed: 1/125` migration result uses legacy
`core::Thm` with strict trust metadata. `KernelTrustedClosed` is `0/125`: no
current HOL slice has a checked
`CProp : prop`, immutable theory/logic context, explicit HOL axiom-basis
provenance, and fully supported new-kernel replay.

Trusted kernel rules use `Hyps::kernel_alpha_eq`. The old broad matching is
isolated as `Hyps::compat_alpha_eq` and must remain explicitly marked as
compatibility-only until front-end representation gaps are fixed.

## T4 Proofterm Replay Status

Current supported independent replay rules:

```text
assume
reflexive
symmetric
transitive
implies_intr
implies_elim
```

Current trusted replay behavior:

- `Thm::check_proof()` reconstructs theorem shape from stored proof data and
  compares `prop`, `hyps`, `tpairs`, and `oracles`.
- `Thm::validate_proof()` uses the same burden-aware validation semantics.
- `ProofBody::check(expected_prop)` is proposition-only compatibility code and
  is not a trusted theorem validation gate.
- Admitted/oracle-backed theorems fail independent replay.
- Unsupported replay rules fail explicitly.
- Open theorem replay can succeed, but open theorems still do not count as
  closed proved lemmas.
- `check_kernel_invariants(Strict)` only invokes replay when the stored
  derivation is in the currently supported replay subset. Unsupported strict
  derivations are structurally audited but are not replay-checked.

This is a minimal kernel derivation replay checker. It is not full Isabelle
`proofterm.ML` or `Proof_Checker.thm_of_proof`.

Deferred replay backlog:

```text
beta_conversion / forall_intr / forall_elim
combination / abstraction / equal_intr / equal_elim
instantiate_checked / generalize
legacy resolution-family coverage
```

This is not the current dependency chain. Resume it after immutable context
identity and acceptance are stable, or for a focused soundness fix.

## Verification Commands

Trusted-kernel gate:

Run `scripts/dev-check.sh strict`.

Large theory runs:

Run `scripts/dev-check.sh core`, `tier2`, or `tier3`.

Do not claim broad `cargo test --lib` success unless the known theory-loader
stack overflow has been verified fixed.

## Reporting Rules

When reporting project status:

- Label `is_strict_closed_proved()`-derived counts as
  `TransitionalStrictClosed`, not kernel-trusted verified lemmas.
- Report `KernelTrustedClosed` separately from actual context-bound
  `src/kernel::TrustedTheorem` values; it is currently `0/125` for sampled HOL.
- State admitted counts separately.
- State open theorem facts separately when relevant.
- Do not equate searchable facts with trusted theorem-table entries.
- Do not market the project as a full Isabelle rewrite.
