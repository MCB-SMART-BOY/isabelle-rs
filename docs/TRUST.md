# Trust Model

Core promise:

```text
The system must not lie about what was proved.
```

If Isabelle-rs cannot prove a proposition, it may accept it only through an
explicit oracle/admit footprint. Open theorems, admitted theorems, searchable
facts, and closed proved lemmas must remain distinguishable.

This document should be read together with
[PROJECT_STATUS.md](PROJECT_STATUS.md), [KERNEL_RULES.md](KERNEL_RULES.md),
[KERNEL_PRIMITIVES.md](KERNEL_PRIMITIVES.md),
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

Full de Bruijn-style trust requires all four. Current work is in the strict
kernel phase: hardening equality and certification before expanding T4 replay
coverage.

## Strict Kernel Nucleus

`src/kernel/` is the new strict TCB nucleus. It is not a replacement for all old
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
- `SearchFactDb` cannot promote facts to trusted theorems.

Current strict nucleus implementation includes the base primitive rule set,
a conservative `resolve1_match` prototype, and conservative `subst_premise`.
`resolve1_match` uses one-way strict matching, deterministic substitution
ordering, hypothesis substitution/union, and invariant replay. `subst_premise`
rewrites one selected goal premise using propositional equality only, fixed
lhs -> rhs direction, exact strict alpha-equivalence, and invariant replay. It
does not perform symmetric rewriting, object-equality rewriting, unification,
lifting, freshening, or flex-flex handling. Full Isabelle-style `bicompose`,
higher-order unification, and elimination resolution remain out of scope.

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
  => the theorem is eligible for trusted theorem-table/statistics acceptance
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
| Strict closed proved theorem | strict kernel construction, `|- P`, no oracle footprint, no `tpairs`, no dummy types | Yes |
| Compat closed-shaped theorem | no oracle/hyps/`tpairs`, but constructed through legacy compatibility paths | No |
| Oracle-free open theorem | `A1, ..., An |- P`, no oracle footprint | No |
| Admitted theorem | accepted proposition with `admitted:*` oracle footprint | No |
| Searchable fact | fact available to proof search; may be open/admitted/generated/compat | No, unless also strict closed proved |

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
```

Rules:

- Proof fallback must use `admit`, not `assume`.
- Unsupported features and stubs must use `admit`, not fake theorem
  constructors.
- Attribute transformations that do not have a real kernel derivation must use
  `admitted:attribute_transformation`.
- Oracle footprints must union through multi-premise rules and be preserved
  through single-premise rules.

## Closed Theorem Acceptance

A theorem may be counted as a verified lemma only if:

```rust
thm.is_strict_closed_proved()
```

`is_closed_proved()` remains a useful closed-shape predicate:

```text
thm.oracles().is_empty()
&& thm.hyps().is_empty()
&& thm.tpairs().is_empty()
```

It is not sufficient for trusted acceptance because a compatibility theorem can
have that shape. The strict gate additionally requires:

```text
thm.trust_status() == ThmTrust::Strict
&& !thm.contains_dummy_type()
```

For audit gates, use:

```rust
thm.check_kernel_invariants(KernelCheckMode::Strict)
```

`is_strict_closed_proved()` is the cheap theorem-table/statistics predicate.
`check_kernel_invariants(Strict)` is stronger: it rejects compat/admitted
provenance, residual dummy types, malformed proposition CTerms, `maxidx` drift,
oracle-tainted strict theorems, and burden mismatches for the currently
replay-supported derivation subset.

It is not a closed-lemma predicate. Open strict theorems are legal theorem
values. Closed trusted acceptance remains a separate `is_strict_closed_proved()`
decision.

Current architecture:

```text
HolTheoremDb / theorem_index
  = proof-search fact indexes
  = may contain open/admitted facts

final Theory theorem table
  = trusted exported theorem table
  = accepts only is_strict_closed_proved()
```

`SessionBuilder` and verification statistics should report strict closed proved
theorem counts, not raw indexed theorem entries or compatibility closed shapes.

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
- final trusted tables, `SessionBuilder`, and `HolTheoremDb::closed_proved_count`
  now use `is_strict_closed_proved()`;
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
| `Typ::dummy()` tolerance | Lets ill-typed terms survive too far. | Migrate trusted paths to `CTerm::certify_checked` and checked kernel entry points. |
| Best-effort `CTerm::certify` | Still widely used by parser/HOL/Isar compatibility paths. | Keep it compatibility-only; explicit `_compat` theorem constructors are migration debt, not TCB. |
| `Option<Thm>` proof-search APIs | Can hide `KernelError` diagnostics. | Move trusted paths toward `Result<Option<Thm>, KernelError>`. |

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

Next replay expansion batches:

1. `beta_conversion`, `forall_intr`, `forall_elim`.
2. `combination`, `abstraction`, `equal_intr`, `equal_elim`.
3. `instantiate_checked`, `generalize`.
4. `subst_premise` (strict conservative version implemented), then future
   `bicompose` / `bicompose_eresolve` strict replacements. Legacy-core
   resolution remains compatibility debt. See `docs/RESOLUTION_DESIGN.md`.

## Verification Commands

Trusted-kernel gate:

```bash
cargo fmt --check
cargo test --test kernel_soundness
cargo test core::proofterm::tests::
cargo test core::thm::tests::
cargo test --lib core::
cargo check
```

Large theory runs:

```bash
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture
```

Do not claim broad `cargo test --lib` success unless the known theory-loader
stack overflow has been verified fixed.

## Reporting Rules

When reporting project status:

- Use `is_strict_closed_proved()`-derived counts for verified lemmas.
- State admitted counts separately.
- State open theorem facts separately when relevant.
- Do not equate searchable facts with trusted theorem-table entries.
- Do not market the project as a full Isabelle rewrite.
