# Architecture

This document describes the current Isabelle-rs architecture as a trusted-kernel
research prototype. It intentionally does not claim feature parity with
Isabelle/HOL, Isabelle/Isar, or Isabelle/PIDE.

Read root [AGENTS.md](../AGENTS.md), then
[PROJECT_STATUS.md](PROJECT_STATUS.md), before using this architecture.

## Architectural Position

Isabelle-rs is organized around a small trusted theorem-construction boundary:

```text
Strict TCB (src/kernel/):
  ProofContext::certify_term / certify_prop
    -> CTerm / CProp
    -> KernelRules (15 primitives + resolve1_match + subst_premise + bicompose wrapper)
    -> KernelThm / ClosedThm / OpenThm
    -> TrustedTheorem (current context-free invariant-replay wrapper)
    -> TrustedTheory

Legacy quarantine (src/core/):
  source / generated facts
    -> parser / loader / type inference
    -> certified terms (CTerm with CertStatus)
    -> ThmKernel (LEGACY: full bicompose/eresolve remain compatibility debt;
                  subst_premise and conservative bicompose have strict replacements)
    -> Thm
    -> theorem acceptance filters
    -> proof-search indexes or transitional legacy theory tables
```

The current `TrustedTheory` type accepts only `src/kernel::TrustedTheorem`
values, but it does not yet bind them to immutable theory/signature/logic
identity or reject conflicting theorem identities. The target final arrow adds
those checks before recording `KernelTrustedClosed`. No sampled HOL theorem has
reached that target boundary; `KernelTrustedClosed` is `0/125`.

The project currently prioritizes, in dependency order:

1. Immutable `SignatureId` / `TheoryId` propagation and mixed-context
   rejection.
2. One context-bound acceptance API and mutually exclusive
   `KernelTrustedClosed` outcome.
3. A source-aware proposition AST before legacy lowering.
4. Checked judgment/constant/polymorphic-scheme elaboration into `CProp : prop`.
5. A data-only HOL basis replayed by generic kernel code.
6. Generic conservative definitions.
7. A real new-kernel `HOL::TrueI`.
8. Ongoing private construction, oracle/admit accounting, invariant replay,
   firewall enforcement, and trusted-boundary attack tests.

Design-only high-performance symbolic compute remains an untrusted parallel
track and cannot reorder this chain.

It does not currently prioritize broad HOL command coverage, PIDE parity, LSP
features, Sledgehammer, SMT, or Code Generator work.
It also does not currently add Burn/CubeCL or GPU dependencies; those remain
future optional backends after a deterministic CPU symbolic-compute baseline.

## Trusted Boundary

### Theorem Construction

`Thm` is the central abstract theorem type. Its fields are private; external
code must use `ThmKernel` operations.

```text
CTerm
  -> ThmKernel::{assume, reflexive, ..., admit}
  -> Thm { hyps, prop, tpairs, shyps, oracles, derivation }
```

Core theorem classes:

| Class | Shape | Trusted status |
|---|---|---|
| Transitional strict closed theorem | legacy strict construction, `|- P`, no oracle, no `tpairs`, no dummy types | Migration/reporting only; may not enter final `TrustedTheory`. |
| Kernel-trusted closed theorem | context-bound `src/kernel::TrustedTheorem`, `CProp : prop`, immutable theory/logic provenance, required replay | May enter final `TrustedTheory`. |
| Compat closed-shaped theorem | no oracle/hyps/`tpairs`, but legacy construction | Searchable only; not trusted output. |
| Open theorem | `A1, ..., An |- P` | Valid theorem, but not a proved lemma. |
| Admitted theorem | `|- P` with oracle footprint | Accepted for progress; never counted as independently proved. |
| Searchable fact | Any theorem-like fact used by proof search | May be open/admitted; not automatically trusted output. |

The legacy transitional classification predicate is:

```text
thm.is_strict_closed_proved()
  == thm.trust_status() == ThmTrust::Strict
  && thm.oracles().is_empty()
  && thm.hyps().is_empty()
  && thm.tpairs().is_empty()
  && !thm.contains_dummy_type()
```

`is_closed_proved()` means closed shape only. `is_fully_proved()` means
oracle-free only. `is_strict_closed_proved()` is stronger but still classifies
legacy `core::Thm`; none of these predicates authorizes final new-kernel
acceptance.

### Admit / Oracle Entry

`ThmKernel::admit(cterm, reason)` is the explicit unproved-entry point. It is
used for proof-engine fallback, unsupported features, generated stubs, and
attribute transformations that do not yet have a real kernel derivation.

`ThmKernel::assume(P)` means `P |- P`; it is only correct for local assumptions
and goal initialization. It must not be used as a proof-failure fallback.

## Core Modules

| Layer | Main files | Current role |
|---|---|---|
| Terms/types | `src/core/term.rs`, `types.rs`, `type_infer.rs`, `term_subst.rs` | Basic Pure term/type representation and substitution. Still has parser/type-boundary debt. |
| Certified terms | `src/core/thm.rs`, `src/core/sign.rs` | `CTerm` certification boundary. Not yet a fully hard type boundary. |
| Kernel | `src/core/thm.rs`, `logic.rs`, `unify.rs`, `envir.rs` | LCF-style primitive rules, checked instantiation, burden propagation. |
| Proof replay | `src/core/proofterm.rs`, `src/core/thm.rs` | Minimal burden-aware replay for a small primitive rule set. |
| Tactics/conversions | `src/core/tactic.rs`, `conv.rs`, `simplifier.rs`, `bires.rs`, `more_thm.rs` | Proof-search and rewrite front-ends that must route theorem construction back through the kernel. |
| Isar layer | `src/isar/*` | Partial structured proof state machine and method dispatch. |
| HOL layer | `src/hol/*`, `src/tools/*` | Partial HOL loading, theorem DB, simplifier/Metis/Meson/linarith stubs and tools. |
| Theory/session | `src/theory/*` | Theory processing, closed theorem statistics, session summaries. |
| Future symbolic compute | `docs/HPC_SYMBOLIC_COMPUTE_DESIGN.md` | Untrusted packed term/fact/rewrite prefilter design; no current source module and no theorem construction authority. |
| UI/runtime | `src/lsp/*`, `src/server/*`, `src/wasm/*` | Skeleton infrastructure; not part of the current trust-critical path. |

## Theory Processing Flow

```text
.thy file
  -> OuterSyntax / theory loader
  -> TheoryProcessor
     -> local proof search / method execution
     -> theorem_index searchable facts
     -> LocalTheory::finalize()
  -> legacy Theory transitional table

checked source + immutable theory/logic context
  -> src/kernel::TrustedTheorem over CProp : prop
  -> required replay in the same context
  -> KernelTrustedClosed
  -> final TrustedTheory
```

Important split:

```text
theorem_index / HolTheoremDb
  = proof-search fact indexes
  = may contain open/admitted/generated facts

core::theory::Theory
  = transitional legacy output table
  = filters with `is_strict_closed_proved()`

src::kernel::TrustedTheory
  = current new-kernel theorem table, type-gated to `TrustedTheorem`
  = still lacks the target immutable context and conflict checks

target final trusted table
  = accepts only context-bound `src/kernel::TrustedTheorem` values
```

`SessionBuilder` reports legacy `TransitionalStrictClosed` counts. It must not
present them, raw indexed entries, or compatibility closed-shapes as
`KernelTrustedClosed`; the sampled metrics are `TransitionalStrictClosed: 1/125`
and `KernelTrustedClosed: 0/125`.

## Proofterm Replay Flow

Current minimal T4 replay:

```text
Thm
  -> proof_term()
  -> replay proof derivation
  -> reconstructed prop/hyps/tpairs/oracles
  -> compare with current theorem fields
```

Supported replay rules:

```text
assume
reflexive
symmetric
transitive
implies_intr
implies_elim
```

Current semantics:

- `assume(A)` replays successfully as `A |- A`, but remains non-closed.
- admitted/oracle-backed theorems fail independent kernel replay.
- unsupported rules fail explicitly.
- `Thm::check_proof()` and `Thm::validate_proof()` are the trusted replay gates.
- `ProofBody::check(expected_prop)` is proposition-only compatibility code and
  must not be used as a theorem validation gate.

## Known Architecture Debts

| Debt | Impact | Direction |
|---|---|---|
| `Typ::dummy()` at trusted boundaries | Allows ill-typed terms to survive too far. | Strengthen parser, type inference, and `CTerm` certification. |
| Compatibility Free/Const matching | Old behavior is isolated in `compat_alpha_eq`; trusted kernel equality rejects it. | Align parser/loader term heads and remove/narrow compatibility usage. |
| Compatibility Var/Free matching | Old behavior is isolated in `compat_alpha_eq`; trusted kernel equality rejects it. | Align theorem DB and parser variable representation. |
| `Option<Thm>` proof-search APIs | Erases distinction between type rejection and ordinary non-match. | Move trusted boundaries toward `Result<Option<Thm>, KernelError>`. |
| Partial proofterm replay | Only validates a small primitive subset. | Extend replay rule-by-rule with attack tests. |
| HOL tool stubs/fallbacks | Many generated facts are admitted or heuristic. | Keep fallback admitted; reduce by cause later. |

## Verification Gates

For trusted-boundary code changes:

Run `scripts/dev-check.sh strict`.

For broad theory runs:

Run `scripts/dev-check.sh core`, `tier2`, or `tier3`.

Full `cargo test --lib` has a known stack-sensitive loader test in this
checkout. Report it separately unless it has been verified fixed.
