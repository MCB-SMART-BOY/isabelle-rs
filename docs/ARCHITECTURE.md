# Architecture

This document describes the current Isabelle-rs architecture as a trusted-kernel
research prototype. It intentionally does not claim feature parity with
Isabelle/HOL, Isabelle/Isar, or Isabelle/PIDE.

Read [PROJECT_STATUS.md](PROJECT_STATUS.md) first for the canonical status.

## Architectural Position

Isabelle-rs is organized around a small trusted theorem-construction boundary:

```text
Strict TCB (src/kernel/):
  ProofContext::certify_term / certify_prop
    -> CTerm / CProp
    -> KernelRules (15 primitives + resolve1_match)
    -> KernelThm / ClosedThm / OpenThm
    -> TrustedTheorem (invariant replay)
    -> TrustedTheory

Legacy quarantine (src/core/):
  source / generated facts
    -> parser / loader / type inference
    -> certified terms (CTerm with CertStatus)
    -> ThmKernel (LEGACY: bicompose/eresolve/subst_premise are core-only)
    -> Thm
    -> theorem acceptance filters
    -> proof-search indexes or final trusted theory tables
```

The project currently prioritizes:

1. Private theorem fields and kernel-only theorem construction (`pub(in crate::kernel)` visibility).
2. Explicit `admitted:*` / oracle footprints.
3. Correct distinction between open, admitted, oracle-free, closed proved, and strict-closed proved theorems.
4. Strict-kernel invariant replay as an independent derivation check (separate from legacy T4 proofterm replay).
5. Attack tests for trusted-boundary regressions.
6. Automated firewall enforcement (`scripts/check-kernel-firewall.sh`, `scripts/check-strict-kernel.sh`).
7. Design-only high-performance symbolic compute as an untrusted candidate
   generation/prefilter layer, with CPU strict-kernel acceptance unchanged.

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
| Strict closed proved theorem | strict construction, `|- P`, no oracle, no `tpairs`, no dummy types | May enter final trusted theorem tables. |
| Compat closed-shaped theorem | no oracle/hyps/`tpairs`, but legacy construction | Searchable only; not trusted output. |
| Open theorem | `A1, ..., An |- P` | Valid theorem, but not a proved lemma. |
| Admitted theorem | `|- P` with oracle footprint | Accepted for progress; never counted as independently proved. |
| Searchable fact | Any theorem-like fact used by proof search | May be open/admitted; not automatically trusted output. |

The acceptance predicate for proved lemmas is:

```text
thm.is_strict_closed_proved()
  == thm.trust_status() == ThmTrust::Strict
  && thm.oracles().is_empty()
  && thm.hyps().is_empty()
  && thm.tpairs().is_empty()
  && !thm.contains_dummy_type()
```

`is_closed_proved()` means closed shape only. `is_fully_proved()` means
oracle-free only. Neither is sufficient for trusted lemma verification
statistics once compatibility theorem construction is explicit.

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
  -> final Theory trusted theorem table
```

Important split:

```text
theorem_index / HolTheoremDb
  = proof-search fact indexes
  = may contain open/admitted/generated facts

core::theory::Theory
  = final trusted theorem table
  = must only contain `is_strict_closed_proved()` facts
```

`SessionBuilder` reports strict closed proved theorem counts. It must not use
raw indexed theorem entries or compatibility closed-shapes as verified theorem
statistics.

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

```bash
cargo fmt --check
cargo test --test kernel_soundness
cargo test core::proofterm::tests::
cargo test core::thm::tests::
cargo test --lib core::
cargo check
```

For broad theory runs:

```bash
RUST_MIN_STACK=268435456 cargo test test_verify_all_core_files -- --nocapture
RUST_MIN_STACK=268435456 cargo test --test tier2_verify -- --nocapture
```

Full `cargo test --lib` has a known stack-sensitive loader test in this
checkout. Report it separately unless it has been verified fixed.
