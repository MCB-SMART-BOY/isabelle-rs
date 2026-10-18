# Architecture

> Historical architecture snapshot (2026-10-03 sampled checkpoint), not the
> current implementation inventory or verification result. The trust boundary
> has since moved to `crates/kernel` (`src/kernel/mod.rs` re-exports it).
> At the 2026-10-07 bundled sample, audited `HOL::TrueI` reaches
> `KernelTrustedClosed: 1/125`, with `TransitionalStrictClosed: 0/125`;
> independent Pure/HOL fixtures remain outside that batch. For current
> behavior and metrics read [AGENTS.md](../../AGENTS.md),
> [PROJECT_STATUS.md](../status/PROJECT_STATUS.md),
> [TRUST.md](../status/TRUST.md), and
> [MIGRATION_MATRIX.md](../kernel/MIGRATION_MATRIX.md). For the automation
> cutover, see [dated xtask evidence](../status/PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11)
> and [current engineering workflow](../guides/DEVELOPMENT.md#engineering-workflow).
> The following diagrams and priorities record the earlier design, not
> work still outstanding today. The approved native compatibility program
> now also targets official Isabelle/ML and PIDE; this archived prioritization
> does not supersede it or make ISIP a replacement.
> The `src/core`/T4 diagrams and six-rule replay list below are descriptions
> of this earlier checkpoint, not the present kernel API: for current variable
> transformations and finite checked composition see
> [KERNEL_PRIMITIVES.md](../kernel/KERNEL_PRIMITIVES.md) and
> [NATIVE_THM_INTERFACE_INVENTORY.md](../status/NATIVE_THM_INTERFACE_INVENTORY.md).

## Architectural Position

Isabelle-rs is organized around a small trusted theorem-construction boundary:

```text
Strict TCB (src/kernel/):
  ProofContext::certify_term / certify_prop
    -> CTerm / CProp
    -> KernelRules (Pure primitives + conservative wrappers)
    -> KernelThm / ClosedThm / OpenThm
    -> accept_closed_theorem(exact immutable owner)
    -> child TrustedTheory + sealed TrustedTheorem

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

At this earlier checkpoint, `TrustedTheory` was immutable owner/fact ancestry.
`accept_closed_theorem` recursively recertified and replayed one closed
candidate, reconstructed ancestor-theorem dependencies, rejected duplicate
names and owner/store inconsistencies, and atomically returned the accepted
child and token. No sampled HOL theorem then had the prerequisite
source/basis/definition chain; `KernelTrustedClosed` was `0/125` in this
historical snapshot.

At that checkpoint, the project prioritized, in dependency order:

1. Keep completed immutable context identity and exact-owner acceptance stable.
2. Keep the implemented data-only source proposition AST unresolved and outside
   theorem authority.
3. Next, integrate source parsing and elaborate checked judgments, constants,
   and polymorphic schemes into `CProp : prop`.
4. Install a data-only HOL basis replayed by generic kernel code.
5. Add generic conservative definitions.
6. Re-derive a real new-kernel `HOL::TrueI`.
7. Ongoing private construction, oracle/admit accounting, invariant replay,
   firewall enforcement, and trusted-boundary attack tests.

Design-only high-performance symbolic compute remains an untrusted parallel
track and cannot reorder this chain.

At this checkpoint, the project did not prioritize broad HOL command coverage,
PIDE parity, LSP features, Sledgehammer, SMT, or Code Generator work. Burn/CubeCL
and GPU dependencies were not included; they were optional backend ideas after
a deterministic CPU symbolic-compute baseline, not the official-compatibility plan.

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
| Future symbolic compute | [`HPC_SYMBOLIC_COMPUTE_DESIGN.md`](../design/HPC_SYMBOLIC_COMPUTE_DESIGN.md) | Untrusted packed term/fact/rewrite prefilter design; no theorem construction authority. |
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

data-only SourceProposition
  -> declaration-aware parser/elaborator [not implemented]
  -> checked source + authorized immutable theory/logic context
  -> ClosedThm over CProp : prop
  -> accept_closed_theorem with recursive replay/dependency validation
  -> child TrustedTheory + sealed TrustedTheorem
  -> ProofOutcome::KernelTrustedClosed
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
  = immutable owner and accepted-fact ancestry
  = exact-context recursive replay and dependency validation
  = duplicate-safe, non-forgeable token insertion
  = the final trusted table for current Pure derivations
```

`SessionBuilder` reports legacy `TransitionalStrictClosed` counts. It must not
present them, raw indexed entries, or compatibility closed-shapes as
`KernelTrustedClosed`; the 2026-10-03 sampled metrics were
`TransitionalStrictClosed: 1/125` and `KernelTrustedClosed: 0/125`.

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

## Verification Gates (Historical Guidance)

The historical project gate was `scripts/dev-check.sh strict`; `core`, `tier2`,
and `tier3` were separate theory runs. Those are the invocation names associated
with this older guidance, not xtask-produced results. A passing strict gate did
not establish full library or global workstation validation. The then-recorded
full tests were killed for memory use; a serial retry timed out. Consult
[engineering workflow](../guides/DEVELOPMENT.md#engineering-workflow) for
current commands and
[xtask cutover](../status/PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11)
for the separately observed automation results; do not attribute these older
test outcomes to xtask.
