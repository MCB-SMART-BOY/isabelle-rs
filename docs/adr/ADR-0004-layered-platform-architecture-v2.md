# ADR-0004: Layered Platform Architecture v2

## Status

Accepted (2026-07-21). Supersedes ADR-0002's layer ordering with the B+C+G
model. This is a dependency-direction decision, not a claim that the proposed
runtime, interfaces, crate metadata, or multi-logic IDs already exist. The
Layer 0 crate exists at `crates/kernel/`; the Cargo workspace contains root,
kernel, offline `isabelle-evidence`, and `xtask`, not independent product
runtime layers. The pre-cutover audited sampled `HOL::TrueI` projection yielded
`KernelTrustedClosed: 1/125`; resumed native P2/P3/P4 implementation has not
rerun that sample or completed theory compilation. Separately approved
compile-time Rust native plugins remain an implementation direction outside
ISIP conformance; see [PROJECT_STATUS.md](../status/PROJECT_STATUS.md#jvm-free-architecture-direction-2026-10-16).

## Context

The kernel TCB checkpoint (branch `wip/kernel-trusted-slice`) demonstrated that axiom authorization, polymorphic matching, and theorem-reference chains can be hardened within the existing kernel API. The next phase requires a stable layering contract before adding proof runtime (B), agent interaction (C), or multi-logic support (G).

## Decision

The platform is organized into four layers with strict dependency direction:

### Layer 0: Trusted Computing Base (`isabelle-kernel`)

- Single crate with dependencies: `sha2`, `thiserror` only.
- Zero warnings (enforced by `RUSTFLAGS="-D warnings"` in strict gate).
- No async runtime, no database, no network, no WASM, no GPU.
- Exports: `RawTerm`, `Ty`, `CTerm`, `CProp`, `KernelThm`, `ClosedThm`, `TrustedTheory`, `TrustedTheorem`, `KernelRules`, `Derivation`, `Signature`, `TheoryId`.
- `accept_closed_theorem` is the ONLY `TrustedTheorem` constructor.
- All other crates depend on Layer 0; Layer 0 depends on nothing project-internal.

### Layer 1: Logic Backend

- Responsible for: declaration-aware parsing, name resolution, checked elaboration, `LogicBasis` manifests, axiom/definition instantiation.
- Current: Pure/HOL in `src/hol/` (monolithic within root crate).
- Future: separate `isabelle-pure`, `isabelle-hol` crates.
- Proposed interface: `trait LogicBackend` — `elaborate`, `available_actions`, `apply`, `check` (not present as a trait in the current code).
- Future multi-logic identity goal: carry `LogicId` in theorem identity (not present in the current `TheoremId`).

### Layer 2: Document & Proof Runtime

- Headless, editor-independent engine.
- Manages: document versions, incremental updates, dependency graph, diagnostics, cancellation, semantic markup, snapshots, goals, fork/rollback/replay.
- Future: `isabelle-session` crate.
- Proposed interfaces: `trait DocumentEngine`, `trait ProofSession` (not yet present as traits).

### Layer 3: Adapters

- CLI, LSP, Agent protocol — all share a single Layer 2 runtime.
- Adapters have NO theorem construction authority.
- Multiple adapters must produce identical proof state, diagnostics, and trust deltas for the same input.

### Cross-Cutting Rules

1. **`stable` vs `experimental` separation:** Crate metadata tags are a proposed gate, not currently present in `Cargo.toml`. Experimental crates cannot appear in the TCB dependency graph.
2. **No silent compatibility:** Migration adapters are explicit, tracked in trust reports, and cannot upgrade to `KernelTrustedClosed`.
3. **Headless-first:** Every new capability is first exposed via a headless API before any UI adapter.
4. **Common runtime, capability extensions:** An extensible `ActionSchemaId` protocol is proposed, not implemented; avoid a monolithic `ProofAction` enum.

## Consequences

- Layer 2 and 3 expansion is gated by broader sampled HOL migration, not merely crate extraction: two narrow standalone source fixtures and one audited sampled `HOL::TrueI` projection create kernel tokens (`KernelTrustedClosed: 1/125`), but unrelated HOL/ML commands are not executed.
- Multi-logic support (G) requires `LogicId` in every identity type; this remains a target, not current Pure/HOL identity behavior.
- The kernel-to-legacy adapter (`src/core/kernel_convert.rs`) is untrusted migration code, not a permanent Layer 1 component.

## References

- [ADR-0001](ADR-0001-kernel-core-rewrite.md): kernel-core rewrite
- [ADR-0002](ADR-0002-layered-platform-architecture.md): original layer ordering (superseded here)
- [ADR-0003](ADR-0003-hol-logic-trusted-extension.md): proposed HOL logic trusted extension

## Relationship to ISIP

This ADR is the architectural foundation for the ISIP standard suite
(see [ISIP overview](../isip/ISIP.md)). ISIP-000 states the proposed layer
model as a design specification; it does not certify present conformance.
