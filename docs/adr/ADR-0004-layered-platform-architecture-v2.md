# ADR-0004: Layered Platform Architecture v2

## Status

Accepted (2026-07-21). Supersedes the layer ordering in ADR-0002 with the B+C+G model from the post-checkpoint audit.

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
- Interface: `trait LogicBackend` — `elaborate`, `available_actions`, `apply`, `check`.
- Every `TheoremId` carries `LogicId`.

### Layer 2: Document & Proof Runtime

- Headless, editor-independent engine.
- Manages: document versions, incremental updates, dependency graph, diagnostics, cancellation, semantic markup, snapshots, goals, fork/rollback/replay.
- Future: `isabelle-session` crate.
- Interface: `trait DocumentEngine`, `trait ProofSession`.

### Layer 3: Adapters

- CLI, LSP, Agent protocol — all share a single Layer 2 runtime.
- Adapters have NO theorem construction authority.
- Multiple adapters must produce identical proof state, diagnostics, and trust deltas for the same input.

### Cross-Cutting Rules

1. **`stable` vs `experimental` separation:** Crates are tagged in `Cargo.toml` metadata. Experimental crates cannot appear in the TCB dependency graph.
2. **No silent compatibility:** Migration adapters are explicit, tracked in trust reports, and cannot upgrade to `KernelTrustedClosed`.
3. **Headless-first:** Every new capability is first exposed via a headless API before any UI adapter.
4. **Common runtime, capability extensions:** Logic-specific proof actions use an extensible `ActionSchemaId` protocol, not a monolithic `ProofAction` enum.

## Consequences

- Layer 2 and 3 are blocked on completing Layer 1's `ConservativeDefinition` certificate and the first production `KernelTrustedClosed` theorem.
- Multi-logic support (G) requires `LogicId` in every identity type — this is forward-compatible with the current pure-HOL implementation.
- The kernel->legacy conversion (`src/kernel/convert.rs`) is a migration adapter, not a permanent Layer 1 component.

## References

- ADR-0001: kernel-core rewrite
- ADR-0002: layered platform architecture (original)
- ADR-0003: HOL logic trusted extension

## Relationship to ISIP

This ADR is the architectural foundation for the ISIP standard suite
(see `docs/isip/ISIP.md`). ISIP-000 formalizes the same layer model as a
specification with RFC 2119 normative language.
