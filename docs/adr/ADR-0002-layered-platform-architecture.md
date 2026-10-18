# ADR-0002: Layered Platform Architecture

## Status

Accepted as a historical target architecture; its detailed layer ordering was
superseded by [ADR-0004](ADR-0004-layered-platform-architecture-v2.md).
The independent TCB crate exists at `crates/kernel/`; the Cargo workspace has
root, `isabelle-kernel`, `isabelle-evidence`, and `xtask` members (root-only
default members). `isabelle-evidence` handles offline evidence, not theorem
authority. This workspace does **not** implement the proposed session, protocol,
compute, or multi-crate product runtime. The pre-cutover bundled sample's audited
`HOL::TrueI` projection reached `KernelTrustedClosed: 1/125`
(`TransitionalStrictClosed: 0/125`); resumed native P2/P3/P4 work has not
rerun that sample or completed HOL theory compilation. The WASM plugin model
below is a historical proposal: the separately approved direction is
compile-time-linked Rust native plugins, still under implementation, not ISIP
conformance or complete native-build acceptance. See
[PROJECT_STATUS.md](../status/PROJECT_STATUS.md#jvm-free-architecture-direction-2026-10-16),
[ROADMAP.md](../status/ROADMAP.md), and the
[engineering workflow](../guides/DEVELOPMENT.md#engineering-workflow).

## Context

ADR-0001 established the strangler-pattern kernel reset: the strict nucleus
now lives in `crates/kernel/` and `src/kernel/mod.rs` re-exports it. That
decision was about *how* to build the kernel.

This ADR addresses *what comes after the kernel* — the overall system
architecture that the strict kernel nucleus enables.

At the time of this decision, the codebase was largely a monolithic crate with
internal modules (`core`, `hol`, `isar`, `theory`, `tools`, `session`, `lsp`,
`server`, `wasm`, `syntax`, `kernel`). The TCB has since moved to its own crate;
most other platform layers remain in the root crate. The original structure
motivated work on:

- Independent verification of the TCB size.
- Structured compatibility measurement against Isabelle/HOL.
- Reproducible project builds with dependency locking.
- Agent-native proof interaction at the proof-state level.
- WASM plugin sandboxing with clear capability boundaries.
- Ecosystem distribution (AFP registry, toolchain pinning).

## Decision

Evolve isabelle-rs from a monolithic proof-assistant prototype into a layered
proof engineering platform. The target architecture has these layers, ordered
by dependency (upper layers depend on lower layers; lower layers must not
depend on upper layers):

```text
┌────────────────────────────────────────────────────┐
│                    User Interfaces                  │
│ CLI / VS Code / Neovim / Web UI / Notebook          │
└────────────────────────────────────────────────────┘
                         │
         ┌───────────────┴────────────────┐
         │                                │
┌────────▼────────┐              ┌────────▼────────┐
│  isabelle-lsp   │              │ isabelle-agent  │
│ human editing   │              │ APP / MCP bridge│
└────────┬────────┘              └────────┬────────┘
         │                                │
         └───────────────┬────────────────┘
                         │
┌────────────────────────▼────────────────────────────┐
│                isabelle-session                      │
│ incremental checking / snapshots / rollback / cache  │
└────────────────────────┬────────────────────────────┘
                         │
┌────────────────────────▼────────────────────────────┐
│                isabelle-isar                         │
│ proof state machine / commands / local theory        │
└────────────────────────┬────────────────────────────┘
                         │
┌────────────────────────▼────────────────────────────┐
│       isabelle-automation / isabelle-hammer          │
│ simp / auto / metis / meson / smt / reconstruction   │
└────────────────────────┬────────────────────────────┘
                         │
        ┌────────────────┴────────────────┐
        │                                 │
┌───────▼────────┐               ┌────────▼────────┐
│ isabelle-index │               │ isabelle-compute│
│ facts / terms  │               │ untrusted HPC   │
└───────┬────────┘               │ prefilters      │
        │                        └─────────────────┘
        │
┌────────────────────────▼────────────────────────────┐
│              isabelle-hol / isabelle-logic           │
│ Pure / HOL / datatype / quotient / transfer / BNF    │
└────────────────────────┬────────────────────────────┘
                         │
┌────────────────────────▼────────────────────────────┐
│                  isabelle-kernel                     │
│ LCF kernel / theorem / primitive inference / trust   │
└─────────────────────────────────────────────────────┘
```

Two proposed cross-cutting systems span the target layers (not current
implementations of these responsibilities):

```text
isabelle-build     proposed project scaffolding, dependency resolution,
                   lockfile, toolchain pinning, CI integration

isabelle-plugin    WASM/Rust plugin API, capability-based sandbox,
                   proof-script-only return boundary
```

The existing `isabelle-build` binary is instead a narrow source-backed fixture
compiler; `xtask` orchestrates repository builds/checks, not sessions/projects.

### Layer 1: `isabelle-kernel` — Trusted Computing Base

The only crate permitted to construct trusted theorems. Must have minimal
dependencies (no tokio, no LSP, no WASM, no parser generator, no SMT/ATP).

Responsibilities:

```text
type / term / cterm / theorem
primitive inference rules
certified substitution
unification checking
explicit logical-basis/axiom and definition dependencies
invariant checking and exact-owner replay
```

Explicitly excluded:

```text
parser, Isar, simp, auto, metis, sledgehammer, LSP, package manager,
Agent API, WASM plugin
```

### Layer 2: `isabelle-logic` / `isabelle-hol` — Object Logic

Separates Pure logical framework from HOL object logic. Datatype, typedef,
quotient, and BNF are *definitional packages* — they generate proof scripts
checked by the kernel rather than adding axioms directly.

### Layer 3: `isabelle-isar` — Proof Language

Isar state machine, proof methods, command dispatch. Depends on kernel for
theorem construction and on logic/HOL for object-level rules.

### Layer 4: `isabelle-automation` / `isabelle-hammer` — Proof Services

Automation methods (simp, auto, blast, fast, best, metis, meson, arith) and
external ATP/SMT bridges (Sledgehammer). These return proof scripts or
kernel-checkable evidence, not raw theorems.

### Layer 4a: `isabelle-index` / `isabelle-compute` — Untrusted Symbolic Compute

Indexes and high-performance symbolic compute are optional acceleration layers
for proof search. They may perform term/fact fingerprinting, fact prefiltering,
rewrite-rule candidate filtering, finite-domain counterexample search, and
batch proof-obligation quick rejection.

They are not trusted theorem constructors. Their outputs are candidates,
scores, fingerprints, diagnostics, or certificate drafts. Any result that
affects theorem state must still be replayed through exact proof-search code and
accepted by the CPU strict kernel.

`isabelle-compute` starts with a deterministic CPU baseline. Burn/CubeCL may be
evaluated later as an optional backend for packed symbolic compute, but no
backend-specific dependency may enter `isabelle-kernel`.

### Layer 5: `isabelle-session` — Incremental Engine

Content-addressed incremental checking with snapshot/rollback. Shared
infrastructure for both LSP (human editing) and Agent protocol (machine proof
search).

A design-only standalone API skeleton is
[proof_session.rs](../../scripts/templates/proof_session.rs). Its standalone
compilation does not validate integration with the current session API.

### Layer 6: `isabelle-lsp` / `isabelle-agent` — Interface Protocols

LSP serves human editors (diagnostics, hover, completion, go-to-definition).
Agent Proof Protocol (APP) serves machine proof search (goals, state diff,
rollback, method budget, proof tree, trust footprint, fact retrieval).

Both share `isabelle-session` but expose different protocol semantics.

### Layer 7: `isabelle-build` — Project System

Lake-style project scaffolding:

The proposed manifest is maintained as
[isabelle-project.toml](../../scripts/templates/isabelle-project.toml).

### Layer 8: `isabelle-plugin` — Historical Extensibility Proposal

The original proposal specified WASM-sandboxed plugins returning proof scripts,
but that platform layer was not implemented. The approved native direction
instead uses compile-time-linked Rust plugins with explicit registration and
host capability gates; in-process plugin code is trusted, not a WASM sandbox.
This authorization does not establish full native ROOT/HOL or ISIP delivery.

## Design Principles

```text
Kernel must be tiny.         — TCB minimal, auditable, independent.
Compatibility measurable.    — Core / Tier2 / AFP smoke matrix with CI.
Automation untrusted.        — Methods return proof scripts, not Thm.
Compute untrusted.           — GPU/multi-backend compute returns candidates,
                                not TrustedTheorem.
Projects reproducible.       — Lockfile, toolchain pinning, content-addressed cache.
Proof states structured.     — Goals, hyps, trust footprint as structured data.
Agents first-class.          — APP as a peer protocol to LSP, not an afterthought.
```

## Migration Strategy

Do not rewrite the entire system at once. Follow the strangler pattern already
established by ADR-0001:

| Phase | Deliverable | Depends on |
|-------|-----------|------------|
| **P0** | Stabilize strict kernel nucleus and `resolve1_match` prototype | ADR-0001 |
| **P1 (implemented)** | Extract `isabelle-kernel` as first independent crate | P0 kernel |
| **P1 (planned)** | Structured compatibility matrix (Core → Tier2 → AFP smoke) | P0 kernel |
| **P1/P2 parallel** | HPC symbolic compute design and CPU baseline outside the kernel | P0 kernel + compatibility matrix |
| **P2** | Session incremental engine (snapshot/rollback/cache) | P1 kernel crate |
| **P2** | `isabelle.toml` project system | P1 kernel crate |
| **P3** | Agent Proof Protocol (APP) | P2 session |
| **P3** | Automation returns proof scripts, not Thm | P0 kernel |
| **P4** | WASM plugin sandbox hardening | P3 agent |
| **P5** | AFP large-scale benchmark | P1 compatibility matrix |

## Consequences

- The strict kernel nucleus has been extracted into `crates/kernel/`. Cargo's
  workspace also contains root, the offline `isabelle-evidence` crate and
  `xtask`, with root-only default members; it does not split
  runtime/session/product layers. Agent protocol and runtime work remain
  gated by the current staged roadmap.
- The legacy `src/core/` remains migration/quarantine code. Necessary
  correctness repairs there do not grant it new trusted theorem authority.
- Further runtime crate splits follow only when their dependency boundaries
  are clear; neither extraction nor workspace automation proves the complete
  sampled HOL theorem loop.
- The high-performance symbolic compute layer is an untrusted acceleration
  layer. It must not add GPU dependencies to the kernel or bypass replay.
- Compatibility must have explicit measured evidence, not anecdotal claims.
- Documentation and the existing `.claude` adapter must track layer ownership.

## Related

- [ADR-0001](ADR-0001-kernel-core-rewrite.md) — Strangler-pattern kernel reset.
- [KERNEL_PRIMITIVES.md](../kernel/KERNEL_PRIMITIVES.md) — Strict kernel rule contracts.
- [ROADMAP.md](../status/ROADMAP.md) — Current phase plan.
- [PROJECT_STATUS.md](../status/PROJECT_STATUS.md) — Canonical status.
