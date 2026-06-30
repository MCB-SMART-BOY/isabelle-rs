# ADR-0002: Layered Platform Architecture

## Status

Accepted.

## Context

ADR-0001 established the strangler-pattern kernel reset: `src/kernel/` as the
new strict TCB nucleus with no dummy type, no compat certification, and
`ProofObligation ≠ Thm`. That decision was about *how* to build the kernel.

This ADR addresses *what comes after the kernel* — the overall system
architecture that the strict kernel nucleus enables.

The current codebase is a single monolithic crate with internal modules
(`core`, `hol`, `isar`, `theory`, `tools`, `session`, `lsp`, `server`, `wasm`,
`syntax`, `kernel`). While functional as a research prototype, this structure
will not scale to:

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

Two cross-cutting systems span all layers:

```text
isabelle-build     project scaffolding, dependency resolution,
                   lockfile, toolchain pinning, CI integration

isabelle-plugin    WASM/Rust plugin API, capability-based sandbox,
                   proof-script-only return boundary
```

### Layer 1: `isabelle-kernel` — Trusted Computing Base

The only crate permitted to construct trusted theorems. Must have minimal
dependencies (no tokio, no LSP, no WASM, no parser generator, no SMT/ATP).

Responsibilities:

```text
type / term / cterm / theorem
primitive inference rules
certified substitution
unification checking
oracle footprint
proof certificate hash
invariant checking
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

### Layer 5: `isabelle-session` — Incremental Engine

Content-addressed incremental checking with snapshot/rollback. Shared
infrastructure for both LSP (human editing) and Agent protocol (machine proof
search).

```rust
pub trait ProofSession {
    fn snapshot(&self) -> SnapshotId;
    fn apply_command(&mut self, span: CommandSpan) -> Result<StateDiff>;
    fn rollback(&mut self, snapshot: SnapshotId);
    fn goals(&self) -> Vec<GoalView>;
    fn diagnostics(&self) -> Vec<Diagnostic>;
}
```

### Layer 6: `isabelle-lsp` / `isabelle-agent` — Interface Protocols

LSP serves human editors (diagnostics, hover, completion, go-to-definition).
Agent Proof Protocol (APP) serves machine proof search (goals, state diff,
rollback, method budget, proof tree, trust footprint, fact retrieval).

Both share `isabelle-session` but expose different protocol semantics.

### Layer 7: `isabelle-build` — Project System

Lake-style project scaffolding:

```toml
[package]
name = "my-project"
version = "0.1.0"
logic = "HOL"
edition = "2026"

[toolchain]
isabelle-rs = "2.3.0"

[dependencies]
AFP = "2026.1"

[build]
parallel = true
incremental = true
deny_admit = true
```

### Layer 8: `isabelle-plugin` — Extensibility

WASM-sandboxed plugins with capability restrictions. Plugins return proof
scripts, not theorems.

## Design Principles

```text
Kernel must be tiny.         — TCB minimal, auditable, independent.
Compatibility measurable.    — Core / Tier2 / AFP smoke matrix with CI.
Automation untrusted.        — Methods return proof scripts, not Thm.
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
| **P0** | Strict-kernel compatibility matrix and adapter boundaries | P0 kernel |
| **P1** | Extract `isabelle-kernel` as first independent crate | P0 kernel |
| **P1** | Structured compatibility matrix (Core → Tier2 → AFP smoke) | P0 kernel |
| **P2** | Session incremental engine (snapshot/rollback/cache) | P1 kernel crate |
| **P2** | `isabelle.toml` project system | P1 kernel crate |
| **P3** | Agent Proof Protocol (APP) | P2 session |
| **P3** | Automation returns proof scripts, not Thm | P0 kernel |
| **P4** | WASM plugin sandbox hardening | P3 agent |
| **P5** | AFP large-scale benchmark | P1 compatibility matrix |

## Consequences

- The strict kernel nucleus (`src/kernel/`) remains the top priority. Do not
  start workspace splitting, session redesign, or Agent protocol work before
  the strict-kernel prototype has stable rule contracts, invariant checks,
  attack tests, firewall checks, and adapter-boundary documentation.
- The legacy `src/core/` is frozen. New features go into the appropriate
  target layer, not into the monolithic crate.
- The first workspace split extracts `isabelle-kernel` only. Other crates
  follow only when their dependency boundaries are clear.
- "Compatibility" becomes a measurable CI metric, not an anecdotal claim.
- Documentation and `.codex`/`.claude` references must track which layer a
  change belongs to.

## Related

- [ADR-0001](ADR-0001-kernel-core-rewrite.md) — Strangler-pattern kernel reset.
- [KERNEL_PRIMITIVES.md](KERNEL_PRIMITIVES.md) — Strict kernel rule contracts.
- [ROADMAP.md](ROADMAP.md) — Current phase plan.
- [PROJECT_STATUS.md](PROJECT_STATUS.md) — Canonical status.
