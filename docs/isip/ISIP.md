# ISIP: Isabelle Structured Interaction and Proof Standard

**Version:** Draft 0.1
**Status:** Design document — no runtime implementation until TCB closes.
**Authoritative reference:** `AGENTS.md`, `docs/ADRs/`, source code.

## Abstract

ISIP is a family of standards for editor-agnostic, model-agnostic, transport-agnostic proof interaction. Its goal is to define the semantic model, runtime behavior, evidence format, wire protocol, and integration profiles needed for a modern proof engineering platform that serves human developers, IDEs, AI agents, and automated provers through a single headless runtime.

ISIP is not a single RPC protocol. It is a layered specification suite.

## The Seven Specifications

| Spec | Title | Scope |
|------|-------|-------|
| **ISIP-000** | Architecture and Trust Boundary | System layers, TCB definition, dependency direction |
| **ISIP-100** | Semantic Model | DocumentRevision, ProofSnapshot, Goal, Fact, Action, Transition |
| **ISIP-200** | Runtime Model | State lifecycle, branches, speculative execution, cancellation, leases |
| **ISIP-300** | Evidence and Trust Model | Proof traces, certificates, kernel acceptance, oracle/admit, trust policy |
| **ISIP-400** | Wire Protocol | JSON-RPC 2.0 methods, notifications, error codes, capability negotiation |
| **ISIP-500** | Integration Profiles | LSP, MCP, A2A, Native SDK, CLI/CI mappings |
| **ISIP-600** | Security and Conformance | Permissions, sandboxing, audit, threat model, compatibility levels |

### Dependency Direction

```text
ISIP-500 Profiles (LSP, MCP, A2A, CLI, Native)
    ↓ depends on
ISIP-400 Wire Protocol
    ↓ depends on
ISIP-200 Runtime + ISIP-300 Evidence
    ↓ depends on
ISIP-100 Semantic Model
    ↓ depends on
ISIP-000 Architecture + Kernel TCB
```

**Critical rule:** The kernel (Layer 0) MUST NOT depend on ISIP, MCP, LSP, A2A, JSON-RPC, or AI. All ISIP specifications describe what sits ABOVE the kernel, never inside it.

## Layer Architecture

```text
┌─────────────────────────────────────────────────────┐
│ IDE │ AI Host │ Multi-Agent │ CLI/CI │ Web/Cloud    │
├─────────┬──────────┬──────────┬──────────┬───────────┤
│   LSP   │   MCP    │   A2A    │ ISIP-CLI │ Native SDK│  ← ISIP-500
├─────────┴──────────┴──────────┴──────────┴───────────┤
│                    ISIP-Wire                         │  ← ISIP-400
├─────────────────────────────────────────────────────┤
│              ISIP Runtime and Semantics              │  ← ISIP-100/200
│                                                     │
│ Document Runtime │ Proof Runtime │ Search Runtime    │
│ Branch Runtime   │ Artifact Runtime │ Trust Service  │
├─────────────────────────────────────────────────────┤
│             Logic Backend / Elaboration              │  ← ISIP-300
│ Pure/HOL │ DTT │ Separation Logic │ SMT/SAT Checker │
├─────────────────────────────────────────────────────┤
│          Sealed Kernel APIs / Certificate Checkers   │  ← ISIP-000
└─────────────────────────────────────────────────────┘
```

## Identity Model

ISIP distinguishes four identity categories:

| Category | Example | Properties |
|----------|---------|------------|
| **Content identity** | `TheorySnapshotId`, `TrustedArtifactId` | Immutable, computed from canonical content |
| **Runtime handle** | `ProofSnapshotHandle`, `TaskId` | Session-local, opaque, not persistent |
| **Mutable reference** | `BranchId`, `SessionId` | Points to current content identity |
| **External reference** | `"thm:abc"` in JSON-RPC | Query-only, never grants theorem authority |

## Trust Model

The core formula:

```text
Authoritative Snapshot
        +
Typed Action
        ↓
Speculative Transition + State Diff + Trust Delta
        ↓
Selected Evidence
        ↓
Independent Check (replay or certificate verification)
        ↓
Kernel-Accepted Artifact
```

ISIP-300 defines four sub-models:

- **LogicalDependencies:** axioms, definitions, theorems used
- **Provenance:** methods, solvers, agents, source revisions
- **TrustBurden:** admits, oracles, unchecked external results
- **EvidenceStatus:** certificate, derivation replayed, kernel accepted

## Six Normative Requirements

1. **Kernel MUST NOT depend on ISIP, MCP, LSP, A2A, or AI.**
2. **External identifiers MUST NOT constitute theorem authority.**
3. **Speculative states MUST NOT directly extend a trusted theory.**
4. **StateDiff MUST NOT be the authoritative representation of state.**
5. **Search MAY be nondeterministic, but selected evidence MUST be independently checkable.**
6. **Cross-logic reuse MUST require explicit translation evidence.**

## Isabelle-rs Implementation Phases

ISIP implementation is **design-only** until the TCB closes (`KernelTrustedClosed: 1/125`).

| ISIP Stage | Prerequisite | Content |
|------------|-------------|---------|
| **Stage 0 (now)** | None | ISIP-000 ADR, ISIP-100 Semantic Draft, ISIP-300 Identity Draft |
| **Stage 1: Observable** | TCB closed | `proof/getSnapshot`, `proof/getGoals`, `proof/getContext`, diagnostics |
| **Stage 2: Transactional** | Stage 1 | `ProofSnapshotId`, `LogicalAction`, `StateTransition`, `StateDiff` |
| **Stage 3: Branching + Agent** | Stage 2 | `fork`, `moveHead`, `tryBatch`, `explore`, budget, cancel, MCP Profile |
| **Stage 4: Evidence-Aware** | Stage 3 | Derivation replay, certificate checking, artifact persistence, theory extension |
| **Stage 5: Multi-Logic** | Stage 4 | Second logic backend, `TranslationEvidence`, A2A Profile |

See [ROADMAP.md](../ROADMAP.md) for the current TCB main line that precedes ISIP implementation.

## What ISIP Does NOT Govern

- Kernel internal data structures
- How `accept_closed_theorem` is implemented
- Which Rust types represent theorems
- AI model selection or training
- The Isar language grammar
- Specific proof method implementations
- Build system or package management

## References

- [ISIP-000: Architecture and Trust Boundary](ISIP-000-architecture.md)
- [ADR-0004: Layered Platform Architecture v2](../ADR-0004-layered-platform-architecture-v2.md)
- [PROJECT_STATUS.md](../PROJECT_STATUS.md)
- [AGENTS.md](../../AGENTS.md)
