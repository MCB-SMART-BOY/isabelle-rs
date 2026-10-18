# ISIP: Isabelle Structured Interaction and Proof Standard

ISIP is an Isabelle-rs project proposal. “Standard” in this title refers to
the proposed specification suite, not a claim of adoption by an external
standards body or endorsement by the Isabelle developers or their institutions.

**Version:** Draft 0.1
**Status:** Design-only suite; no ISIP runtime. The strict kernel crate exists.
The pre-cutover bundled HOL sample reported `TransitionalStrictClosed: 0/125`
and `KernelTrustedClosed: 1/125`: only `HOL::TrueI` was accepted through its
audited source projection, checked basis and definition, Pure transport, and
owner replay. Independent Pure/HOL fixtures remain outside the sample. This
has not been rerun by the subsequently resumed P2/P3/P4 native closure
implementation and does not close the broader trusted HOL gate or authorize
any ISIP runtime. The approved
[native compatibility program](../status/ROADMAP.md#approved-native-compatibility-program)
separately targets official Isabelle capabilities, including Isabelle/ML and
PIDE. Package B has a historical reference-side baseline; C–H are unaccepted.
The separately approved compile-time Rust native plugin direction does not
implement ISIP or establish broad compatibility. ISIP stages do not replace
official PIDE/ML compatibility.
**Authoritative reference:** [AGENTS.md](../../AGENTS.md),
[ADR-0004](../adr/ADR-0004-layered-platform-architecture-v2.md), and
[PROJECT_STATUS.md](../status/PROJECT_STATUS.md) for implementation status.

## Abstract

ISIP is a proposed project specification suite for editor-agnostic, model-agnostic, transport-agnostic proof interaction. Its goal is to define the semantic model, runtime behavior, evidence format, wire protocol, and integration profiles needed for a modern proof engineering platform that serves human developers, IDEs, AI agents, and automated provers through a single headless runtime.

ISIP is not a single RPC protocol. It is a layered specification suite.

## Seven-Specification Plan

Only this overview and [ISIP-000](ISIP-000-architecture.md) exist as draft
specifications (also in [Chinese](ISIP.zh.md) and
[Chinese ISIP-000](ISIP-000-architecture.zh.md)). ISIP-100–600 below are
planned titles and scopes, not published specs or implemented interfaces.

| Spec | Title | Scope |
|------|-------|-------|
| [ISIP-000](ISIP-000-architecture.md) | Architecture and Trust Boundary | System layers, TCB definition, dependency direction |
| ISIP-100 (planned) | Semantic Model | DocumentRevision, ProofSnapshot, Goal, Fact, Action, Transition |
| ISIP-200 (planned) | Runtime Model | State lifecycle, branches, speculative execution, cancellation, leases |
| ISIP-300 (planned) | Evidence and Trust Model | Proof traces, certificates, kernel acceptance, oracle/admit, trust policy |
| ISIP-400 (planned) | Wire Protocol | JSON-RPC 2.0 methods, notifications, error codes, capability negotiation |
| ISIP-500 (planned) | Integration Profiles | LSP, MCP, A2A, Native SDK, CLI/CI mappings |
| ISIP-600 (planned) | Security and Conformance | Permissions, sandboxing, audit, threat model, compatibility levels |

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

**Critical rule:** The kernel (Layer 0) MUST NOT depend on ISIP, MCP, LSP, A2A, JSON-RPC, or AI. All ISIP specifications describe what sits ABOVE the kernel, never inside it. This is a proposed dependency model, not implemented ISIP conformance.

## Layer Architecture

```text
┌─────────────────────────────────────────────────────┐
│ IDE │ AI Host │ Multi-Agent │ CLI/CI │ Web/Cloud    │
├─────────┬──────────┬──────────┬──────────┬───────────┤
│   LSP   │   MCP    │   A2A    │ ISIP-CLI │ Native SDK│  ← ISIP-500
├─────────┴──────────┴──────────┴──────────┴───────────┤
│                    ISIP-Wire                         │  ← ISIP-400
├─────────────────────────────────────────────────────┤
│           Proposed runtime and semantics             │  ← ISIP-100/200 (planned)
│                                                     │
│ Document Runtime │ Proof Runtime │ Search Runtime    │
│ Branch Runtime   │ Artifact Runtime │ Trust Service  │
├─────────────────────────────────────────────────────┤
│             Logic Backend / Elaboration              │  ← Layer 1, not ISIP-300
│ Pure/HOL │ DTT │ Separation Logic │ SMT/SAT Checker │
├─────────────────────────────────────────────────────┤
│          Sealed Kernel APIs / Certificate Checkers   │  ← ISIP-000 boundary
└─────────────────────────────────────────────────────┘
```

ISIP-300 is the planned cross-cutting evidence/trust model; it is not the
logic-backend layer. The diagram shows the proposed architecture, not deployed
ISIP services or conformance.

## Identity Model

ISIP proposes four identity categories. These are design examples, not
implemented runtime type names:

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

The planned ISIP-300 would define four sub-models:

- **LogicalDependencies:** axioms, definitions, theorems used
- **Provenance:** methods, solvers, agents, source revisions
- **TrustBurden:** admits, oracles, unchecked external results
- **EvidenceStatus:** certificate, derivation replayed, kernel accepted

## Six Normative Requirements

1. **Kernel MUST NOT depend on ISIP, MCP, LSP, A2A, JSON-RPC, or AI.**
2. **External identifiers MUST NOT constitute theorem authority.**
3. **Speculative states MUST NOT directly extend a trusted theory.**
4. **StateDiff MUST NOT be the authoritative representation of state.**
5. **Search MAY be nondeterministic, but selected evidence MUST be independently checkable.**
6. **Cross-logic reuse MUST require explicit translation evidence.**

## Proposed ISIP Stages (separate from native compatibility packages A–H)

ISIP remains **design-only**; one sampled trusted HOL token does not close the
broader trusted HOL loop or authorize implementation of an ISIP runtime. The bundled sampler
reports `TransitionalStrictClosed: 0/125` and `KernelTrustedClosed: 1/125`,
from the narrowly audited `HOL::TrueI` source projection. Independent Pure/HOL
fixtures do not enter that batch; other HOL/ML commands have not been executed
by this path.

| ISIP Stage | Prerequisite | Content |
|------------|-------------|---------|
| **Stage 0 (now)** | None | This overview and ISIP-000 draft; ISIP-100 and ISIP-300 planned |
| **Stage 1: Observable** | Broader TCB closure; 1/125 alone is insufficient | `proof/getSnapshot`, `proof/getGoals`, `proof/getContext`, diagnostics |
| **Stage 2: Transactional** | Stage 1 | `ProofSnapshotId`, `LogicalAction`, `StateTransition`, `StateDiff` |
| **Stage 3: Branching + Agent** | Stage 2 | `fork`, `moveHead`, `tryBatch`, `explore`, budget, cancel, MCP Profile |
| **Stage 4: Evidence-Aware** | Stage 3 | Derivation replay, certificate checking, artifact persistence, theory extension |
| **Stage 5: Multi-Logic** | Stage 4 | Second logic backend, `TranslationEvidence`, A2A Profile |

See [ROADMAP.md](../status/ROADMAP.md) for the current TCB prerequisite and
approved native compatibility program. For automation evidence distinguish
the [historical package-A record](../status/PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11)
from the [2026-10-14 native automation record](../status/PROJECT_STATUS.md#native-rust-automation-verification-2026-10-14);
current commands are in the [engineering workflow](../guides/DEVELOPMENT.md#engineering-workflow).

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
- [ADR-0004: Layered Platform Architecture v2](../adr/ADR-0004-layered-platform-architecture-v2.md)
- [PROJECT_STATUS.md](../status/PROJECT_STATUS.md)
- [AGENTS.md](../../AGENTS.md)
