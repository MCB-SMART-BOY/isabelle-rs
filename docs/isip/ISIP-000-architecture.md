# ISIP-000: Architecture and Trust Boundary

**ISIP Version:** Draft 0.1
**Status:** Design document
**Depends on:** Nothing (this is the root specification)

## 1. Scope

ISIP-000 defines the layered system architecture for an ISIP-compliant proof platform. It establishes the Trusted Computing Base (TCB), dependency direction, and the boundary between trusted kernel operations and untrusted platform services.

## 2. Layer Model

An ISIP-compliant system SHALL be organized into at least these four layers:

### Layer 0: Trusted Computing Base

The TCB is the set of components whose correctness is necessary for theorem soundness.

**Contains:** Theorem types, primitive inference rules, certified terms/propositions, theory ancestry, certificate checkers, the `accept_closed_theorem` operation.

**MUST NOT contain:** Async runtimes, databases, network I/O, WASM, GPU compute, AI models, LSP handlers, JSON serialization, session state, document versions, proof search algorithms.

**Dependencies:** Limited to cryptographic hashing (`sha2`) and error handling (`thiserror`). In Isabelle-rs, this is the `isabelle-kernel` crate.

**Zero-warning policy:** The TCB MUST compile with zero warnings under `RUSTFLAGS="-D warnings"`.

### Layer 1: Logic Backend

Responsible for declaration-aware parsing, name resolution, checked elaboration, logic-basis manifests, axiom/definition instantiation.

**Interface:** `trait LogicBackend` with methods for `elaborate`, `available_actions`, `apply`, and `check`.

**Contains:** Pure/HOL elaborator, type inference, sort checking, `LogicBasis` manifests, axiom schema replay.

**MUST NOT:** Construct `TrustedTheorem` values directly. All theorem construction goes through Layer 0.

### Layer 2: Document and Proof Runtime

Headless, editor-independent engine managing document versions, incremental updates, dependency graphs, diagnostics, cancellation, semantic markup, proof snapshots, goals, and fork/rollback/replay.

**Interface:** `trait DocumentEngine` and `trait ProofSession`.

**Contains:** `DocumentRevision`, `ProofSnapshot`, `BranchId`, `GoalId`, `StateTransition`, `StateDiff`, `Diagnostic`, lease management, garbage collection.

**MUST NOT:** Depend on any specific editor, IDE, AI framework, or protocol.

### Layer 3: Adapters

Thin protocol adapters mapping ISIP semantics to specific client protocols.

**Contains:** LSP adapter, MCP adapter, A2A adapter, CLI adapter, Native SDK.

**MUST NOT:** Own proof state, construct theorems, or make trust decisions. Adapters translate requests/responses only.

## 3. Dependency Direction

Dependencies MUST flow strictly downward:

```text
Layer 3 (Adapters)
    ↓
Layer 2 (Runtime)
    ↓
Layer 1 (Logic)
    ↓
Layer 0 (Kernel)
```

**Forbidden dependencies:**
- Layer 0 → any higher layer
- Layer 1 → Layer 3
- Kernel → MCP, LSP, A2A, JSON-RPC, Tokio, HTTP
- Kernel → AI models, GPU, WASM

## 4. Stable vs Experimental Separation

Crates SHALL be tagged as `stable` or `experimental` in `Cargo.toml` metadata.

- **Experimental** crates MUST NOT appear in the dependency graph of any `stable` crate.
- **Experimental** crates MUST NOT construct or certify `TrustedTheorem` values.
- The TCB (Layer 0) is always `stable`.

## 5. Theorem Authority

External clients (LSP, MCP, A2A, CLI, AI agents) MAY submit:

- References to existing theorems (by content identity)
- Candidate proof actions
- Candidate derivations
- Candidate certificates

They MUST NOT submit:

- `TrustedTheorem` tokens
- `KernelThm` values
- `CertifiedTerm` / `CProp` values
- Theory extension authority

All external identifiers are query references, never theorem capabilities. The runtime MUST resolve external IDs against current theory ancestry before authorizing any operation that depends on theorem identity.

## 6. Speculative Execution

The runtime MAY execute proof actions in isolated branches.

- Speculative branches MUST NOT extend the trusted theory.
- Speculative results MUST be replayed or certificate-checked before acceptance.
- Failed speculative branches MAY be garbage-collected.

## 7. What ISIP-000 Does NOT Specify

- Kernel implementation details (Rust types, algorithm choices)
- Proof language grammar (Isar, tactic scripts)
- Specific proof methods or automation
- Build system, package management
- Network transport, serialization formats
- AI model architecture or training

## 8. Conformance

An implementation MAY claim ISIP-000 conformance if it:

1. Has a clearly bounded TCB with documented dependencies
2. Enforces the layer dependency direction
3. Separates stable from experimental code
4. Does not allow external clients to construct theorem values
5. Requires kernel acceptance (not just trial success) for trusted artifacts
6. Distinguishes speculative states from accepted theory extensions

## References

- [ISIP Overview](ISIP.md)
- [ADR-0004: Layered Platform Architecture v2](../ADR-0004-layered-platform-architecture-v2.md)
- [AGENTS.md: Platform Architecture](../../AGENTS.md)
