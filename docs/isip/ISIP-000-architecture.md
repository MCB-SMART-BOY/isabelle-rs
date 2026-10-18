# ISIP-000: Architecture and Trust Boundary

**ISIP Version:** Draft 0.1
**Status:** Design only; not an implemented conformance claim. Only this
specification and the overview exist; ISIP-100–600 remain planned.
**Depends on:** Nothing (this is the root design specification)

## 1. Scope

ISIP-000 defines the layered system architecture for an ISIP-compliant proof platform. It establishes the Trusted Computing Base (TCB), dependency direction, and the boundary between trusted kernel operations and untrusted platform services.

Current implementation checkpoint: `crates/kernel/` is the isolated strict
TCB crate (`sha2` and `thiserror` dependencies); `src/kernel/mod.rs` re-exports
it. The pre-cutover bundled HOL sample reported
`TransitionalStrictClosed: 0/125` and `KernelTrustedClosed: 1/125`, solely for the audited `HOL::TrueI`
source projection; independent Pure/HOL fixtures are outside the batch.
The subsequently resumed P2/P3/P4 native closure implementation has not rerun
that sample or established broader HOL acceptance. It neither authorizes ISIP
runtime work nor establishes whole-theory execution, a protocol, or conformance.
The approved [native compatibility program](../status/ROADMAP.md#approved-native-compatibility-program)
separately targets official Isabelle/ML and PIDE functionality. Package B has
a historical reference-side baseline; C–H remain unaccepted, and ISIP does not
replace that compatibility work. Separately approved compile-time Rust native
plugins do not implement the ISIP layers or certify platform conformance.
For [historical package-A evidence](../status/PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11),
the [2026-10-14 native automation record](../status/PROJECT_STATUS.md#native-rust-automation-verification-2026-10-14),
and current commands see the [engineering workflow](../guides/DEVELOPMENT.md#engineering-workflow).

## 2. Layer Model

An ISIP-compliant system SHALL be organized into at least these four layers:

### Layer 0: Trusted Computing Base

The TCB is the set of components whose correctness is necessary for theorem soundness.

**Proposed TCB responsibilities:** Theorem types, primitive inference rules, certified terms/propositions, theory ancestry, certificate checkers, the `accept_closed_theorem` operation. This list is a design constraint, not proof of implementation completeness.

**MUST NOT contain or depend on:** ISIP, MCP/LSP/A2A, AI models, async runtimes, databases, network I/O, WASM, GPU compute, LSP handlers, JSON serialization, session state, document versions, proof search algorithms.

**Dependencies:** Limited to cryptographic hashing (`sha2`) and error handling (`thiserror`). In Isabelle-rs, this is the `isabelle-kernel` crate.

**Zero-warning policy:** The TCB MUST compile with zero warnings under `RUSTFLAGS="-D warnings"`; this is a design requirement, not a claim that every present quality gate passes.

### Layer 1: Logic Backend

Responsible for declaration-aware parsing, name resolution, checked elaboration, logic-basis manifests, axiom/definition instantiation.

**Proposed interface:** `trait LogicBackend` with methods for `elaborate`,
`available_actions`, `apply`, and `check`; the trait is not implemented today.

**Responsibility:** Pure/HOL elaboration, type inference and sort checking,
logic-basis manifests. The strict kernel validates installed axiom schemas and
replays theorem derivations; this logic layer does not authorize theorem roots.

**MUST NOT:** Construct `TrustedTheorem` values directly. All theorem construction goes through Layer 0.

### Layer 2: Document and Proof Runtime

Headless, editor-independent engine managing document versions, incremental updates, dependency graphs, diagnostics, cancellation, semantic markup, proof snapshots, goals, and fork/rollback/replay.

**Proposed interfaces:** `trait DocumentEngine` and `trait ProofSession`;
these traits are not present in the current code.

**Proposed schema (not present as ISIP runtime types):** `DocumentRevision`, `ProofSnapshot`, `BranchId`, `GoalId`, `StateTransition`, `StateDiff`, `Diagnostic`, lease management, garbage collection.

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

The proposed `stable` / `experimental` crate classification is not present
as enforced metadata or dependency policy in the current workspace. Cargo
does not enforce such a classification automatically. Future implementation
would need an explicit policy and enforcement:

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

An implementation MAY claim ISIP-000 conformance only after demonstrating the
following behavior; the current Isabelle-rs code does not claim conformance:

1. Has a clearly bounded TCB with documented dependencies
2. Enforces the layer dependency direction
3. Separates stable from experimental code
4. Does not allow external clients to construct theorem values
5. Requires kernel acceptance (not just trial success) for trusted artifacts
6. Distinguishes speculative states from accepted theory extensions

## References

- [ISIP Overview](ISIP.md)
- [ADR-0004: Layered Platform Architecture v2](../adr/ADR-0004-layered-platform-architecture-v2.md)
- [AGENTS.md: Platform Architecture](../../AGENTS.md)
