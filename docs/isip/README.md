# ISIP Specifications

## Status

All ISIP specifications are currently **Draft** (design documents). No runtime implementation exists. Implementation begins after the TCB closes (`KernelTrustedClosed: 1/125`).

## Specification Index

| Spec | Title | Status | Lines | Impl Phase |
|------|-------|--------|-------|------------|
| [ISIP.md](ISIP.md) | Standard Suite Overview | Draft | — | Stage 0 |
| [ISIP-000](ISIP-000-architecture.md) | Architecture and Trust Boundary | Draft | — | Stage 0 |
| ISIP-100 | Semantic Model | Planned | — | Stage 0 |
| ISIP-200 | Runtime Model | Planned | — | Stage 2 |
| ISIP-300 | Evidence and Trust Model | Planned | — | Stage 0 |
| ISIP-400 | Wire Protocol | Planned | — | Stage 2 |
| ISIP-500 | Integration Profiles | Planned | — | Stage 3 |
| ISIP-600 | Security and Conformance | Planned | — | Stage 4 |

## Implementation Phase Mapping

| ISIP Stage | Isabelle-rs Prerequisite | Specs Affected |
|------------|--------------------------|----------------|
| Stage 0: Design | None (current) | ISIP-000, ISIP-100 draft, ISIP-300 draft |
| Stage 1: Observable | TCB closed | ISIP-100 finalized |
| Stage 2: Transactional | Stage 1 | ISIP-200, ISIP-400 |
| Stage 3: Branching + Agent | Stage 2 | ISIP-500 (MCP, Native) |
| Stage 4: Evidence-Aware | Stage 3 | ISIP-300 finalized, ISIP-600 |
| Stage 5: Multi-Logic | Stage 4 | ISIP-500 (A2A), ISIP-100 v2 |

## Normative Language

ISIP specifications use [RFC 2119](https://www.ietf.org/rfc/rfc2119.txt) keywords:
- **MUST** / **MUST NOT** — absolute requirement
- **SHOULD** / **SHOULD NOT** — recommended, may be violated with good reason
- **MAY** — optional

All "MUST" statements in ISIP specs are design constraints for future implementation, not assertions about current code compliance.

## Chinese Versions

- [ISIP.zh.md](ISIP.zh.md) — 标准体系总览
- [ISIP-000-architecture.zh.md](ISIP-000-architecture.zh.md) — 架构与可信边界
