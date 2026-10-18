# ISIP Specifications

## Status

These are Isabelle-rs project drafts, not a claim of external standardization
or official Isabelle endorsement.

Only the overview and ISIP-000 currently exist (each in English and Chinese).
They are **Draft**, design-only documents. ISIP-100 through ISIP-600 are
planned titles, not existing specifications or runtime features. The
pre-cutover bundled HOL sample reported `TransitionalStrictClosed: 0/125` and
`KernelTrustedClosed: 1/125`, solely for the audited `HOL::TrueI` source
projection; independent trusted fixtures remain outside the sample. The
subsequently resumed P2/P3/P4 native closure implementation has not rerun this
sample or established broader HOL acceptance. This token neither closes the
trusted HOL gate nor authorizes an ISIP runtime. The approved
[native compatibility program](../status/ROADMAP.md#approved-native-compatibility-program)
targets official Isabelle functionality, including PIDE and Isabelle/ML.
Package B has a historical reference-side baseline, not native acceptance;
C–H remain unaccepted. The separately approved compile-time Rust native plugin
direction is not an ISIP implementation or proof of broad platform compatibility.
ISIP cannot substitute for official PIDE/ML compatibility. Distinguish the
[historical package-A record](../status/PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11)
from the [2026-10-14 native automation record](../status/PROJECT_STATUS.md#native-rust-automation-verification-2026-10-14);
current commands are in the [engineering workflow](../guides/DEVELOPMENT.md#engineering-workflow).

## Specification Index

| Spec | Title | Status | Earliest stage |
|------|-------|--------|----------------|
| [ISIP.md](ISIP.md) | Proposed Specification Suite Overview | Draft | Stage 0 |
| [ISIP-000](ISIP-000-architecture.md) | Architecture and Trust Boundary | Draft | Stage 0 |
| ISIP-100 | Semantic Model | Planned, no file | Stage 0 design |
| ISIP-200 | Runtime Model | Planned, no file | Stage 2 |
| ISIP-300 | Evidence and Trust Model | Planned, no file | Stage 0 design |
| ISIP-400 | Wire Protocol | Planned, no file | Stage 2 |
| ISIP-500 | Integration Profiles | Planned, no file | Stage 3 |
| ISIP-600 | Security and Conformance | Planned, no file | Stage 4 |

## Proposed ISIP Stage Mapping (not native compatibility packages A–H)

| ISIP Stage | Isabelle-rs Prerequisite | Specs Affected |
|------------|--------------------------|----------------|
| Stage 0: Design | None (current) | Overview and ISIP-000 exist; ISIP-100 and ISIP-300 planned |
| Stage 1: Observable | Broader trusted-kernel HOL closure, not the single sampled token | ISIP-100 (planned) |
| Stage 2: Transactional | Stage 1 | ISIP-200, ISIP-400 |
| Stage 3: Branching + Agent | Stage 2 | ISIP-500 (MCP, Native) |
| Stage 4: Evidence-Aware | Stage 3 | ISIP-300 and ISIP-600 (planned) |
| Stage 5: Multi-Logic | Stage 4 | ISIP-500 and ISIP-100 revisions (planned) |

## Normative Language

ISIP specifications use [RFC 2119](https://www.ietf.org/rfc/rfc2119.txt) keywords:
- **MUST** / **MUST NOT** — absolute requirement
- **SHOULD** / **SHOULD NOT** — recommended, may be violated with good reason
- **MAY** — optional

All "MUST" statements in existing ISIP drafts are design constraints for future
implementation, not assertions about current code compliance. The TCB
MUST NOT depend on ISIP, MCP, LSP, A2A, protocols, or AI.

## Chinese Versions

- [ISIP.zh.md](ISIP.zh.md) — 标准体系总览
- [ISIP-000-architecture.zh.md](ISIP-000-architecture.zh.md) — 架构与可信边界
