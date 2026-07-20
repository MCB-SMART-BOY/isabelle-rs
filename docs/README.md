# Isabelle-rs Documentation Index

This file classifies every markdown document in the repository.

## Classification Tags

| Tag | Meaning |
|-----|---------|
| **ADR** | Architecture Decision Record |
| **Status** | Canonical project status/position |
| **Design** | Design document (may precede implementation) |
| **Guide** | Agent or developer guide |
| **Reference** | Reference material (primitive lists, rule tables) |
| **Historical** | Superseded or archival |
| **ISIP** | ISIP standard specification |

| Layer | Meaning |
|-------|---------|
| **Kernel** | TCB, trusted theorem construction |
| **Logic** | Pure/HOL elaboration, checked judgments |
| **Runtime** | Session, document, proof state |
| **Adapter** | LSP, CLI, Agent protocol |
| **Cross-cutting** | Spans multiple layers |
| **Meta** | Project governance, workflow, agent rules |

## Root Documents

| File | Type | Layer | Status | Description |
|------|------|-------|--------|-------------|
| [AGENTS.md](../AGENTS.md) | Guide | Meta | Current | Harness-neutral agent entry point, authority order, TCB boundaries, ISIP vision |
| [AGENTS.zh.md](../AGENTS.zh.md) | Guide | Meta | Current | 中文摘要：代理指南、可信边界、ISIP 愿景 |
| [README.md](../README.md) | Status | Cross-cutting | Current | Project README |
| [README.zh.md](../README.zh.md) | Status | Cross-cutting | Current | 项目中文说明 |
| [CHANGELOG.md](../CHANGELOG.md) | Reference | Meta | Current | Version history |
| [CLAUDE.md](../CLAUDE.md) | Guide | Meta | Current | Claude Code agent configuration |

## Status & Trust Documents

| File | Type | Layer | Status | Description |
|------|------|-------|--------|-------------|
| [PROJECT_STATUS.md](PROJECT_STATUS.md) | Status | Cross-cutting | Current | Canonical high-level status, trust metrics, known debts |
| [PROJECT_STATUS.zh.md](PROJECT_STATUS.zh.md) | Status | Cross-cutting | Current | 项目状态中文摘要 |
| [TRUST.md](TRUST.md) | Status | Kernel | Current | Trust model, T1-T4 criteria, theorem status semantics |
| [KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](KERNEL_TRUSTED_ACCEPTANCE_GAPS.md) | Status | Kernel | Current | Remaining gaps between current acceptance and full TCB closure |
| [BASELINE.md](BASELINE.md) | Reference | Kernel | Current | First trusted-kernel engineering checkpoint baseline |

## Architecture Decision Records

| File | Type | Layer | Status | Description |
|------|------|-------|--------|-------------|
| [ADR-0001-kernel-core-rewrite.md](ADR-0001-kernel-core-rewrite.md) | ADR | Kernel | Accepted | Kernel/core rewrite motivation and boundary |
| [ADR-0002-layered-platform-architecture.md](ADR-0002-layered-platform-architecture.md) | ADR | Cross-cutting | Superseded | Original layered architecture (superseded by ADR-0004) |
| [ADR-0003-hol-logic-trusted-extension.md](ADR-0003-hol-logic-trusted-extension.md) | ADR | Logic | Accepted | HOL logic trusted extension design gate |
| [ADR-0004-layered-platform-architecture-v2.md](ADR-0004-layered-platform-architecture-v2.md) | ADR | Cross-cutting | Accepted | Layered platform v2 (B+C+G model, 2026-07-21) |

## ISIP Standard Specifications

| File | Type | Layer | Status | Description |
|------|------|-------|--------|-------------|
| [isip/README.md](isip/README.md) | ISIP | Cross-cutting | Draft | ISIP specification index and status |
| [isip/ISIP.md](isip/ISIP.md) | ISIP | Cross-cutting | Draft | ISIP standard suite overview |
| [isip/ISIP.zh.md](isip/ISIP.zh.md) | ISIP | Cross-cutting | Draft | ISIP 标准体系总览（中文） |
| [isip/ISIP-000-architecture.md](isip/ISIP-000-architecture.md) | ISIP | Cross-cutting | Draft | ISIP-000: Architecture and Trust Boundary |
| [isip/ISIP-000-architecture.zh.md](isip/ISIP-000-architecture.zh.md) | ISIP | Cross-cutting | Draft | ISIP-000: 架构与可信边界（中文） |

## Design Documents (Draft)

| File | Type | Layer | Status | Description |
|------|------|-------|--------|-------------|
| [ROADMAP.md](ROADMAP.md) | Design | Cross-cutting | Current | Dependency-ordered implementation roadmap |
| [ARCHITECTURE.md](ARCHITECTURE.md) | Design | Cross-cutting | Historical | Original architecture doc (superseded by ADRs) |
| [CHECKED_DEFINITION_TRANSPORT.md](CHECKED_DEFINITION_TRANSPORT.md) | Design | Logic | Draft | Checked definition transport bridge design |
| [CHECKED_HOL_PROPOSITION_NORMALIZATION.md](CHECKED_HOL_PROPOSITION_NORMALIZATION.md) | Design | Logic | Draft | HOL proposition normalization design |
| [HOL_OBJECT_EQUALITY_BRIDGE.md](HOL_OBJECT_EQUALITY_BRIDGE.md) | Design | Logic | Draft | HOL object equality bridge design |
| [HPC_SYMBOLIC_COMPUTE_DESIGN.md](HPC_SYMBOLIC_COMPUTE_DESIGN.md) | Design | Cross-cutting | Draft | HPC symbolic compute design |
| [PROOF_OUTCOME_DESIGN.md](PROOF_OUTCOME_DESIGN.md) | Design | Kernel | Current | Proof outcome classifier design |
| [RESOLUTION_DESIGN.md](RESOLUTION_DESIGN.md) | Design | Kernel | Current | Strict resolution/rewriting design |

## Reference Documents

| File | Type | Layer | Status | Description |
|------|------|-------|--------|-------------|
| [KERNEL_PRIMITIVES.md](KERNEL_PRIMITIVES.md) | Reference | Kernel | Current | Kernel primitive rule catalog |
| [KERNEL_RULES.md](KERNEL_RULES.md) | Reference | Kernel | Current | Kernel rule reference |
| [KERNEL_ATTACK_TESTS.md](KERNEL_ATTACK_TESTS.md) | Reference | Kernel | Current | TCB attack test catalog |
| [COMPAT_CALLSITES.md](COMPAT_CALLSITES.md) | Reference | Logic | Current | Compatibility callsite inventory |
| [CORE_KERNEL_OVERLAP_INVENTORY.md](CORE_KERNEL_OVERLAP_INVENTORY.md) | Reference | Kernel | Current | Core/kernel overlap inventory |
| [DEVELOPMENT.md](DEVELOPMENT.md) | Guide | Meta | Current | Development setup and conventions |
| [MIGRATION_MATRIX.md](MIGRATION_MATRIX.md) | Reference | Kernel | Current | Core-to-kernel migration tracking |
| [NEXT_STRICT_SLICE_CANDIDATES.md](NEXT_STRICT_SLICE_CANDIDATES.md) | Reference | Cross-cutting | Draft | Next strict slice candidate inventory |

## Historical Documents

| File | Type | Layer | Status | Description |
|------|------|-------|--------|-------------|
| [GAP_ANALYSIS.md](GAP_ANALYSIS.md) | Reference | Cross-cutting | Historical | Early gap analysis (superseded by KERNEL_TRUSTED_ACCEPTANCE_GAPS.md) |
| [SESSION_TRANSFER.md](SESSION_TRANSFER.md) | Reference | Cross-cutting | Historical | Session transfer note |
| [SESSION_TRANSFER_v1.9.0.md](SESSION_TRANSFER_v1.9.0.md) | Reference | Cross-cutting | Historical | Session transfer v1.9.0 note |

## Script Documentation

| File | Type | Layer | Status | Description |
|------|------|-------|--------|-------------|
| [../scripts/README.md](../scripts/README.md) | Guide | Meta | Current | Script usage and modes |
| [../scripts/templates/README.md](../scripts/templates/README.md) | Reference | Meta | Current | Template classification |
