# Isabelle-rs Documentation

## Directory Structure

```text
docs/
  adr/           Architecture Decision Records
  kernel/        Kernel TCB documentation
  design/        Design documents
  status/        Status, trust, and roadmap
  agent/         Agent rules, skills, and configs (mirror of .claude/)
  guides/        Developer guides
  archive/       Historical and superseded documents
  isip/          ISIP standard specifications
```

## ADRs — `docs/adr/`

| File | Status | Description |
|------|--------|-------------|
| [ADR-0001](adr/ADR-0001-kernel-core-rewrite.md) | Accepted | Kernel/core rewrite boundary |
| [ADR-0002](adr/ADR-0002-layered-platform-architecture.md) | Superseded | Original layered architecture |
| [ADR-0003](adr/ADR-0003-hol-logic-trusted-extension.md) | Accepted | HOL logic trusted extension |
| [ADR-0004](adr/ADR-0004-layered-platform-architecture-v2.md) | Accepted | Layered platform v2 (B+C+G) |

## Kernel TCB — `docs/kernel/`

| File | Description |
|------|-------------|
| [KERNEL_PRIMITIVES](kernel/KERNEL_PRIMITIVES.md) | Primitive rule catalog |
| [KERNEL_RULES](kernel/KERNEL_RULES.md) | Kernel rule reference |
| [KERNEL_ATTACK_TESTS](kernel/KERNEL_ATTACK_TESTS.md) | TCB attack test catalog |
| [KERNEL_TRUSTED_ACCEPTANCE_GAPS](kernel/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md) | Remaining acceptance gaps |
| [BASELINE](kernel/BASELINE.md) | First trusted-kernel engineering checkpoint |
| [MIGRATION_MATRIX](kernel/MIGRATION_MATRIX.md) | Core-to-kernel migration tracking |
| [CORE_KERNEL_OVERLAP_INVENTORY](kernel/CORE_KERNEL_OVERLAP_INVENTORY.md) | Core/kernel overlap inventory |
| [PROOF_OUTCOME_DESIGN](kernel/PROOF_OUTCOME_DESIGN.md) | Proof outcome classifier |

## Design — `docs/design/`

| File | Description |
|------|-------------|
| [RESOLUTION_DESIGN](design/RESOLUTION_DESIGN.md) | Resolution and rewriting design |
| [HPC_SYMBOLIC_COMPUTE_DESIGN](design/HPC_SYMBOLIC_COMPUTE_DESIGN.md) | HPC symbolic compute design |
| [CHECKED_HOL_PROPOSITION_NORMALIZATION](design/CHECKED_HOL_PROPOSITION_NORMALIZATION.md) | HOL proposition normalization |
| [CHECKED_DEFINITION_TRANSPORT](design/CHECKED_DEFINITION_TRANSPORT.md) | Checked definition transport |
| [HOL_OBJECT_EQUALITY_BRIDGE](design/HOL_OBJECT_EQUALITY_BRIDGE.md) | HOL object equality bridge |
| [NEXT_STRICT_SLICE_CANDIDATES](design/NEXT_STRICT_SLICE_CANDIDATES.md) | Next strict slice candidates |
| [COMPAT_CALLSITES](design/COMPAT_CALLSITES.md) | Compatibility callsite inventory |

## Status — `docs/status/`

| File | Description |
|------|-------------|
| [PROJECT_STATUS](status/PROJECT_STATUS.md) | Canonical project status and metrics |
| [PROJECT_STATUS.zh](status/PROJECT_STATUS.zh.md) | 项目状态（中文） |
| [TRUST](status/TRUST.md) | Trust model and T1-T4 criteria |
| [ROADMAP](status/ROADMAP.md) | Implementation roadmap |

## Agent — `docs/agent/`

| Directory | Description |
|-----------|-------------|
| [agents/](agent/agents/) | Agent definitions |
| [rules/](agent/rules/) | Coding rules |
| [skills/](agent/skills/) | Skill definitions |
| [hooks/](agent/hooks/) | Post-session hooks |
| [commands/](agent/commands/) | Slash commands |
| [templates/](agent/templates/) | Rule/skill templates |
| [CLAUDE_INTEGRATION](agent/CLAUDE_INTEGRATION.md) | Claude Code integration guide |

## Guides — `docs/guides/`

| File | Description |
|------|-------------|
| [DEVELOPMENT](guides/DEVELOPMENT.md) | Development setup and conventions |
| [DOCUMENT_INDEX](guides/DOCUMENT_INDEX.md) | This file |

## ISIP — `docs/isip/`

| File | Description |
|------|-------------|
| [ISIP](isip/ISIP.md) | Standard suite overview |
| [ISIP.zh](isip/ISIP.zh.md) | 标准体系总览（中文） |
| [ISIP-000](isip/ISIP-000-architecture.md) | Architecture and trust boundary |
| [ISIP-000.zh](isip/ISIP-000-architecture.zh.md) | 架构与可信边界（中文） |
| [README](isip/README.md) | ISIP spec index |

## Archive — `docs/archive/`

| File | Description |
|------|-------------|
| [ARCHITECTURE](archive/ARCHITECTURE.md) | Original architecture doc (superseded) |
| [GAP_ANALYSIS](archive/GAP_ANALYSIS.md) | Early gap analysis (superseded) |
| [SESSION_TRANSFER](archive/SESSION_TRANSFER.md) | Session transfer note |
| [SESSION_TRANSFER_v1.9.0](archive/SESSION_TRANSFER_v1.9.0.md) | Session transfer v1.9.0 |
