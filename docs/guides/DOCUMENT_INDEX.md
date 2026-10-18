# Isabelle-rs Documentation

This index links to the current repository layout. Read [AGENTS.md](../../AGENTS.md)
and the [canonical project status](../status/PROJECT_STATUS.md) before historical
notes; `.claude/` is the sole agent-adapter directory, not a `docs/agent/` mirror.

## Reading and Maintenance Workflow

1. Read current [status](../status/PROJECT_STATUS.md#current-delivery-state),
   [trust](../status/TRUST.md) and the [A–H program](../status/ROADMAP.md#approved-native-compatibility-program).
2. Follow [SCOPE → DESIGN → IMPLEMENT → REVIEW → VERIFY → DELIVER](DEVELOPMENT.md#engineering-workflow).
   The [xtask catalog](../../scripts/README.md#verification) owns executable
   commands; the workflow owns planning, review and evidence selection.
3. Use the relevant kernel/design reference for implementation details.
   `.claude/` is routing/configuration metadata, not a second status authority.
4. Keep current contracts, proposed designs and dated history distinct.
   Update bilingual summaries and dependent routes without rewriting old
   results or claiming that a parsed adapter is runtime-validated.

First-party documentation covers root entrypoints, `docs/`, `.claude/` and
classified `scripts/` reference-input/template documentation. All maintained
automation is Rust [xtask](../../xtask/), including script tests (`selftest`);
neither `scripts/` nor Markdown supplies another executable project workflow.
Current commands and
[documentation gate limits](../../scripts/README.md#documentation-checks-and-script-ownership)
are distinct from historical commands, design snippets and upstream ML probes.
Upstream `isabelle-source`, bundled theory/license texts, generated output and
runtime memory are not rewritten by a documentation refresh.
Run `cargo +stable xtask docs` and check changed configuration and reader paths;
integrated code delivery additionally uses `cargo +stable xtask verify`.
Then run the full global validator. Report inherited failures separately.
The earlier [dated package-A evidence](../status/PROJECT_STATUS.md#xtask-automation-cutover-2026-10-11)
does not verify today's tree. Native closure work has resumed but is not fully
accepted; official reference execution is disabled locally. Use the current
delivery record for scoped results, unresolved quality gates and the solver
cleanup blocker instead of copying historical results into current summaries.

## Directory Structure

```text
docs/
  adr/           Architecture Decision Records
  kernel/        Kernel TCB documentation
  design/        Design documents
  status/        Status, trust, and roadmap
  guides/        Developer guides
  archive/       Historical and superseded documents
  isip/          ISIP overview and ISIP-000 (later series are planned)
```

## Repository Entrypoints

| File | Description |
|------|-------------|
| [README](../../README.md) / [README.zh](../../README.zh.md) | Project introduction |
| [AGENTS](../../AGENTS.md) / [AGENTS.zh](../../AGENTS.zh.md) | Harness-neutral contributor rules |
| [CLAUDE](../../CLAUDE.md) | Claude adapter entrypoint |
| [CHANGELOG](../../CHANGELOG.md) | Historical changes |
| [scripts/README](../../scripts/README.md) | Maintained commands, CLI entrypoints and verification modes |
| [scripts/templates/README](../../scripts/templates/README.md) | Classified examples and design-only templates |

## ADRs — `docs/adr/`

| File | Status | Description |
|------|--------|-------------|
| [ADR-0001](../adr/ADR-0001-kernel-core-rewrite.md) | Accepted | Kernel/core rewrite boundary |
| [ADR-0002](../adr/ADR-0002-layered-platform-architecture.md) | Superseded | Original layered architecture |
| [ADR-0003](../adr/ADR-0003-hol-logic-trusted-extension.md) | Proposed | HOL logic trusted extension; narrow implementation checkpoint only |
| [ADR-0004](../adr/ADR-0004-layered-platform-architecture-v2.md) | Accepted | Layered platform v2 (B+C+G) |

## Kernel TCB — `docs/kernel/`

| File | Description |
|------|-------------|
| [KERNEL_PRIMITIVES](../kernel/KERNEL_PRIMITIVES.md) | Primitive rule catalog |
| [KERNEL_RULES](../kernel/KERNEL_RULES.md) | Kernel rule reference |
| [KERNEL_ATTACK_TESTS](../kernel/KERNEL_ATTACK_TESTS.md) | TCB attack test catalog |
| [KERNEL_TRUSTED_ACCEPTANCE_GAPS](../kernel/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md) | Remaining acceptance gaps |
| [BASELINE](../kernel/BASELINE.md) | First trusted-kernel engineering checkpoint |
| [MIGRATION_MATRIX](../kernel/MIGRATION_MATRIX.md) | Core-to-kernel migration tracking |
| [CORE_KERNEL_OVERLAP_INVENTORY](../kernel/CORE_KERNEL_OVERLAP_INVENTORY.md) | Core/kernel overlap inventory |
| [PROOF_OUTCOME_DESIGN](../kernel/PROOF_OUTCOME_DESIGN.md) | Proof outcome classifier |

## Design — `docs/design/`

| File | Description |
|------|-------------|
| [RESOLUTION_DESIGN](../design/RESOLUTION_DESIGN.md) | Resolution and rewriting design |
| [HPC_SYMBOLIC_COMPUTE_DESIGN](../design/HPC_SYMBOLIC_COMPUTE_DESIGN.md) | HPC symbolic compute design |
| [CHECKED_HOL_PROPOSITION_NORMALIZATION](../design/CHECKED_HOL_PROPOSITION_NORMALIZATION.md) | HOL proposition normalization |
| [CHECKED_DEFINITION_TRANSPORT](../design/CHECKED_DEFINITION_TRANSPORT.md) | Checked definition transport |
| [HOL_OBJECT_EQUALITY_BRIDGE](../design/HOL_OBJECT_EQUALITY_BRIDGE.md) | HOL object equality bridge |
| [NEXT_STRICT_SLICE_CANDIDATES](../design/NEXT_STRICT_SLICE_CANDIDATES.md) | Next strict slice candidates |
| [COMPAT_CALLSITES](../design/COMPAT_CALLSITES.md) | Compatibility callsite inventory |

## Status — `docs/status/`

| File | Description |
|------|-------------|
| [PROJECT_STATUS](../status/PROJECT_STATUS.md) | Canonical project status and metrics |
| [PROJECT_STATUS.zh](../status/PROJECT_STATUS.zh.md) | 项目状态（中文） |
| [TRUST](../status/TRUST.md) | Trust model and T1-T4 criteria |
| [ROADMAP](../status/ROADMAP.md) | A–H program and [next delivery dependencies/exit criteria](../status/ROADMAP.md#next-delivery-plan-2026-10-19) |
| [NATIVE_THM_INTERFACE_INVENTORY](../status/NATIVE_THM_INTERFACE_INVENTORY.md) | Fixed official THM signature mapped to Rust implementation, partial support and missing ML interfaces |

## Agent adapters — `.claude/`

| Location | Description |
|----------|-------------|
| [README](../../.claude/README.md) | Agent-adapter routing and limitations |
| [rules/](../../.claude/rules/) | Project-local rules |
| [skills/](../../.claude/skills/) | Project-local skills |
| [hooks/](../../.claude/hooks/) | Hooks |
| [commands/](../../.claude/commands/) | Commands |
| [agents/](../../.claude/agents/) | Agent definitions |
| [templates/](../../.claude/templates/) | Adapter templates |

## Guides — `docs/guides/`

| File | Description |
|------|-------------|
| [DEVELOPMENT](DEVELOPMENT.md) | Canonical engineering lifecycle, evidence selection, setup and runtime boundaries |
| [DOCUMENT_INDEX](DOCUMENT_INDEX.md) | This file |

## ISIP — `docs/isip/`

| File | Description |
|------|-------------|
| [ISIP](../isip/ISIP.md) | Standard suite overview |
| [ISIP.zh](../isip/ISIP.zh.md) | 标准体系总览（中文） |
| [ISIP-000](../isip/ISIP-000-architecture.md) | Architecture and trust boundary |
| [ISIP-000.zh](../isip/ISIP-000-architecture.zh.md) | 架构与可信边界（中文） |
| [README](../isip/README.md) | Existing specs and planned series |

## Archive — `docs/archive/`

| File | Description |
|------|-------------|
| [ARCHITECTURE](../archive/ARCHITECTURE.md) | Original architecture doc (superseded) |
| [GAP_ANALYSIS](../archive/GAP_ANALYSIS.md) | Early gap analysis (superseded) |
| [SESSION_TRANSFER](../archive/SESSION_TRANSFER.md) | Superseded session transfer note |
| [SESSION_TRANSFER_v1.9.0](../archive/SESSION_TRANSFER_v1.9.0.md) | Historical v1.9.0 session transfer |
