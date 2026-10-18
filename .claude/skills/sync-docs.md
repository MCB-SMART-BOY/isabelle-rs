---
name: Sync Documentation
description: Synchronize versioned agent rules and current trust/status documentation after semantic changes without rewriting historical snapshots.
category: maintenance
version: 3.0.0
triggers: [sync docs, update docs, doc sync, stale docs, after code change, update documentation]
permissions: [Read, Write, Edit, Bash:git, Bash:cargo]
---
# Sync Documentation

Use the [`engineering workflow`](../../docs/guides/DEVELOPMENT.md#engineering-workflow)
rather than treating [`ROADMAP.md`](../../docs/status/ROADMAP.md) A–H product
stages as a second task lifecycle. Start with
root [`AGENTS.md`](../../AGENTS.md), [`PROJECT_STATUS.md`](../../docs/status/PROJECT_STATUS.md)
and [`TRUST.md`](../../docs/status/TRUST.md) as current assessments.
Synchronize README, trust/architecture/roadmap/attack docs, `.claude/`, and
agent references only where semantics changed. Do not rewrite historical
snapshots or promote search, Compat, or legacy Strict to kernel trust.

Record actual verification results and distinguish untested gates. Keep short
explanatory Rust/TOML/JSON/command examples in Markdown; maintained automation
belongs in `xtask/`, while `scripts/` retains official reference probe inputs
and classified design templates. Standalone template compilation does not
validate the production API. Use `cargo +stable xtask docs` for documentation
and `verify` for deterministic repository verification; `selftest` and external
security/global gates are independent. Source or trust changes additionally
need their applicable `strict`/`core` checks. Report failures separately.
