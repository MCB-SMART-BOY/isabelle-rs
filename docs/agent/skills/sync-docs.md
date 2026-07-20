---
name: Sync Documentation
description: Synchronize versioned agent rules and current trust/status documentation after semantic changes without rewriting historical snapshots.
category: maintenance
version: 3.0.0
triggers: [sync docs, update docs, doc sync, stale docs, after code change, update documentation]
permissions: [Read, Write, Edit, Bash:git, Bash:cargo]
---
# Sync Documentation

Start with root `AGENTS.md` and use `docs/PROJECT_STATUS.md` as the canonical
assessment. Synchronize README, trust/architecture/roadmap/attack docs,
`.claude/`, and Isabelle-rs-specific `~/.codex` references/rules/skills only
where their semantics changed.

Always distinguish `TransitionalStrictClosed` from `KernelTrustedClosed`, state
which kernel produced a theorem, and record actual verification results. Short
explanatory Bash/Rust/PowerShell/TOML/JSON blocks are allowed in Markdown;
large runnable or repeated examples belong in `scripts/` or classified
`scripts/templates/`. Standalone template compilation is not production API
validation. Run `scripts/dev-check.sh docs`, plus `strict` and theory modes when
source or trust semantics changed.
