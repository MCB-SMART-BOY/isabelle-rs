# Agent Documentation

This directory contains browsable copies of the `.claude/` configuration files
used by Claude Code and other coding agents.

**The authoritative source is `.claude/`** — these copies are provided for
documentation browsing. The `.claude/` directory is the active runtime
configuration; changes should be made there.

## Directory Mapping

| `.claude/` | `docs/agent/` | Purpose |
|------------|---------------|---------|
| `agents/` | [agents/](agents/) | Agent definitions (kernel-reviewer, port-reviewer, theory-parser) |
| `rules/` | [rules/](rules/) | Coding rules (kernel, code-quality, api-design, etc.) |
| `skills/` | [skills/](skills/) | Skill definitions (audit-kernel, verify, build-theory, etc.) |
| `hooks/` | [hooks/](hooks/) | Post-session hook documentation |
| `commands/` | [commands/](commands/) | Slash command definitions (audit, bench, fix, verify-all) |
| `templates/` | [templates/](templates/) | Rule, skill, and phase-plan templates |
| `README.md` | [CLAUDE_INTEGRATION.md](CLAUDE_INTEGRATION.md) | Claude Code integration guide |

## Relationship

`.claude/` is the directory Claude Code reads at runtime. It contains
`settings.json`, `skills.toml`, and the active rules/agents/hooks. This
`docs/agent/` directory is a documentation mirror for human readers browsing
the project on GitHub or locally.

To modify agent behavior, edit the files in `.claude/`, then run:

```bash
cp .claude/agents/*.md docs/agent/agents/
cp .claude/rules/*.md docs/agent/rules/
# ... etc
```

to keep this documentation copy in sync.
