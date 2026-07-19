# CLAUDE.md — Isabelle-rs

Claude Code must follow the repository-wide rules in [AGENTS.md](AGENTS.md).
That file is authoritative for every agent harness; this file is only the
Claude-specific compatibility entry point.

## Canonical Reading Order

1. [AGENTS.md](AGENTS.md)
2. [docs/PROJECT_STATUS.md](docs/PROJECT_STATUS.md)
3. [docs/TRUST.md](docs/TRUST.md)
4. [docs/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md](docs/KERNEL_TRUSTED_ACCEPTANCE_GAPS.md)
5. [docs/ROADMAP.md](docs/ROADMAP.md)
6. [docs/KERNEL_RULES.md](docs/KERNEL_RULES.md)
7. [docs/KERNEL_ATTACK_TESTS.md](docs/KERNEL_ATTACK_TESTS.md)

Source code and tests in the current checkout override stale agent memory,
`.claude/` notes, or user-level `~/.codex` caches.

## Current Guardrails

```text
TransitionalStrictClosed: 1/125
KernelTrustedClosed:      0/125
```

The current `HOL::TrueI` result is a bool-valued legacy migration experiment,
not a context-bound `src/kernel::TrustedTheorem`.

Immutable context identity, exact-owner theorem acceptance, and the data-only
source proposition AST are implemented. The next slice is declaration-aware
source parsing and checked judgment/constant/type-scheme elaboration into
`CProp`. Do not implement `HOL::trans`, `hol_subst`, another theorem adapter,
or new trusted HOL proof power in `src/core`.

## Claude-Specific Routing

- `.claude/rules/` contains domain-specific compatibility rules.
- `.claude/skills/` and `.claude/commands/` are thin workflow adapters.
- `.claude/agents/` may perform bounded review; high-risk TCB changes still need
  independent evidence and the repository gates.
- Do not create commits, rewrite history, or push without explicit user
  instruction.

Use `scripts/dev-check.sh docs`, `strict`, `core`, and the theory modes rather
than copied command sequences. Short explanatory code blocks are allowed in
Markdown; large runnable or repeated examples belong in `scripts/` or
classified `scripts/templates/`.
