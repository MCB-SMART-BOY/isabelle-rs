# .claude — Isabelle-rs Project Configuration

Claude Code project configuration for the isabelle-rs proof assistant reimplementation.

## Directory Structure

```
.claude/
├── README.md               # This file
├── settings.json           # Project-wide settings (permissions, hooks, env)
├── settings.local.json     # User-local overrides (gitignored)
├── .gitignore              # Local files to exclude from git
│
├── commands/               # Custom slash commands
│   ├── verify-all.md       # /verify-all — full verification suite
│   ├── audit.md            # /audit — kernel safety audit
│   ├── bench.md            # /bench — test matrix benchmarks
│   └── fix.md              # /fix — auto-fix common issues
│
├── skills/                 # Domain-specific workflows
│   ├── skills.toml         # Central registry (all skill metadata)
│   ├── SKILL.md            # Architecture + lifecycle documentation
│   ├── verify.md           # Verify lemma(s) through 6-layer architecture
│   ├── debug-overflow.md   # Diagnose and fix stack overflows
│   ├── audit-kernel.md     # Kernel safety audit
│   ├── add-method.md       # Add proof method (4-step pattern)
│   ├── add-isar-command.md # Add Isar command (3-mode state machine)
│   ├── port-isabelle.md    # Port from Isabelle/ML to Rust
│   ├── refactor.md         # Safe refactoring (project-specific)
│   ├── build-theory.md     # Build and verify .thy files
│   ├── search-db.md        # Navigate HolTheoremDb (42K+ theorems)
│   ├── bench.md            # Run test matrix at correct stack sizes
│   └── release.md          # Phase SOP + doc sync
│
├── agents/                 # Custom subagent types
│   ├── kernel-reviewer.md  # LCF kernel code review specialist
│   ├── theory-parser.md    # Theory file parsing debugger
│   └── port-reviewer.md    # Isabelle/ML → Rust porting reviewer
│
├── memory/                 # Project-level persistent memory
│   └── .gitkeep
│
└── hooks/                  # Custom automation hooks
    └── README.md           # Hooks documentation
```

## Quick Reference

### Commands
| Command | Purpose |
|---------|---------|
| `/verify-all` | Run full verification test suite |
| `/audit` | Quick kernel safety scan |
| `/bench` | Run benchmark/test matrix |
| `/fix` | Auto-fix formatting, clippy, cargo fix |

### Skills
| Skill | Trigger |
|-------|---------|
| `verify` | Lemma verification failure, test failure |
| `debug-overflow` | Stack overflow, SIGABRT |
| `audit-kernel` | Kernel change, new inference rule |
| `add-method` | Add new proof method |
| `add-isar-command` | Add new Isar command |
| `port-isabelle` | Port ML code to Rust |
| `refactor` | Refactor ≥3 files |
| `build-theory` | .thy parse failure, batch compile |
| `search-db` | Find theorem by name/type/pattern |
| `bench` | Run tests, check regressions |
| `release` | Version bump, doc sync |

### Agents
| Agent | Use Case |
|-------|----------|
| `kernel-reviewer` | Review kernel code changes |
| `theory-parser` | Debug theory file parsing |
| `port-reviewer` | Review ML→Rust ported code |

## Related

- `../CLAUDE.md` — Project entry point and skill index
- `../.claude/rules/` — Domain and engineering rules
- `../docs/` — Architecture, roadmap, gap analysis
