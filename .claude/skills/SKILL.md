---
description: Isabelle-rs skills architecture — design principles, lifecycle, contribution guide
category: meta
version: 2.1.0
---

# Isabelle-rs Skills Architecture

## Directory Structure

```
.claude/skills/
├── skills.toml          # Central registry: all skills with metadata
├── SKILL.md             # This file: architecture + lifecycle guide
├── verify.md            # Skill: verify lemma
├── debug-overflow.md    # Skill: debug stack overflow
├── audit-kernel.md      # Skill: audit kernel safety
├── add-method.md        # Skill: add proof method
├── add-isar-command.md  # Skill: add Isar command
├── port-isabelle.md     # Skill: port from Isabelle/ML
├── refactor.md          # Skill: safe refactoring
├── build-theory.md      # Skill: build theory files
├── search-db.md         # Skill: search theorem DB
├── bench.md             # Skill: run test matrix
└── release.md           # Skill: release phase
```

## Design Principles

1. **Trigger-driven** — Every skill has clear `triggers` in `skills.toml` that define when it fires
2. **Permission-aware** — Each skill declares required permissions in the registry
3. **Self-contained** — Skills are readable in one sitting (80-150 lines)
4. **Actionable** — Concrete commands and code snippets, not abstract advice
5. **Dependency-tracked** — Skills declare their `.claude/rules/` and skill dependencies
6. **Lifecycle-managed** — Every skill has a status, review interval, and version

## Skill Anatomy

Each skill file follows this structure:

```markdown
---
name: skill-name
description: One-line summary
category: category-name
version: X.Y.Z
---

# Skill Title

## When to Use
- Scenario list

## Workflow
### Step 1: ...
### Step 2: ...

## Reference / Patterns
(if applicable)

## Related
- `.claude/rules/xxx.md`
- `.claude/skills/yyy.md`
```

The canonical metadata lives in `skills.toml`. Skill file frontmatter is a subset for quick reference.

## Skill Lifecycle

```
experimental → active → deprecated → retired
```

### Lifecycle Rules
- **experimental**: New skill, limited testing. May have rough edges.
- **active**: In regular use. Must have all fields complete in `skills.toml`.
- **deprecated**: Being phased out. Skills using it should be updated.
- **retired**: Removed from active use. `skills.toml` entry kept with `status = "retired"` for history.

### Review Cadence
| Interval | For skills that... |
|----------|-------------------|
| 30 days | Frequently used, safety-critical (verify, audit-kernel) |
| 60 days | Used regularly, moderate impact (add-method, build-theory) |
| 90 days | Stable, low-frequency (refactor, release, search-db) |

### Adding a New Skill
1. Write `new-skill.md` following the anatomy above
2. Add entry to `skills.toml` with `status = "experimental"`
3. Add to `CLAUDE.md` skill index
4. After 2+ successful uses, promote to `active`

### Modifying a Skill
1. Update `skills.toml` version + `last_reviewed`
2. Update skill `.md` content
3. If breaking change: update all `related_skills` references in other skills
4. Update `CLAUDE.md` if name or description changed

## Categories

| Category | Purpose | Skills |
|----------|---------|--------|
| **verification** | Lemma verification, test running, failure diagnosis | verify |
| **debugging** | Stack overflow, performance, build errors | debug-overflow |
| **safety** | Kernel audits, type safety, LCF invariants | audit-kernel |
| **development** | Adding methods, commands, porting from ML, running the app | add-method, add-isar-command, port-isabelle, refactor, run-isabelle-rs |
| **theory** | Theory building, DB search, parse debugging | build-theory, search-db |
| **release** | Version bumps, changelog, doc sync | release |
| **maintenance** | Doc sync, code hygiene | sync-docs |
| **meta** | Benchmarks, test matrices | bench |

## Permission Model

Skills declare permissions in `skills.toml`. Claude Code uses these to request user approval when a skill invokes restricted tools.

| Permission | Tools Covered |
|-----------|--------------|
| `Bash:cargo build` | `cargo build` commands |
| `Bash:cargo test` | `cargo test` commands |
| `Bash:cargo check` | `cargo check` commands |
| `Bash:cargo clippy` | `cargo clippy` commands |
| `Bash:cargo fmt` | `cargo fmt` commands |
| `Bash:cargo run` | `cargo run` commands |
| `Bash:rg` | `rg` (ripgrep) commands |
| `Bash:git` | `git` commands |
| `Bash:RUST_MIN_STACK` | Commands using `RUST_MIN_STACK` env |
| `Read` | Reading source files |
| `Edit` | Modifying source files |
| `Grep` | Content search |
| `Write` | Creating new files |

## Related

- `CLAUDE.md` — Project entry point + skill index
- `.claude/rules/` — Domain and engineering rules referenced by skills
- `docs/` — Architecture, roadmap, gap analysis referenced by skills
